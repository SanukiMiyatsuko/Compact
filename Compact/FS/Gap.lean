import Compact.FS.Tgt

/-! 隙間（`NatGap`）：`t` の真の部分項で `t` 未満のものは `t[n]` 未満。目標が `Ω_c` の崩壊 `t = Ψ^0_{Ω_c}(X)`。

* 後者の引数：`X` の部分項で `t` 未満のものは種 `Ψ^0(pred X)` 未満（`lt_seed_of_sub`）で、列は種以上。
* 極限の引数：加数 `R` の隙間から、`X` の節点の引数について「`X` 未満なら近似 `A_n` 未満」（大きさの議論と辞書式の区間、
  `Approx1.argCond_summand`）。`X` の前線が `t[n]` 未満なら移し替え（`HullHyp`）で隙間が出る。
* 素の近似が種 `p` を越えないとき、`p` は最後の加数で `p = Ψ^0_{Ω_c}(φ)`、`X < φ`。`p` の部分項は `Ψ^0(φ + 1)` との比較で
  `p` 未満（`seed_last`）。 -/

namespace RTKA.Fund

open Tm W

/-- 先頭の加数が主要項 `z` 未満なら全体も `z` 未満 -/
theorem lt_prin_of_head {v z h : Tm} {r : List Tm} (hs : summands v = h :: r)
    (hzp : isPrincipal z = true) (hp : isPrincipal h = true) (hlt : Lt h z) : Lt v z := by
  unfold Lt
  rw [cmp_eq, hs, summands_principal hzp]
  rw [lt_principal_iff hp hzp] at hlt
  exact cmpList_head_lt _ _ hlt

/-- 引数の部分項の比較は、加数の部分項の比較に帰着する -/
theorem lt_of_summands_sub {X t y v : Tm} (hX : WNF X) (htF : WNF t) (hy : isPrincipal y = true)
    (hy0 : y ≠ .zero) (h : ∀ s, s ∈ summands X → ∀ w, w ∈ subs s → Lt w t → Lt w y)
    (hv : v ∈ subs X) (hlt : Lt v t) : Lt v y := by
  have hvF := hX.of_mem_subs hv
  cases hs : summands v with
  | nil =>
    rw [eq_zero_of_summands_nil hs]
    exact zero_lt hy0
  | cons a r =>
    have hN := nfl_summands hvF
    have ham : a ∈ summands v := by
      rw [hs]
      exact List.mem_cons_self
    have hm := hN.1 a ham
    have hle : Le a v := by
      have := le_ofSummands_of_mem hN ham
      rwa [ofSummands_summands v hvF] at this
    obtain ⟨s, hsm, has⟩ := mem_subs_summand hm.2 (subs_trans hv (mem_subs_of_mem_summands ham))
    exact lt_prin_of_head hs hy hm.2 (h s hsm a has (lt_of_le_of_ltY hm.1 hvF htF hle hlt))

/-! ### 後者の引数 -/

namespace Approx1

variable {ξ π X P : Tm} {pre rest : List Tm} {R x : Tm}

/-- 種が前線の元なら、列は種より大きい -/
theorem hseed (H : Approx1 ξ π X P pre rest R x) (hp : P ∈ fr π P) :
    Lt P (.Psi ξ π (approx pre P x)) :=
  FWOrder.k2 H.hnf P (fr_oadd_of_right H.hpreF H.hy (fr_nsum_of_right H.hx H.hPF hp))

theorem hy0 (H : Approx1 ξ π X P pre rest R x) (hx0 : x ≠ .zero) : nsum x P ≠ .zero := by
  intro e
  have h := le_nsum_left H.hx H.hPF
  rw [e] at h
  rcases h with h | h
  · exact hx0 h
  · exact not_lt_zero _ h

/-- `pre` と `R` の中の節点の引数は、`X` 未満なら `A` 未満 -/
theorem argCond_summand (H : Approx1 ξ π X P pre rest R x) (t : Tm)
    (hx0 : x = .zero → ∀ v, v ∈ subs R → v = R)
    (hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v x) {s : Tm}
    (hs : s ∈ pre ∨ s = R) : ArgCond t X (approx pre P x) s := by
  have hsF : WNF s := by
    rcases hs with hs | rfl
    · exact (H.hN.1 s (List.mem_append_left _ hs)).1
    · exact H.hRF
  have hu : ∀ z a, z ∈ subs s → a ∈ subs z → a ≠ z → Lt a X → Lt a (approx pre P x) := by
    intro z a hz ha hne hlt
    have haF : WNF a := hsF.of_mem_subs (subs_trans hz ha)
    have hne' : a ≠ s :=
      ne_of_size_lt (Nat.lt_of_lt_of_le (size_lt_of_mem_subs_ne ha hne) (size_le_of_mem_subs hz))
    have hlt' : Lt a (ofSummands (pre ++ R :: rest)) := by
      rw [← H.hXeq]
      exact hlt
    rcases hs with hs | rfl
    · exact lt_pre_of_subs H.hN H.hy H.hyR hs (subs_trans hz ha) hne' haF hlt'
    · exact lt_approx_of_gap H.hN H.hy (H.hy0 fun e => hne' (hx0 e a (subs_trans hz ha))) H.hyR H.hx
        (le_nsum_left H.hx H.hPF) hgap (subs_trans hz ha) hne' haF hlt'
  refine ⟨fun s' k a hz _ hlt => hu _ a hz (subs_psi_a (self_mem_subs a)) ?_ hlt,
    fun m b hz _ hlt => hu _ b hz (subs_xi (self_mem_subs b)) ?_ hlt⟩
  · exact ne_of_size_lt (by simp only [Tm.size]; omega)
  · exact ne_of_size_lt (by simp only [Tm.size]; omega)

/-- 移し替えの仮定 -/
theorem hull (H : Approx1 ξ π X P pre rest R x) : HullHyp π X ξ π (approx pre P x) :=
  ⟨H.ht, H.hnf, Or.inl rfl, rfl, Or.inr H.hAlt, fun f hf => FWOrder.k2t H.hnf f hf⟩

/-- `pre`・`R` の部分項で `t` 未満のものは近似の崩壊未満 -/
theorem lt_of_sub_summand (H : Approx1 ξ π X P pre rest R x)
    (hx0 : x = .zero → ∀ v, v ∈ subs R → v = R)
    (hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v x)
    (hF : ∀ f, f ∈ fr π X → Lt f (.Psi ξ π (approx pre P x))) {s w : Tm}
    (hs : s ∈ pre ∨ s = R) (hw : w ∈ subs s) (hlt : Lt w (.Psi .zero π X)) :
    Lt w (.Psi ξ π (approx pre P x)) := by
  have hsF : WNF s := by
    rcases hs with hs | rfl
    · exact (H.hN.1 s (List.mem_append_left _ hs)).1
    · exact H.hRF
  exact H.hull.lt_of_lt (hsF.of_mem_subs hw) ((H.argCond_summand _ hx0 hgap hs).sub hw)
    (H.hull.arg2_of_fr hF (hsF.of_mem_subs hw)) hlt

end Approx1

/-- 主要項 `z` が `x` 未満なら、`x` の先頭の加数以下 -/
theorem le_head_of_prin_lt {z x h : Tm} {r : List Tm} (hz : WNF z) (hzp : isPrincipal z = true)
    (hx : WNF x) (hs : summands x = h :: r) (hlt : Lt z x) : Le z h := by
  have hm := (nfl_summands hx).1 h (by rw [hs]; exact List.mem_cons_self)
  by_cases hlt' : Lt h z
  · exact absurd (lt_prin_of_head hs hzp hm.2 hlt') (Lt.asymmY hz hx hlt)
  · exact le_of_not_ltY hm.1 hz hlt'

/-- 素の近似の 0 番目 `y₀` が種 `p`（最後の加数）未満なら、`p` の真の部分項で `t` 未満のものは `y₀` 未満 -/
theorem sub_lt_first {π X p x v : Tm} {pre : List Tm} (H : Approx1 .zero π X .zero pre [] p x)
    (hx0 : x = .zero → ∀ v, v ∈ subs p → v = p)
    (hG : ∀ v, v ∈ subs p → v ≠ p → Lt v p → Lt v x)
    (hlt : Lt (.Psi .zero π (approx pre .zero x)) p) (hpπ : Lt p π)
    (hpt : Lt p (.Psi .zero π X))
    (hfr : ∀ f, f ∈ fr π X → Le f p) (hv : v ∈ subs p) (hne : v ≠ p)
    (hvt : Lt v (.Psi .zero π X)) : Lt v (.Psi .zero π (approx pre .zero x)) := by
  have ht := H.ht
  have hX := H.hX
  have hπF := H.hπF
  have hpF := H.hRF
  have hy := H.hnf
  have hA := H.hAF
  have hvF := hpF.of_mem_subs hv
  have hsize := size_lt_of_mem_subs_ne hv hne
  refine H.hull.lt_of_lt hvF ((H.argCond_summand _ hx0 hG (Or.inr rfl)).sub hv) ?_ hvt
  intro s k a hz hzt hXa hyz
  have hzF : WNF (.Psi s k a) := hvF.of_mem_subs hz
  have hzs : Tm.Psi s k a ∈ subs p := subs_trans hv hz
  have hzne : Tm.Psi s k a ≠ p :=
    ne_of_size_lt (Nat.lt_of_le_of_lt (size_le_of_mem_subs hz) hsize)
  have hzπ : Lt (.Psi s k a) π := lt_transY hzF ht hπF hzt (lt_psi_targetY ht)
  by_cases hf : ∀ f, f ∈ fr π X → Lt f (.Psi s k a)
  · exact Or.inl ((inC_frY hX hπF hzF hX hzF.psi.aF ht.psi.Ca (Or.inr hzπ) hXa).mpr fun w hw =>
      WFY.inC_of_ltY _ (hX.of_mem_subs (fr_spec hw).1) hzF (hf w hw))
  · obtain ⟨f, hfm, hfz⟩ : ∃ f, f ∈ fr π X ∧ ¬ Lt f (.Psi s k a) :=
      Classical.byContradiction fun hn => hf fun f hfm =>
        Classical.byContradiction fun hl => hn ⟨f, hfm, hl⟩
    have hfF := hX.of_mem_subs (fr_spec hfm).1
    have hzp : Lt (.Psi s k a) p :=
      (le_transY hzF hfF hpF (le_of_not_ltY hfF hzF hfz) (hfr f hfm)).resolve_left hzne
    have hAX := H.hAlt
    have hyne : Tm.Psi .zero π (approx pre .zero x) ≠ .Psi s k a := fun e => by
      cases e
      exact not_lt_of_leY hX hA hXa hAX
    have hyz' : Lt (.Psi .zero π (approx pre .zero x)) (.Psi s k a) := hyz.resolve_left hyne
    have hl : lev π = lev k := by
      have h1 : lev k ≤ lev π := show lev (Tm.Psi s k a) ≤ lev π from lev_le_of_lt_gen hzπ
      rcases Nat.lt_or_eq_of_le h1 with h2 | h2
      · exact absurd (lt_of_lev_lt' (a := .Psi s k a) (b := .Psi .zero π (approx pre .zero x)) h2)
          (not_lt_of_leY hy hzF hyz)
      · exact h2.symm
    have hAa : Lt (approx pre .zero x) a ∧ inC (approx pre .zero x) a (.Psi s k a) = true := by
      rcases (lt_psi_psiY hl hyne).mp hyz' with h1 | ⟨-, -, hc | hc | hc | hc⟩
      · exact absurd hzπ h1
      · exact ⟨hc.1, hc.2.1⟩
      · exact absurd (lt_of_lt_of_leY hA hX hzF.psi.aF hAX hXa)
          (not_lt_of_leY hzF.psi.aF hA (le_of_ne_gtY hzF.psi.aF hA hc.1))
      · have e := FWOrder.eq hA hzF.psi.aF hc.1
        rw [e] at hAX
        exact absurd hAX (not_lt_of_leY hX hzF.psi.aF hXa)
      · exact absurd hc.1 (not_lt_zero _)
    have hxC : inC x a (.Psi s k a) = true := by
      have h1 : inC (nsum x .zero) a (.Psi s k a) = true :=
        (inC_iff_summands H.hy).mpr fun q hq =>
          inC_of_mem_summands hA hAa.2 (mem_summands_oadd_right H.hpreF H.hy hq)
      exact inC_nsum_left H.hx WNF.zero h1
    have hzx : Lt (.Psi s k a) x := hG _ hzs hzne hzp
    cases hsx : summands x with
    | nil =>
      rw [eq_zero_of_summands_nil hsx] at hzx
      exact absurd hzx (not_lt_zero _)
    | cons h r =>
      have hhm := (nfl_summands H.hx).1 h (by rw [hsx]; exact List.mem_cons_self)
      have hzh := le_head_of_prin_lt hzF rfl H.hx hsx hzx
      have hhC : inC h a (.Psi s k a) = true :=
        inC_of_mem_summands H.hx hxC (by rw [hsx]; exact List.mem_cons_self)
      have hhx : Le h x := by
        have := le_ofSummands_of_mem (nfl_summands H.hx) (by rw [hsx]; exact List.mem_cons_self : h ∈ summands x)
        rwa [ofSummands_summands x H.hx] at this
      have hhp : Lt h p := lt_of_le_of_ltY hhm.1 H.hx hpF hhx H.hxR
      by_cases hhk : Lt h k
      · exfalso
        obtain ⟨s₂, a₂, hmem, ha₂, hw, hvis⟩ := above_coll hzF _ (Nat.le_refl _) hhm.1 hhk hzh
        have hwF := hhm.1.of_mem_subs hmem
        rcases inC_psi_iff.mp (hvis a _ hzF (Or.inl rfl) hhC) with h5 | ⟨-, -, -, h6⟩
        · exact absurd h5 (not_lt_of_leY hzF hwF hw)
        · exact absurd h6 (not_lt_of_leY hzF.psi.aF hwF.psi.aF ha₂)
      · exact Or.inr (lt_of_le_of_ltY hzF.psi.piF hhm.1 ht (le_of_not_ltY hhm.1 hzF.psi.piF hhk)
          (lt_transY hhm.1 hpF ht hhp hpt))

/-- 共終数 `ω` の列の不変量 -/
def NatInv (t : Tm) (s : SeqD) : Prop := NatUB t s ∧ NatGap t s

/-! ### 極限の引数 -/

theorem maxL_none {l : List Tm} (h : maxL l = none) : l = [] := by
  cases l with
  | nil => rfl
  | cons x xs =>
    simp only [maxL] at h
    split at h
    · cases h
    · split at h <;> cases h

/-- 最大の元以下 -/
theorem le_maxL : ∀ {l : List Tm} {p f : Tm}, (∀ x, x ∈ l → WNF x) → maxL l = some p → f ∈ l → Le f p
  | [], _, _, _, h, _ => by simp [maxL] at h
  | x :: xs, p, f, hw, h, hf => by
    have hxF := hw x List.mem_cons_self
    have hxs : ∀ y, y ∈ xs → WNF y := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    simp only [maxL] at h
    cases e : maxL xs with
    | none =>
      rw [e] at h
      simp only [Option.some.injEq] at h
      subst h
      rw [maxL_none e] at hf
      rw [List.mem_singleton.mp hf]
      exact Or.inl rfl
    | some y =>
      rw [e] at h
      simp only at h
      have hyF : WNF y := hxs y (maxL_mem e)
      split at h
      · rename_i hlt
        simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hf with rfl | hf
        · exact Or.inr (ltB_iff.mp hlt)
        · exact le_maxL hxs e hf
      · rename_i hlt
        simp only [Option.some.injEq] at h
        subst h
        have hyx : Le y x := le_of_not_ltY hxF hyF (fun h' => hlt (ltB_iff.mpr h'))
        rcases List.mem_cons.mp hf with rfl | hf
        · exact Or.inl rfl
        · have hfF : WNF f := hxs f hf
          exact le_transY hfF hyF hxF (le_maxL hxs e hf) hyx

/-- 単調な列の項は 0 番目以上 -/
theorem le_of_mono {y : Nat → Tm} (hF : ∀ n, WNF (y n)) (h : ∀ n, Lt (y n) (y (n + 1))) :
    ∀ n, Le (y 0) (y n)
  | 0 => Or.inl rfl
  | n + 1 => Or.inr (lt_of_le_of_ltY (hF 0) (hF n) (hF (n + 1)) (le_of_mono hF h n) (h n))

theorem first_app_of_not_big {τ : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD} {P c : Tm}
    (hdom : ∀ σ, r.dom ≠ .big σ) :
    (SeqD.app τ g pre R r P c).first = (SeqD.app τ g pre R r P c).nat 0 := by
  unfold SeqD.first
  have : (SeqD.app τ g pre R r P c).dom = (Cof.omega : Cof Tm) := by
    show (match r.dom with
      | Cof.big σ => if ltB σ τ then Cof.big σ else Cof.omega
      | _ => Cof.omega : Cof Tm) = _
    split
    · rename_i σ h
      exact absurd h (hdom σ)
    · rfl
  rw [this]

theorem getLast?_append_cons₂ {α : Type} : ∀ (L : List α) (a b : α) (t : List α),
    (L ++ a :: b :: t).getLast? = (b :: t).getLast?
  | [], a, b, t => by simp [List.getLast?_cons_cons]
  | x :: xs, a, b, t => by
    show (x :: (xs ++ a :: b :: t)).getLast? = _
    have hne : xs ++ a :: b :: t ≠ [] := by simp
    obtain ⟨y, ys, e⟩ := List.exists_cons_of_ne_nil hne
    rw [e, List.getLast?_cons_cons, ← e]
    exact getLast?_append_cons₂ xs a b t

end RTKA.Fund
