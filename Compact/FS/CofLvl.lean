import Compact.FS.CofLim

/-! 共終性の一歩：`x < t` の節点を目標で分ける。

* `node_arg'`：`x < y` でなければ、`x` の目標 `k` は `t` より大きく `C(X, t)` に入る（したがって `π` 以上）。
* 目標が列の項の目標 `τ` より小さい節点は下の段（仮定 `hlow`）、等しい節点は段の節点（引数が `T` 未満なら `ArgS`、
  そうでなければ仮定 `hN`）、大きい節点は `tgt_wit`（`a ≤ r(τ) < A` か隙間）。
* 共終数が大きい列は `cof_big`：`x < σ` なら閉じた点 `β` の下、`σ ≤ x` なら部分項の前線は `x` の前線に入る。 -/

namespace RTKA.Fund

open Tm W

/-- 節点の目標 -/
def tgtN : Tm → Tm
  | .Psi _ k _ => k
  | .Xi j _ => .K j
  | _ => .zero

/-- `node_arg` に目標の情報を足したもの -/
theorem node_arg' {π X y A T x : Tm} (ht : WNF (.Psi .zero π X)) (C : Clo y A T)
    (htT : Lt (.Psi .zero π X) T) (hG : Gp (.Psi .zero π X) y) (hx : WNF x)
    (hxt : Lt x (.Psi .zero π X)) (hF : ∀ w, w ∈ parF x → Lt w y)
    (hk : ∀ s k a, x = .Psi s k a → Lt k (.Psi .zero π X) → Lt k y) :
    Lt x y ∨ ∃ a, argR? x = some a ∧ Lt a X ∧ inC a a (.Psi .zero π X) = true ∧
      (∀ u, u ∈ fr (.Psi .zero π X) a → u ∈ parF x) ∧ Lt (.Psi .zero π X) (tgtN x) ∧
      inC (tgtN x) X (.Psi .zero π X) = true := by
  have hxT := lt_transY hx ht C.hT hxt htT
  have hy := C.hy
  have hlow : ∀ w, w ∈ parF x → Lt w (.Psi .zero π X) := fun w hw =>
    lt_transY (hx.of_mem_subs (parL_sub (parF_sub_parL hw)).1) hx ht (parF_lt hx hw) hxt
  cases x with
  | Psi s k a =>
    have hP := hx.psi
    rcases below_psi ht hx hxt with h | ⟨w, hw, hle⟩ | ⟨htk, h, -, -, hkC⟩
    · exact Or.inl (lt_transY hx hP.piF hy (lt_psi_targetY hx) (hk s k a rfl h))
    · have hwy := gp_fr ht hG hw
      have hwF : WNF w := by
        rcases hw with hw | hw
        · exact ht.psi.aF.of_mem_subs (fr_spec hw).1
        · exact ht.psi.piF.of_mem_subs (fr_spec hw).1
      exact Or.inl (lt_of_le_of_ltY hx hwF hy hle hwy)
    · have hfr : ∀ w, w ∈ fr k a → w ∈ parF (.Psi s k a) := fun w hw => by simp [parF, hw]
      refine Or.inr ⟨a, rfl, h, ?_,
        fun u hu => hfr u (fr_up ht hP.piF htk hP.aF (fun w hw => hlow w (hfr w hw)) hu), htk, hkC⟩
      exact inC_of_fr_lt hP.aF hP.piF ht hP.aF hP.aF hP.Ca (Or.inr htk) (Or.inl rfl)
        fun w hw => hlow w (hfr w hw)
  | Xi j b =>
    obtain ⟨hj, hbF, -, -, hbC⟩ := hx.xi
    have hKF := WNF.K' hj
    rcases below_xi ht hx hxt with h | ⟨w, hw, hle⟩ | ⟨htK, h, -⟩
    · have h1 : Lt (.K j) y := C.coll _ hKF (inC_K _ _ _) (lt_transY hKF ht C.hT h htT)
      exact Or.inl (lt_transY hx hKF hy ((lt_K_iffY hx hj).mpr (Nat.le_refl _)) h1)
    · have hwy := gp_fr ht hG (Or.inr hw)
      exact Or.inl (lt_of_le_of_ltY hx (ht.psi.piF.of_mem_subs (fr_spec hw).1) hy hle hwy)
    · refine Or.inr ⟨b, rfl, h, ?_, fun u hu => fr_up ht hKF htK hbF (fun w hw => hlow w hw) hu, htK,
        inC_K _ _ _⟩
      exact inC_of_fr_lt hbF hKF ht hbF hbF hbC (Or.inr htK) (Or.inl rfl) fun w hw => hlow w hw
  | _ => exact Or.inl (C.lt hx hxT hF fun _ e => by cases e)

/-- 節点の目標は標準形 -/
theorem tgtN_wnf {x a : Tm} (hx : WNF x) (h : argR? x = some a) : WNF (tgtN x) := by
  cases x with
  | Psi s k a' => exact hx.psi.piF
  | Xi j b => exact WNF.K' hx.xi.1
  | _ => cases h

/-- 節点は自分の目標への崩壊 -/
theorem clo_node {x a : Tm} (hx : WNF x) (h : argR? x = some a) : Clo x a (tgtN x) := by
  cases x with
  | Psi s k a' =>
    cases h
    exact Clo.psi hx
  | Xi j b =>
    cases h
    exact Clo.xi hx
  | _ => cases h

/-- `C(X, t)` の目標で `t` より大きいものは `π` 以上 -/
theorem tgt_ge {π X k : Tm} (ht : WNF (.Psi .zero π X)) (hkF : WNF k) (htk : Lt (.Psi .zero π X) k)
    (hkC : inC k X (.Psi .zero π X) = true) : Le π k :=
  le_of_not_ltY hkF ht.psi.piF fun h => Lt.asymmY ht hkF htk (coll_psiY ht k hkF hkC h)

/-! ### 前線の前線 -/

theorem fr_fr {σ k : Tm} (hσ : WNF σ) (hk : WNF k) (hσk : Le σ k) :
    ∀ {a w f : Tm}, WNF a → w ∈ fr k a → f ∈ fr σ w → f ∈ fr σ a
  | .zero, _, _, _, h, _ | .one, _, _, _, h, _ | .K _, _, _, _, h, _ => by simp [fr] at h
  | .plus a b, w, f, ha, h, hf => by
    obtain ⟨h1, h2, -, -⟩ := ha.plus
    rw [fr, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (fr_fr hσ hk hσk h1 h hf)
    · exact Or.inr (fr_fr hσ hk hσk h2 h hf)
  | .Om a, w, f, ha, h, hf => by
    rw [fr] at h ⊢
    exact fr_fr hσ hk hσk ha.om.1 h hf
  | .Xi m a, w, f, ha, h, hf => by
    rw [fr] at h
    by_cases h1 : Lt (.Xi m a) k
    · simp only [h1, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact hf
    · simp only [h1, ↓reduceIte] at h
      have h2 : ¬ Lt (.Xi m a) σ := fun h' => h1 (lt_of_lt_of_leY ha hσ hk h' hσk)
      rw [fr]
      simp only [h2, ↓reduceIte]
      exact fr_fr hσ hk hσk ha.xi.2.1 h hf
  | .Psi s p a, w, f, ha, h, hf => by
    rw [fr] at h
    by_cases h1 : Lt (.Psi s p a) k
    · simp only [h1, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact hf
    · simp only [h1, ↓reduceIte, List.mem_append] at h
      have h2 : ¬ Lt (.Psi s p a) σ := fun h' => h1 (lt_of_lt_of_leY ha hσ hk h' hσk)
      rw [fr]
      simp only [h2, ↓reduceIte, List.mem_append]
      have hP := ha.psi
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (fr_fr hσ hk hσk hP.xiF h hf))
      · exact Or.inl (Or.inr (fr_fr hσ hk hσk hP.piF h hf))
      · exact Or.inr (fr_fr hσ hk hσk hP.aF h hf)

/-- `σ ≤ x` なら、`x` の部分項の前線は `x` の前線 -/
theorem parL_fr {σ : Tm} (hσ : WNF σ) :
    ∀ {x w f : Tm}, WNF x → Le σ x → w ∈ parL x → f ∈ fr σ w → f ∈ fr σ x
  | .zero, _, _, _, _, h, _ | .one, _, _, _, _, h, _ | .K _, _, _, _, _, h, _ => by simp [parL, parF] at h
  | .plus a b, w, f, _, _, h, hf => by
    simp only [parL, parF, List.mem_cons, List.not_mem_nil, or_false] at h
    rw [fr, List.mem_append]
    rcases h with rfl | rfl
    · exact Or.inl hf
    · exact Or.inr hf
  | .Om e, w, f, _, _, h, hf => by
    simp only [parL, parF, List.mem_singleton] at h
    subst h
    rw [fr]
    exact hf
  | .Xi j b, w, f, hx, hσx, h, hf => by
    have hj := hx.xi.1
    have hKF := WNF.K' hj
    have hxK : Lt (.Xi j b) (.K j) := (lt_K_iffY hx hj).mpr (Nat.le_refl _)
    have h2 : ¬ Lt (.Xi j b) σ := not_lt_of_leY hσ hx hσx
    rw [fr]
    simp only [h2, ↓reduceIte]
    exact fr_fr hσ hKF (le_transY hσ hx hKF hσx (Or.inr hxK)) hx.xi.2.1 h hf
  | .Psi s k a, w, f, hx, hσx, h, hf => by
    have hP := hx.psi
    have hσk : Le σ k := le_transY hσ hx hP.piF hσx (Or.inr (lt_psi_targetY hx))
    have h2 : ¬ Lt (.Psi s k a) σ := not_lt_of_leY hσ hx hσx
    rw [fr]
    simp only [h2, ↓reduceIte, List.mem_append]
    simp only [parL, List.mem_cons, List.mem_append] at h
    rcases h with rfl | (h | h) | h
    · exact Or.inl (Or.inr hf)
    · exact Or.inr (fr_fr hσ hP.piF hσk hP.aF h hf)
    · exact Or.inl (Or.inl (fr_fr hσ hP.piF hσk hP.xiF h hf))
    · exact Or.inl (Or.inr (fr_fr hσ hP.piF hσk hP.piF h hf))

/-- 引数の前線は節点の前線（節点が `σ` 以上のとき） -/
theorem fr_arg {σ x a f : Tm} (hσ : WNF σ) (hx : WNF x) (hσx : Le σ x) (h : argR? x = some a)
    (hf : f ∈ fr σ a) : f ∈ fr σ x := by
  cases x with
  | Psi s k a' =>
    cases h
    have h2 : ¬ Lt (.Psi s k a) σ := not_lt_of_leY hσ hx hσx
    rw [fr]
    simp only [h2, ↓reduceIte, List.mem_append]
    exact Or.inr hf
  | Xi j b =>
    cases h
    have h2 : ¬ Lt (.Xi j a) σ := not_lt_of_leY hσ hx hσx
    rw [fr]
    simp only [h2, ↓reduceIte]
    exact hf
  | _ => cases h

/-- 共終数が大きい列の共終性の帰納法 -/
theorem cof_big {t σ : Tm} {Y : Tm → Tm} (hσF : WNF σ)
    (hβY : ∀ β, WNF β → Lt β σ → Cl σ β → Le β (Y β)) (hYF : ∀ β, WNF β → Lt β σ → WNF (Y β))
    (hstep : ∀ x β, WNF x → Lt x t → WNF β → Lt β σ → Cl σ β → (∀ f, f ∈ fr σ x → Lt f β) →
      Le σ x → (∀ w, w ∈ parL x → Lt w t → Lt w (Y β)) → Lt x (Y β)) :
    ∀ x β, WNF x → Lt x t → WNF β → Lt β σ → Cl σ β → (∀ f, f ∈ fr σ x → Lt f β) → Lt x (Y β) := by
  intro x
  induction hn : x.size using Nat.strongRecOn generalizing x with
  | ind n ih =>
    intro β hx hxt hβ hβσ hCl hfr
    by_cases hxσ : Lt x σ
    · exact lt_of_lt_of_leY hx hβ (hYF β hβ hβσ) (hCl.2 x hx hxσ hfr) (hβY β hβ hβσ hCl)
    have hσx : Le σ x := le_of_not_ltY hx hσF hxσ
    refine hstep x β hx hxt hβ hβσ hCl hfr hσx fun w hw hwt => ?_
    obtain ⟨h1, h2⟩ := parL_sub hw
    exact ih w.size (by omega) w rfl β (hx.of_mem_subs h1) hwt hβ hβσ hCl
      fun f hf => hfr f (parL_fr hσF hx hσx hw hf)

/-! ### 葉の一歩 -/

/-- 列の項 `y = Ψ^ξ_τ(A)` の一歩：節点の目標で分ける -/
theorem leaf_one {π X ξ τ A y x : Tm} (ht : WNF (.Psi .zero π X)) (hτt : IsTgt τ) (hπτ : Le π τ)
    (hτfr : ∀ u, u ∈ fr τ τ → u ∈ fr π π) (hy : WNF y) (hyA : y = .Psi ξ τ A)
    (hG : Gp (.Psi .zero π X) y) (hx : WNF x) (hxt : Lt x (.Psi .zero π X))
    (hpar : ∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w y) :
    Lt x y ∨ ∃ a, argR? x = some a ∧ Lt a X ∧ inC a a (.Psi .zero π X) = true ∧
      (∀ u, u ∈ fr (.Psi .zero π X) a → Lt u y) ∧ Lt (.Psi .zero π X) (tgtN x) ∧ Le π (tgtN x) ∧
      (Lt (tgtN x) τ ∨ ∃ s, x = .Psi s τ a) := by
  subst hyA
  have hP := hy.psi
  have hτF := hP.piF
  have hπF := ht.psi.piF
  have C := Clo.psi hy
  have htτ : Lt (.Psi .zero π X) τ := lt_of_lt_of_leY ht hπF hτF (lt_psi_targetY ht) hπτ
  have hF : ∀ w, w ∈ parF x → Lt w (.Psi ξ τ A) := fun w hw =>
    hpar w (parF_sub_parL hw)
      (lt_transY (hx.of_mem_subs (parL_sub (parF_sub_parL hw)).1) hx ht (parF_lt hx hw) hxt)
  have hk : ∀ s k a, x = .Psi s k a → Lt k (.Psi .zero π X) → Lt k (.Psi ξ τ A) := fun s k a e h =>
    hpar k (by subst e; exact List.mem_cons_self) h
  rcases node_arg' ht C htτ hG hx hxt hF hk with h | ⟨a, harg, haX, haC, hafr, htk, hkC⟩
  · exact Or.inl h
  have hkF := tgtN_wnf hx harg
  have hπk := tgt_ge ht hkF htk hkC
  have hxτ : Lt x τ := lt_transY hx ht hτF hxt htτ
  rcases triY hkF hτF with hkτ | hkτ | hkτ
  · exact Or.inr ⟨a, harg, haX, haC, fun u hu => hF u (hafr u hu), htk, hπk, Or.inl hkτ⟩
  · refine Or.inr ⟨a, harg, haX, haC, fun u hu => hF u (hafr u hu), htk, hπk, Or.inr ?_⟩
    cases x with
    | Psi s k a' =>
      cases harg
      exact ⟨s, by rw [show k = τ from hkτ]⟩
    | Xi j b =>
      exact absurd hkτ.symm (IsTgt.ne_K hτt j)
    | _ => cases harg
  · -- 目標が `τ` より大きい：`a ≤ r(τ) < A` か隙間
    have Cx := clo_node hx harg
    rcases tgt_wit hτF hτt Cx hxτ hkτ with ⟨r, hr, har⟩ | ⟨u, hu, hxu⟩
    · refine Or.inl (C.lt hx hxτ hF fun a' e => ?_)
      rw [harg] at e
      cases e
      exact lt_of_le_of_ltY (wnf_of_argR hx harg) (wnf_of_argR hτF hr) hP.aF har (arg_lt_of_psi hy hr)
    · have huF := hτF.of_mem_subs (fr_spec hu).1
      exact Or.inl (lt_of_le_of_ltY hx huF hy hxu (gp_fr ht hG (Or.inr (hτfr u hu))))

/-- `ω` 型の崩壊の列の共終性：段の節点で引数が `T` 未満なら `ArgS`、そうでなければ `hN`、下の段は `hlow` -/
theorem leaf_nat {π X ξ τ T : Tm} {s : SeqD} (ht : WNF (.Psi .zero π X)) (hτt : IsTgt τ) (hπτ : Le π τ)
    (hτfr : ∀ u, u ∈ fr τ τ → u ∈ fr π π) (hI : NatInv (.Psi .zero π X) s)
    (hform : ∀ n, ∃ A, s.nat n = .Psi ξ τ A) (hS : ArgS (.Psi .zero π X) T ξ τ s)
    (hlow : ∀ x N, WNF x → Lt x (.Psi .zero π X) →
      (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w (s.nat N)) →
      Lt (.Psi .zero π X) (tgtN x) → Lt (tgtN x) τ → Le π (tgtN x) → ∃ n, Lt x (s.nat n))
    (hN : ∀ x N, WNF x → Lt x (.Psi .zero π X) →
      (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w (s.nat N)) →
      ∀ s' a, x = .Psi s' τ a → Lt a X → ¬ Lt a T → ∃ n, Lt x (s.nat n)) :
    ∀ x, WNF x → Lt x (.Psi .zero π X) → ∃ n, Lt x (s.nat n) := by
  have hyF : ∀ n, WNF (s.nat n) := fun n => (hI.1.good n).1
  have hm : ∀ n, Lt (s.nat n) (s.nat (n + 1)) := fun n => (hI.1.good n).2.2
  refine cof_nat hyF hm fun x hx hxt N hpar => ?_
  obtain ⟨A, hA⟩ := hform N
  rcases leaf_one ht hτt hπτ hτfr (hyF N) hA (fun v hv hne hl => hI.2 N v hv hne hl) hx hxt hpar with
    h | ⟨a, harg, haX, haC, hafr, htk, hπk, hkτ | ⟨s', rfl⟩⟩
  · exact ⟨N, h⟩
  · exact hlow x N hx hxt hpar htk hkτ hπk
  · have haF := wnf_of_argR hx harg
    by_cases haT : Lt a T
    · obtain ⟨n, B, hNn, hB, haB⟩ := hS a N haF haT haC hafr
      have hyn := hyF n
      rw [hB] at hyn
      have Cn := Clo.psi hyn
      refine ⟨n, ?_⟩
      rw [hB]
      have hτF := hyn.psi.piF
      exact Cn.lt hx (lt_transY hx ht hτF hxt (lt_of_lt_of_leY ht ht.psi.piF hτF (lt_psi_targetY ht) hπτ))
        (fun w hw => by
          have hwt := lt_transY (hx.of_mem_subs (parL_sub (parF_sub_parL hw)).1) hx ht (parF_lt hx hw) hxt
          have h1 := hpar w (parF_sub_parL hw) hwt
          rw [← hB]
          exact lt_of_lt_of_leY (hx.of_mem_subs (parL_sub (parF_sub_parL hw)).1) (hyF N) (hyF n) h1
            (mono_le hyF hm hNn))
        fun a' e => by
          cases harg
          cases e
          exact haB
    · exact hN _ N hx hxt hpar s' a rfl haX haT

end RTKA.Fund
