import Compact.WF.FYL1

/-! 断片 `FY` の順序の性質の証明：新しい項 `t` との反対称性の枠組みと、前線の片方向の言い換え。

* `inC_of_fr`・`fr_of_inC`・`wit_of_not_inC`：前線による `C` への所属の片方向ずつの言い換え。
  `FX` の `inC_fr` と違い、向きごとに必要な仮定だけを取る。
* `fr_subG`：前線の取り替え（順序の仮定の代わりに部分項についての推移性を仮定）。
* `coll_xi0`：`Ξ_n(γ)` の崩壊の性質（順序の仮定なしで成り立つ）。`GoodY.coll_psi`：`Ψ^0_π(γ)` の崩壊の性質
  （`π ∈ S` なら、`t` が `S` に入らなくてもよい）。
* `GoodY.ne_new`：`S` の元と新しい項 `t` の `cmp` は `.eq` にならない。
* `GoodY.anti_new`：`Ψ` どうしの場合の反対称性を仮定すれば、`t` は `S` の全ての元と反対称。
* `linOn_of_cutY`：反対称性と切断性から推移性へ。 -/

namespace RTKA

open Tm

/-! ### 前線の片方向の言い換え -/

/-- 前線の各節点が `C(g, d)` に入り、`R` 以上の節点の引数が `g0` 未満（したがって `g` 未満）なら、
    `x ∈ C(g, d)` -/
theorem inC_of_fr {R g0 g d : Tm} : ∀ x : Tm, inC x g0 R = true →
    (∀ v, v ∈ subs x → Lt v g0 → Lt v g) →
    (∀ w, w ∈ fr R x → inC w g d = true) → inC x g d = true
  | .zero, _, _, _ => inC_zero _ _
  | .one, _, _, _ => inC_one _ _
  | .K n, _, _, _ => inC_K n _ _
  | .plus a b, h0, hg, hw => by
    rw [inC_plus, Bool.and_eq_true] at h0 ⊢
    exact ⟨inC_of_fr a h0.1 (fun v hv => hg v (subs_plus_l hv))
        (fun w h => hw w (by rw [fr, List.mem_append]; exact Or.inl h)),
      inC_of_fr b h0.2 (fun v hv => hg v (subs_plus_r hv))
        (fun w h => hw w (by rw [fr, List.mem_append]; exact Or.inr h))⟩
  | .Om a, h0, hg, hw => by
    rw [inC_om] at h0 ⊢
    exact inC_of_fr a h0 (fun v hv => hg v (subs_om hv)) (fun w h => hw w (by rw [fr]; exact h))
  | .Xi m a, h0, hg, hw => by
    by_cases hR : Lt (.Xi m a) R
    · exact hw _ (by rw [fr]; simp [hR])
    · rcases inC_xi_iff.mp h0 with h | ⟨ha, hlt⟩
      · exact absurd h hR
      · exact inC_xi_iff.mpr (Or.inr ⟨inC_of_fr a ha (fun v hv => hg v (subs_xi hv))
          (fun w h => hw w (by rw [fr]; simp only [hR, ↓reduceIte]; exact h)),
          hg a (mem_subs_xi m a) hlt⟩)
  | .Psi s p a, h0, hg, hw => by
    by_cases hR : Lt (.Psi s p a) R
    · exact hw _ (by rw [fr]; simp [hR])
    · rcases inC_psi_iff.mp h0 with h | ⟨hp, hs, ha, hlt⟩
      · exact absurd h hR
      · have hw' : ∀ w, w ∈ fr R s ++ fr R p ++ fr R a → inC w g d = true := fun w h =>
          hw w (by rw [fr]; simp only [hR, ↓reduceIte]; exact h)
        refine inC_psi_iff.mpr (Or.inr ⟨?_, ?_, ?_, hg a (mem_subs_psi_a s p a) hlt⟩)
        · exact inC_of_fr p hp (fun v hv => hg v (subs_psi_p hv)) (fun w h => hw' w (by simp [h]))
        · exact inC_of_fr s hs (fun v hv => hg v (subs_psi_s hv)) (fun w h => hw' w (by simp [h]))
        · exact inC_of_fr a ha (fun v hv => hg v (subs_psi_a hv)) (fun w h => hw' w (by simp [h]))

/-- `R` 以上の節点が `d` 未満でなければ、`x ∈ C(g, d)` から前線の各節点が `C(g, d)` に入る -/
theorem fr_of_inC {R g d : Tm} : ∀ x : Tm,
    (∀ w, w ∈ subs x → ¬ Lt w R → ¬ Lt w d) → inC x g d = true →
    ∀ w, w ∈ fr R x → inC w g d = true
  | .zero, _, _, w, h | .one, _, _, w, h | .K _, _, _, w, h => by simp [fr] at h
  | .plus a b, hd, hx, w, h => by
    rw [inC_plus, Bool.and_eq_true] at hx
    rw [fr, List.mem_append] at h
    rcases h with h | h
    · exact fr_of_inC a (fun v hv => hd v (subs_plus_l hv)) hx.1 w h
    · exact fr_of_inC b (fun v hv => hd v (subs_plus_r hv)) hx.2 w h
  | .Om a, hd, hx, w, h => by
    rw [inC_om] at hx
    rw [fr] at h
    exact fr_of_inC a (fun v hv => hd v (subs_om hv)) hx w h
  | .Xi m a, hd, hx, w, h => by
    rw [fr] at h
    by_cases hR : Lt (.Xi m a) R
    · simp only [hR, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact hx
    · simp only [hR, ↓reduceIte] at h
      rcases inC_xi_iff.mp hx with h' | ⟨ha, _⟩
      · exact absurd h' (hd _ (self_mem_subs _) hR)
      · exact fr_of_inC a (fun v hv => hd v (subs_xi hv)) ha w h
  | .Psi s p a, hd, hx, w, h => by
    rw [fr] at h
    by_cases hR : Lt (.Psi s p a) R
    · simp only [hR, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact hx
    · simp only [hR, ↓reduceIte, List.mem_append] at h
      rcases inC_psi_iff.mp hx with h' | ⟨hp, hs, ha, _⟩
      · exact absurd h' (hd _ (self_mem_subs _) hR)
      · rcases h with (h | h) | h
        · exact fr_of_inC s (fun v hv => hd v (subs_psi_s hv)) hs w h
        · exact fr_of_inC p (fun v hv => hd v (subs_psi_p hv)) hp w h
        · exact fr_of_inC a (fun v hv => hd v (subs_psi_a hv)) ha w h

/-- `x ∉ C(g, d)` なら前線に `d` 未満でない節点がある -/
theorem wit_of_not_inC {R g0 g d x : Tm} (h0 : inC x g0 R = true)
    (hg : ∀ v, v ∈ subs x → Lt v g0 → Lt v g) (hn : inC x g d = false) :
    ∃ w, w ∈ fr R x ∧ ¬ Lt w d := by
  by_cases h : ∀ w, w ∈ fr R x → inC w g d = true
  · rw [inC_of_fr x h0 hg h] at hn
    cases hn
  · obtain ⟨w, hw, hw'⟩ := exists_of_not_forall_mem _ h
    exact ⟨w, hw, fun h' => hw' (inC_of_lt_node (fr_node hw) h')⟩

/-- 前線の取り替え：`x` の部分項について `v < R' → v < R` なら、`R` についての前線の `R'` 未満の元は
    `R'` についての前線の元 -/
theorem fr_subG {R R' : Tm} : ∀ {x w : Tm}, (∀ v, v ∈ subs x → Lt v R' → Lt v R) →
    w ∈ fr R x → Lt w R' → w ∈ fr R' x
  | .zero, _, _, h, _ | .one, _, _, h, _ | .K _, _, _, h, _ => by simp [fr] at h
  | .plus a b, w, hR, h, hw => by
    rw [fr, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (fr_subG (fun v hv => hR v (subs_plus_l hv)) h hw)
    · exact Or.inr (fr_subG (fun v hv => hR v (subs_plus_r hv)) h hw)
  | .Om a, w, hR, h, hw => by
    rw [fr] at h ⊢
    exact fr_subG (fun v hv => hR v (subs_om hv)) h hw
  | .Xi m a, w, hR, h, hw => by
    rw [fr] at h ⊢
    by_cases hl : Lt (.Xi m a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      subst h
      simp only [hw, ↓reduceIte, List.mem_singleton]
    · simp only [hl, ↓reduceIte] at h
      have hl' : ¬ Lt (.Xi m a) R' := fun h' => hl (hR _ (self_mem_subs _) h')
      simp only [hl', ↓reduceIte]
      exact fr_subG (fun v hv => hR v (subs_xi hv)) h hw
  | .Psi s p a, w, hR, h, hw => by
    rw [fr] at h ⊢
    by_cases hl : Lt (.Psi s p a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      subst h
      simp only [hw, ↓reduceIte, List.mem_singleton]
    · simp only [hl, ↓reduceIte, List.mem_append] at h
      have hl' : ¬ Lt (.Psi s p a) R' := fun h' => hl (hR _ (self_mem_subs _) h')
      simp only [hl', ↓reduceIte, List.mem_append]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (fr_subG (fun v hv => hR v (subs_psi_s hv)) h hw))
      · exact Or.inl (Or.inr (fr_subG (fun v hv => hR v (subs_psi_p hv)) h hw))
      · exact Or.inr (fr_subG (fun v hv => hR v (subs_psi_a hv)) h hw)

/-- 引数の前線が全て `Ψ^0_π(γ)` 未満なら `γ ∈ C(γ, Ψ^0_π(γ))` -/
theorem inC_arg_of_k2 {π γ : Tm} (h : FYNF (.Psi .zero π γ))
    (hk : ∀ w, w ∈ fr π γ → Lt w (.Psi .zero π γ)) : inC γ γ (.Psi .zero π γ) = true :=
  inC_of_fr γ h.psi.2.2.2.2.1 (fun _ _ h => h)
    (fun w hw => inC_of_lt_node (fr_node hw) (hk w hw))

/-- 目標の前線が全て `Ψ^0_π(γ)` 未満なら `π ∈ C(γ, Ψ^0_π(γ))` -/
theorem inC_tgt_of_k2t {π γ : Tm} (h : FYNF (.Psi .zero π γ))
    (hk : ∀ w, w ∈ fr π π → Lt w (.Psi .zero π γ)) : inC π γ (.Psi .zero π γ) = true :=
  inC_of_fr π h.psi.2.2.2.2.2 (fun _ _ h => h)
    (fun w hw => inC_of_lt_node (fr_node hw) (hk w hw))

/-! ### 崩壊の性質 -/

/-- 底は同じ階以上の底でない主要項より小さい -/
theorem bot_ltY {h t : Tm} (hb : isBot h = true) (hl : lev h ≤ lev t) (htp : isPrincipal t = true)
    (htb : isBot t = false) (ht : FYNF t) : Lt h t := by
  have hp : isPrincipal h = true := by cases h <;> simp_all [isBot, isPrincipal]
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · exact lt_of_lev_lt' hl
  · exact (lt_principal_iff hp htp).mpr (lt_of_isBotY hl hb htb htp ht)

theorem lev_pos_psi {π γ : Tm} (ht : FYNF (.Psi .zero π γ)) : 1 ≤ lev (.Psi .zero π γ) :=
  lev_posY ht (by intro e; cases e)

/-- `Ξ_n(γ)` の崩壊の性質（順序の仮定なし） -/
theorem coll_xi0 {n : Nat} {γ : Tm} (ht : FYNF (.Xi n γ)) :
    ∀ z, FYNF z → inC z γ (.Xi n γ) = true → Lt z (.K n) → Lt z (.Xi n γ) := by
  obtain ⟨hn, -, -, -, -⟩ := ht.xi
  intro z
  induction z with
  | zero => intros; exact zero_lt (by intro e; cases e)
  | one => intros; exact bot_ltY rfl (by simp only [lev]; omega) rfl rfl ht
  | K m =>
    intro hz _ hlt
    exact bot_ltY rfl ((lt_K_iffY hz hn).mp hlt) rfl rfl ht
  | plus a b iha _ =>
    intro hz hin hlt
    rw [inC_plus, Bool.and_eq_true] at hin
    obtain ⟨haF, -, -, -⟩ := hz.plus
    have hl := (lt_K_iffY hz hn).mp hlt
    exact (lt_plus_prin_iffY hz rfl).mpr (iha haF hin.1 ((lt_K_iffY haF hn).mpr hl))
  | Om g ihg =>
    intro hz hin hlt
    rw [inC_om] at hin
    have hgF := hz.om.1
    have hl := (lt_K_iffY hz hn).mp hlt
    exact (lt_om_OFG (Or.inl ⟨n, γ, rfl⟩)).mpr (ihg hgF hin ((lt_K_iffY hgF hn).mpr hl))
  | Xi m f _ =>
    intro hz hin hlt
    rcases inC_xi_iff.mp hin with h | ⟨hf, hfγ⟩
    · exact h
    have hl := (lt_K_iffY hz hn).mp hlt
    simp only [lev] at hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · subst hl
      have hne : f ≠ γ := fun e => by subst e; exact Lt.irrefl _ hfγ
      rw [lt_principal_iff rfl rfl, cmpP_xi_xi, xiLtXi_eq]
      unfold Lt at hfγ
      simp [hne, hfγ, hf]
  | Psi s κ β _ ihκ _ =>
    intro hz hin hlt
    obtain ⟨rfl, -, hκF, -, -, -⟩ := hz.psi
    rcases inC_psi_iff.mp hin with h | ⟨hκ, -, -, -⟩
    · exact h
    have hl := (lt_K_iffY hz hn).mp hlt
    simp only [lev] at hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · have hκX := ihκ hκF hκ ((lt_K_iffY hκF hn).mpr (by omega))
      refine (lt_psi_xiY hl).mpr (Or.inl ?_)
      unfold Lt at hκX
      rw [hκX]
      decide

namespace GoodY

variable {S : List Tm} (G : GoodY S)
include G

/-- `Ψ^0_π(γ)` の崩壊の性質（`π ∈ S`。`Ψ^0_π(γ)` 自身は `S` に入らなくてよい） -/
theorem coll_psi {π γ : Tm} (ht : FYNF (.Psi .zero π γ)) (hπS : π ∈ S) :
    ∀ z, z ∈ S → inC z γ (.Psi .zero π γ) = true → Lt z π → Lt z (.Psi .zero π γ) := by
  obtain ⟨-, hT, hπF, -, -, -⟩ := ht.psi
  have hlt0 := lev_pos_psi ht
  intro z
  induction z with
  | zero => intros; exact zero_lt (by intro e; cases e)
  | one => intros; exact bot_ltY rfl hlt0 rfl rfl ht
  | K m =>
    intro _ _ hlt
    exact bot_ltY rfl (lev_le_of_lt_gen (y := π) hlt) rfl rfl ht
  | plus a b iha _ =>
    intro hz hin hlt
    rw [inC_plus, Bool.and_eq_true] at hin
    have hzF := G.nf _ hz
    have haS := G.sub hz (show a ∈ subs (.plus a b) by simp [subs, self_mem_subs])
    have hao : Lt a π := G.trans haS hz hπS (lt_plus_leftY hzF) hlt
    exact (lt_plus_prin_iffY hzF rfl).mpr (iha haS hin.1 hao)
  | Om e ihe =>
    intro hz hin hlt
    rw [inC_om] at hin
    have hzF := G.nf _ hz
    have heS := G.sub hz (mem_subs_om e)
    rcases hT with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
    · have hcS := G.sub hπS (mem_subs_om c)
      exact (lt_om_psiY ht).mpr ((G.lt_om_iffS heS hcS).mp hlt)
    · exact (lt_om_OFG (Or.inr ⟨n, p, γ, rfl⟩)).mpr
        (ihe heS hin (G.trans heS hz hπS hzF.om.2.2 hlt))
  | Xi m f _ =>
    intro hz hin hlt
    rcases inC_xi_iff.mp hin with h | ⟨hf, hfγ⟩
    · exact h
    have hl := lev_le_of_lt_gen hlt
    simp only [lev] at hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · have hgt : cmp π (.Xi m f) = .gt := by
        unfold Lt at hlt; rw [G.swap hz hπS, hlt]; rfl
      rw [lt_xi_psiY hl.symm, lt_psi_xiY hl.symm]
      rintro (h | ⟨-, h⟩)
      · exact h hgt
      · rw [hf] at h; cases h
  | Psi s κ β _ _ _ =>
    intro hz hin hlt
    obtain ⟨rfl, -, -, -, -, -⟩ := (G.nf _ hz).psi
    rcases inC_psi_iff.mp hin with h | ⟨hκ, -, hβ, hβγ⟩
    · exact h
    have hl := lev_le_of_lt_gen hlt
    simp only [lev] at hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · have hne : Tm.Psi .zero κ β ≠ .Psi .zero π γ := by
        intro e; cases e; exact Lt.irrefl _ hβγ
      rw [lt_psi_psiY hl hne]
      by_cases h1 : Lt (.Psi .zero π γ) κ
      · exact Or.inr ⟨h1, hlt, Or.inl ⟨hβγ, hβ, hκ⟩⟩
      · exact Or.inl h1

/-- `S` の元の崩壊 `Ψ^0_π(γ)` の性質 -/
theorem coll_psiS {π γ : Tm} (ht : Tm.Psi .zero π γ ∈ S) :
    ∀ z, z ∈ S → inC z γ (.Psi .zero π γ) = true → Lt z π → Lt z (.Psi .zero π γ) :=
  G.coll_psi (G.nf _ ht) (G.sub ht (by simp [subs, self_mem_subs]))

theorem inC_argS {π γ : Tm} (ht : Tm.Psi .zero π γ ∈ S) : inC γ γ (.Psi .zero π γ) = true :=
  inC_arg_of_k2 (G.nf _ ht) (G.k2 π γ ht)

theorem inC_tgtS {π γ : Tm} (ht : Tm.Psi .zero π γ ∈ S) : inC π γ (.Psi .zero π γ) = true :=
  inC_tgt_of_k2t (G.nf _ ht) (G.k2t π γ ht)

/-- `S` での前線の取り替え -/
theorem fr_sub {R R' x w : Tm} (hR : R ∈ S) (hR' : R' ∈ S) (hx : x ∈ S) (hle : Le R' R)
    (hw : w ∈ fr R x) (hwR : Lt w R') : w ∈ fr R' x :=
  fr_subG (fun _ hv h => G.lt_of_lt_of_le (G.sub hx hv) hR' hR h hle) hw hwR

end GoodY

/-! ### 新しい項 `t` との反対称性 -/

/-- `t` と `s` の反対称性と相等 -/
def AntiT (t s : Tm) : Prop := cmp s t = (cmp t s).swap ∧ (cmp t s = .eq → t = s)

/-- `Ω_X`（`X` は `Ω` の不動点）は標準形でない -/
theorem not_FYNF_om_OF {X : Tm} (hX : IsOF X) (h : FYNF (.Om X)) : False := by
  have := h.om.2.2
  rw [cmp_principal hX.principal rfl, cmpP_OF_om hX rfl, cmp_self] at this
  exact absurd this (by decide)

/-- `cmpPsi` が `.eq` なら等しい -/
theorem cmpPsi_eq {xi pi a sg ka b : Tm} (h : cmpPsi (.Psi xi pi a) (.Psi sg ka b) = .eq) :
    Tm.Psi xi pi a = .Psi sg ka b := by
  rw [cmpPsi.eq_def] at h
  simp only [] at h
  by_cases h1 : (Tm.Psi xi pi a == Tm.Psi sg ka b) = true
  · exact eq_of_beq h1
  · exfalso
    simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    revert h
    split
    · intro h; cases h
    · split
      · intro h; cases h
      · split <;> intro h <;> cases h

theorem swap_eq_eq {o : Ordering} (h : o.swap = .eq) : o = .eq := by
  cases o <;> first | rfl | cases h

namespace GoodY

variable {S : List Tm} (G : GoodY S)
include G

/-- 同じ階の主要項どうしの、`t` の側の相等（`.eq` にならない） -/
theorem eqP_new {t y : Tm} (ht : FYNF t) (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S)
    (hy : y ∈ S) (hne : y ≠ t) (htp : isPrincipal t = true) (hyp : isPrincipal y = true)
    (ih : ∀ u, u ∈ S → u.size < y.size → cmp u t ≠ .eq) :
    cmpP t y ≠ .eq ∧ cmpP y t ≠ .eq := by
  have hyF := G.nf y hy
  by_cases h1 : lev t < lev y
  · rw [cmpP_of_lev_lt h1, cmpP_of_lev_gt h1]; exact ⟨by decide, by decide⟩
  by_cases h2 : lev y < lev t
  · rw [cmpP_of_lev_gt h2, cmpP_of_lev_lt h2]; exact ⟨by decide, by decide⟩
  have hl : lev t = lev y := by omega
  have sub1 : ∀ e, e ∈ subs t → e.size < t.size → e ∈ S := fun e he hs =>
    hsub e he (ne_of_mem_subs_lt hs)
  cases t <;> cases y
  all_goals first
    | (exfalso; simp [isPrincipal] at htp hyp; done)
    | skip
  case one.one => exact absurd rfl hne
  case K.K m n =>
    have : n = m := by simp only [lev] at hl; omega
    subst this
    exact absurd rfl hne
  case Om.Om e a =>
    have heS := sub1 e (mem_subs_om e) (by simp only [Tm.size]; omega)
    have haS := G.sub hy (mem_subs_om a)
    have hl' : lev e = lev a := hl
    rw [cmpP_om_om hl', cmpP_om_om hl'.symm]
    refine ⟨fun h => hne ?_, fun h => hne ?_⟩
    · rw [G.eq heS haS h]
    · rw [G.eq haS heS h]
  case Om.Xi e n b =>
    have heS := sub1 e (mem_subs_om e) (by simp only [Tm.size]; omega)
    have hl' : lev e = n := hl
    rw [cmpP_om_xi hl', cmpP_xi_om hl']
    have key : cmp e (.Xi n b) ≠ .eq := fun h => by
      have := G.eq heS hy h
      subst this
      exact not_FYNF_om_OF (Or.inl ⟨n, b, rfl⟩) ht
    exact ⟨key, fun h => key (swap_eq_eq h)⟩
  case Xi.Om n b a =>
    have haS := G.sub hy (mem_subs_om a)
    have hl' : lev a = n := hl.symm
    rw [cmpP_om_xi hl', cmpP_xi_om hl']
    have key := ih a haS (by simp only [Tm.size]; omega)
    exact ⟨fun h => key (swap_eq_eq h), key⟩
  case Om.Psi e xi κ β =>
    obtain ⟨rfl, hT, -⟩ := hyF.psi
    have heS := sub1 e (mem_subs_om e) (by simp only [Tm.size]; omega)
    rcases hT with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
    · have h' : lev e = lev c := hl
      rw [cmpP_om_psi0 h', cmpP_psi0_om h']
      by_cases h : cmp e c = .lt <;> simp [h]
    · have hX : IsOF (.Psi .zero (.Xi n p) β) := Or.inr ⟨n, p, β, rfl⟩
      have hl' : lev e = lev (Tm.Psi .zero (.Xi n p) β) := hl
      rw [cmpP_om_OF hX hl', cmpP_OF_om hX hl']
      have key : cmp e (.Psi .zero (.Xi n p) β) ≠ .eq := fun h => by
        have := G.eq heS hy h
        subst this
        exact not_FYNF_om_OF hX ht
      exact ⟨key, fun h => key (swap_eq_eq h)⟩
  case Psi.Om xi π γ a =>
    obtain ⟨rfl, hT, -⟩ := ht.psi
    have haS := G.sub hy (mem_subs_om a)
    rcases hT with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
    · have h' : lev a = lev c := hl.symm
      rw [cmpP_om_psi0 h', cmpP_psi0_om h']
      by_cases h : cmp a c = .lt <;> simp [h]
    · have hX : IsOF (.Psi .zero (.Xi n p) γ) := Or.inr ⟨n, p, γ, rfl⟩
      have hl' : lev a = lev (Tm.Psi .zero (.Xi n p) γ) := hl.symm
      rw [cmpP_om_OF hX hl', cmpP_OF_om hX hl']
      have key := ih a haS (by simp only [Tm.size]; omega)
      exact ⟨fun h => key (swap_eq_eq h), key⟩
  case Xi.Xi n γ m b =>
    have : n = m := hl
    subst this
    rw [cmpP_xi_xi, cmpP_xi_xi]
    have h1 : γ ≠ b := fun e => hne (by rw [e])
    have h2 : b ≠ γ := fun e => h1 e.symm
    simp only [h1, h2, ↓reduceIte]
    exact ⟨by split <;> decide, by split <;> decide⟩
  case Psi.Xi xi π γ m b =>
    have hl' : lev π = m := hl
    rw [cmpP_psi_xi hl', cmpP_xi_psi hl']
    exact ⟨by split <;> decide, by split <;> decide⟩
  case Xi.Psi m b xi κ β =>
    have hl' : lev κ = m := hl.symm
    rw [cmpP_psi_xi hl', cmpP_xi_psi hl']
    exact ⟨by split <;> decide, by split <;> decide⟩
  case Psi.Psi xi π γ sg κ β =>
    have hl' : lev π = lev κ := hl
    rw [cmpP_psi_psi hl', cmpP_psi_psi hl'.symm]
    exact ⟨fun h => hne (cmpPsi_eq h).symm, fun h => hne (cmpPsi_eq h)⟩
  case K.Om m b =>
    have hne' := hyF.om_ne_k (m := m)
    rw [cmpP.eq_def, cmpP.eq_def]
    simp [hl, hne']
  case Om.K a m =>
    have hne' := ht.om_ne_k (m := m)
    rw [cmpP.eq_def, cmpP.eq_def]
    simp [hl, hne']
  all_goals
    simp only [cmpP.eq_def]
    simp_all [lev]

/-- `S` の元と新しい項 `t` の `cmp` は `.eq` にならない -/
theorem ne_new {t : Tm} (ht : FYNF t) (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S) (htS : t ∉ S) :
    ∀ z, z ∈ S → cmp z t ≠ .eq ∧ cmp t z ≠ .eq := by
  have key : ∀ N, ∀ z, z ∈ S → z.size ≤ N → cmp z t ≠ .eq ∧ cmp t z ≠ .eq := by
    intro N
    induction N with
    | zero => intro z _ h; exact absurd h (by have := Tm.size_pos z; omega)
    | succ N ih =>
      intro z hz hs
      have hzF := G.nf z hz
      have hP : ∀ x, x ∈ summands z → ∀ w, w ∈ summands t →
          (cmpP x w = .eq → x = w) ∧ (cmpP w x = .eq → w = x) := by
        intro x hx w hw
        have hxS := G.sub hz (mem_subs_of_mem_summands hx)
        obtain ⟨-, hxp⟩ := summands_FYNF z hzF x hx
        obtain ⟨-, hwp⟩ := summands_FYNF t ht w hw
        cases htp : isPrincipal t
        · have hwS : w ∈ S := hsub w (mem_subs_of_mem_summands hw) (by
            intro e; subst e; rw [hwp] at htp; cases htp)
          exact ⟨G.eq_of_cmpP_eq hxS hwS hxp hwp, G.eq_of_cmpP_eq hwS hxS hwp hxp⟩
        · rw [summands_principal' htp, List.mem_singleton] at hw
          subst hw
          have hxs := size_le_of_mem_summands z x hx
          have := G.eqP_new ht hsub hxS (fun e => htS (e ▸ hxS)) htp hxp
            (fun u hu hus => (ih u hu (by omega)).1)
          exact ⟨fun h => absurd h this.2, fun h => absurd h this.1⟩
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [cmp_eq] at h
        have := eq_of_summands_eq hzF.1 ht.1
          (eq_of_cmpList_eq _ _ (fun x hx w hw => (hP x hx w hw).1) h)
        exact htS (this ▸ hz)
      · rw [cmp_eq] at h
        have := eq_of_summands_eq ht.1 hzF.1
          (eq_of_cmpList_eq _ _ (fun w hw x hx => (hP x hx w hw).2) h)
        exact htS (this ▸ hz)
  exact fun z hz => key _ z hz (Nat.le_refl _)

/-- `S` の元 `z` が `cmp z t ≠ .gt` なら `z < t` -/
theorem lt_of_ne_gt_new {t z : Tm} (ht : FYNF t) (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S)
    (htS : t ∉ S) (hz : z ∈ S) (h : cmp z t ≠ .gt) : Lt z t := by
  have := (G.ne_new ht hsub htS z hz).1
  unfold Lt
  cases e : cmp z t
  · rfl
  · exact absurd e this
  · exact absurd e h

/-- 同じ階の主要項どうしの、`t` との反対称性（`Ψ` どうしは仮定 `hPsi`） -/
theorem swapP_new {t y : Tm} (ht : FYNF t) (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S)
    (hy : y ∈ S) (htp : isPrincipal t = true) (hyp : isPrincipal y = true)
    (hPsi : ∀ π γ κ β, t = .Psi .zero π γ → y = .Psi .zero κ β → lev π = lev κ →
      cmpPsi y t = (cmpPsi t y).swap) :
    cmpP y t = (cmpP t y).swap := by
  have hyF := G.nf y hy
  by_cases h1 : lev t < lev y
  · rw [cmpP_of_lev_lt h1, cmpP_of_lev_gt h1]; rfl
  by_cases h2 : lev y < lev t
  · rw [cmpP_of_lev_gt h2, cmpP_of_lev_lt h2]; rfl
  have hl : lev t = lev y := by omega
  have sub1 : ∀ e, e ∈ subs t → e.size < t.size → e ∈ S := fun e he hs =>
    hsub e he (ne_of_mem_subs_lt hs)
  cases t <;> cases y
  all_goals first
    | (exfalso; simp [isPrincipal] at htp hyp; done)
    | skip
  case one.one => rw [cmpP_self]; rfl
  case Om.Om e a =>
    have heS := sub1 e (mem_subs_om e) (by simp only [Tm.size]; omega)
    have haS := G.sub hy (mem_subs_om a)
    have hl' : lev e = lev a := hl
    rw [cmpP_om_om hl', cmpP_om_om hl'.symm]
    exact G.swap heS haS
  case Om.Xi e n b =>
    have hl' : lev e = n := hl
    rw [cmpP_om_xi hl', cmpP_xi_om hl']
  case Xi.Om n b a =>
    have hl' : lev a = n := hl.symm
    rw [cmpP_om_xi hl', cmpP_xi_om hl', Ordering.swap_swap]
  case Om.Psi e xi κ β =>
    obtain ⟨rfl, hT, -⟩ := hyF.psi
    rcases hT with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
    · have h' : lev e = lev c := hl
      rw [cmpP_om_psi0 h', cmpP_psi0_om h']
    · have hX : IsOF (.Psi .zero (.Xi n p) β) := Or.inr ⟨n, p, β, rfl⟩
      have hl' : lev e = lev (Tm.Psi .zero (.Xi n p) β) := hl
      rw [cmpP_om_OF hX hl', cmpP_OF_om hX hl']
  case Psi.Om xi π γ a =>
    obtain ⟨rfl, hT, -⟩ := ht.psi
    rcases hT with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
    · have h' : lev a = lev c := hl.symm
      rw [cmpP_om_psi0 h', cmpP_psi0_om h', Ordering.swap_swap]
    · have hX : IsOF (.Psi .zero (.Xi n p) γ) := Or.inr ⟨n, p, γ, rfl⟩
      have hl' : lev a = lev (Tm.Psi .zero (.Xi n p) γ) := hl.symm
      rw [cmpP_om_OF hX hl', cmpP_OF_om hX hl', Ordering.swap_swap]
  case Xi.Xi n γ m b =>
    have : n = m := hl
    subst this
    have hγS := sub1 γ (mem_subs_xi n γ) (by simp only [Tm.size]; omega)
    have hbS := G.sub hy (mem_subs_xi n b)
    exact (xi_SE (G.anti γ hγS b hbS)).1
  case Psi.Xi xi π γ m b =>
    have hl' : lev π = m := hl
    rw [cmpP_psi_xi hl', cmpP_xi_psi hl']
    split <;> rfl
  case Xi.Psi m b xi κ β =>
    have hl' : lev κ = m := hl.symm
    rw [cmpP_psi_xi hl', cmpP_xi_psi hl']
    split <;> rfl
  case Psi.Psi xi π γ sg κ β =>
    obtain ⟨rfl, -⟩ := ht.psi
    obtain ⟨rfl, -⟩ := hyF.psi
    have hl' : lev π = lev κ := hl
    rw [cmpP_psi_psi hl', cmpP_psi_psi hl'.symm]
    exact hPsi π γ κ β rfl rfl hl'
  case K.Om m b =>
    have hne' := hyF.om_ne_k (m := m)
    rw [cmpP.eq_def, cmpP.eq_def]
    simp [hl, hne']
  case Om.K a m =>
    have hne' := ht.om_ne_k (m := m)
    rw [cmpP.eq_def, cmpP.eq_def]
    simp [hl, hne']
  all_goals
    simp only [cmpP.eq_def]
    simp_all [lev]

/-- `Ψ` どうしの反対称性を仮定すれば、新しい項 `t` は `S` の全ての元と反対称 -/
theorem anti_new {t : Tm} (ht : FYNF t) (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S) (htS : t ∉ S)
    (hPsi : ∀ π γ κ β, t = .Psi .zero π γ → Tm.Psi .zero κ β ∈ S → lev π = lev κ →
      cmpPsi (.Psi .zero κ β) t = (cmpPsi t (.Psi .zero κ β)).swap) :
    ∀ z, z ∈ S → AntiT t z := by
  intro z hz
  have hzF := G.nf z hz
  refine ⟨?_, fun h => absurd h (G.ne_new ht hsub htS z hz).2⟩
  rw [cmp_eq z t, cmp_eq t z]
  apply cmpList_swap
  intro x hx y hy
  have hyS := G.sub hz (mem_subs_of_mem_summands hy)
  obtain ⟨-, hyp⟩ := summands_FYNF z hzF y hy
  obtain ⟨-, hxp⟩ := summands_FYNF t ht x hx
  cases htp : isPrincipal t
  · have hxS : x ∈ S := hsub x (mem_subs_of_mem_summands hx) (by
      intro e; subst e; rw [hxp] at htp; cases htp)
    rw [← cmp_principal hyp hxp, ← cmp_principal hxp hyp]
    exact G.swap hxS hyS
  · rw [summands_principal' htp, List.mem_singleton] at hx
    subst hx
    exact G.swapP_new ht hsub hyS htp hyp (fun π γ κ β e1 e2 hl => by
      subst e2; exact hPsi π γ κ β e1 hyS hl)

end GoodY

/-! ### 反対称性と切断性から推移性へ -/

theorem AntiOn.asymm {S : List Tm} (hA : AntiOn S) {a b : Tm} (ha : a ∈ S) (hb : b ∈ S)
    (h : Lt a b) : ¬ Lt b a := by
  unfold Lt at *
  rw [(hA a ha b hb).1, h]
  decide

theorem AntiOn.tri {S : List Tm} (hA : AntiOn S) {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) :
    Lt a b ∨ a = b ∨ Lt b a := by
  cases e : cmp a b with
  | lt => exact Or.inl e
  | eq => exact Or.inr (Or.inl ((hA a ha b hb).2 e))
  | gt =>
    refine Or.inr (Or.inr ?_)
    unfold Lt
    rw [(hA a ha b hb).1, e]
    rfl

theorem linOn_of_cutY {S S' : List Tm} {t : Tm} (hA : AntiOn S) (hLin : LinOn S')
    (inS' : ∀ s, s ∈ S → s ≠ t → s ∈ S') (cut : CutT S' t) : LinOn S := by
  intro a ha b hb c hc hab hbc
  by_cases eat : a = t <;> by_cases ebt : b = t <;> by_cases ect : c = t
  · subst eat; subst ebt; exact absurd hab (Lt.irrefl _)
  · subst eat; subst ebt; exact absurd hab (Lt.irrefl _)
  · subst eat; subst ect; exact absurd hbc (hA.asymm ha hb hab)
  · subst eat
    rcases hA.tri ha hc with h | h | h
    · exact h
    · exact absurd h.symm ect
    · exact absurd hab (hA.asymm hb ha (cut c b (inS' c hc ect) (inS' b hb ebt) hbc h))
  · subst ebt; subst ect; exact absurd hbc (Lt.irrefl _)
  · subst ebt
    rcases hA.tri ha hc with h | h | h
    · exact h
    · subst h; exact absurd hbc (hA.asymm ha hb hab)
    · exact absurd hbc (hA.asymm hc hb (cut a c (inS' a ha eat) (inS' c hc ect) h hab))
  · subst ect
    exact cut b a (inS' b hb ebt) (inS' a ha eat) hab hbc
  · exact hLin a (inS' a ha eat) b (inS' b hb ebt) c (inS' c hc ect) hab hbc

end RTKA
