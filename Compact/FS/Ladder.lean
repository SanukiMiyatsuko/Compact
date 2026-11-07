import Compact.FS.FSNF

/-! 梯子の準備：項の上の降下列 `DescT x b`（`b` から `b[0]` をたどる列に `x` が現れる）。

* 推移性、全ての降下列は 0 に達する（`desc_zero`）、`NF` の `InD` への移し替え（`inD_of_descT`）。
* 和：`(a + b)[ξ] = a + b[ξ]`（`fund_plus`）なので、`b` の降下列は `a + ·` で写る（`desc_oadd`）。 -/

namespace RTKA.Fund

open Tm W

/-- 項の上の降下列 -/
inductive DescT (x : Tm) : Tm → Prop
  | refl : DescT x x
  | step {b : Tm} : DescT x (fund b .zero) → DescT x b

theorem DescT.trans {x y z : Tm} (h1 : DescT x y) (h2 : DescT y z) : DescT x z := by
  induction h2 with
  | refl => exact h1
  | step _ ih => exact .step ih

/-- 0 でない項の 0 番目は自分未満 -/
theorem fund_zero_lt {b : Tm} (hb : WNF b) (hb0 : b ≠ .zero) : Lt (fund b .zero) b := by
  rw [fund_eq]
  cases hd : dom b with
  | zero => exact absurd ((dom_eq_zero_iff hb).mp hd) hb0
  | one => exact pred_lt hb ((dom_eq_one_iff hb).mp hd)
  | omega => exact ((seqI_dom_nat hb hd).1.good 0).2.1
  | big σ =>
    obtain ⟨hU, hreg⟩ := seqI_dom_big hb hd
    show Lt (fundBig b (if ltB .zero σ = true then .zero else .zero)) b
    have e : (if ltB Tm.zero σ = true then Tm.zero else Tm.zero) = .zero := by split <;> rfl
    rw [e]
    exact (hU.good.1 .zero WNF.zero (zero_lt hreg.ne_zero)).2

/-- 全ての降下列は 0 に達する -/
theorem desc_zero (b : NF) : DescT .zero b.1 := by
  refine WellFounded.induction (C := fun b : NF => DescT .zero b.1) wellFounded_isNF b ?_
  intro b ih
  by_cases hb0 : b.1 = .zero
  · rw [hb0]
    exact .refl
  · exact .step (ih ⟨fund b.1 .zero, fund_wnf b.2 WNF.zero⟩ (fund_zero_lt b.2 hb0))

/-- `NF` の降下列への移し替え -/
theorem inD_of_descT {x : NF} : ∀ {b : Tm}, DescT x.1 b → ∀ hb : WNF b, FSDesc.InD p0 x ⟨b, hb⟩ := by
  intro b h
  induction h with
  | refl => intro _; exact .refl
  | step _ ih => intro hb; exact .step (ih (fund_wnf hb WNF.zero))

/-! ### 和 -/

theorem pred_plus {a b : Tm} (h : WNF (.plus a b)) : pred (.plus a b) = oadd a (pred b) := by
  obtain ⟨-, hb, hap, hb0⟩ := h.plus
  have hN := nfl_summands h
  have hsb : summands b ≠ [] := summands_ne_nil hb0
  unfold pred
  show ofSummands (a :: summands b).dropLast = oadd a (ofSummands (summands b).dropLast)
  rw [List.dropLast_cons_of_ne_nil hsb]
  cases hdl : (summands b).dropLast with
  | nil => rfl
  | cons x r =>
    have hsplit := List.dropLast_concat_getLast hsb
    rw [hdl] at hsplit
    have hsb' : summands b = x :: (r ++ [(summands b).getLast hsb]) := hsplit.symm
    have hN' : NFL (a :: summands b) := hN
    rw [hsb'] at hN'
    have hxa : leB x a = true := leB_iff.mpr hN'.2.1
    have hxr : ∀ y, y ∈ x :: r → isPrincipal y = true := fun y hy => by
      have : y ∈ summands b := by
        rw [hsb']
        rcases List.mem_cons.mp hy with rfl | hy
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ hy)
      exact (hN.1 y (List.mem_cons_of_mem _ this)).2
    have hpb : summands (ofSummands (x :: r)) = x :: r := summands_ofSummands _ hxr
    show Tm.plus a (ofSummands (x :: r)) = oadd a (ofSummands (x :: r))
    unfold oadd
    rw [hpb, summands_principal hap]
    simp [hxa]
    rfl

theorem fund_plus {a b : Tm} (h : WNF (.plus a b)) (ξ : Tm) : fund (.plus a b) ξ = oadd a (fund b ξ) := by
  obtain ⟨-, hb, -, hb0⟩ := h.plus
  rw [fund_eq (.plus a b), fund_eq b, dom_plus]
  cases hd : dom b with
  | zero => exact absurd ((dom_eq_zero_iff hb).mp hd) hb0
  | one => exact pred_plus h
  | omega => rfl
  | big σ => rfl

/-- 加数が全て主要項 `a` 以下の項の下にある項の加数も `a` 以下 -/
theorem summands_le_of_lt_mul {z a : Tm} (hz : WNF z) (ha : WNF a) (hap : isPrincipal a = true) (k : Nat)
    (h : Lt z (mulNat a k)) : ∀ s, s ∈ summands z → Le s a := by
  intro s hs
  have hsN := (nfl_summands hz).1 s hs
  have hsz : Le s z := by
    have := le_ofSummands_of_mem (nfl_summands hz) hs
    rwa [ofSummands_summands z hz] at this
  refine le_of_not_ltY ha hsN.1 fun has => ?_
  have h1 := mulNat_lt_prin hap hsN.2 has k
  exact Lt.asymmY (wnf_mulNat ha hap k) hsN.1 h1 (lt_of_le_of_ltY hsN.1 hz (wnf_mulNat ha hap k) hsz h)

/-- 主要項 `a` と、加数が `a` 以下の `y ≠ 0` の和 -/
theorem oadd_prin_eq {a y : Tm} (hap : isPrincipal a = true) (hy : WNF y) (hy0 : y ≠ .zero)
    (hle : ∀ s, s ∈ summands y → Le s a) : oadd a y = .plus a y := by
  have hsy : summands y ≠ [] := summands_ne_nil hy0
  obtain ⟨h, r, hs⟩ := List.exists_cons_of_ne_nil hsy
  have hha : leB h a = true := le_leB (hle h (by rw [hs]; exact List.mem_cons_self))
  unfold oadd
  rw [hs, summands_principal hap]
  simp only [List.takeWhile_cons, hha, ite_true, List.takeWhile_nil, List.singleton_append]
  show Tm.plus a (ofSummands (h :: r)) = .plus a y
  rw [← hs, ofSummands_summands y hy]

/-- 和の降下列：`y` の降下列は `a + ·` で写る（`y` の加数は主要項 `a` 以下） -/
theorem desc_oadd {a : Tm} (ha : WNF a) (hap : isPrincipal a = true) :
    ∀ {x y : Tm}, DescT x y → WNF y → (∀ s, s ∈ summands y → Le s a) → DescT (oadd a x) (oadd a y) := by
  intro x y h
  induction h with
  | refl => intro _ _; exact .refl
  | @step y _ ih =>
    intro hy hsa
    by_cases hy0 : y = .zero
    · subst hy0
      exact ih WNF.zero fun s hs => by simp [summands, fund_zero] at hs
    · have hpy : WNF (fund y .zero) := fund_wnf hy WNF.zero
      have hlt := fund_zero_lt hy hy0
      have hk := lt_mulNat_of_le hy hap hsa
      have hsa' : ∀ s, s ∈ summands (fund y .zero) → Le s a :=
        summands_le_of_lt_mul hpy ha hap _ (lt_transY hpy hy (wnf_mulNat ha hap _) hlt hk)
      have hP : WNF (.plus a y) := by
        rw [← oadd_prin_eq hap hy hy0 hsa]
        exact wnf_oadd ha hy
      rw [oadd_prin_eq hap hy hy0 hsa]
      refine .step ?_
      rw [fund_plus hP]
      exact ih hpy hsa'


/-! ### 和の項と倍数の列の梯子 -/

theorem summands_le_head_plus {a b : Tm} (h : WNF (.plus a b)) : ∀ s, s ∈ summands b → Le s a := fun s hs =>
  le_head_mem (nfl_summands h) (List.mem_cons_of_mem _ hs)

/-- `b` の加数が主要項 `a` 以下なら、`b` 以下の項の加数も `a` 以下 -/
theorem summands_le_of_le {a b z : Tm} (ha : WNF a) (hap : isPrincipal a = true) (hb : WNF b) (hz : WNF z)
    (hsb : ∀ s, s ∈ summands b → Le s a) (hzb : Le z b) : ∀ s, s ∈ summands z → Le s a :=
  summands_le_of_lt_mul hz ha hap _ (lt_of_le_of_ltY hz hb (wnf_mulNat ha hap _) hzb (lt_mulNat_of_le hb hap hsb))

/-- 和の項の梯子（ω 型）：最後の加数の梯子から -/
theorem ladder_plus_nat {a b : Tm} (h : WNF (.plus a b)) (hd : dom b = .omega) (n : Nat)
    (hb : DescT (fund b (ofNatT n)) (fund b (ofNatT (n + 1)))) :
    DescT (fund (.plus a b) (ofNatT n)) (fund (.plus a b) (ofNatT (n + 1))) := by
  obtain ⟨ha, hbF, hap, -⟩ := h.plus
  rw [fund_plus h, fund_plus h]
  have hyF := fund_wnf hbF (wnf_ofNatT (n + 1))
  have hyb : Le (fund b (ofNatT (n + 1))) b := by
    rw [fund_omega hd]
    exact Or.inr ((seqI_dom_nat hbF hd).1.good _).2.1
  exact desc_oadd ha hap hb hyF (summands_le_of_le ha hap hbF hyF (summands_le_head_plus h) hyb)

/-- 和の項の梯子（big 型）：最後の加数の梯子から -/
theorem ladder_plus_big {a b σ ξ : Tm} (h : WNF (.plus a b)) (hd : dom b = .big σ) (hξ : WNF ξ)
    (hξσ : Lt ξ σ) (hb : DescT (fund b .zero) (fund b ξ)) :
    DescT (fund (.plus a b) .zero) (fund (.plus a b) ξ) := by
  obtain ⟨ha, hbF, hap, -⟩ := h.plus
  rw [fund_plus h, fund_plus h]
  have hyF := fund_wnf hbF hξ
  have hyb : Le (fund b ξ) b := by
    rw [fund_big hd hξσ]
    exact Or.inr ((seqI_dom_big hbF hd).1.good.1 ξ hξ hξσ).2
  exact desc_oadd ha hap hb hyF (summands_le_of_le ha hap hbF hyF (summands_le_head_plus h) hyb)

theorem mulNat_succ_ne_zero {p : Tm} (hpp : isPrincipal p = true) (k : Nat) : mulNat p (k + 1) ≠ .zero := by
  intro e
  have := congrArg summands e
  rw [summands_mulNat hpp] at this
  simp [summands] at this

/-- 倍数の梯子：`p·(k+1) ∈ D(p·(k+2))` -/
theorem ladder_mulNat {p : Tm} (hp : WNF p) (hpp : isPrincipal p = true) :
    ∀ k, DescT (mulNat p (k + 1)) (mulNat p (k + 2))
  | 0 => by
    have hsp : ∀ s, s ∈ summands p → Le s p := fun s hs => by
      rw [summands_principal hpp, List.mem_singleton] at hs
      rw [hs]
      exact Or.inl rfl
    have h := desc_oadd hp hpp (desc_zero ⟨p, hp⟩) hp hsp
    rw [oadd_zero, oadd_prin_eq hpp hp (mulNat_succ_ne_zero hpp 0) hsp] at h
    exact h
  | k + 1 => by
    have ih := ladder_mulNat hp hpp k
    have hsk : ∀ j, ∀ s, s ∈ summands (mulNat p j) → Le s p := fun j s hs => by
      rw [summands_mulNat hpp] at hs
      rw [List.eq_of_mem_replicate hs]
      exact Or.inl rfl
    have h := desc_oadd hp hpp ih (wnf_mulNat hp hpp _) (hsk (k + 2))
    rw [oadd_prin_eq hpp (wnf_mulNat hp hpp _) (mulNat_succ_ne_zero hpp k) (hsk (k + 1)),
      oadd_prin_eq hpp (wnf_mulNat hp hpp _) (mulNat_succ_ne_zero hpp (k + 1)) (hsk (k + 2))] at h
    exact h

end RTKA.Fund
