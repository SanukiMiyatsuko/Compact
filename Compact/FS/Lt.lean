import Compact.FS.NF

/-! 基本列が元の項より小さいこと・添字について単調であること（構造的な部分）。
崩壊 `Ψ^0_π(X)` の列の場合は仮定として受け取る。 -/

namespace RTKA.Fund

open Tm W

/-- 標準形の和 `a + b` は `a ⊕ b` -/
theorem oadd_plus {a b : Tm} (h : WNF (.plus a b)) : oadd a b = .plus a b := by
  obtain ⟨ha, hb, hap, hb0⟩ := h.plus
  obtain ⟨h', rest, hs⟩ := List.exists_cons_of_ne_nil (summands_ne_nil hb0)
  have hle : leB h' a = true := by simpa [leB] using WNF.plus_head h hs
  rw [oadd_eq_ofSummands ha hb hs, summands_principal hap, hs]
  simp only [List.takeWhile_cons, hle, ↓reduceIte, List.takeWhile_nil, List.cons_append, List.nil_append]
  show Tm.plus a (ofSummands (h' :: rest)) = _
  rw [← hs, ofSummands_summands b hb]

theorem base_K_lt (n : Nat) : Lt (base (.K n)) (.K n) := by
  simp only [base]
  split
  · exact zero_lt (by intro e; cases e)
  · rename_i h
    unfold Lt cmp
    simp only [summands, cmpList, cmpP, lev]
    have : n - 1 + 1 < n + 1 := by omega
    simp [this]

/-- 崩壊 `Ψ^0_π(X)` の、共終数が正則項の場合の列が元の項より小さいこと -/
def PsiBigLt : Prop :=
  ∀ π X ξ σ, WNF (.Psi .zero π X) → WNF ξ → dom (.Psi .zero π X) = .big σ → Lt ξ σ →
    Lt (fundBig (.Psi .zero π X) ξ) (.Psi .zero π X)

theorem fundBig_lt_of (hψ : PsiBigLt) (hnf : PsiBigNF) :
    ∀ (t ξ σ : Tm), WNF t → WNF ξ → dom t = .big σ → Lt ξ σ → Lt (fundBig t ξ) t
  | .plus a b, ξ, σ, ht, hξ, hd, hlt => by
    obtain ⟨ha, hb, -, -⟩ := ht.plus
    rw [dom_plus] at hd
    rw [fundBig_plus, ← oadd_plus ht]
    exact oadd_lt_oadd ha (wnf_fundBig_of hnf b ξ σ hb hξ hd hlt) hb
      (fundBig_lt_of hψ hnf b ξ σ hb hξ hd hlt)
  | .K n, ξ, σ, ht, hξ, hd, hlt => by
    rw [dom_K, Cof.big.injEq] at hd
    subst hd
    rw [fundBig_K]
    exact oadd_lt_prin (wnf_base_K n) hξ rfl (base_K_lt n) hlt
  | .Xi m q, ξ, σ, ht, hξ, hd, hlt => by
    rw [dom_xi, Cof.big.injEq] at hd
    subst hd
    rw [fundBig_xi]
    exact oadd_lt_prin (wnf_base_xi ht) hξ rfl (lt_psi_targetY (wnf_base_xi ht)) hlt
  | .Om c, ξ, σ, ht, hξ, hd, hlt => by
    rw [fundBig_om]
    split
    · rename_i hs
      rw [dom_om, ite_eq_left hs, Cof.big.injEq] at hd
      subst hd
      exact oadd_lt_prin (wnf_base_om ht hs) hξ rfl (lt_psi_targetY (wnf_base_om ht hs)) hlt
    · rename_i hs
      rw [dom_om, ite_eq_right hs] at hd
      have hc := ht.om.1
      have hf := wnf_fundBig_of hnf c ξ σ hc hξ hd hlt
      have hlt' := fundBig_lt_of hψ hnf c ξ σ hc hξ hd hlt
      show Lt (.Om (succT (fundBig c ξ))) (.Om c)
      rw [lt_om_iffY (succT_WNF hf) hc]
      rcases succT_leY hf hc hlt' with e | e
      · exfalso
        have := isSucc_succT (fundBig c ξ)
        rw [e] at this
        exact hs this
      · exact e
  | .Psi ζ κ γ, ξ, σ, ht, hξ, hd, hlt => by
    by_cases hζ : ζ = .zero
    · subst hζ
      exact hψ κ γ ξ σ ht hξ hd hlt
    · rw [dom_psi, ite_eq_right hζ, Cof.big.injEq] at hd
      subst hd
      rw [fundBig_psi, ite_eq_right hζ]
      exact oadd_lt_prin (wnf_base_psi ht hζ) hξ rfl (lt_psi_targetY (wnf_base_psi ht hζ)) hlt
  | .zero, _, _, _, _, hd, _ | .one, _, _, _, _, hd, _ => by cases hd

/-- 崩壊 `Ψ^0_π(X)` の、共終数が `ω` の場合の列が元の項より小さいこと -/
def PsiNatLt : Prop :=
  ∀ π X n, WNF (.Psi .zero π X) → dom (.Psi .zero π X) = .omega →
    Lt (fundNat (.Psi .zero π X) n) (.Psi .zero π X)

/-- `x < c`、`c` が後者でないなら `x + 1 < c` -/
theorem succT_lt_of_not_succ {x c : Tm} (hx : WNF x) (hc : WNF c) (hs : ¬ isSucc c = true)
    (h : Lt x c) : Lt (succT x) c := by
  rcases succT_leY hx hc h with e | e
  · exfalso
    have := isSucc_succT x
    rw [e] at this
    exact hs this
  · exact e

theorem fundNat_lt_of (hψ : PsiNatLt) (hnf : PsiNatNF) :
    ∀ (t : Tm) (n : Nat), WNF t → dom t = .omega → Lt (fundNat t n) t
  | .plus a b, n, ht, hd => by
    obtain ⟨ha, hb, -, -⟩ := ht.plus
    rw [dom_plus] at hd
    rw [fundNat_plus, ← oadd_plus ht]
    exact oadd_lt_oadd ha (wnf_fundNat_of hnf b n hb hd) hb (fundNat_lt_of hψ hnf b n hb hd)
  | .Om c, n, ht, hd => by
    rw [dom_om] at hd
    split at hd
    · cases hd
    · rename_i hs
      rw [fundNat_om hs]
      have hc := ht.om.1
      have hf := wnf_fundNat_of hnf c n hc hd
      show Lt (.Om (succT (fundNat c n))) (.Om c)
      rw [lt_om_iffY (succT_WNF hf) hc]
      exact succT_lt_of_not_succ hf hc hs (fundNat_lt_of hψ hnf c n hc hd)
  | .Psi ζ κ γ, n, ht, hd => by
    by_cases hζ : ζ = .zero
    · subst hζ
      exact hψ κ γ n ht hd
    · rw [dom_psi, ite_eq_right hζ] at hd
      cases hd
  | .zero, _, _, hd | .one, _, _, hd | .K _, _, _, hd | .Xi _ _, _, _, hd => by cases hd

/-! ### 単調性 -/

/-- 崩壊 `Ψ^0_π(X)` の、共終数が正則項の場合の列の単調性 -/
def PsiBigMono : Prop :=
  ∀ π X ξ η σ, WNF (.Psi .zero π X) → WNF ξ → WNF η → dom (.Psi .zero π X) = .big σ → Lt ξ η → Lt η σ →
    Lt (fundBig (.Psi .zero π X) ξ) (fundBig (.Psi .zero π X) η)

/-- 崩壊 `Ψ^0_π(X)` の、共終数が `ω` の場合の列の単調性 -/
def PsiNatMono : Prop :=
  ∀ π X n, WNF (.Psi .zero π X) → dom (.Psi .zero π X) = .omega →
    Lt (fundNat (.Psi .zero π X) n) (fundNat (.Psi .zero π X) (n + 1))

theorem succT_lt_succT {a b : Tm} (ha : WNF a) (hb : WNF b) (h : Lt a b) : Lt (succT a) (succT b) :=
  lt_of_le_of_ltY (succT_WNF ha) hb (succT_WNF hb) (succT_leY ha hb h) (lt_succT b)

theorem fundBig_mono_of (hψ : PsiBigMono) (hnf : PsiBigNF) :
    ∀ (t ξ η σ : Tm), WNF t → WNF ξ → WNF η → dom t = .big σ → Lt ξ σ → Lt ξ η → Lt η σ →
      Lt (fundBig t ξ) (fundBig t η)
  | .plus a b, ξ, η, σ, ht, hξ, hη, hd, hξ', hlt, hη' => by
    obtain ⟨ha, hb, -, -⟩ := ht.plus
    rw [dom_plus] at hd
    rw [fundBig_plus, fundBig_plus]
    exact oadd_lt_oadd ha (wnf_fundBig_of hnf b ξ σ hb hξ hd hξ') (wnf_fundBig_of hnf b η σ hb hη hd hη')
      (fundBig_mono_of hψ hnf b ξ η σ hb hξ hη hd hξ' hlt hη')
  | .K n, ξ, η, _, _, hξ, hη, _, _, hlt, _ => by
    rw [fundBig_K, fundBig_K]
    exact oadd_lt_oadd (wnf_base_K n) hξ hη hlt
  | .Xi m q, ξ, η, _, ht, hξ, hη, _, _, hlt, _ => by
    rw [fundBig_xi, fundBig_xi]
    exact oadd_lt_oadd (wnf_base_xi ht) hξ hη hlt
  | .Om c, ξ, η, σ, ht, hξ, hη, hd, hξ', hlt, hη' => by
    rw [fundBig_om, fundBig_om]
    split
    · rename_i hs
      exact oadd_lt_oadd (wnf_base_om ht hs) hξ hη hlt
    · rename_i hs
      rw [dom_om, ite_eq_right hs] at hd
      have hc := ht.om.1
      have h1 := wnf_fundBig_of hnf c ξ σ hc hξ hd hξ'
      have h2 := wnf_fundBig_of hnf c η σ hc hη hd hη'
      show Lt (.Om (succT (fundBig c ξ))) (.Om (succT (fundBig c η)))
      rw [lt_om_iffY (succT_WNF h1) (succT_WNF h2)]
      exact succT_lt_succT h1 h2 (fundBig_mono_of hψ hnf c ξ η σ hc hξ hη hd hξ' hlt hη')
  | .Psi ζ κ γ, ξ, η, σ, ht, hξ, hη, hd, _, hlt, hη' => by
    by_cases hζ : ζ = .zero
    · subst hζ
      exact hψ κ γ ξ η σ ht hξ hη hd hlt hη'
    · rw [fundBig_psi, fundBig_psi, ite_eq_right hζ, ite_eq_right hζ]
      exact oadd_lt_oadd (wnf_base_psi ht hζ) hξ hη hlt
  | .zero, _, _, _, _, _, _, hd, _, _, _ | .one, _, _, _, _, _, _, hd, _, _, _ => by cases hd

theorem fundNat_mono_of (hψ : PsiNatMono) (hnf : PsiNatNF) :
    ∀ (t : Tm) (n : Nat), WNF t → dom t = .omega → Lt (fundNat t n) (fundNat t (n + 1))
  | .plus a b, n, ht, hd => by
    obtain ⟨ha, hb, -, -⟩ := ht.plus
    rw [dom_plus] at hd
    rw [fundNat_plus, fundNat_plus]
    exact oadd_lt_oadd ha (wnf_fundNat_of hnf b n hb hd) (wnf_fundNat_of hnf b (n + 1) hb hd)
      (fundNat_mono_of hψ hnf b n hb hd)
  | .Om c, n, ht, hd => by
    rw [dom_om] at hd
    split at hd
    · cases hd
    · rename_i hs
      rw [fundNat_om hs, fundNat_om hs]
      have hc := ht.om.1
      have h1 := wnf_fundNat_of hnf c n hc hd
      have h2 := wnf_fundNat_of hnf c (n + 1) hc hd
      show Lt (.Om (succT (fundNat c n))) (.Om (succT (fundNat c (n + 1))))
      rw [lt_om_iffY (succT_WNF h1) (succT_WNF h2)]
      exact succT_lt_succT h1 h2 (fundNat_mono_of hψ hnf c n hc hd)
  | .Psi ζ κ γ, n, ht, hd => by
    by_cases hζ : ζ = .zero
    · subst hζ
      exact hψ κ γ n ht hd
    · rw [dom_psi, ite_eq_right hζ] at hd
      cases hd
  | .zero, _, _, hd | .one, _, _, hd | .K _, _, _, hd | .Xi _ _, _, _, hd => by cases hd

end RTKA.Fund
