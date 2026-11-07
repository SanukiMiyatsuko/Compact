import Compact.FS.Inner

/-! 塔の始点：閉じた点の探索（`maxCl`）の仕様。 -/

namespace RTKA.Fund

open Tm W

/-- `x` が `e` の中に `x` 以上の節点だけを通って現れるなら、`e ∈ C(g, d)` から `x ∈ C(g, d)` -/
theorem inC_of_selfVis {x g d : Tm} (hx : WNF x) (hd : WNF d) : ∀ {e : Tm}, WNF e → selfVis x e = true →
    inC e g d = true → inC x g d = true
  | .zero, _, h, _ | .one, _, h, _ | .K _, _, h, _ => by simp [selfVis] at h
  | .plus a b, he, h, hC => by
    obtain ⟨ha, hb, -, -⟩ := he.plus
    rw [inC_plus, Bool.and_eq_true] at hC
    simp only [selfVis, Bool.or_eq_true] at h
    rcases h with h | h
    · exact inC_of_selfVis hx hd ha h hC.1
    · exact inC_of_selfVis hx hd hb h hC.2
  | .Om a, he, h, hC => by
    rw [inC_om] at hC
    exact inC_of_selfVis hx hd he.om.1 h hC
  | .Xi m a, he, h, hC => by
    simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with h | ⟨h1, h2⟩
    · rw [← h]
      exact hC
    · have hle : Le x (.Xi m a) := le_of_ne_gtY hx he (leB_iff.mp h1)
      rcases inC_xi_iff.mp hC with h3 | ⟨h3, -⟩
      · exact WFY.inC_of_ltY _ hx hd (lt_of_le_of_ltY hx he hd hle h3)
      · exact inC_of_selfVis hx hd he.xi.2.1 h2 h3
  | .Psi s p a, he, h, hC => by
    simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with h | ⟨h1, h2⟩
    · rw [← h]
      exact hC
    · have hle : Le x (.Psi s p a) := le_of_ne_gtY hx he (leB_iff.mp h1)
      have hP := he.psi
      rcases inC_psi_iff.mp hC with h3 | ⟨h3, h4, h5, -⟩
      · exact WFY.inC_of_ltY _ hx hd (lt_of_le_of_ltY hx he hd hle h3)
      · rcases h2 with (h2 | h2) | h2
        · exact inC_of_selfVis hx hd hP.xiF h2 h4
        · exact inC_of_selfVis hx hd hP.piF h2 h3
        · exact inC_of_selfVis hx hd hP.aF h2 h5

theorem maxOpt_cases {P Q : Option Tm} {x : Tm} (h : maxOpt P Q = some x) : P = some x ∨ Q = some x := by
  unfold maxOpt at h
  split at h
  · exact Or.inr h
  · exact Or.inl h
  · simp only [Option.some.injEq] at h
    split at h
    · exact Or.inr (by rw [h])
    · exact Or.inl (by rw [h])

/-- 始点の仕様 -/
theorem maxCl_spec {cl : Tm → Bool} {ub G : Tm} : ∀ {e : Tm}, maxCl cl ub e = some G →
    G ∈ subs e ∧ cl G = true ∧ selfVis G ub = true
  | .zero, h | .one, h | .K _, h => by simp [maxCl] at h
  | .plus a b, h => by
    rcases maxOpt_cases h with h | h
    · obtain ⟨h1, h2, h3⟩ := maxCl_spec h
      exact ⟨subs_plus_l h1, h2, h3⟩
    · obtain ⟨h1, h2, h3⟩ := maxCl_spec h
      exact ⟨subs_plus_r h1, h2, h3⟩
  | .Om a, h => by
    obtain ⟨h1, h2, h3⟩ := maxCl_spec (e := a) h
    exact ⟨subs_om h1, h2, h3⟩
  | .Xi m' a, h => by
    rcases maxOpt_cases h with h | h
    · split at h
      · rename_i hc
        simp only [Bool.and_eq_true, Option.some.injEq] at hc h
        subst h
        exact ⟨self_mem_subs _, hc.1.1, hc.2⟩
      · cases h
    · obtain ⟨h1, h2, h3⟩ := maxCl_spec h
      exact ⟨subs_xi h1, h2, h3⟩
  | .Psi s p a, h => by
    rcases maxOpt_cases h with h | h
    · split at h
      · rename_i hc
        simp only [Bool.and_eq_true, Option.some.injEq] at hc h
        subst h
        exact ⟨self_mem_subs _, hc.1.1, hc.2⟩
      · cases h
    · rcases maxOpt_cases h with h | h
      · obtain ⟨h1, h2, h3⟩ := maxCl_spec h
        exact ⟨subs_psi_s h1, h2, h3⟩
      · rcases maxOpt_cases h with h | h
        · obtain ⟨h1, h2, h3⟩ := maxCl_spec h
          exact ⟨subs_psi_p h1, h2, h3⟩
        · obtain ⟨h1, h2, h3⟩ := maxCl_spec h
          exact ⟨subs_psi_a h1, h2, h3⟩

theorem maxXiClosed_spec {m : Nat} {ub G e : Tm} (h : maxXiClosed m ub e = some G) :
    G ∈ subs e ∧ closedPt m G = true ∧ selfVis G ub = true :=
  maxCl_spec h

/-- 閉じた点は `K_m` 未満 -/
theorem closedPt_lt {m : Nat} (hm : 1 ≤ m) : ∀ {G : Tm}, WNF G → closedPt m G = true → Lt G (.K m)
  | .zero, _, h | .one, _, h | .K _, _, h | .plus _ _, _, h | .Om _, _, h => by simp [closedPt] at h
  | .Xi m' w, hG, h => by
    simp only [closedPt, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1] at hG ⊢
    exact (lt_K_iffY hG hm).mpr (Nat.le_refl _)
  | .Psi s ρ a, hG, h => by
    have hP := hG.psi
    exact lt_transY hG hP.piF (WNF.K' hm) (lt_psi_targetY hG) (closedPt_lt hm hP.piF h)

/-- 始点の性質 -/
theorem start_spec {m : Nat} {c P : Tm} (hm : 1 ≤ m) (hc : WNF c) (hP : WNF P) :
    WNF (kStart m c P) ∧ Lt (kStart m c P) (.K m) ∧
      ∀ g d, WNF d → inC c g d = true → inC P g d = true → inC (kStart m c P) g d = true := by
  unfold kStart
  cases h : maxOpt (maxXiClosed m c c) (maxXiClosed m P P) with
  | none => exact ⟨WNF.zero, zero_lt (by intro e; cases e), fun _ _ _ _ _ => inC_zero _ _⟩
  | some G =>
    rcases maxOpt_cases h with h' | h'
    · obtain ⟨h1, h2, h3⟩ := maxXiClosed_spec h'
      have hG := hc.of_mem_subs h1
      exact ⟨hG, closedPt_lt hm hG h2, fun g d hd hC _ => inC_of_selfVis hG hd hc h3 hC⟩
    · obtain ⟨h1, h2, h3⟩ := maxXiClosed_spec h'
      have hG := hP.of_mem_subs h1
      exact ⟨hG, closedPt_lt hm hG h2, fun g d hd _ hC => inC_of_selfVis hG hd hP h3 hC⟩

/-! ### `col` -/

/-- 閉じた点は `σ` 未満 -/
theorem closedS_lt {σ T : Tm} (hσ : WNF σ) : ∀ {G : Tm}, WNF G → closedS σ T G = true → Lt G σ
  | .zero, _, h | .one, _, h | .K _, _, h | .plus _ _, _, h | .Om _, _, h | .Xi _ _, _, h => by
    simp [closedS] at h
  | .Psi s ρ w, hG, h => by
    have hP := hG.psi
    simp only [closedS, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, -⟩ | h
    · exact lt_psi_targetY hG
    · exact lt_transY hG hP.piF hσ (lt_psi_targetY hG) (closedS_lt hσ hP.piF h)

theorem closedS_ns {σ T : Tm} : ∀ {G : Tm}, closedS σ T G = true → ¬ isSucc G = true
  | .zero, h | .one, h | .K _, h | .plus _ _, h | .Om _, h | .Xi _ _, h => by simp [closedS] at h
  | .Psi s ρ w, _ => by
    rw [isSucc_principal rfl]
    simp

/-- 塔の始点の性質 -/
theorem sStart_spec {σ T c P : Tm} (hσ : WNF σ) (hσ0 : σ ≠ .zero) (hc : WNF c) (hP : WNF P) :
    WNF (sStart σ T c P) ∧ Lt (sStart σ T c P) σ ∧ ¬ isSucc (sStart σ T c P) = true ∧
      ∀ g d, WNF d → inC c g d = true → inC P g d = true → inC (sStart σ T c P) g d = true := by
  unfold sStart
  cases h : maxOpt (maxCl (closedS σ T) c c) (maxCl (closedS σ T) P P) with
  | none => exact ⟨WNF.zero, zero_lt hσ0, by simp [isSucc, summands], fun _ _ _ _ _ => inC_zero _ _⟩
  | some G =>
    rcases maxOpt_cases h with h' | h'
    · obtain ⟨h1, h2, h3⟩ := maxCl_spec h'
      have hG := hc.of_mem_subs h1
      exact ⟨hG, closedS_lt hσ hG h2, closedS_ns h2, fun g d hd hC _ => inC_of_selfVis hG hd hc h3 hC⟩
    · obtain ⟨h1, h2, h3⟩ := maxCl_spec h'
      have hG := hP.of_mem_subs h1
      exact ⟨hG, closedS_lt hσ hG h2, closedS_ns h2, fun g d hd _ hC => inC_of_selfVis hG hd hP h3 hC⟩

end RTKA.Fund
