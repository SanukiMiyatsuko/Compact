import Compact.FS.Ladder

/-! `Ω` の写し：`Ω_{y+1}` の降下列は `Ψ^0_{Ω_{y+1}}(0) → Ω̂(y)·2 → … → Ω̂(y)` を通る。`y` が `Ω` の不動点でなければ
`Ω̂(y) = Ω_y` で、そこから一歩で `Ω_{y[0]+1}` に届く（`desc_om_step`）。区間に不動点がなければ降下列全体が写る（`desc_om`）。 -/

namespace RTKA.Fund

open Tm W

theorem DescT.le {x z : Tm} (hx : WNF x) (hz : WNF z) (h : DescT x z) : Le x z := by
  induction h with
  | refl => exact Or.inl rfl
  | @step z _ ih =>
    have hpz := fund_wnf hz WNF.zero
    by_cases hz0 : z = .zero
    · subst hz0
      exact ih hpz
    · exact le_transY hx hpz hz (ih hpz) (Or.inr (fund_zero_lt hz hz0))

theorem fund_om_succ {c : Tm} (hs : isSucc c = true) : fund (.Om c) .zero = .Psi .zero (.Om c) .zero := by
  rw [fund_eq]
  have hd : dom (.Om c) = .big (.Om c) := by
    rw [dom_om, ite_eq_left hs]
  rw [hd]
  show fundBig (.Om c) (if ltB .zero (.Om c) = true then .zero else .zero) = _
  have e : (if ltB Tm.zero (.Om c) = true then Tm.zero else Tm.zero) = .zero := by split <;> rfl
  rw [e, fundBig_om, ite_eq_left hs]
  rfl

theorem fund_om_lim {c : Tm} (hc : WNF (.Om c)) (hs : ¬ isSucc c = true) :
    fund (.Om c) .zero = .Om (sc (fund c .zero)) := by
  obtain ⟨hcF, hc0, -⟩ := hc.om
  rw [fund_eq, fund_eq c]
  have hd : dom (.Om c) = dom c := by
    rw [dom_om, ite_eq_right hs]
  rw [hd]
  cases hdc : dom c with
  | zero => exact absurd ((dom_eq_zero_iff hcF).mp hdc) hc0
  | one => exact absurd ((dom_eq_one_iff hcF).mp hdc) hs
  | omega => exact fundNat_om hs _
  | big σ =>
    show fundBig (.Om c) _ = .Om (sc (fundBig c _))
    rw [fundBig_om, ite_eq_right hs]

theorem fund_psi_om_zero {c : Tm} :
    fund (.Psi .zero (.Om c) .zero) .zero = mulNat (if c = one then one else omHat (pred c)) 2 := by
  rw [fund_eq]
  have hd : dom (.Psi .zero (.Om c) .zero) = .omega := by
    rw [dom_psi0, cs_om_zero]
    rfl
  rw [hd]
  show fundNat _ (natOf .zero) = _
  rw [fundNat_psi0, cs_om_zero]
  rfl

theorem sc_ne_one {y : Tm} (hy0 : y ≠ .zero) : sc y ≠ .one := by
  intro e
  have h := congrArg summands e
  simp only [sc, summands_succT] at h
  have h2 : summands y = [] := by
    have := h
    simp [summands] at this
    exact this
  exact hy0 (eq_zero_of_summands_nil h2)

/-- `Ω` の写し（一段）：`y` が `Ω` の不動点でなければ `Ω_{y[0]+1} ∈ D(Ω_{y+1})` -/
theorem desc_om_step {y : Tm} (hy : WNF y) (hy0 : y ≠ .zero) (hfix : omHat y = .Om y) :
    DescT (.Om (sc (fund y .zero))) (.Om (sc y)) := by
  have hOm : WNF (.Om (sc y)) := WNF.om_succT hy
  have hs : isSucc (sc y) = true := isSucc_succT y
  have hψ : WNF (.Psi .zero (.Om (sc y)) .zero) := wnf_base_om hOm hs
  have hB : (if sc y = one then one else omHat (pred (sc y))) = .Om y := by
    rw [ite_eq_right (sc_ne_one hy0)]
    show omHat (pred (succT y)) = _
    rw [pred_succT hy, hfix]
  obtain ⟨hBF, hBp, -⟩ := mul_base_lt hψ
  rw [hB] at hBF hBp
  refine .step ?_
  rw [fund_om_succ hs]
  refine .step ?_
  rw [fund_psi_om_zero, hB]
  refine DescT.trans ?_ (ladder_mulNat hBF hBp 0)
  show DescT _ (.Om y)
  by_cases hsy : isSucc y = true
  · have hd : dom y = .one := (dom_eq_one_iff hy).mpr hsy
    rw [fund_of_dom_one _ hd]
    show DescT (.Om (succT (pred y))) (.Om y)
    rw [succT_pred hy hsy]
    exact .refl
  · refine .step ?_
    rw [fund_om_lim hBF hsy]
    exact .refl

/-- `Ω` の写し：`x ∈ D(y)` で区間 `(x, y]` に `Ω` の不動点がなければ `Ω_{x+1} ∈ D(Ω_{y+1})` -/
theorem desc_om {x : Tm} (hx : WNF x) : ∀ {y : Tm}, DescT x y → WNF y →
    (∀ z, WNF z → Lt x z → Le z y → omHat z = .Om z) → DescT (.Om (sc x)) (.Om (sc y)) := by
  intro y h
  induction h with
  | refl => intro _ _; exact .refl
  | @step y h' ih =>
    intro hy hfix
    have hpy := fund_wnf hy WNF.zero
    by_cases hy0 : y = .zero
    · subst hy0
      exact ih hpy hfix
    · have hlt := fund_zero_lt hy hy0
      have hxy : Le x (fund y .zero) := DescT.le hx hpy h'
      have hxy' : Lt x y := lt_of_le_of_ltY hx hpy hy hxy hlt
      exact DescT.trans (ih hpy fun z hz h1 h2 => hfix z hz h1 (le_transY hz hpy hy h2 (Or.inr hlt)))
        (desc_om_step hy hy0 (hfix y hy hxy' (Or.inl rfl)))

end RTKA.Fund
