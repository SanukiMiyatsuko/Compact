import Compact.FS.Arith

/-! `C(g, d)` への所属（`inC`）と和・自然な和・倍・後者。 -/

namespace RTKA.Fund

open Tm W

theorem inC_ofSummands {g d : Tm} : ∀ l : List Tm,
    inC (ofSummands l) g d = true ↔ ∀ x, x ∈ l → inC x g d = true
  | [] => by simp [ofSummands, inC_zero]
  | [a] => by simp [ofSummands]
  | a :: b :: rest => by
    show inC (.plus a (ofSummands (b :: rest))) g d = true ↔ _
    rw [inC_plus, Bool.and_eq_true, inC_ofSummands (b :: rest)]
    simp only [List.mem_cons]
    constructor
    · rintro ⟨h1, h2⟩ x (rfl | hx)
      · exact h1
      · exact h2 x hx
    · intro h
      exact ⟨h a (Or.inl rfl), fun x hx => h x (Or.inr hx)⟩

theorem inC_iff_summands {t g d : Tm} (ht : WNF t) :
    inC t g d = true ↔ ∀ x, x ∈ summands t → inC x g d = true := by
  have := inC_ofSummands (g := g) (d := d) (summands t)
  rwa [ofSummands_summands t ht] at this

theorem inC_oadd {x y g d : Tm} (hx : WNF x) (hy : WNF y) (h1 : inC x g d = true)
    (h2 : inC y g d = true) : inC (oadd x y) g d = true := by
  rw [inC_iff_summands (wnf_oadd hx hy)]
  rw [inC_iff_summands hx] at h1
  rw [inC_iff_summands hy] at h2
  intro s hs
  cases hsy : summands y with
  | nil =>
    rw [eq_zero_of_summands_nil hsy, oadd_zero] at hs
    exact h1 s hs
  | cons h r =>
    have hX := nfl_summands hx
    have hY := nfl_summands hy
    rw [summands_oadd hsy (nfl_principal hX) (nfl_principal hY)] at hs
    rcases List.mem_append.mp hs with hs | hs
    · exact h1 s ((List.takeWhile_sublist _).subset hs)
    · exact h2 s hs

theorem inC_nsum {x y g d : Tm} (hx : WNF x) (hy : WNF y) (h1 : inC x g d = true)
    (h2 : inC y g d = true) : inC (nsum x y) g d = true := by
  unfold nsum
  rw [inC_ofSummands]
  rw [inC_iff_summands hx] at h1
  rw [inC_iff_summands hy] at h2
  intro s hs
  rcases mem_merge hs with hs | hs
  · exact h1 s hs
  · exact h2 s hs

theorem inC_mulNat {x g d : Tm} (h : inC x g d = true) (n : Nat) : inC (mulNat x n) g d = true := by
  unfold mulNat
  rw [inC_ofSummands]
  intro s hs
  rw [List.eq_of_mem_replicate hs]
  exact h

theorem inC_succT : ∀ {z g d : Tm}, inC z g d = true → inC (succT z) g d = true
  | .zero, _, _, _ => inC_one _ _
  | .plus a b, g, d, h => by
    rw [inC_plus, Bool.and_eq_true] at h
    show inC (.plus a (succT b)) g d = true
    rw [inC_plus, Bool.and_eq_true]
    exact ⟨h.1, inC_succT h.2⟩
  | .one, g, d, h | .K _, g, d, h | .Om _, g, d, h | .Xi _ _, g, d, h | .Psi _ _ _, g, d, h => by
    show inC (.plus _ .one) g d = true
    rw [inC_plus, Bool.and_eq_true]
    exact ⟨h, inC_one _ _⟩

/-- 和の接頭辞の所属 -/
theorem inC_of_mem_summands {t g d s : Tm} (ht : WNF t) (h : inC t g d = true)
    (hs : s ∈ summands t) : inC s g d = true :=
  (inC_iff_summands ht).mp h s hs

/-- `a < y + 1` なら `a ≤ y` -/
theorem le_of_lt_succT {a y : Tm} (ha : WNF a) (hy : WNF y) (h : Lt a (succT y)) : Le a y := by
  apply le_of_not_ltY hy ha
  intro hya
  exact not_lt_of_leY (succT_WNF hy) ha (succT_leY hy ha hya) h

/-- サイズの議論：`w` の大きさが `y` 以下なら、`w` の中の節点の引数は `y` と異なるので、
    `w ∈ C(y + 1, d)` から `w ∈ C(y, d)` -/
theorem inC_pred_of_size {y d : Tm} (hy : WNF y) :
    ∀ w : Tm, WNF w → w.size ≤ y.size → inC w (succT y) d = true → inC w y d = true
  | .zero, _, _, _ => inC_zero _ _
  | .one, _, _, _ => inC_one _ _
  | .K _, _, _, _ => inC_K _ _ _
  | .plus a b, hw, hs, h => by
    obtain ⟨ha, hb, -, -⟩ := hw.plus
    rw [inC_plus, Bool.and_eq_true] at h ⊢
    simp only [Tm.size] at hs
    exact ⟨inC_pred_of_size hy a ha (by omega) h.1, inC_pred_of_size hy b hb (by omega) h.2⟩
  | .Om a, hw, hs, h => by
    rw [inC_om] at h ⊢
    simp only [Tm.size] at hs
    exact inC_pred_of_size hy a hw.om.1 (by omega) h
  | .Xi n a, hw, hs, h => by
    rcases inC_xi_iff.mp h with h | ⟨h1, h2⟩
    · exact inC_xi_iff.mpr (Or.inl h)
    · have ha := hw.xi.2.1
      simp only [Tm.size] at hs
      refine inC_xi_iff.mpr (Or.inr ⟨inC_pred_of_size hy a ha (by omega) h1, ?_⟩)
      rcases le_of_lt_succT ha hy h2 with e | e
      · subst e; omega
      · exact e
  | .Psi s k δ, hw, hs, h => by
    rcases inC_psi_iff.mp h with h | ⟨hk, hs', hδ, hlt⟩
    · exact inC_psi_iff.mpr (Or.inl h)
    · have hP := hw.psi
      simp only [Tm.size] at hs
      refine inC_psi_iff.mpr (Or.inr ⟨inC_pred_of_size hy k hP.piF (by omega) hk,
        inC_pred_of_size hy s hP.xiF (by omega) hs', inC_pred_of_size hy δ hP.aF (by omega) hδ, ?_⟩)
      rcases le_of_lt_succT hP.aF hy hlt with e | e
      · subst e; omega
      · exact e

end RTKA.Fund
