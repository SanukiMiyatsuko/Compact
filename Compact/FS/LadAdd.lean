import Compact.FS.LadLB

/-! 区間の下界の写し：和 `a + ·`（`lbi_oadd`）と倍数の列（`lbi_mulNat`）。

`y` の加数が主要項 `a` 以下なら、`a ⊕ y` 以下で `a ⊕ x` より大きい項は `a ⊕ w'`（`x < w' ≤ y`）の形で
（`le_oadd_split`）、その 0 番目は `a ⊕ w'[0]` なので、`LBI x y` がそのまま写る。 -/

namespace RTKA.Fund

open Tm W

/-- `oadd a ·` は単調 -/
theorem oadd_le_oadd {a u v : Tm} (ha : WNF a) (hu : WNF u) (hv : WNF v) (h : Le u v) :
    Le (oadd a u) (oadd a v) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (oadd_lt_oadd ha hu hv h)

/-- `a ⊕ y`（`y` の加数は主要項 `a` 以下）以下で `a` より大きい項は `a ⊕ w'`（`w' ≤ y`） -/
theorem le_oadd_split {a y w : Tm} (ha : WNF a) (hap : isPrincipal a = true) (hy : WNF y) (hw : WNF w)
    (hsy : ∀ s, s ∈ summands y → Le s a) (h1 : Lt a w) (h2 : Le w (oadd a y)) :
    ∃ w', WNF w' ∧ Le w' y ∧ w = oadd a w' := by
  by_cases hy0 : y = .zero
  · subst hy0
    rw [oadd_zero] at h2
    exact absurd h1 (not_lt_of_leY hw ha h2)
  have e := oadd_prin_eq hap hy hy0 hsy
  rw [e] at h2
  have hP : WNF (.plus a y) := by rw [← e]; exact wnf_oadd ha hy
  rcases h2 with h2 | h2
  · exact ⟨y, hy, Or.inl rfl, by rw [h2, e]⟩
  · rcases lt_plus_split hP hw h2 with h3 | ⟨w', hw', hlt, -, e'⟩
    · exact absurd h1 (not_lt_of_leY hw ha h3)
    · exact ⟨w', hw', Or.inr hlt, e'⟩

/-- 和の下界の写し：`y` の加数が主要項 `a` 以下なら、`LBI x y` から `LBI (a ⊕ x) (a ⊕ y)` -/
theorem lbi_oadd {a x y : Tm} (ha : WNF a) (hap : isPrincipal a = true) (hx : WNF x) (hy : WNF y)
    (hsy : ∀ s, s ∈ summands y → Le s a) (h : LBI x y) : LBI (oadd a x) (oadd a y) := by
  intro w hw h1 h2
  have hax : Le a (oadd a x) := le_oadd_left ha hx
  have haw : Lt a w := lt_of_le_of_ltY ha (wnf_oadd ha hx) hw hax h1
  obtain ⟨w', hw', hwy, rfl⟩ := le_oadd_split ha hap hy hw hsy haw h2
  have hxw : Lt x w' := by
    refine Classical.byContradiction fun hn => ?_
    have := oadd_le_oadd ha hw' hx (le_of_not_ltY hx hw' hn)
    exact not_lt_of_leY (wnf_oadd ha hw') (wnf_oadd ha hx) this h1
  have hw'0 : w' ≠ .zero := ne_zero_of_lt hxw
  have hsw : ∀ s, s ∈ summands w' → Le s a := summands_le_of_le ha hap hy hw' hsy hwy
  have hP : WNF (.plus a w') := by rw [← oadd_prin_eq hap hw' hw'0 hsw]; exact wnf_oadd ha hw'
  rw [oadd_prin_eq hap hw' hw'0 hsw, fund_plus hP]
  exact oadd_le_oadd ha hx (fund_wnf hw' WNF.zero) (h w' hw' hxw hwy)

/-- `0` からの区間は自明 -/
theorem lbi_zero (y : Tm) : LBI .zero y := fun w _ _ _ => zero_le _

theorem oadd_mulNat {p : Tm} (hp : WNF p) (hpp : isPrincipal p = true) :
    ∀ k, oadd p (mulNat p k) = mulNat p (k + 1)
  | 0 => rfl
  | k + 1 => by
    have hsk : ∀ s, s ∈ summands (mulNat p (k + 1)) → Le s p := fun s hs => by
      rw [summands_mulNat hpp] at hs
      rw [List.eq_of_mem_replicate hs]
      exact Or.inl rfl
    rw [oadd_prin_eq hpp (wnf_mulNat hp hpp _) (mulNat_succ_ne_zero hpp k) hsk]
    rfl

/-- 倍数の列の下界：`LBI (p·k) (p·(k+1))` -/
theorem lbi_mulNat {p : Tm} (hp : WNF p) (hpp : isPrincipal p = true) :
    ∀ k, LBI (mulNat p k) (mulNat p (k + 1))
  | 0 => lbi_zero _
  | k + 1 => by
    have hsk : ∀ s, s ∈ summands (mulNat p (k + 1)) → Le s p := fun s hs => by
      rw [summands_mulNat hpp] at hs
      rw [List.eq_of_mem_replicate hs]
      exact Or.inl rfl
    have h := lbi_oadd hp hpp (wnf_mulNat hp hpp k) (wnf_mulNat hp hpp (k + 1)) hsk (lbi_mulNat hp hpp k)
    rwa [oadd_mulNat hp hpp k, oadd_mulNat hp hpp (k + 1)] at h

end RTKA.Fund
