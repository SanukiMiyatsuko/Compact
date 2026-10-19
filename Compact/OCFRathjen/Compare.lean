import Compact.OCFRathjen.Mahlo

/-! 比較の補題（Rathjen §4 の Lemma 4.14, Prop. 4.21 の加法版）。

同じ階 `m`（`K_{m-1} < · < K_m`）の項どうしの比較で、記法系 `T⁺` の `xiLtXi`・`psiLtXi` がそのまま使う形。

* `Xi_lt_Xi_iff`（Lemma 4.14）：`Ξ_m(α) < Ξ_m(β)` ⟺ `α < β ∧ α ∈ C(β, Ξ_m(β))` または `β < α ∧ β ∉ C(α, Ξ_m(α))`。
* `Xi_inj`（Cor. 4.15）：`α ≠ β` なら `Ξ_m(α) ≠ Ξ_m(β)`。
* `Psi_lt_Xi_iff`（Prop. 4.21）：`Ψ^ξ_π(α) < Ξ_m(β)` ⟺ `π ≤ Ξ_m(β)` または `β < α ∧ β ∉ C(α, Ψ^ξ_π(α))`。

`Ξ_m(α)` については、`Ξ_m(α) ∈ M^α` かつ `K_{m-1} < Ξ_m(α) < K_m`（`XiGood`）を仮定する。
弱コンパクト性から導かれる定常性仮定 (S)（`StationaryHyp`）のもとで、標準形の項の値はこれを満たす（`Xi_mem`）。 -/

namespace OCF.Rathjen

universe u

open Ordinal

noncomputable section

variable [Setting.{u}]

/-- `Ξ_m(α) ∈ M^α` かつ `K_{m-1} < Ξ_m(α) < K_m` -/
def XiGood (m : Nat) (α : Ordinal.{u}) : Prop :=
  M α (Xi m α) ∧ K (m - 1) < Xi m α ∧ Xi m α < K m

/-- `XiGood` から `α ∈ C(α, Ξ_m(α))` と `C(α, Ξ_m(α)) ∩ K_m ⊆ Ξ_m(α)` -/
theorem XiGood.spec {m : Nat} {α : Ordinal.{u}} (hα0 : 0 < α) (h : XiGood m α) :
    C α (Xi m α) α ∧ ∀ x, C α (Xi m α) x → x < K m → x < Xi m α := by
  have hM := (M_pos_iff (ne_of_gt hα0) _).mp h.1
  have hK : Kabove (Xi m α) = K m := Kabove_eq_of_between (Or.inl h.2.1) h.2.2
  refine And.intro hM.2.2.1 ?_
  intro x hx hxK
  exact hM.2.1 x hx (by rw [hK]; exact hxK)

/-- Lemma 4.14 -/
theorem Xi_lt_Xi_iff {m : Nat} {α β : Ordinal.{u}} (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα : XiGood m α) (hβ : XiGood m β) :
    Xi m α < Xi m β ↔ (α < β ∧ C β (Xi m β) α) ∨ (β < α ∧ ¬ C α (Xi m α) β) := by
  have sα := hα.spec hα0
  have sβ := hβ.spec hβ0
  apply Iff.intro
  · intro hlt
    cases lt_total α β with
    | inl hαβ =>
      exact Or.inl (And.intro hαβ (C_mono_base (Or.inl hlt) (C_mono_arg (Or.inl hαβ) sα.1)))
    | inr h =>
      cases h with
      | inl e => rw [e] at hlt; exact absurd hlt (lt_irrefl _)
      | inr hβα =>
        refine Or.inr (And.intro hβα ?_)
        intro hC
        have hXi : Xi m β < Xi m α := sα.2 _ (C_Xi m hβ0 hβα hC) hβ.2.2
        exact lt_asymm hlt hXi
  · intro h
    cases h with
    | inl h => exact sβ.2 _ (C_Xi m hα0 h.1 h.2) hα.2.2
    | inr h =>
      apply lt_of_not_le
      intro hle
      exact h.2 (C_mono_arg (Or.inl h.1) (C_mono_base hle sβ.1))

/-- Cor. 4.15 -/
theorem Xi_inj {m : Nat} {α β : Ordinal.{u}} (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα : XiGood m α) (hβ : XiGood m β) (e : Xi m α = Xi m β) : α = β := by
  have sα := hα.spec hα0
  have sβ := hβ.spec hβ0
  cases lt_total α β with
  | inl hαβ =>
    have hC : C β (Xi m β) α := by rw [← e]; exact C_mono_arg (Or.inl hαβ) sα.1
    have hlt := sβ.2 _ (C_Xi m hα0 hαβ hC) hα.2.2
    rw [e] at hlt
    exact absurd hlt (lt_irrefl _)
  | inr h =>
    cases h with
    | inl h => exact h
    | inr hβα =>
      have hC : C α (Xi m α) β := by rw [e]; exact C_mono_arg (Or.inl hβα) sβ.1
      have hlt := sα.2 _ (C_Xi m hβ0 hβα hC) hβ.2.2
      rw [e] at hlt
      exact absurd hlt (lt_irrefl _)

/-- Prop. 4.21：同じ階 `m` の `Ψ^ξ_π(α)`（`π < K_m`）と `Ξ_m(β)` の比較 -/
theorem Psi_lt_Xi_iff {m : Nat} {ξ π α β : Ordinal.{u}} (hβ0 : 0 < β) (hβ : XiGood m β)
    (hψ : Psi ξ π α < π) (hπK : π < K m) :
    Psi ξ π α < Xi m β ↔ π ≤ Xi m β ∨ (β < α ∧ ¬ C α (Psi ξ π α) β) := by
  have sβ := hβ.spec hβ0
  have sψ := Psi_spec hψ
  apply Iff.intro
  · intro hlt
    cases le_or_lt π (Xi m β) with
    | inl h => exact Or.inl h
    | inr hXπ =>
      refine Or.inr ?_
      cases lt_or_le β α with
      | inr hαβ =>
        have hπC : C β (Xi m β) π := C_mono_base (Or.inl hlt) (C_mono_arg hαβ sψ.2.2.2.1)
        exact absurd (sβ.2 π hπC hπK) (not_lt_of_le (Or.inl hXπ))
      | inl hβα =>
        refine And.intro hβα ?_
        intro hC
        have hXψ : Xi m β < Psi ξ π α := sψ.2.2.1 _ (C_Xi m hβ0 hβα hC) hXπ
        exact lt_asymm hlt hXψ
  · intro h
    cases h with
    | inl h => exact lt_of_lt_of_le hψ h
    | inr h =>
      apply lt_of_not_le
      intro hle
      cases hle with
      | inl hlt =>
        exact h.2 (C_mono_arg (Or.inl h.1) (C_mono_base (Or.inl hlt) sβ.1))
      | inr e =>
        exact h.2 (C_mono_arg (Or.inl h.1) (by rw [← e]; exact sβ.1))

end
end OCF.Rathjen
