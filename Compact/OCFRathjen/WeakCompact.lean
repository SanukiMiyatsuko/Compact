import Compact.OCFRathjen.Eval

/-! The weak-compact reflection step in Rathjen's Theorem 4.12.

`StageReflectionAt n` is the local reflection statement needed at `K n`.  The
induction below derives `StationaryHyp` from those reflection statements.
`StageReflectionAt` itself is proved from the partition property of `K n`
(`PartitionProp` in `Setting.lean`) by `stageReflectionAt_of_partition` in
`ReflMain.lean`, and `WeaklyCompact.lean` puts the two together.
-/

namespace OCF.Rathjen

universe u

open Ordinal

noncomputable section

variable [Setting.{u}]

/-- The reflection conclusion required at stage `n` in Theorem 4.12. -/
def StageReflectionAt (n : Nat) : Prop :=
  ∀ α, 0 < α → α ≤ Om (K n + succ 0) → C α (K n) α →
    (∀ β, β < α → 0 < β → β ≤ Om (K n + succ 0) → C β (K n) β →
      Stationary (K n) (M β)) →
    ∀ E, Club (K n) E →
      ∃ τ, τ < K n ∧ E τ ∧ IsReg τ ∧ C α τ α ∧
        (∀ x, C α τ x → x < Kabove τ → x < τ) ∧
        (∀ β, β < α → C α τ β → Stationary τ (M β))

/-- Rathjen's induction step: the local reflection conclusion at every `K n`
implies `StationaryHyp`. -/
theorem stationaryHyp_of_stageReflection
    (hreflect : ∀ n, 1 ≤ n → StageReflectionAt n) : StationaryHyp.{u} := by
  intro n hn α
  induction α using lt_wellFounded.induction with
  | h α ih =>
    intro hα0 hαK hC E hE
    cases hreflect n hn α hα0 hαK hC ih E hE with
    | intro τ hτ =>
      exact ⟨τ, hτ.1, hτ.2.1,
        (M_pos_iff (ne_of_gt hα0) τ).mpr
          ⟨hτ.2.2.1, hτ.2.2.2.2.1, hτ.2.2.2.1, hτ.2.2.2.2.2⟩⟩

end
end OCF.Rathjen
