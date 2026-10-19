import Compact.OCFRathjen.Basic

/-! Enumerations of classes of ordinals (`EnumDef`, continuity at limits, behaviour below a regular)
and closures.

Copied from the Subsp repository (`Subsp/OCF/Jaeger/Psi.lean`, the generic part before `ISet`). -/

namespace OCF.Rathjen

universe u

open Ordinal

noncomputable section

def EnumDef (X : Ordinal.{u} → Prop) (α : Ordinal.{u}) : Prop :=
  ∃ ξ, X ξ ∧ ∀ β, β < α → enum X β < ξ

section Enum

variable {X : Ordinal.{u} → Prop}

theorem EnumDef.of_le {α β : Ordinal.{u}} (h : EnumDef X α) (hβ : β ≤ α) : EnumDef X β := by
  cases h with
  | intro ξ hξ =>
    exact Exists.intro ξ (And.intro hξ.1 (fun γ hγ => hξ.2 γ (lt_of_lt_of_le hγ hβ)))

theorem EnumDef.mem {α : Ordinal.{u}} (h : EnumDef X α) : X (enum X α) := (enum_spec X α h).1

theorem EnumDef.lt {α β : Ordinal.{u}} (h : EnumDef X α) (hβ : β < α) :
    enum X β < enum X α := (enum_spec X α h).2 β hβ

theorem EnumDef.le_of_le {α β : Ordinal.{u}} (h : EnumDef X α) (hβ : β ≤ α) :
    enum X β ≤ enum X α := by
  cases hβ with
  | inl hβ => exact le_of_lt (h.lt hβ)
  | inr hβ => rw [hβ]; exact le_refl _

theorem enum_le_of {α ξ : Ordinal.{u}} (hX : X ξ) (h : ∀ β, β < α → enum X β < ξ) :
    enum X α ≤ ξ := enum_le X α ξ hX h

theorem enum_eq_zero {α : Ordinal.{u}} (h : ¬ EnumDef X α) : enum X α = 0 := by
  rw [enum_eq]
  unfold least
  exact dite_eq_right h

theorem EnumDef.of_ne_zero {α : Ordinal.{u}} (h : enum X α ≠ 0) : EnumDef X α :=
  Classical.byContradiction (fun hn => h (enum_eq_zero hn))

theorem EnumDef.le_enum {α : Ordinal.{u}} (h : EnumDef X α) : α ≤ enum X α := by
  induction α using lt_wellFounded.induction with
  | h α ih =>
    apply le_of_not_lt
    intro hlt
    exact not_lt_of_le (ih _ hlt (h.of_le (le_of_lt hlt))) (h.lt hlt)

theorem EnumDef.lt_iff {α β : Ordinal.{u}} (hα : EnumDef X α) (hβ : EnumDef X β) :
    enum X β < enum X α ↔ β < α := by
  apply Iff.intro
  · intro h
    apply lt_of_not_le
    intro hle
    exact not_lt_of_le (hβ.le_of_le hle) h
  · exact hα.lt

theorem EnumDef.inj {α β : Ordinal.{u}} (hα : EnumDef X α) (hβ : EnumDef X β)
    (e : enum X α = enum X β) : α = β := by
  cases lt_total α β with
  | inl h => exact absurd e (ne_of_lt (hβ.lt h))
  | inr h =>
    cases h with
    | inl h => exact h
    | inr h => exact absurd e (ne_of_gt (hα.lt h))

theorem enum_surj {α ξ : Ordinal.{u}} (hX : X ξ) (hξ : ξ ≤ enum X α) :
    ∃ β, β ≤ α ∧ enum X β = ξ := by
  cases Ordinal.exists_min (fun β => ξ ≤ enum X β) (Exists.intro α hξ) with
  | intro β hβ =>
    have hβα : β ≤ α := le_of_not_lt (fun hlt => hβ.2 α hlt hξ)
    exact Exists.intro β (And.intro hβα (le_antisymm
      (enum_le_of hX (fun γ hγ => lt_of_not_le (hβ.2 γ hγ))) hβ.1))

def LimClosed (X : Ordinal.{u} → Prop) : Prop := ∀ ξ, IsLimitPoint X ξ → X ξ

theorem IsLimitPoint.isLimit {ξ : Ordinal.{u}} (h : IsLimitPoint X ξ) : IsLimit ξ := by
  apply And.intro h.1
  intro β hβ
  cases h.2 β hβ with
  | intro a ha => exact lt_of_le_of_lt (succ_le_of_lt ha.2.1) ha.2.2

theorem enum_limit (hX : LimClosed X) {l : Ordinal.{u}} (hl : IsLimit l)
    (h : ∀ β, β < l → EnumDef X β) : EnumDef X l ∧ enum X l = supLt l (enum X) := by
  have hlt : ∀ β, β < l → enum X β < supLt l (enum X) := by
    intro β hβ
    exact lt_of_lt_of_le ((h (succ β) (hl.2 β hβ)).lt (lt_succ_self β))
      (le_supLt l (enum X) (hl.2 β hβ))
  have hXs : X (supLt l (enum X)) := by
    apply hX
    apply And.intro (lt_of_le_of_lt (zero_le _) (hlt 0 hl.1))
    intro η hη
    cases (lt_supLt_iff l (enum X) η).mp hη with
    | intro β hβ => exact Exists.intro (enum X β) (And.intro (h β hβ.1).mem
        (And.intro hβ.2 (hlt β hβ.1)))
  have hdef : EnumDef X l := Exists.intro _ (And.intro hXs hlt)
  refine And.intro hdef (le_antisymm (enum_le_of hXs hlt) ?_)
  exact (supLt_le_iff _ _ _).mpr (fun β hβ => le_of_lt (hdef.lt hβ))

theorem enum_below_regular {θ : Ordinal.{u}} (hθ : IsRegular θ)
    (hunb : ∀ η, η < θ → ∃ ξ, X ξ ∧ η < ξ ∧ ξ < θ) :
    ∀ α, α < θ → EnumDef X α ∧ enum X α < θ := by
  intro α
  induction α using lt_wellFounded.induction with
  | h α ih =>
    intro hα
    have hs : supLt α (enum X) < θ :=
      hθ.supLt_lt hα (fun β hβ => (ih β hβ (lt_trans β α θ hβ hα)).2)
    cases hunb _ hs with
    | intro ξ hξ =>
      have hbelow : ∀ β, β < α → enum X β < ξ :=
        fun β hβ => lt_of_le_of_lt (le_supLt α (enum X) hβ) hξ.2.1
      exact And.intro (Exists.intro ξ (And.intro hξ.1 hbelow))
        (lt_of_le_of_lt (enum_le_of hξ.1 hbelow) hξ.2.2)

theorem enum_fixed_regular {θ : Ordinal.{u}} (hθ : IsRegular θ)
    (hunb : ∀ η, η < θ → ∃ ξ, X ξ ∧ η < ξ ∧ ξ < θ) (hXθ : X θ) :
    EnumDef X θ ∧ enum X θ = θ := by
  have hb := enum_below_regular hθ hunb
  have hdef : EnumDef X θ := Exists.intro θ (And.intro hXθ (fun β hβ => (hb β hβ).2))
  exact And.intro hdef (le_antisymm (enum_le_of hXθ (fun β hβ => (hb β hβ).2)) hdef.le_enum)

end Enum

theorem subset_closure {A : Ordinal.{u} → Prop} {ξ : Ordinal.{u}} (h : A ξ) : closure A ξ :=
  (closure_iff A ξ).mpr (Or.inl h)

theorem isLimitPoint_of_closure {A : Ordinal.{u} → Prop} {ξ : Ordinal.{u}}
    (h : IsLimitPoint (closure A) ξ) : IsLimitPoint A ξ := by
  apply And.intro h.1
  intro η hη
  cases h.2 η hη with
  | intro b hb =>
    cases (closure_iff A b).mp hb.1 with
    | inl hA => exact Exists.intro b (And.intro hA hb.2)
    | inr hlp =>
      cases hlp.2 η hb.2.1 with
      | intro a ha => exact Exists.intro a (And.intro ha.1 (And.intro ha.2.1
          (lt_trans a b ξ ha.2.2 hb.2.2)))

theorem closure_limClosed (A : Ordinal.{u} → Prop) : LimClosed (closure A) :=
  fun ξ h => (closure_iff A ξ).mpr (Or.inr (isLimitPoint_of_closure h))

theorem enum_closure_zero_mem {A : Ordinal.{u} → Prop} (h : EnumDef (closure A) 0) :
    A (enum (closure A) 0) := by
  cases (closure_iff A _).mp h.mem with
  | inl hA => exact hA
  | inr hlp =>
    cases hlp.2 0 hlp.1 with
    | intro a ha =>
      have := enum_le_of (X := closure A) (α := 0) (subset_closure ha.1)
        (fun β hβ => absurd hβ (not_lt_zero β))
      exact absurd (lt_of_lt_of_le ha.2.2 this) (lt_irrefl a)

theorem enum_closure_succ_mem {A : Ordinal.{u} → Prop} {β : Ordinal.{u}}
    (h : EnumDef (closure A) (succ β)) : A (enum (closure A) (succ β)) := by
  cases (closure_iff A _).mp h.mem with
  | inl hA => exact hA
  | inr hlp =>
    cases hlp.2 _ (h.lt (lt_succ_self β)) with
    | intro a ha =>
      have hβ : EnumDef (closure A) β := h.of_le (le_of_lt (lt_succ_self β))
      have := enum_le_of (X := closure A) (α := succ β) (subset_closure ha.1)
        (fun γ hγ => lt_of_le_of_lt (hβ.le_of_le (le_of_lt_succ hγ)) ha.2.1)
      exact absurd (lt_of_lt_of_le ha.2.2 this) (lt_irrefl a)

theorem R.omega_lt {ξ : Ordinal.{u}} (h : R ξ) : omega < ξ := h.1

theorem R.regular {ξ : Ordinal.{u}} (h : R ξ) : IsRegular ξ := h.2

theorem R.pos {ξ : Ordinal.{u}} (h : R ξ) : 0 < ξ := h.2.pos

theorem R.isLimit {ξ : Ordinal.{u}} (h : R ξ) : IsLimit ξ := h.2.isLimit

theorem R.isPrincipal {ξ : Ordinal.{u}} (h : R ξ) : IsPrincipal ξ := h.2.isPrincipal

end
end OCF.Rathjen
