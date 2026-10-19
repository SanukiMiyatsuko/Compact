import Compact.OCFRathjen.Club

/-! 基数の設定：`K_1 < K_2 < ⋯`、`Λ = sup K_n`、`Ω_ξ`。

* `K_n`（`n ≥ 1`）は正則で、正則基数の極限（弱到達不能）であることを課す（`Setting`）。
  各 `K_n` の弱コンパクト性は `WeakCompact.lean` の公理 `weaklyCompact` として課し、
  定常性仮定 (S)（`Eval.lean` の `StationaryHyp`）はそこで `stationaryHyp` として導かれる。
* `Ω_ξ` は `{0} ∪ closure R` の数え上げ。`Ω_0 = 0`、`Ω_{ξ+1}` は正則（`Om_succ_R`）で、
  `Ω` は `Λ` 未満で狭義増加かつ連続、`Ω_{K_n} = K_n`。 -/

namespace OCF.Rathjen

universe u

open Ordinal

noncomputable section

/-! ### `Ω` -/

/-- `{0} ∪ closure R`（`0` と非可算基数） -/
def CardSet (ξ : Ordinal.{u}) : Prop := ξ = 0 ∨ closure R ξ

/-- `Ω_ξ`：`CardSet` の数え上げ（`Ω_0 = 0`、`Ω_1` は最初の非可算正則基数） -/
def Om : Ordinal.{u} → Ordinal.{u} := enum CardSet

theorem cardSet_limClosed : LimClosed (CardSet.{u}) := by
  intro ξ hξ
  apply Or.inr
  apply closure_limClosed R ξ
  apply And.intro hξ.1
  intro η hη
  cases hξ.2 η hη with
  | intro β hβ =>
    cases hβ.1 with
    | inl h0 => rw [h0] at hβ; exact absurd hβ.2.1 (not_lt_zero η)
    | inr hc => exact Exists.intro β (And.intro hc hβ.2)

theorem Om_zero : Om (0 : Ordinal.{u}) = 0 := by
  exact (le_zero_iff _).mp (enum_le_of (X := CardSet) (Or.inl rfl)
    (fun β hβ => absurd hβ (not_lt_zero β)))

/-! ### 弱コンパクト基数の列 -/

/-- 弱コンパクト基数の列 `K_1 < K_2 < ⋯` についての仮定（`Kseq n` が `K_{n+1}`） -/
class Setting : Type (u + 1) where
  Kseq : Nat → Ordinal.{u}
  Kseq_R : ∀ n, R (Kseq n)
  Kseq_lt : ∀ n, Kseq n < Kseq (n + 1)
  Kseq_inacc : ∀ n η, η < Kseq n → ∃ ρ, R ρ ∧ η < ρ ∧ ρ < Kseq n

variable [Setting.{u}]

/-- `K_0 = 0`、`K_{n+1} = Kseq n` -/
def K : Nat → Ordinal.{u}
  | 0 => 0
  | n + 1 => Setting.Kseq n

def Λ : Ordinal.{u} := sup (fun n : ULift.{u} Nat => K n.down)

theorem K_succ (n : Nat) : K.{u} (n + 1) = Setting.Kseq n := rfl

theorem K_zero : K.{u} 0 = 0 := rfl

theorem R_K {n : Nat} (h : 1 ≤ n) : R (K.{u} n) := by
  cases n with
  | zero => exact absurd h (by decide)
  | succ n => exact Setting.Kseq_R n

theorem K_lt_K_succ (n : Nat) : K.{u} n < K (n + 1) := by
  cases n with
  | zero => exact lt_of_le_of_lt (zero_le _) (lt_trans _ _ _ zero_lt_omega (Setting.Kseq_R 0).1)
  | succ n => exact Setting.Kseq_lt n

theorem K_lt {m n : Nat} (h : m < n) : K.{u} m < K n := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ n ih =>
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with
    | inl h' => exact lt_trans _ _ _ (ih h') (K_lt_K_succ n)
    | inr h' => rw [h']; exact K_lt_K_succ n

theorem K_le {m n : Nat} (h : m ≤ n) : K.{u} m ≤ K n := by
  cases Nat.lt_or_eq_of_le h with
  | inl h' => exact Or.inl (K_lt h')
  | inr h' => rw [h']; exact le_refl _

theorem K_lt_iff {m n : Nat} : K.{u} m < K n ↔ m < n := by
  apply Iff.intro
  · intro h
    cases Nat.lt_or_ge m n with
    | inl h' => exact h'
    | inr h' => exact absurd h (not_lt_of_le (K_le h'))
  · exact K_lt

theorem K_inj {m n : Nat} (h : K.{u} m = K n) : m = n := by
  cases Nat.lt_trichotomy m n with
  | inl h' => exact absurd h (ne_of_lt (K_lt h'))
  | inr h' =>
    cases h' with
    | inl h' => exact h'
    | inr h' => exact absurd h (ne_of_gt (K_lt h'))

theorem K_le_Λ (n : Nat) : K.{u} n ≤ Λ :=
  le_sup (fun k : ULift.{u} Nat => K k.down) (ULift.up n)

theorem K_lt_Λ (n : Nat) : K.{u} n < Λ :=
  lt_of_lt_of_le (K_lt_K_succ n) (K_le_Λ (n + 1))

theorem lt_Λ_iff (α : Ordinal.{u}) : α < Λ ↔ ∃ n, α < K n := by
  apply Iff.intro
  · intro h
    cases (lt_sup_iff _ α).mp h with
    | intro n hn => exact Exists.intro n.down hn
  · intro h
    cases h with
    | intro n hn => exact lt_trans _ _ _ hn (K_lt_Λ n)

theorem omega_lt_K {n : Nat} (h : 1 ≤ n) : omega < K.{u} n := (R_K h).1

/-- `K_n`（`n ≥ 1`）未満の正則基数は非有界 -/
theorem K_inacc {n : Nat} (h : 1 ≤ n) (η : Ordinal.{u}) (hη : η < K n) :
    ∃ ρ, R ρ ∧ η < ρ ∧ ρ < K n := by
  cases n with
  | zero => exact absurd h (by decide)
  | succ n => exact Setting.Kseq_inacc n η hη

/-! ### `Ω`（続き） -/

theorem cardSet_unbounded_K {n : Nat} (h : 1 ≤ n) :
    ∀ η, η < K.{u} n → ∃ ξ, CardSet ξ ∧ η < ξ ∧ ξ < K n := by
  intro η hη
  cases K_inacc h η hη with
  | intro ρ hρ => exact Exists.intro ρ (And.intro (Or.inr (subset_closure hρ.1)) hρ.2)

theorem Om_def_lt_K {n : Nat} (h : 1 ≤ n) {α : Ordinal.{u}} (hα : α < K n) :
    EnumDef CardSet α ∧ Om α < K n :=
  enum_below_regular (R_K h).2 (cardSet_unbounded_K h) α hα

theorem Om_def {α : Ordinal.{u}} (hα : α < Λ) : EnumDef CardSet α := by
  cases (lt_Λ_iff α).mp hα with
  | intro n hn =>
    cases n with
    | zero => exact absurd hn (not_lt_zero α)
    | succ n => exact (Om_def_lt_K (Nat.succ_le_succ (Nat.zero_le n)) hn).1

theorem Om_lt_K {n : Nat} (h : 1 ≤ n) {α : Ordinal.{u}} (hα : α < K n) : Om α < K n :=
  (Om_def_lt_K h hα).2

theorem Om_lt_Λ {α : Ordinal.{u}} (hα : α < Λ) : Om α < Λ := by
  cases (lt_Λ_iff α).mp hα with
  | intro n hn =>
    cases n with
    | zero => exact absurd hn (not_lt_zero α)
    | succ n =>
      exact lt_trans _ _ _ (Om_lt_K (Nat.succ_le_succ (Nat.zero_le n)) hn) (K_lt_Λ _)

theorem Om_K {n : Nat} (h : 1 ≤ n) : Om (K.{u} n) = K n :=
  (enum_fixed_regular (R_K h).2 (cardSet_unbounded_K h) (Or.inr (subset_closure (R_K h)))).2

theorem Om_lt_Om {α β : Ordinal.{u}} (hαβ : α < β) (hβ : β < Λ) : Om α < Om β :=
  (Om_def hβ).lt hαβ

theorem Om_lt_Om_iff {α β : Ordinal.{u}} (hα : α < Λ) (hβ : β < Λ) : Om α < Om β ↔ α < β :=
  (Om_def hβ).lt_iff (Om_def hα)

theorem Om_inj {α β : Ordinal.{u}} (hα : α < Λ) (hβ : β < Λ) (h : Om α = Om β) : α = β :=
  (Om_def hα).inj (Om_def hβ) h

theorem le_Om {α : Ordinal.{u}} (hα : α < Λ) : α ≤ Om α := (Om_def hα).le_enum

theorem cardSet_Om {α : Ordinal.{u}} (hα : α < Λ) : CardSet (Om α) := (Om_def hα).mem

/-- `Ω_{β+1}` は正則 -/
theorem Om_succ_R {β : Ordinal.{u}} (hβ : succ β < Λ) : R (Om (succ β)) := by
  have hdef := Om_def hβ
  have hβdef : EnumDef CardSet β := hdef.of_le (le_of_lt (lt_succ_self β))
  have hlt : Om β < Om (succ β) := hdef.lt (lt_succ_self β)
  cases hdef.mem with
  | inl h0 => exact absurd h0 (ne_of_gt (lt_of_le_of_lt (zero_le _) hlt))
  | inr hc =>
    cases (closure_iff R _).mp hc with
    | inl hR => exact hR
    | inr hlp =>
      cases hlp.2 _ hlt with
      | intro ρ hρ =>
        have hle : Om (succ β) ≤ ρ :=
          enum_le_of (X := CardSet) (Or.inr (subset_closure hρ.1))
            (fun γ hγ => lt_of_le_of_lt (hβdef.le_of_le (le_of_lt_succ hγ)) hρ.2.1)
        exact absurd hρ.2.2 (not_lt_of_le hle)

/-- `Ω` は極限で連続 -/
theorem Om_limit {l : Ordinal.{u}} (hl : IsLimit l) (hlΛ : l < Λ) : Om l = supLt l Om :=
  (enum_limit cardSet_limClosed hl (fun _ hβ => Om_def (lt_trans _ _ _ hβ hlΛ))).2

end
end OCF.Rathjen
