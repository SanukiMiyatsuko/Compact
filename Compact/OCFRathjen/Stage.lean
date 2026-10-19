import Compact.OCFRathjen.Setting

/-! `C(α, β)`・`M^α`・`Ξ_m(α)`・`Ψ^ξ_π(α)` の定義（Rathjen, *Proof theory of reflection*, Def. 4.8 の加法版）。

`α` についての再帰で、段 `α` に次をまとめて定める（`Stage`）。

* `C(α, β)`：`β ∪ {1} ∪ {K_m}` を `+`、`Ω`（引数 `< Λ`）、`Ξ_m(ξ)`（`0 < ξ < α`）、
  `Ψ^ξ_π(δ)`（`ξ ≤ δ < α`、`π ∈ Reg`）で閉じたもの（`K_0 = 0` も入る）。
* `M^0 = Lim ∩ Λ`。`α > 0` なら
  `M^α = {π ∈ Reg : C(α, π) ∩ K(π) ⊆ π ∧ α ∈ C(α, π) ∧ ∀ ξ ∈ C(α, π) ∩ α, M^ξ は π で定常}`。
* `Ξ_m(α) = min({π ∈ M^α : K_{m-1} < π < K_m} ∪ {K_m})`。
* `Ψ^ξ_π(α) = min({ρ ∈ M^ξ ∩ π : C(α, ρ) ∩ π ⊆ ρ ∧ π, α ∈ C(α, ρ)} ∪ {π})`（`ξ ≤ α`。`ξ > α` なら `π`）。

`C(α, β)` は自然数で段階を付けた帰納的定義 `StageC` の和で、`|C(α, β)| < π`（`C_small`）の証明に段階を使う。 -/

namespace OCF.Rathjen

universe u

open Ordinal

noncomputable section

variable [Setting.{u}]

/-- `Reg`：`Λ` 未満の非可算正則基数で、どの `K_n` とも等しくないもの -/
def IsReg (π : Ordinal.{u}) : Prop := R π ∧ π < Λ ∧ ∀ n, π ≠ K n

/-- `K(π)`：`π` より大きい最小の `K_n` -/
def Kabove (π : Ordinal.{u}) : Ordinal.{u} := least (fun κ => (∃ n, κ = K n) ∧ π < κ)

/-- 段 `α` で定まるもの -/
structure Stage : Type (u + 1) where
  /-- `C β x`：`x ∈ C(α, β)` -/
  C : Ordinal.{u} → Ordinal.{u} → Prop
  /-- `M^α` -/
  M : Ordinal.{u} → Prop
  /-- `Ξ_m(α)` -/
  Xi : Nat → Ordinal.{u}
  /-- `Ψ^ξ_π(α)` -/
  Psi : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}

/-- `C(α, β)` の段階 `n` の元 -/
inductive StageC (α : Ordinal.{u}) (prev : (γ : Ordinal.{u}) → γ < α → Stage.{u})
    (β : Ordinal.{u}) : Nat → Ordinal.{u} → Prop where
  | lt (n : Nat) (γ : Ordinal.{u}) (h : γ < β) : StageC α prev β n γ
  | one (n : Nat) : StageC α prev β n (succ 0)
  | kc (n m : Nat) : StageC α prev β n (K m)
  | add (n : Nat) (x y : Ordinal.{u}) (hx : StageC α prev β n x) (hy : StageC α prev β n y) :
      StageC α prev β (n + 1) (x + y)
  | om (n : Nat) (x : Ordinal.{u}) (hΛ : x < Λ) (hx : StageC α prev β n x) :
      StageC α prev β (n + 1) (Om x)
  | xi (n m : Nat) (x : Ordinal.{u}) (hpos : 0 < x) (hα : x < α) (hx : StageC α prev β n x) :
      StageC α prev β (n + 1) ((prev x hα).Xi m)
  | psi (n : Nat) (ξ π δ : Ordinal.{u}) (hα : δ < α) (hξδ : ξ ≤ δ) (hπ : IsReg π)
      (hξ : StageC α prev β n ξ) (hπC : StageC α prev β n π) (hδ : StageC α prev β n δ) :
      StageC α prev β (n + 1) ((prev δ hα).Psi ξ π)

open Classical in
/-- 段 `α` での `M^ξ`（`ξ < α` なら前の段、`ξ = α` なら `Mcur`、`ξ > α` なら空） -/
def Mof (α : Ordinal.{u}) (prev : (γ : Ordinal.{u}) → γ < α → Stage.{u}) (Mcur : Ordinal.{u} → Prop)
    (ξ : Ordinal.{u}) : Ordinal.{u} → Prop :=
  if h : ξ < α then (prev ξ h).M else if ξ = α then Mcur else fun _ => False

omit [Setting] in
theorem Mof_lt {α ξ : Ordinal.{u}} (prev : (γ : Ordinal.{u}) → γ < α → Stage.{u})
    (Mcur : Ordinal.{u} → Prop) (h : ξ < α) : Mof α prev Mcur ξ = (prev ξ h).M := by
  unfold Mof
  rw [dite_eq_left h]

omit [Setting] in
theorem Mof_self {α : Ordinal.{u}} (prev : (γ : Ordinal.{u}) → γ < α → Stage.{u})
    (Mcur : Ordinal.{u} → Prop) : Mof α prev Mcur α = Mcur := by
  unfold Mof
  rw [dite_eq_right (lt_irrefl α), ite_eq_left rfl]

omit [Setting] in
theorem Mof_gt {α ξ : Ordinal.{u}} (prev : (γ : Ordinal.{u}) → γ < α → Stage.{u})
    (Mcur : Ordinal.{u} → Prop) (h : α < ξ) : Mof α prev Mcur ξ = fun _ => False := by
  unfold Mof
  rw [dite_eq_right (lt_asymm h), ite_eq_right (ne_of_gt h)]

open Classical in
def makeStage (α : Ordinal.{u}) (prev : (γ : Ordinal.{u}) → γ < α → Stage.{u}) : Stage.{u} :=
  let C : Ordinal.{u} → Ordinal.{u} → Prop := fun β x => ∃ n, StageC α prev β n x
  let M : Ordinal.{u} → Prop := fun ρ =>
    if α = 0 then IsLimit ρ ∧ ρ < Λ
    else IsReg ρ ∧ (∀ x, C ρ x → x < Kabove ρ → x < ρ) ∧ C ρ α ∧
      ∀ ξ (h : ξ < α), C ρ ξ → Stationary ρ (prev ξ h).M
  { C := C
    M := M
    Xi := fun m => least (fun π => (M π ∧ K (m - 1) < π ∧ π < K m) ∨ π = K m)
    Psi := fun ξ π => least (fun ρ =>
      (Mof α prev M ξ ρ ∧ ρ < π ∧ (∀ x, C ρ x → x < π → x < ρ) ∧ C ρ π ∧ C ρ α) ∨ ρ = π) }

def stages : Ordinal.{u} → Stage.{u} := lt_wellFounded.fix makeStage

theorem stages_eq (α : Ordinal.{u}) : stages α = makeStage α (fun γ _ => stages γ) :=
  WellFounded.fix_eq lt_wellFounded makeStage α

/-- `x ∈ C(α, β)` の段階 `n` -/
def Cn (α β : Ordinal.{u}) (n : Nat) (x : Ordinal.{u}) : Prop :=
  StageC α (fun γ _ => stages γ) β n x

/-- `x ∈ C(α, β)` -/
def C (α β x : Ordinal.{u}) : Prop := ∃ n, Cn α β n x

/-- `ρ ∈ M^α` -/
def M (α ρ : Ordinal.{u}) : Prop := (stages α).M ρ

/-- `Ξ_m(α)` -/
def Xi (m : Nat) (α : Ordinal.{u}) : Ordinal.{u} := (stages α).Xi m

/-- `Ψ^ξ_π(α)` -/
def Psi (ξ π α : Ordinal.{u}) : Ordinal.{u} := (stages α).Psi ξ π

/-! ### 定義の展開 -/

theorem stages_C (α β x : Ordinal.{u}) : (stages α).C β x ↔ C α β x := by
  rw [stages_eq α]
  exact Iff.rfl

open Classical in
theorem M_zero_iff (ρ : Ordinal.{u}) : M 0 ρ ↔ IsLimit ρ ∧ ρ < Λ := by
  unfold M
  rw [stages_eq 0]
  show (if (0 : Ordinal.{u}) = 0 then _ else _) ↔ _
  rw [ite_eq_left rfl]

open Classical in
theorem M_pos_iff {α : Ordinal.{u}} (hα : α ≠ 0) (ρ : Ordinal.{u}) :
    M α ρ ↔ IsReg ρ ∧ (∀ x, C α ρ x → x < Kabove ρ → x < ρ) ∧ C α ρ α ∧
      ∀ ξ, ξ < α → C α ρ ξ → Stationary ρ (M ξ) := by
  unfold M
  rw [stages_eq α]
  show (if α = 0 then _ else _) ↔ _
  rw [ite_eq_right hα]
  exact Iff.rfl

theorem Xi_eq (m : Nat) (α : Ordinal.{u}) :
    Xi m α = least (fun π => (M α π ∧ K (m - 1) < π ∧ π < K m) ∨ π = K m) := by
  unfold Xi M
  rw [stages_eq α]
  rfl

theorem Psi_eq {ξ α : Ordinal.{u}} (hξ : ξ ≤ α) (π : Ordinal.{u}) :
    Psi ξ π α = least (fun ρ =>
      (M ξ ρ ∧ ρ < π ∧ (∀ x, C α ρ x → x < π → x < ρ) ∧ C α ρ π ∧ C α ρ α) ∨ ρ = π) := by
  cases hξ with
  | inl h =>
    unfold Psi
    rw [stages_eq α]
    show least (fun ρ => (Mof α (fun γ _ => stages γ) _ ξ ρ ∧ _) ∨ _) = _
    rw [Mof_lt _ _ h]
    rfl
  | inr h =>
    subst h
    unfold Psi M
    rw [stages_eq ξ]
    show least (fun ρ => (Mof ξ (fun γ _ => stages γ) _ ξ ρ ∧ _) ∨ _) = _
    rw [Mof_self]
    rfl

omit [Setting] in
theorem least_false_or_eq (Q : Ordinal.{u} → Prop) (π : Ordinal.{u}) :
    least (fun ρ => ((fun _ => False) ρ ∧ Q ρ) ∨ ρ = π) = π := by
  have hs := (least_spec (fun ρ => ((fun _ : Ordinal.{u} => False) ρ ∧ Q ρ) ∨ ρ = π)
    (Exists.intro π (Or.inr rfl))).1
  cases hs with
  | inl hf => exact absurd hf.1 id
  | inr he => exact he

theorem Psi_eq_of_lt {ξ α : Ordinal.{u}} (hξ : α < ξ) (π : Ordinal.{u}) : Psi ξ π α = π := by
  unfold Psi
  rw [stages_eq α]
  show least (fun ρ => (Mof α (fun γ _ => stages γ) _ ξ ρ ∧ _) ∨ _) = _
  rw [Mof_gt _ _ hξ]
  exact least_false_or_eq _ π

/-! ### `C(α, β)` の構成子 -/

theorem Cn_lt (α β : Ordinal.{u}) (n : Nat) {x : Ordinal.{u}} (h : x < β) : Cn α β n x :=
  StageC.lt n x h

theorem Cn_one (α β : Ordinal.{u}) (n : Nat) : Cn α β n (succ 0) := StageC.one n

theorem Cn_K (α β : Ordinal.{u}) (n m : Nat) : Cn α β n (K m) := StageC.kc n m

theorem Cn_zero (α β : Ordinal.{u}) (n : Nat) : Cn α β n 0 := Cn_K α β n 0

theorem Cn_succ {α β : Ordinal.{u}} {n : Nat} {x : Ordinal.{u}} (h : Cn α β n x) :
    Cn α β (n + 1) x := by
  have hadd : Cn α β (n + 1) (x + 0) := StageC.add n x 0 h (Cn_zero α β n)
  rw [add_zero] at hadd
  exact hadd

theorem Cn_mono {α β : Ordinal.{u}} {n m : Nat} (hnm : n ≤ m) {x : Ordinal.{u}} (h : Cn α β n x) :
    Cn α β m x := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact Cn_succ ih

theorem C_lt {α β x : Ordinal.{u}} (h : x < β) : C α β x := Exists.intro 0 (Cn_lt α β 0 h)

theorem C_one (α β : Ordinal.{u}) : C α β (succ 0) := Exists.intro 0 (Cn_one α β 0)

theorem C_K (α β : Ordinal.{u}) (m : Nat) : C α β (K m) := Exists.intro 0 (Cn_K α β 0 m)

theorem C_zero (α β : Ordinal.{u}) : C α β 0 := C_K α β 0

theorem C_add {α β x y : Ordinal.{u}} (hx : C α β x) (hy : C α β y) : C α β (x + y) := by
  cases hx with
  | intro n hn =>
    cases hy with
    | intro m hm =>
      exact Exists.intro (max n m + 1) (StageC.add (max n m) x y
        (Cn_mono (Nat.le_max_left n m) hn) (Cn_mono (Nat.le_max_right n m) hm))

theorem C_Om {α β x : Ordinal.{u}} (hΛ : x < Λ) (hx : C α β x) : C α β (Om x) := by
  cases hx with
  | intro n hn => exact Exists.intro (n + 1) (StageC.om n x hΛ hn)

theorem C_Xi {α β x : Ordinal.{u}} (m : Nat) (hpos : 0 < x) (hα : x < α) (hx : C α β x) :
    C α β (Xi m x) := by
  cases hx with
  | intro n hn => exact Exists.intro (n + 1) (StageC.xi n m x hpos hα hn)

theorem C_Psi {α β ξ π δ : Ordinal.{u}} (hα : δ < α) (hξδ : ξ ≤ δ) (hπ : IsReg π)
    (hξ : C α β ξ) (hπC : C α β π) (hδ : C α β δ) : C α β (Psi ξ π δ) := by
  cases hξ with
  | intro n hn =>
    cases hπC with
    | intro m hm =>
      cases hδ with
      | intro k hk =>
        refine Exists.intro (max n (max m k) + 1) (StageC.psi (max n (max m k)) ξ π δ hα hξδ hπ
          (Cn_mono (Nat.le_max_left _ _) hn)
          (Cn_mono (Nat.le_trans (Nat.le_max_left m k) (Nat.le_max_right _ _)) hm)
          (Cn_mono (Nat.le_trans (Nat.le_max_right m k) (Nat.le_max_right _ _)) hk))

/-! ### Lemma 4.11 (i)：単調性 -/

theorem Cn_mono_arg {α α' β : Ordinal.{u}} (hα : α ≤ α') {n : Nat} {x : Ordinal.{u}}
    (h : Cn α β n x) : Cn α' β n x := by
  unfold Cn at h ⊢
  induction h with
  | lt n γ hγ => exact StageC.lt n γ hγ
  | one n => exact StageC.one n
  | kc n m => exact StageC.kc n m
  | add n x y _ _ ihx ihy => exact StageC.add n x y ihx ihy
  | om n x hΛ _ ih => exact StageC.om n x hΛ ih
  | xi n m x hpos hxα _ ih => exact StageC.xi n m x hpos (lt_of_lt_of_le hxα hα) ih
  | psi n ξ π δ hδα hξδ hπ _ _ _ ihξ ihπ ihδ =>
    exact StageC.psi n ξ π δ (lt_of_lt_of_le hδα hα) hξδ hπ ihξ ihπ ihδ

theorem C_mono_arg {α α' β x : Ordinal.{u}} (hα : α ≤ α') (h : C α β x) : C α' β x := by
  cases h with
  | intro n hn => exact Exists.intro n (Cn_mono_arg hα hn)

theorem Cn_mono_base {α β β' : Ordinal.{u}} (hβ : β ≤ β') {n : Nat} {x : Ordinal.{u}}
    (h : Cn α β n x) : Cn α β' n x := by
  unfold Cn at h ⊢
  induction h with
  | lt n γ hγ => exact StageC.lt n γ (lt_of_lt_of_le hγ hβ)
  | one n => exact StageC.one n
  | kc n m => exact StageC.kc n m
  | add n x y _ _ ihx ihy => exact StageC.add n x y ihx ihy
  | om n x hΛ _ ih => exact StageC.om n x hΛ ih
  | xi n m x hpos hxα _ ih => exact StageC.xi n m x hpos hxα ih
  | psi n ξ π δ hδα hξδ hπ _ _ _ ihξ ihπ ihδ => exact StageC.psi n ξ π δ hδα hξδ hπ ihξ ihπ ihδ

theorem C_mono_base {α β β' x : Ordinal.{u}} (hβ : β ≤ β') (h : C α β x) : C α β' x := by
  cases h with
  | intro n hn => exact Exists.intro n (Cn_mono_base hβ hn)

/-! ### Lemma 4.11 (iii)：極限での連続性 -/

theorem Cn_limit {α β : Ordinal.{u}} (hβ : IsLimit β) {n : Nat} {x : Ordinal.{u}}
    (h : Cn α β n x) : ∃ η, η < β ∧ Cn α η n x := by
  unfold Cn at h
  induction h with
  | lt n γ hγ => exact Exists.intro (succ γ) (And.intro (hβ.succ_lt hγ) (StageC.lt n γ (lt_succ_self γ)))
  | one n => exact Exists.intro 0 (And.intro hβ.1 (StageC.one n))
  | kc n m => exact Exists.intro 0 (And.intro hβ.1 (StageC.kc n m))
  | add n x y _ _ ihx ihy =>
    cases ihx with
    | intro η₁ h₁ =>
      cases ihy with
      | intro η₂ h₂ =>
        exact Exists.intro (omax η₁ η₂) (And.intro (omax_lt h₁.1 h₂.1)
          (StageC.add n x y (Cn_mono_base (le_omax_left η₁ η₂) h₁.2)
            (Cn_mono_base (le_omax_right η₁ η₂) h₂.2)))
  | om n x hΛ _ ih =>
    cases ih with
    | intro η h => exact Exists.intro η (And.intro h.1 (StageC.om n x hΛ h.2))
  | xi n m x hpos hxα _ ih =>
    cases ih with
    | intro η h => exact Exists.intro η (And.intro h.1 (StageC.xi n m x hpos hxα h.2))
  | psi n ξ π δ hδα hξδ hπ _ _ _ ihξ ihπ ihδ =>
    cases ihξ with
    | intro η₁ h₁ =>
      cases ihπ with
      | intro η₂ h₂ =>
        cases ihδ with
        | intro η₃ h₃ =>
          refine Exists.intro (omax η₁ (omax η₂ η₃)) (And.intro
            (omax_lt h₁.1 (omax_lt h₂.1 h₃.1)) (StageC.psi n ξ π δ hδα hξδ hπ
              (Cn_mono_base (le_omax_left _ _) h₁.2)
              (Cn_mono_base (le_trans (le_omax_left η₂ η₃) (le_omax_right _ _)) h₂.2)
              (Cn_mono_base (le_trans (le_omax_right η₂ η₃) (le_omax_right _ _)) h₃.2)))

theorem C_limit {α β x : Ordinal.{u}} (hβ : IsLimit β) (h : C α β x) : ∃ η, η < β ∧ C α η x := by
  cases h with
  | intro n hn =>
    cases Cn_limit hβ hn with
    | intro η hη => exact Exists.intro η (And.intro hη.1 (Exists.intro n hη.2))

/-! ### `Ψ` と `Ξ` の基本的な性質（Lemma 4.11 (iv)(v)） -/

theorem Psi_le (ξ π α : Ordinal.{u}) : Psi ξ π α ≤ π := by
  cases le_or_lt ξ α with
  | inl h =>
    rw [Psi_eq h]
    exact least_le _ (Or.inr rfl)
  | inr h => rw [Psi_eq_of_lt h]; exact le_refl π

/-- `Ψ^ξ_π(α) < π` なら、`Ψ^ξ_π(α) ∈ M^ξ` で `C(α, Ψ^ξ_π(α)) ∩ π ⊆ Ψ^ξ_π(α)`、`π, α ∈ C(α, Ψ^ξ_π(α))` -/
theorem Psi_spec {ξ π α : Ordinal.{u}} (h : Psi ξ π α < π) :
    ξ ≤ α ∧ M ξ (Psi ξ π α) ∧ (∀ x, C α (Psi ξ π α) x → x < π → x < Psi ξ π α) ∧
      C α (Psi ξ π α) π ∧ C α (Psi ξ π α) α := by
  cases le_or_lt ξ α with
  | inr hlt => rw [Psi_eq_of_lt hlt] at h; exact absurd h (lt_irrefl π)
  | inl hle =>
    refine And.intro hle ?_
    have hs := (least_spec (fun ρ =>
      (M ξ ρ ∧ ρ < π ∧ (∀ x, C α ρ x → x < π → x < ρ) ∧ C α ρ π ∧ C α ρ α) ∨ ρ = π)
      (Exists.intro π (Or.inr rfl))).1
    rw [← Psi_eq hle] at hs
    cases hs with
    | inl hs => exact And.intro hs.1 hs.2.2
    | inr he => exact absurd he (ne_of_lt h)

/-- `Ψ^ξ_π(α)` は条件を満たす `ρ < π` 以下 -/
theorem Psi_le_of {ξ π α ρ : Ordinal.{u}} (hξ : ξ ≤ α) (hM : M ξ ρ) (hρ : ρ < π)
    (hC : ∀ x, C α ρ x → x < π → x < ρ) (hπ : C α ρ π) (hα : C α ρ α) : Psi ξ π α ≤ ρ := by
  rw [Psi_eq hξ]
  exact least_le _ (Or.inl ⟨hM, hρ, hC, hπ, hα⟩)

theorem Xi_le (m : Nat) (α : Ordinal.{u}) : Xi m α ≤ K m := by
  rw [Xi_eq]
  exact least_le _ (Or.inr rfl)

/-- `Ξ_m(α) < K_m` なら、`Ξ_m(α) ∈ M^α` で `K_{m-1} < Ξ_m(α)` -/
theorem Xi_spec {m : Nat} {α : Ordinal.{u}} (h : Xi m α < K m) :
    M α (Xi m α) ∧ K (m - 1) < Xi m α := by
  have hs := (least_spec (fun π => (M α π ∧ K (m - 1) < π ∧ π < K m) ∨ π = K m)
    (Exists.intro (K m) (Or.inr rfl))).1
  rw [← Xi_eq] at hs
  cases hs with
  | inl hs => exact And.intro hs.1 hs.2.1
  | inr he => exact absurd he (ne_of_lt h)

/-- `Ξ_m(α)` は条件を満たす `π` 以下 -/
theorem Xi_le_of {m : Nat} {α π : Ordinal.{u}} (hM : M α π) (h1 : K (m - 1) < π) (h2 : π < K m) :
    Xi m α ≤ π := by
  rw [Xi_eq]
  exact least_le _ (Or.inl ⟨hM, h1, h2⟩)

end
end OCF.Rathjen
