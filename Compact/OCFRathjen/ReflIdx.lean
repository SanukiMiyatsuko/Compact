import Compact.OCFRathjen.ReflB3
import Compact.OCFRathjen.Pairing

/-! `α < Ω_{K n + 1}` から `K n` への単射（Hartogs）、`C(α, K n)` から `K n` への単射（`exists_inj_C`）、
閉包点の club。 -/

namespace OCF.Rathjen

universe u

open Ordinal

set_option linter.unusedSectionVars false

noncomputable section

variable [Setting.{u}]

/-- `α < Ω_{K n + 1}` なら、`α` から `K n` への（順序数としての）単射がある -/
theorem exists_inj_of_lt_Om_succ {n : Nat} (hn : 1 ≤ n) {α : Ordinal.{u}}
    (hα : α < Om (K n + succ 0)) :
    ∃ j : Ordinal.{u} → Ordinal.{u}, (∀ β, β < α → j β < K n) ∧
      ∀ β β', β < α → β' < α → j β = j β' → β = β' := by
  classical
  let κ := K.{u} n
  have hκR : R κ := R_K hn
  let X := (representative κ).Carrier
  obtain ⟨pair, hpair⟩ := pairing_of_omega_le κ (Or.inl hκR.1)
  have hκθ : κ < hartogs X := lt_hartogs_of_injective κ (fun x => x) (fun x y h => h)
  have hωθ : omega < hartogs X := lt_trans _ _ _ hκR.1 hκθ
  have hθlim : IsLimit (hartogs X) := hartogs_isLimit_of_omega_lt hωθ
  have hθreg : IsRegular (hartogs X) := hartogs_regular_of_pair_injective hθlim pair hpair
  have hθR : R (hartogs X) := ⟨hωθ, hθreg⟩
  have h2 := Om_succ_le_of_R hn hθR hκθ
  have hαθ : α < hartogs X := lt_of_lt_of_le hα h2
  obtain ⟨f, hf⟩ := injective_of_lt_hartogs hαθ
  let j : Ordinal.{u} → Ordinal.{u} := fun β =>
    if h : β < α then type ((representative κ).below (f (pointBelow α β h))) else 0
  have hj : ∀ β (h : β < α), j β = type ((representative κ).below (f (pointBelow α β h))) :=
    fun β h => dite_eq_left h
  refine ⟨j, ?_, ?_⟩
  · intro β h
    rw [hj β h]
    exact initial_lt κ _
  · intro β β' h h' e
    rw [hj β h, hj β' h'] at e
    have e1 := initial_injective κ _ _ e
    have e2 := hf _ _ e1
    exact pointBelow_inj e2

/-- `K n < Ω_{K n + 1}` -/
theorem K_lt_Om_succK {n : Nat} (hn : 1 ≤ n) : K.{u} n < Om (K n + succ 0) := by
  have h := Om_lt_Om (by rw [add_one_eq_succ]; exact lt_succ_self (K.{u} n)) (K_add_one_lt_Λ n)
  rw [Om_K hn] at h
  exact h

/-- `Ω_{K n + 1}` は非可算正則 -/
theorem R_Om_succK (n : Nat) : R (Om (K.{u} n + succ 0)) := by
  rw [add_one_eq_succ]
  exact Om_succ_R (by rw [← add_one_eq_succ]; exact K_add_one_lt_Λ n)

/-- `C(α, K n)` から `K n` への単射（`|C(α, K n)| < Ω_{K n + 1}` による。`α` には制限が無い） -/
theorem exists_inj_C {n : Nat} (hn : 1 ≤ n) (α : Ordinal.{u}) :
    ∃ j : Ordinal.{u} → Ordinal.{u}, (∀ β, j β < K n) ∧
      ∀ β β', C α (K n) β → C α (K n) β' → j β = j β' → β = β' := by
  classical
  obtain ⟨γ, hγ, f, hf, hfinj⟩ := C_small (R_Om_succK n) (K_lt_Om_succK hn) α
  obtain ⟨j₀, hj₀κ, hj₀inj⟩ := exists_inj_of_lt_Om_succ hn hγ
  refine ⟨fun β => if C α (K n) β then j₀ (f β) else 0, ?_, ?_⟩
  · intro β
    by_cases hβ : C α (K n) β
    · dsimp only
      rw [ite_eq_left hβ]
      exact hj₀κ _ (hf β hβ)
    · dsimp only
      rw [ite_eq_right hβ]
      exact (R_K hn).2.pos
  · intro β β' hβ hβ' e
    dsimp only at e
    rw [ite_eq_left hβ, ite_eq_left hβ'] at e
    exact hfinj β β' hβ hβ' (hj₀inj _ _ (hf β hβ) (hf β' hβ') e)

theorem Club.congr {κ : Ordinal.{u}} {X Y : Ordinal.{u} → Prop} (h : ∀ ρ, X ρ ↔ Y ρ)
    (hX : Club κ X) : Club κ Y := by
  have e : X = Y := funext (fun ρ => propext (h ρ))
  rw [← e]
  exact hX

/-- 吸収される集合 `Q ρ` が単調・連続・有界なら、`Q ρ ∩ κ ⊆ ρ` となる `ρ` は club -/
theorem club_absorb {κ : Ordinal.{u}} (hκ : R κ) (Q : Ordinal.{u} → Ordinal.{u} → Prop)
    (hmono : ∀ ρ ρ' y, ρ ≤ ρ' → Q ρ y → Q ρ' y)
    (hcont : ∀ l y, IsLimit l → Q l y → ∃ ρ, ρ < l ∧ Q ρ y)
    (hbdd : ∀ ρ, ρ < κ → ∃ γ, γ < κ ∧ ∀ y, Q ρ y → y < κ → y < γ)
    {μ₀ : Ordinal.{u}} (hμ₀ : μ₀ < κ) :
    Club κ (fun ρ => μ₀ < ρ ∧ ∀ y, Q ρ y → y < κ → y < ρ) := by
  classical
  apply And.intro
  · intro η hη
    let bnd : Ordinal.{u} → Ordinal.{u} := fun δ =>
      if h : δ < κ then Classical.choose (hbdd δ h) else 0
    have hbnd : ∀ δ, δ < κ → bnd δ < κ ∧ ∀ y, Q δ y → y < κ → y < bnd δ := by
      intro δ hδ
      have e : bnd δ = Classical.choose (hbdd δ hδ) := dite_eq_left hδ
      rw [e]
      exact Classical.choose_spec (hbdd δ hδ)
    let s : Nat → Ordinal.{u} := fun n =>
      Nat.rec (succ (omax η μ₀)) (fun _ δ => omax (succ δ) (bnd δ)) n
    have hs0 : s 0 = succ (omax η μ₀) := rfl
    have hsS : ∀ n, s (n + 1) = omax (succ (s n)) (bnd (s n)) := fun _ => rfl
    have hsκ : ∀ n, s n < κ := by
      intro n
      induction n with
      | zero => rw [hs0]; exact hκ.2.1.succ_lt (omax_lt hη hμ₀)
      | succ n ih =>
        rw [hsS]
        exact omax_lt (hκ.2.1.succ_lt ih) (hbnd _ ih).1
    have hs : ∀ n, s n < s (n + 1) := by
      intro n
      rw [hsS]
      exact lt_of_lt_of_le (lt_succ_self _) (le_omax_left _ _)
    let δs := omegaSup s
    have hδsκ : δs < κ := omegaSup_lt hκ hsκ
    have hδslim : IsLimit δs := by
      apply And.intro (lt_of_le_of_lt (zero_le _) (lt_omegaSup hs 0))
      intro β hβ
      cases (lt_omegaSup_iff β).mp hβ with
      | intro n hn => exact lt_of_le_of_lt (succ_le_of_lt hn) (lt_omegaSup hs n)
    have hlt0 : omax η μ₀ < δs := lt_trans _ _ _ (lt_succ_self _) (lt_omegaSup hs 0)
    refine Exists.intro δs (And.intro (And.intro
      (lt_of_le_of_lt (le_omax_right η μ₀) hlt0) ?_)
      (And.intro (lt_of_le_of_lt (le_omax_left η μ₀) hlt0) hδsκ))
    intro y hy hyκ
    cases hcont δs y hδslim hy with
    | intro ζ hζ =>
      cases (lt_omegaSup_iff ζ).mp hζ.1 with
      | intro n hn =>
        have hyn : y < bnd (s n) :=
          (hbnd _ (hsκ n)).2 y (hmono ζ (s n) y (Or.inl hn) hζ.2) hyκ
        exact lt_trans _ _ _ hyn (lt_of_le_of_lt (by rw [hsS n]; exact le_omax_right _ _)
          (lt_omegaSup hs (n + 1)))
  · intro l hlκ hlp
    have hl : IsLimit l := by
      apply And.intro hlp.1
      intro β hβ
      cases hlp.2 β hβ with
      | intro γ hγ => exact lt_of_le_of_lt (succ_le_of_lt hγ.2.1) hγ.2.2
    apply And.intro
    · cases hlp.2 0 hlp.1 with
      | intro γ hγ => exact lt_trans _ _ _ hγ.1.1 hγ.2.2
    · intro y hy hyκ
      cases hcont l y hl hy with
      | intro ζ hζ =>
        cases hlp.2 ζ hζ.1 with
        | intro ρ hρ =>
          exact lt_trans _ _ _ (hρ.1.2 y (hmono ζ ρ y (Or.inl hρ.2.1) hζ.2) hyκ) hρ.2.2

/-- `j[C(α, ρ) ∩ α] ⊆ ρ` となる `ρ` は club -/
theorem club_j {n : Nat} (hn : 1 ≤ n) {α : Ordinal.{u}} {j : Ordinal.{u} → Ordinal.{u}}
    (hjκ : ∀ β, β < α → j β < K n) {μ₀ : Ordinal.{u}} (hμ₀ : μ₀ < K n) :
    Club (K n) (fun ρ => μ₀ < ρ ∧ ∀ x, C α ρ x → x < α → j x < ρ) := by
  have hκ : R (K n) := R_K hn
  have hc := club_absorb hκ (fun ρ y => ∃ x, C α ρ x ∧ x < α ∧ y = j x) ?_ ?_ ?_ hμ₀
  · refine Club.congr (fun ρ => ?_) hc
    apply and_congr_right
    intro _
    constructor
    · intro h x hx hxα
      exact h (j x) ⟨x, hx, hxα, rfl⟩ (hjκ x hxα)
    · intro h y hy _
      cases hy with
      | intro x hx => rw [hx.2.2]; exact h x hx.1 hx.2.1
  · intro ρ ρ' y hρ hy
    cases hy with
    | intro x hx => exact ⟨x, C_mono_base hρ hx.1, hx.2⟩
  · intro l y hl hy
    cases hy with
    | intro x hx =>
      cases C_limit hl hx.1 with
      | intro η hη => exact ⟨η, hη.1, x, hη.2, hx.2⟩
  · intro ρ hρ
    have hsm : Small (K n) (fun y => ∃ x, (C α ρ x ∧ x < α) ∧ y = j x) :=
      ((C_small hκ hρ α).mono (A := fun x => C α ρ x ∧ x < α) (fun _ h => h.1)).image j
    have hb := Small.bounded hκ.2 hsm (A := fun y => ∃ x, (C α ρ x ∧ x < α) ∧ y = j x) (by
      intro y hy
      cases hy with
      | intro x hx => rw [hx.2]; exact hjκ x hx.1.2)
    cases hb with
    | intro γ hγ =>
      refine ⟨γ, hγ.1, ?_⟩
      intro y hy _
      cases hy with
      | intro x hx => exact hγ.2 y ⟨x, ⟨hx.1, hx.2.1⟩, hx.2.2⟩

end
end OCF.Rathjen
