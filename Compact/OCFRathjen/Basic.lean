import Compact.OCFRathjen.Ordinal

/-! Generic ordinal notions: least elements, `ω`, limits, closures, enumerations, cofinality,
regularity, smallness (`Small κ A`: fewer than `κ` elements) and Cantor normal forms.

Copied from the Subsp repository (`Subsp/OCF/Jaeger/Ordinal.lean`), omitting the parts specific
to Jäger's collapsing functions (`Inaccessible`, `I`, `regPred`, `Λ₀`, the stages of `C` and `Ψ`). -/

namespace OCF.Rathjen

universe u

open Ordinal

noncomputable section

def least (P : Ordinal.{u} → Prop) : Ordinal.{u} :=
  open Classical in
  if h : ∃ ξ, P ξ then Classical.choose (Ordinal.exists_min P h) else 0

theorem least_spec (P : Ordinal.{u} → Prop) (h : ∃ ξ, P ξ) :
    P (least P) ∧ ∀ ξ, ξ < least P → ¬ P ξ := by
  unfold least
  rw [dite_eq_left h]
  exact Classical.choose_spec (Ordinal.exists_min P h)

theorem least_le (P : Ordinal.{u} → Prop) {ξ : Ordinal.{u}} (h : P ξ) : least P ≤ ξ :=
  (not_lt_iff_le ξ (least P)).mp
    (fun hlt => (least_spec P (Exists.intro ξ h)).2 ξ hlt h)

def ordNat : Nat → Ordinal.{u}
  | 0 => 0
  | n + 1 => succ (ordNat n)

def omega : Ordinal.{u} := sup (fun n : ULift.{u} Nat => ordNat n.down)

def IsLimit (α : Ordinal.{u}) : Prop := 0 < α ∧ ∀ β, β < α → succ β < α

theorem not_isLimit_succ (β : Ordinal.{u}) : ¬ IsLimit (succ β) :=
  fun h => lt_irrefl (succ β) (h.2 β (lt_succ_self β))

def IsSupOf (B : Ordinal.{u} → Prop) (ξ : Ordinal.{u}) : Prop :=
  (∀ β, B β → β ≤ ξ) ∧ ∀ η, η < ξ → ∃ β, B β ∧ η < β

def IsClosed (A : Ordinal.{u} → Prop) : Prop :=
  ∀ B : Ordinal.{u} → Prop, (∀ β, B β → A β) → (∃ β, B β) → ∀ ξ, IsSupOf B ξ → A ξ

def closure (A : Ordinal.{u} → Prop) (ξ : Ordinal.{u}) : Prop :=
  ∀ S : Ordinal.{u} → Prop, (∀ β, A β → S β) → IsClosed S → S ξ

def IsLimitPoint (A : Ordinal.{u} → Prop) (ξ : Ordinal.{u}) : Prop :=
  0 < ξ ∧ ∀ η, η < ξ → ∃ β, A β ∧ η < β ∧ β < ξ

theorem closure_iff (A : Ordinal.{u} → Prop) (ξ : Ordinal.{u}) :
    closure A ξ ↔ A ξ ∨ IsLimitPoint A ξ := by
  apply Iff.intro
  · intro h
    apply h (fun ζ => A ζ ∨ IsLimitPoint A ζ) (fun β hβ => Or.inl hβ)
    intro B hB hne ζ hζ
    cases Classical.em (B ζ) with
    | inl hζB => exact hB ζ hζB
    | inr hζB =>
      have hlt : ∀ β, B β → β < ζ := by
        intro β hβ
        cases hζ.1 β hβ with
        | inl h => exact h
        | inr h =>
          rw [h] at hβ
          exact False.elim (hζB hβ)
      apply Or.inr
      apply And.intro
      · cases hne with
        | intro β hβ => exact lt_of_le_of_lt (zero_le β) (hlt β hβ)
      · intro η hη
        cases hζ.2 η hη with
        | intro β hβ =>
          cases hB β hβ.1 with
          | inl hA => exact Exists.intro β (And.intro hA (And.intro hβ.2 (hlt β hβ.1)))
          | inr hβlim =>
            cases hβlim.2 η hβ.2 with
            | intro a ha =>
              exact Exists.intro a
                (And.intro ha.1 (And.intro ha.2.1 (lt_trans a β ζ ha.2.2 (hlt β hβ.1))))
  · intro h S hAS hS
    cases h with
    | inl hA => exact hAS ξ hA
    | inr hlim =>
      apply hS (fun β => A β ∧ β < ξ) (fun β hβ => hAS β hβ.1)
      · cases hlim.2 0 hlim.1 with
        | intro β hβ => exact Exists.intro β (And.intro hβ.1 hβ.2.2)
      · apply And.intro
        · intro β hβ
          exact Or.inl hβ.2
        · intro η hη
          cases hlim.2 η hη with
          | intro β hβ => exact Exists.intro β (And.intro (And.intro hβ.1 hβ.2.2) hβ.2.1)

def enum (X : Ordinal.{u} → Prop) : Ordinal.{u} → Ordinal.{u} :=
  lt_wellFounded.fix (fun α previous =>
    least (fun ξ => X ξ ∧ ∀ β (h : β < α), previous β h < ξ))

theorem enum_eq (X : Ordinal.{u} → Prop) (α : Ordinal.{u}) :
    enum X α = least (fun ξ => X ξ ∧ ∀ β, β < α → enum X β < ξ) :=
  WellFounded.fix_eq lt_wellFounded _ α

theorem enum_spec (X : Ordinal.{u} → Prop) (α : Ordinal.{u})
    (h : ∃ ξ, X ξ ∧ ∀ β, β < α → enum X β < ξ) :
    X (enum X α) ∧ ∀ β, β < α → enum X β < enum X α := by
  rw [enum_eq X α]
  exact (least_spec _ h).1

theorem enum_le (X : Ordinal.{u} → Prop) (α ξ : Ordinal.{u}) (hX : X ξ)
    (h : ∀ β, β < α → enum X β < ξ) : enum X α ≤ ξ := by
  rw [enum_eq X α]
  exact least_le _ (And.intro hX h)

def ordClosure (A : Ordinal.{u} → Prop) : Ordinal.{u} → Ordinal.{u} := enum (closure A)

def CofinalFrom (β α : Ordinal.{u}) : Prop :=
  ∃ f : (representative β).Carrier → Ordinal.{u}, (∀ x, f x < α) ∧ sup f = α

def cf (α : Ordinal.{u}) : Ordinal.{u} := least (fun β => CofinalFrom β α)

def IsRegular (α : Ordinal.{u}) : Prop := IsLimit α ∧ cf α = α

/-- A regular ordinal cannot inject into a smaller ordinal.  This records the
initial-ordinal consequence of `cf κ = κ` using the cofinality notion used in
this development. -/
theorem IsRegular.no_injective_to_smaller {κ β : Ordinal.{u}}
    (hκ : IsRegular κ) (hβ : β < κ)
    (f : (representative κ).Carrier → (representative β).Carrier)
    (hf : ∀ x y, f x = f y → x = y) : False := by
  classical
  let g : (representative β).Carrier → Ordinal.{u} := fun y =>
    if hy : ∃ x, f x = y then
      type ((representative κ).below (Classical.choose hy))
    else 0
  have hgf : ∀ x, g (f x) = type ((representative κ).below x) := by
    intro x
    have hx : ∃ y, f y = f x := ⟨x, rfl⟩
    have heq : Classical.choose hx = x := hf _ _ (Classical.choose_spec hx)
    simp [g, hx, heq]
  have hgbound : ∀ y, g y < κ := by
    intro y
    by_cases hy : ∃ x, f x = y
    · simp only [g, dite_eq_left hy]
      exact initial_lt κ (Classical.choose hy)
    · simp [g, hy, hκ.1.1]
  have hsup : sup g ≤ κ := (sup_le_iff g κ).mpr (fun y => Or.inl (hgbound y))
  have hκsup : κ ≤ sup g := by
    apply (not_lt_iff_le (sup g) κ).mp
    intro hsupκ
    let ξ := sup g
    have hξκ : ξ < κ := by simpa [ξ] using hsupκ
    have hsuccκ : succ ξ < κ := hκ.1.2 ξ hξκ
    obtain ⟨x, hx⟩ := initial_surjective κ (succ ξ) hsuccκ
    have hval : g (f x) = succ ξ := by
      rw [hgf x, ← hx]
    have hle : succ ξ ≤ sup g := by
      simpa only [hval] using le_sup g (f x)
    have hle' : succ ξ ≤ ξ := by simpa [ξ] using hle
    exact lt_irrefl ξ (lt_of_lt_of_le (lt_succ_self ξ) hle')
  have hsup_eq : sup g = κ := le_antisymm hsup hκsup
  have hcof : CofinalFrom β κ := ⟨g, hgbound, hsup_eq⟩
  have hcf : cf κ ≤ β := least_le _ hcof
  rw [hκ.2] at hcf
  exact lt_irrefl β (lt_of_lt_of_le hβ hcf)

def R (ξ : Ordinal.{u}) : Prop := omega < ξ ∧ IsRegular ξ

/-- A cofinal sequence shorter than a Hartogs ordinal would combine the
injections of all its initial segments into one injection of the Hartogs
ordinal.  The only cardinal-arithmetic input is an injection `X × X → X`. -/
theorem no_short_cofinal_map_to_hartogs {X : Type u} {δ : Ordinal.{u}}
    (hδ : δ < hartogs X) (g : (representative δ).Carrier → Ordinal.{u})
    (hg : ∀ i, g i < hartogs X) (hgsup : sup g = hartogs X)
    (pair : X × X → X) (hpair : ∀ a b, pair a = pair b → a = b) : False := by
  classical
  let θ := hartogs X
  obtain ⟨q, hq⟩ := (lt_hartogs_iff_injective X δ).mp hδ
  let rank : (representative θ).Carrier → Ordinal.{u} := fun x =>
    type ((representative θ).below x)
  have hindex (x : (representative θ).Carrier) :
      ∃ i, rank x < g i := by
    have hlt : rank x < sup g := by
      rw [hgsup]
      exact initial_lt θ x
    exact (lt_sup_iff g (rank x)).mp hlt
  let index (x : (representative θ).Carrier) : (representative δ).Carrier :=
    Classical.choose (hindex x)
  have hindex_spec (x : (representative θ).Carrier) : rank x < g (index x) :=
    Classical.choose_spec (hindex x)
  let embed (i : (representative δ).Carrier) :
      (representative (g i)).Carrier → X :=
    Classical.choose (injective_of_lt_hartogs (hg i))
  have hembed (i : (representative δ).Carrier) :
      ∀ a b, embed i a = embed i b → a = b :=
    Classical.choose_spec (injective_of_lt_hartogs (hg i))
  let Packed := Sigma fun i : (representative δ).Carrier =>
    (representative (g i)).Carrier
  let pack (p : Packed) : X × X :=
    (q p.1, embed p.1 p.2)
  have hpack : ∀ p r : Packed, pack p = pack r → p = r := by
    intro p r hpr
    cases p with
    | mk i a =>
      cases r with
      | mk j b =>
        have hi : i = j := hq _ _ (congrArg Prod.fst hpr)
        subst j
        have hab : a = b := hembed i a b (congrArg Prod.snd hpr)
        subst b
        rfl
  let point (x : (representative θ).Carrier) :
      (representative (g (index x))).Carrier :=
    Classical.choose (initial_surjective (g (index x)) (rank x) (hindex_spec x))
  have hpoint (x : (representative θ).Carrier) :
      rank x = type ((representative (g (index x))).below (point x)) :=
    Classical.choose_spec (initial_surjective (g (index x)) (rank x) (hindex_spec x))
  let code (x : (representative θ).Carrier) : X :=
    pair (pack ⟨index x, point x⟩)
  have hcode : ∀ x y, code x = code y → x = y := by
    intro x y hxy
    have hp := hpair _ _ hxy
    have hσ := hpack _ _ hp
    let measure (p : Packed) : Ordinal.{u} :=
      type ((representative (g p.1)).below p.2)
    have hrank := calc
      rank x = measure ⟨index x, point x⟩ := hpoint x
      _ = measure ⟨index y, point y⟩ := congrArg measure hσ
      _ = rank y := (hpoint y).symm
    exact initial_injective θ x y hrank
  exact no_injection_hartogs X code hcode

/-- Hartogs is regular when the underlying type admits an injective pairing.
The lemma above supplies the cofinality part; `hlim` supplies the limit part. -/
theorem hartogs_regular_of_pair_injective {X : Type u}
    (hlim : IsLimit (hartogs X)) (pair : X × X → X)
    (hpair : ∀ a b, pair a = pair b → a = b) : IsRegular (hartogs X) := by
  let θ := hartogs X
  have hcofinal : CofinalFrom θ θ := by
    let f : (representative θ).Carrier → Ordinal.{u} := fun x =>
      type ((representative θ).below x)
    have hlt : ∀ x, f x < θ := fun x => initial_lt θ x
    have hsup : sup f = θ := by
      apply le_antisymm
      · apply (sup_le_iff f θ).mpr
        intro x
        exact Or.inl (hlt x)
      · apply (not_lt_iff_le (sup f) θ).mp
        intro hsupθ
        let ξ := sup f
        have hξθ : ξ < θ := by simpa [ξ] using hsupθ
        obtain ⟨x, hx⟩ := initial_surjective θ (succ ξ) (hlim.2 ξ hξθ)
        have hvalue : f x = succ ξ := by simpa [f] using hx.symm
        have hle : succ ξ ≤ sup f := by
          simpa only [hvalue] using le_sup f x
        have hle' : succ ξ ≤ ξ := by simpa [ξ] using hle
        exact lt_irrefl ξ (lt_of_lt_of_le (lt_succ_self ξ) hle')
    exact ⟨f, hlt, hsup⟩
  have hcf_le : cf θ ≤ θ := least_le _ hcofinal
  have hθ_le_cf : θ ≤ cf θ := by
    apply (not_lt_iff_le (cf θ) θ).mp
    intro hcf_lt
    have hcf_def : CofinalFrom (cf θ) θ := by
      unfold cf
      exact (least_spec (fun β => CofinalFrom β θ)
        (Exists.intro θ hcofinal)).1
    obtain ⟨g, hg, hgsup⟩ := hcf_def
    exact no_short_cofinal_map_to_hartogs hcf_lt g hg hgsup pair hpair
  exact ⟨hlim, le_antisymm hcf_le hθ_le_cf⟩

/-- The Hartogs ordinal of the representative of `η` lies strictly above `η`
and no higher than any regular ordinal `κ` above `η`.  In `Setting.lean`, the
partition property strengthens this to a strict upper bound below a weakly
compact ordinal. -/
theorem IsRegular.hartogs_bounds {κ η : Ordinal.{u}} (hκ : IsRegular κ)
    (hη : η < κ) :
    η < hartogs (representative η).Carrier ∧ hartogs (representative η).Carrier ≤ κ := by
  constructor
  · apply lt_hartogs_of_injective η (fun x => x)
    intro x y h
    exact h
  · apply (not_lt_iff_le _ _).mp
    intro hk
    obtain ⟨f, hf⟩ := (lt_hartogs_iff_injective (representative η).Carrier κ).mp hk
    exact hκ.no_injective_to_smaller hη f hf


end
end OCF.Rathjen


namespace OCF.Ordinal

universe u

theorem le_of_lt {a b : Ordinal.{u}} (h : a < b) : a ≤ b := Or.inl h

theorem lt_or_le (a b : Ordinal.{u}) : a < b ∨ b ≤ a := by
  cases lt_total a b with
  | inl h => exact Or.inl h
  | inr h =>
    cases h with
    | inl h => exact Or.inr (Or.inr h.symm)
    | inr h => exact Or.inr (Or.inl h)

theorem le_or_lt (a b : Ordinal.{u}) : a ≤ b ∨ b < a := by
  cases lt_or_le b a with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h

theorem le_total (a b : Ordinal.{u}) : a ≤ b ∨ b ≤ a := by
  cases lt_or_le a b with
  | inl h => exact Or.inl (Or.inl h)
  | inr h => exact Or.inr h

theorem lt_of_le_of_ne {a b : Ordinal.{u}} (h : a ≤ b) (hne : a ≠ b) : a < b := by
  cases h with
  | inl h => exact h
  | inr h => exact absurd h hne

theorem not_lt_of_le {a b : Ordinal.{u}} (h : a ≤ b) : ¬ b < a :=
  (not_lt_iff_le b a).mpr h

theorem not_le_of_lt {a b : Ordinal.{u}} (h : a < b) : ¬ b ≤ a :=
  fun h' => not_lt_of_le h' h

theorem le_of_not_lt {a b : Ordinal.{u}} (h : ¬ a < b) : b ≤ a := (not_lt_iff_le a b).mp h

theorem lt_of_not_le {a b : Ordinal.{u}} (h : ¬ a ≤ b) : b < a := by
  cases lt_or_le b a with
  | inl h' => exact h'
  | inr h' => exact absurd h' h

theorem ne_of_lt {a b : Ordinal.{u}} (h : a < b) : a ≠ b := by
  intro e
  rw [e] at h
  exact lt_irrefl b h

theorem ne_of_gt {a b : Ordinal.{u}} (h : b < a) : a ≠ b := fun e => ne_of_lt h e.symm

theorem eq_zero_or_pos (a : Ordinal.{u}) : a = 0 ∨ 0 < a := by
  cases zero_le a with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h.symm

theorem le_zero_iff (a : Ordinal.{u}) : a ≤ 0 ↔ a = 0 := by
  apply Iff.intro
  · intro h
    exact le_antisymm h (zero_le a)
  · intro h
    rw [h]
    exact le_refl 0

theorem pos_of_ne_zero {a : Ordinal.{u}} (h : a ≠ 0) : 0 < a := (zero_lt_iff_ne_zero a).mpr h

theorem le_of_lt_succ {a b : Ordinal.{u}} (h : a < succ b) : a ≤ b := (lt_succ_iff_le a b).mp h

theorem lt_succ_of_le {a b : Ordinal.{u}} (h : a ≤ b) : a < succ b := (lt_succ_iff_le a b).mpr h

theorem succ_le_of_lt {a b : Ordinal.{u}} (h : a < b) : succ a ≤ b := (succ_le_iff_lt a b).mpr h

theorem lt_of_succ_le {a b : Ordinal.{u}} (h : succ a ≤ b) : a < b := (succ_le_iff_lt a b).mp h

theorem succ_lt_succ {a b : Ordinal.{u}} (h : a < b) : succ a < succ b :=
  lt_succ_of_le (succ_le_of_lt h)

theorem succ_inj {a b : Ordinal.{u}} (h : succ a = succ b) : a = b := by
  apply le_antisymm
  · apply le_of_lt_succ
    rw [← h]
    exact lt_succ_self a
  · apply le_of_lt_succ
    rw [h]
    exact lt_succ_self b

theorem zero_lt_succ (a : Ordinal.{u}) : 0 < succ a := lt_of_le_of_lt (zero_le a) (lt_succ_self a)

theorem succ_ne_zero (a : Ordinal.{u}) : succ a ≠ 0 := ne_of_gt (zero_lt_succ a)

theorem add_one_eq_succ (a : Ordinal.{u}) : a + succ 0 = succ a := by
  rw [add_succ, add_zero]

theorem add_lt_add_iff_right (a : Ordinal.{u}) {b c : Ordinal.{u}} : a + b < a + c ↔ b < c := by
  apply Iff.intro
  · intro h
    cases lt_or_le b c with
    | inl hbc => exact hbc
    | inr hcb => exact absurd h (not_lt_of_le (add_mono_right a hcb))
  · exact add_lt_add_right a

theorem add_le_add_iff_right (a : Ordinal.{u}) {b c : Ordinal.{u}} : a + b ≤ a + c ↔ b ≤ c := by
  apply Iff.intro
  · intro h
    apply le_of_not_lt
    intro hcb
    exact not_lt_of_le h (add_lt_add_right a hcb)
  · exact add_mono_right a

theorem lt_add_of_pos (a : Ordinal.{u}) {b : Ordinal.{u}} (h : 0 < b) : a < a + b := by
  have h' := add_lt_add_right a h
  rw [add_zero] at h'
  exact h'

theorem add_eq_zero {a b : Ordinal.{u}} (h : a + b = 0) : a = 0 ∧ b = 0 := by
  apply And.intro
  · apply (le_zero_iff a).mp
    rw [← h]
    exact le_add a b
  · apply (le_zero_iff b).mp
    rw [← h]
    exact right_le_add a b

noncomputable def supLt (β : Ordinal.{u}) (F : Ordinal.{u} → Ordinal.{u}) : Ordinal.{u} :=
  sup (fun x : (representative β).Carrier => F (type ((representative β).below x)))

theorem lt_supLt_iff (β : Ordinal.{u}) (F : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u}) :
    a < supLt β F ↔ ∃ ξ, ξ < β ∧ a < F ξ := by
  unfold supLt
  rw [lt_sup_iff]
  apply Iff.intro
  · intro h
    cases h with
    | intro x hx => exact Exists.intro _ (And.intro (initial_lt β x) hx)
  · intro h
    cases h with
    | intro ξ hξ =>
      cases initial_surjective β ξ hξ.1 with
      | intro x hx =>
        refine Exists.intro x ?_
        rw [← hx]
        exact hξ.2

theorem le_supLt (β : Ordinal.{u}) (F : Ordinal.{u} → Ordinal.{u}) {ξ : Ordinal.{u}}
    (h : ξ < β) : F ξ ≤ supLt β F := by
  apply le_of_not_lt
  intro hlt
  exact lt_irrefl _ ((lt_supLt_iff β F _).mpr (Exists.intro ξ (And.intro h hlt)))

theorem supLt_le_iff (β : Ordinal.{u}) (F : Ordinal.{u} → Ordinal.{u}) (c : Ordinal.{u}) :
    supLt β F ≤ c ↔ ∀ ξ, ξ < β → F ξ ≤ c := by
  apply Iff.intro
  · intro h ξ hξ
    exact le_trans (le_supLt β F hξ) h
  · intro h
    apply le_of_not_lt
    intro hc
    cases (lt_supLt_iff β F c).mp hc with
    | intro ξ hξ => exact not_lt_of_le (h ξ hξ.1) hξ.2

end OCF.Ordinal

namespace OCF.Rathjen

universe u

open Ordinal

noncomputable section

theorem isLimit_iff_not (α : Ordinal.{u}) (h0 : α ≠ 0) (hs : ¬ ∃ β, α = succ β) : IsLimit α := by
  apply And.intro (pos_of_ne_zero h0)
  intro β hβ
  cases succ_le_of_lt hβ with
  | inl h => exact h
  | inr h => exact absurd (Exists.intro β h.symm) hs

theorem zero_or_succ_or_limit (α : Ordinal.{u}) :
    α = 0 ∨ (∃ β, α = succ β) ∨ IsLimit α := by
  cases Classical.em (α = 0) with
  | inl h => exact Or.inl h
  | inr h0 =>
    cases Classical.em (∃ β, α = succ β) with
    | inl hs => exact Or.inr (Or.inl hs)
    | inr hs => exact Or.inr (Or.inr (isLimit_iff_not α h0 hs))

theorem zero_or_succ_of_not_isLimit {α : Ordinal.{u}} (h : ¬ IsLimit α) :
    α = 0 ∨ ∃ β, α = succ β := by
  cases zero_or_succ_or_limit α with
  | inl h0 => exact Or.inl h0
  | inr h' =>
    cases h' with
    | inl hs => exact Or.inr hs
    | inr hl => exact absurd hl h

theorem not_isLimit_zero : ¬ IsLimit (0 : Ordinal.{u}) := fun h => lt_irrefl 0 h.1

theorem IsLimit.succ_lt {α β : Ordinal.{u}} (h : IsLimit α) (hβ : β < α) : succ β < α :=
  h.2 β hβ

theorem IsLimit.ne_succ {α : Ordinal.{u}} (h : IsLimit α) (β : Ordinal.{u}) : α ≠ succ β := by
  intro e
  have := h.2 β (by rw [e]; exact lt_succ_self β)
  rw [e] at this
  exact lt_irrefl _ this

theorem ordNat_succ (n : Nat) : ordNat.{u} (n + 1) = succ (ordNat n) := rfl

theorem ordNat_zero : ordNat.{u} 0 = 0 := rfl

theorem ordNat_lt {m n : Nat} (h : m < n) : ordNat.{u} m < ordNat n := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ n ih =>
    rw [ordNat_succ]
    cases Nat.lt_succ_iff_lt_or_eq.mp h with
    | inl h' => exact lt_trans _ _ _ (ih h') (lt_succ_self _)
    | inr h' =>
      rw [h']
      exact lt_succ_self _

theorem ordNat_le {m n : Nat} (h : m ≤ n) : ordNat.{u} m ≤ ordNat n := by
  cases Nat.lt_or_eq_of_le h with
  | inl h' => exact Or.inl (ordNat_lt h')
  | inr h' =>
    rw [h']
    exact le_refl _

theorem ordNat_lt_iff {m n : Nat} : ordNat.{u} m < ordNat n ↔ m < n := by
  apply Iff.intro
  · intro h
    cases Nat.lt_or_ge m n with
    | inl h' => exact h'
    | inr h' => exact absurd h (not_lt_of_le (ordNat_le h'))
  · exact ordNat_lt

theorem ordNat_le_iff {m n : Nat} : ordNat.{u} m ≤ ordNat n ↔ m ≤ n := by
  apply Iff.intro
  · intro h
    cases Nat.lt_or_ge n m with
    | inl h' => exact absurd h (not_le_of_lt (ordNat_lt h'))
    | inr h' => exact h'
  · exact ordNat_le

theorem ordNat_injective {m n : Nat} (h : ordNat.{u} m = ordNat n) : m = n := by
  apply Nat.le_antisymm
  · apply ordNat_le_iff.mp
    rw [h]
    exact le_refl _
  · apply ordNat_le_iff.mp
    rw [h]
    exact le_refl _

theorem ordNat_lt_omega (n : Nat) : ordNat.{u} n < omega :=
  lt_of_lt_of_le (ordNat_lt (Nat.lt_succ_self n))
    (le_sup (fun k : ULift.{u} Nat => ordNat k.down) (ULift.up (n + 1)))

theorem lt_ordNat_iff {a : Ordinal.{u}} {n : Nat} : a < ordNat n ↔ ∃ m, m < n ∧ a = ordNat m := by
  apply Iff.intro
  · intro h
    induction n with
    | zero => exact absurd h (not_lt_zero a)
    | succ n ih =>
      cases le_of_lt_succ h with
      | inl h' =>
        cases ih h' with
        | intro m hm => exact Exists.intro m (And.intro (Nat.lt_succ_of_lt hm.1) hm.2)
      | inr h' => exact Exists.intro n (And.intro (Nat.lt_succ_self n) h')
  · intro h
    cases h with
    | intro m hm =>
      rw [hm.2]
      exact ordNat_lt hm.1

theorem lt_omega_iff (a : Ordinal.{u}) : a < omega ↔ ∃ n, a = ordNat n := by
  apply Iff.intro
  · intro h
    cases (lt_sup_iff _ a).mp h with
    | intro k hk =>
      cases lt_ordNat_iff.mp hk with
      | intro m hm => exact Exists.intro m hm.2
  · intro h
    cases h with
    | intro n hn =>
      rw [hn]
      exact ordNat_lt_omega n

theorem isLimit_omega : IsLimit (omega : Ordinal.{u}) := by
  apply And.intro
  · have h := ordNat_lt_omega.{u} 0
    rw [ordNat_zero] at h
    exact h
  · intro β hβ
    cases (lt_omega_iff β).mp hβ with
    | intro n hn =>
      rw [hn, ← ordNat_succ]
      exact ordNat_lt_omega (n + 1)

theorem ordNat_lt_of_isLimit {α : Ordinal.{u}} (h : IsLimit α) (n : Nat) : ordNat n < α := by
  induction n with
  | zero => exact h.1
  | succ n ih => exact h.2 _ ih

theorem omega_le_of_isLimit {α : Ordinal.{u}} (h : IsLimit α) : omega ≤ α :=
  (sup_le_iff _ α).mpr (fun k => Or.inl (ordNat_lt_of_isLimit h k.down))

theorem zero_lt_omega : (0 : Ordinal.{u}) < omega := isLimit_omega.1

/-- Every infinite ordinal is equinumerous with its successor. -/
theorem exists_injective_succ_into_of_omega_le {β : Ordinal.{u}}
    (hω : omega ≤ β) :
    ∃ f : (representative (succ β)).Carrier → (representative β).Carrier,
      ∀ x y, f x = f y → x = y := by
  classical
  let code (ξ : Ordinal.{u}) : Ordinal.{u} :=
    if htop : ξ = β then 0 else if hfinite : ξ < omega then succ ξ else ξ
  have hcode_lt {ξ : Ordinal.{u}} (hξ : ξ < succ β) : code ξ < β := by
    have hξle : ξ ≤ β := (lt_succ_iff_le ξ β).mp hξ
    by_cases htop : ξ = β
    · simp [code, htop]
      exact lt_of_lt_of_le zero_lt_omega hω
    · have hξβ : ξ < β := by
        cases hξle with
        | inl h => exact h
        | inr h => exact False.elim (htop h)
      by_cases hfinite : ξ < omega
      · simp [code, htop, hfinite]
        exact lt_of_lt_of_le (isLimit_omega.2 ξ hfinite) hω
      · simp [code, htop, hfinite]
        exact hξβ
  have hcode_pos {ξ : Ordinal.{u}} (hξ : ξ < β) : 0 < code ξ := by
    have hnot : ξ ≠ β := ne_of_lt hξ
    by_cases hfinite : ξ < omega
    · have hc : code ξ = succ ξ := by simp [code, hnot, hfinite]
      rw [hc]
      exact zero_lt_succ ξ
    · have hc : code ξ = ξ := by simp [code, hnot, hfinite]
      rw [hc]
      exact lt_of_lt_of_le zero_lt_omega ((not_lt_iff_le ξ omega).mp hfinite)
  have hcode_inj {ξ ζ : Ordinal.{u}} (hξ : ξ < succ β) (hζ : ζ < succ β)
      (heq : code ξ = code ζ) : ξ = ζ := by
    have hξle : ξ ≤ β := (lt_succ_iff_le ξ β).mp hξ
    have hζle : ζ ≤ β := (lt_succ_iff_le ζ β).mp hζ
    by_cases hξtop : ξ = β
    · subst ξ
      by_cases hζtop : ζ = β
      · exact hζtop.symm
      · have hζβ : ζ < β := by
          cases hζle with
          | inl h => exact h
          | inr h => exact False.elim (hζtop h)
        have hpos := hcode_pos hζβ
        have hzero : code β = 0 := by simp [code]
        rw [hzero] at heq
        exact False.elim (ne_of_gt hpos heq.symm)
    · have hξβ : ξ < β := by
        cases hξle with
        | inl h => exact h
        | inr h => exact False.elim (hξtop h)
      by_cases hζtop : ζ = β
      · subst ζ
        have hpos := hcode_pos hξβ
        have hzero : code β = 0 := by simp [code]
        rw [hzero] at heq
        exact False.elim (ne_of_gt hpos heq)
      · have hζβ : ζ < β := by
          cases hζle with
          | inl h => exact h
          | inr h => exact False.elim (hζtop h)
        by_cases hξfinite : ξ < omega
        · by_cases hζfinite : ζ < omega
          · have hξcode : code ξ = succ ξ := by simp [code, ne_of_lt hξβ, hξfinite]
            have hζcode : code ζ = succ ζ := by simp [code, ne_of_lt hζβ, hζfinite]
            rw [hξcode, hζcode] at heq
            apply le_antisymm
            · exact (lt_succ_iff_le ξ ζ).mp (heq ▸ lt_succ_self ξ)
            · exact (lt_succ_iff_le ζ ξ).mp (heq.symm ▸ lt_succ_self ζ)
          · have hleft : code ξ < omega := by
              rw [show code ξ = succ ξ from by
                simp [code, ne_of_lt hξβ, hξfinite]]
              exact isLimit_omega.2 ξ hξfinite
            have hright : omega ≤ code ζ := by
              rw [show code ζ = ζ from by
                simp [code, ne_of_lt hζβ, hζfinite]]
              exact (not_lt_iff_le ζ omega).mp hζfinite
            have hright' : omega ≤ code ξ := by rw [heq]; exact hright
            exact False.elim (not_lt_of_le hright' hleft)
        · by_cases hζfinite : ζ < omega
          · have hleft : omega ≤ code ξ := by
              rw [show code ξ = ξ from by
                simp [code, ne_of_lt hξβ, hξfinite]]
              exact (not_lt_iff_le ξ omega).mp hξfinite
            have hright : code ζ < omega := by
              rw [show code ζ = succ ζ from by
                simp [code, ne_of_lt hζβ, hζfinite]]
              exact isLimit_omega.2 ζ hζfinite
            have hleft' : omega ≤ code ζ := by rw [heq] at hleft; exact hleft
            exact False.elim (not_lt_of_le hleft' hright)
          · have hξcode : code ξ = ξ := by simp [code, ne_of_lt hξβ, hξfinite]
            have hζcode : code ζ = ζ := by simp [code, ne_of_lt hζβ, hζfinite]
            rw [hξcode, hζcode] at heq
            exact heq
  let f (x : (representative (succ β)).Carrier) :
      (representative β).Carrier :=
    Classical.choose (initial_surjective β (code (type ((representative (succ β)).below x)))
      (hcode_lt (initial_lt (succ β) x)))
  have hf_spec (x : (representative (succ β)).Carrier) :
      code (type ((representative (succ β)).below x)) =
        type ((representative β).below (f x)) :=
    Classical.choose_spec (initial_surjective β
      (code (type ((representative (succ β)).below x)))
      (hcode_lt (initial_lt (succ β) x)))
  refine ⟨f, ?_⟩
  intro x y hxy
  have hrank : code (type ((representative (succ β)).below x)) =
      code (type ((representative (succ β)).below y)) := by
    calc
      _ = type ((representative β).below (f x)) := hf_spec x
      _ = type ((representative β).below (f y)) :=
        congrArg (fun z => type ((representative β).below z)) hxy
      _ = _ := (hf_spec y).symm
  exact initial_injective (succ β) x y
    (hcode_inj (initial_lt (succ β) x) (initial_lt (succ β) y) hrank)

/-- Hartogs of an infinite type is a limit ordinal.  If it were a successor,
the predecessor embeds into the type and its successor embeds back into the
predecessor by shifting the finite initial segment. -/
theorem hartogs_isLimit_of_omega_lt {X : Type u} (hω : omega < hartogs X) :
    IsLimit (hartogs X) := by
  let θ := hartogs X
  apply isLimit_iff_not θ
    (ne_of_gt (lt_trans 0 omega (hartogs X) zero_lt_omega hω))
  intro hsucc
  obtain ⟨β, hθ⟩ := hsucc
  have hβθ : β < θ := by rw [hθ]; exact lt_succ_self β
  have hωβ : omega ≤ β := by
    apply (lt_succ_iff_le omega β).mp
    rw [← hθ]
    exact hω
  obtain ⟨shift, hshift⟩ := exists_injective_succ_into_of_omega_le hωβ
  obtain ⟨embed, hembed⟩ := (lt_hartogs_iff_injective X β).mp hβθ
  let iso := representativeOrderIso (representative θ)
    ((type_representative θ).trans hθ)
  let f : (representative θ).Carrier → X := fun x => embed (shift (iso.toFun x))
  have hf : ∀ x y, f x = f y → x = y := by
    intro x y hxy
    have h1 := hembed _ _ hxy
    have h2 := hshift _ _ h1
    have h3 := congrArg iso.invFun h2
    simpa only [iso.left_inv] using h3
  exact no_injection_hartogs X f hf

def natOf (a : Ordinal.{u}) : Nat :=
  open Classical in
  if h : ∃ n, a = ordNat n then Classical.choose h else 0

theorem natOf_ordNat (n : Nat) : natOf (ordNat.{u} n) = n := by
  have h : ∃ m, ordNat.{u} n = ordNat m := Exists.intro n rfl
  unfold natOf
  rw [dite_eq_left h]
  exact (ordNat_injective (Classical.choose_spec h)).symm

def IsPrincipal (α : Ordinal.{u}) : Prop := α ≠ 0 ∧ AddPrincipal α

theorem IsPrincipal.pos {α : Ordinal.{u}} (h : IsPrincipal α) : 0 < α := pos_of_ne_zero h.1

theorem isPrincipal_one : IsPrincipal (succ (0 : Ordinal.{u})) :=
  And.intro (succ_ne_zero 0) succ_zero_principal

theorem IsPrincipal.add_eq {p x y : Ordinal.{u}} (hp : IsPrincipal p) (h : x + y = p) :
    (x = p ∧ y = 0) ∨ y = p := by
  have hx : x ≤ p := by
    rw [← h]
    exact le_add x y
  have hy : y ≤ p := by
    rw [← h]
    exact right_le_add x y
  cases hy with
  | inr hy => exact Or.inr hy
  | inl hy =>
    cases hx with
    | inl hx =>
      have := hp.2 x y hx hy
      rw [h] at this
      exact absurd this (lt_irrefl p)
    | inr hx =>
      apply Or.inl
      apply And.intro hx
      apply add_right_cancel (a := x)
      rw [add_zero, h, hx]

theorem IsPrincipal.succ_lt {p x : Ordinal.{u}} (hp : IsPrincipal p) (h1 : succ 0 < p)
    (hx : x < p) : succ x < p := by
  rw [← add_one_eq_succ]
  exact hp.2 x _ hx h1

theorem IsPrincipal.isLimit {p : Ordinal.{u}} (hp : IsPrincipal p) (h1 : succ 0 < p) :
    IsLimit p :=
  And.intro hp.pos (fun _ hx => hp.succ_lt h1 hx)

theorem AddPrincipal.add_lt_of_lt {p x y : Ordinal.{u}} (hp : AddPrincipal p) (hx : x < p)
    (hy : y < p) : x + y < p := hp x y hx hy

theorem addPrincipal_of_limit {p : Ordinal.{u}}
    (h : ∀ η, η < p → ∃ q, AddPrincipal q ∧ η < q ∧ q ≤ p) : AddPrincipal p := by
  intro x y hx hy
  cases le_total x y with
  | inl hxy =>
    cases h y hy with
    | intro q hq => exact lt_of_lt_of_le (hq.1 x y (lt_of_le_of_lt hxy hq.2.1) hq.2.1) hq.2.2
  | inr hyx =>
    cases h x hx with
    | intro q hq => exact lt_of_lt_of_le (hq.1 x y hq.2.1 (lt_of_le_of_lt hyx hq.2.1)) hq.2.2

theorem IsRegular.isLimit {κ : Ordinal.{u}} (h : IsRegular κ) : IsLimit κ := h.1

theorem IsRegular.pos {κ : Ordinal.{u}} (h : IsRegular κ) : 0 < κ := h.1.1

theorem IsRegular.supLt_lt {κ β : Ordinal.{u}} (hκ : IsRegular κ) (hβ : β < κ)
    {F : Ordinal.{u} → Ordinal.{u}} (hF : ∀ ξ, ξ < β → F ξ < κ) : supLt β F < κ := by
  have hle : supLt β F ≤ κ := (supLt_le_iff β F κ).mpr (fun ξ hξ => Or.inl (hF ξ hξ))
  cases hle with
  | inl h => exact h
  | inr h =>
    have hcof : CofinalFrom β κ :=
      Exists.intro (fun x => F (type ((representative β).below x)))
        (And.intro (fun x => hF _ (initial_lt β x)) h)
    have hcf : cf κ ≤ β := least_le _ hcof
    rw [hκ.2] at hcf
    exact absurd hβ (not_lt_of_le hcf)

theorem IsRegular.add_lt {κ a b : Ordinal.{u}} (hκ : IsRegular κ) (ha : a < κ) (hb : b < κ) :
    a + b < κ := by
  apply lt_of_not_le
  intro hle
  cases le_add_cases a b κ hle (not_lt_of_le (le_of_lt ha)) with
  | intro d hd =>
    have hdκ : d < κ := lt_of_le_of_lt hd.1 hb
    cases zero_or_succ_or_limit d with
    | inl h0 =>
      have := hd.2
      rw [h0, add_zero] at this
      rw [this] at ha
      exact lt_irrefl a ha
    | inr h =>
      cases h with
      | inl hs =>
        cases hs with
        | intro e he =>
          have := hd.2
          rw [he, add_succ] at this
          exact hκ.isLimit.ne_succ _ this
      | inr hl =>
        have hsup : κ ≤ supLt d (fun x => a + x) := by
          apply le_of_not_lt
          intro hlt
          rw [hd.2] at hlt
          cases (lt_add_iff a d _).mp hlt with
          | inl hlta =>
            have : a + 0 ≤ supLt d (fun x => a + x) := le_supLt d _ hl.1
            rw [add_zero] at this
            exact not_lt_of_le this hlta
          | inr hx =>
            cases hx with
            | intro x hx =>
              have h1 : a + succ x ≤ supLt d (fun x => a + x) := le_supLt d _ (hl.2 x hx.1)
              rw [add_succ] at h1
              exact not_lt_of_le hx.2 (lt_of_lt_of_le (lt_succ_self _) h1)
        have hlt : supLt d (fun x => a + x) < κ := by
          apply hκ.supLt_lt hdκ
          intro ξ hξ
          rw [hd.2]
          exact add_lt_add_right a hξ
        exact not_lt_of_le hsup hlt

theorem IsRegular.addPrincipal {κ : Ordinal.{u}} (hκ : IsRegular κ) : AddPrincipal κ :=
  fun _ _ ha hb => hκ.add_lt ha hb

theorem IsRegular.isPrincipal {κ : Ordinal.{u}} (hκ : IsRegular κ) : IsPrincipal κ :=
  And.intro (ne_of_gt hκ.pos) hκ.addPrincipal

def mul (a : Ordinal.{u}) : Ordinal.{u} → Ordinal.{u} :=
  lt_wellFounded.fix (fun b ih =>
    sup (fun x : (representative b).Carrier =>
      ih (type ((representative b).below x)) (initial_lt b x) + a))

theorem mul_eq (a b : Ordinal.{u}) : mul a b = supLt b (fun ξ => mul a ξ + a) :=
  WellFounded.fix_eq lt_wellFounded _ b

theorem mul_add_le {a x b : Ordinal.{u}} (h : x < b) : mul a x + a ≤ mul a b := by
  rw [mul_eq a b]
  exact le_supLt b (fun ξ => mul a ξ + a) h

theorem mul_pair_lt {a b x y : Ordinal.{u}} (hx : x < b) (hy : y < a) :
    mul a x + y < mul a b :=
  lt_of_lt_of_le (add_lt_add_right _ hy) (mul_add_le hx)

theorem mul_pair_inj {a x x' y y' : Ordinal.{u}} (hy : y < a) (hy' : y' < a)
    (h : mul a x + y = mul a x' + y') : x = x' ∧ y = y' := by
  have hx : x = x' := by
    cases lt_total x x' with
    | inl hlt =>
      have h1 := lt_of_lt_of_le (mul_pair_lt (b := x') (a := a) hlt hy) (le_add _ y')
      rw [h] at h1
      exact absurd h1 (lt_irrefl _)
    | inr h' =>
      cases h' with
      | inl e => exact e
      | inr hlt =>
        have h1 := lt_of_lt_of_le (mul_pair_lt (b := x) (a := a) hlt hy') (le_add _ y)
        rw [h] at h1
        exact absurd h1 (lt_irrefl _)
  apply And.intro hx
  rw [hx] at h
  exact add_right_cancel h

theorem IsRegular.mul_lt {κ a b : Ordinal.{u}} (hκ : IsRegular κ) (ha : a < κ) (hb : b < κ) :
    mul a b < κ := by
  induction b using lt_wellFounded.induction with
  | h b ih =>
    rw [mul_eq]
    apply hκ.supLt_lt hb
    intro ξ hξ
    exact hκ.add_lt (ih ξ hξ (lt_trans ξ b κ hξ hb)) ha

def Small (κ : Ordinal.{u}) (A : Ordinal.{u} → Prop) : Prop :=
  ∃ β, β < κ ∧ ∃ f : Ordinal.{u} → Ordinal.{u},
    (∀ x, A x → f x < β) ∧ ∀ x y, A x → A y → f x = f y → x = y

theorem Small.mono {κ : Ordinal.{u}} {A B : Ordinal.{u} → Prop} (h : Small κ B)
    (hAB : ∀ x, A x → B x) : Small κ A := by
  cases h with
  | intro β hβ =>
    cases hβ.2 with
    | intro f hf =>
      exact Exists.intro β (And.intro hβ.1 (Exists.intro f (And.intro
        (fun x hx => hf.1 x (hAB x hx))
        (fun x y hx hy e => hf.2 x y (hAB x hx) (hAB y hy) e))))

theorem small_lt {κ β : Ordinal.{u}} (hβ : β < κ) : Small κ (fun x => x < β) :=
  Exists.intro β (And.intro hβ (Exists.intro (fun x => x) (And.intro
    (fun _ hx => hx) (fun _ _ _ _ e => e))))

theorem Small.union {κ : Ordinal.{u}} {A B : Ordinal.{u} → Prop} (hκ : IsRegular κ)
    (hA : Small κ A) (hB : Small κ B) : Small κ (fun x => A x ∨ B x) := by
  classical
  cases hA with
  | intro βA hA =>
    cases hA.2 with
    | intro fA hfA =>
      cases hB with
      | intro βB hB =>
        cases hB.2 with
        | intro fB hfB =>
          refine Exists.intro (βA + βB) (And.intro (hκ.add_lt hA.1 hB.1) ?_)
          refine Exists.intro (fun x => if A x then fA x else βA + fB x) (And.intro ?_ ?_)
          · intro x hx
            by_cases hAx : A x
            · simp only [hAx, ↓reduceIte]
              exact lt_of_lt_of_le (hfA.1 x hAx) (le_add βA βB)
            · simp only [hAx, ↓reduceIte]
              cases hx with
              | inl h => exact absurd h hAx
              | inr h => exact add_lt_add_right βA (hfB.1 x h)
          · intro x y hx hy e
            by_cases hAx : A x
            · by_cases hAy : A y
              · simp only [hAx, hAy, ↓reduceIte] at e
                exact hfA.2 x y hAx hAy e
              · simp only [hAx, hAy, ↓reduceIte] at e
                have := lt_of_lt_of_le (hfA.1 x hAx) (le_add βA (fB y))
                rw [e] at this
                exact absurd this (lt_irrefl _)
            · by_cases hAy : A y
              · simp only [hAx, hAy, ↓reduceIte] at e
                have := lt_of_lt_of_le (hfA.1 y hAy) (le_add βA (fB x))
                rw [← e] at this
                exact absurd this (lt_irrefl _)
              · simp only [hAx, hAy, ↓reduceIte] at e
                have hBx : B x := by
                  cases hx with
                  | inl h => exact absurd h hAx
                  | inr h => exact h
                have hBy : B y := by
                  cases hy with
                  | inl h => exact absurd h hAy
                  | inr h => exact h
                exact hfB.2 x y hBx hBy (add_right_cancel e)

theorem Small.image {κ : Ordinal.{u}} {A : Ordinal.{u} → Prop} (hA : Small κ A)
    (g : Ordinal.{u} → Ordinal.{u}) : Small κ (fun z => ∃ x, A x ∧ z = g x) := by
  classical
  cases hA with
  | intro β hA =>
    cases hA.2 with
    | intro f hf =>
      let pre : Ordinal.{u} → Ordinal.{u} := fun z =>
        if h : ∃ x, A x ∧ z = g x then Classical.choose h else 0
      have hpre : ∀ z (h : ∃ x, A x ∧ z = g x), A (pre z) ∧ z = g (pre z) := by
        intro z h
        have e : pre z = Classical.choose h := dite_eq_left h
        rw [e]
        exact Classical.choose_spec h
      refine Exists.intro β (And.intro hA.1 (Exists.intro (fun z => f (pre z)) (And.intro ?_ ?_)))
      · intro z hz
        exact hf.1 _ (hpre z hz).1
      · intro z w hz hw e
        have := hf.2 _ _ (hpre z hz).1 (hpre w hw).1 e
        rw [(hpre z hz).2, (hpre w hw).2, this]

theorem Small.image2 {κ : Ordinal.{u}} {A B : Ordinal.{u} → Prop} (hκ : IsRegular κ)
    (hA : Small κ A) (hB : Small κ B) (g : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}) :
    Small κ (fun z => ∃ x y, A x ∧ B y ∧ z = g x y) := by
  classical
  cases hA with
  | intro βA hA =>
    cases hA.2 with
    | intro fA hfA =>
      cases hB with
      | intro βB hB =>
        cases hB.2 with
        | intro fB hfB =>
          let P : Ordinal.{u} → Prop := fun z => ∃ x y, A x ∧ B y ∧ z = g x y
          let preA : Ordinal.{u} → Ordinal.{u} := fun z =>
            if h : P z then Classical.choose h else 0
          let preB : Ordinal.{u} → Ordinal.{u} := fun z =>
            if h : P z then Classical.choose (Classical.choose_spec h) else 0
          have hpre : ∀ z, P z → A (preA z) ∧ B (preB z) ∧ z = g (preA z) (preB z) := by
            intro z h
            have e1 : preA z = Classical.choose h := dite_eq_left h
            have e2 : preB z = Classical.choose (Classical.choose_spec h) := dite_eq_left h
            rw [e1, e2]
            exact Classical.choose_spec (Classical.choose_spec h)
          refine Exists.intro (mul βA βB) (And.intro (hκ.mul_lt hA.1 hB.1) ?_)
          refine Exists.intro (fun z => mul βA (fB (preB z)) + fA (preA z)) (And.intro ?_ ?_)
          · intro z hz
            exact mul_pair_lt (hfB.1 _ (hpre z hz).2.1) (hfA.1 _ (hpre z hz).1)
          · intro z w hz hw e
            have hp := mul_pair_inj (hfA.1 _ (hpre z hz).1) (hfA.1 _ (hpre w hw).1) e
            have eB := hfB.2 _ _ (hpre z hz).2.1 (hpre w hw).2.1 hp.1
            have eA := hfA.2 _ _ (hpre z hz).1 (hpre w hw).1 hp.2
            rw [(hpre z hz).2.2, (hpre w hw).2.2, eA, eB]

theorem Small.iUnion {κ : Ordinal.{u}} {I : Ordinal.{u} → Prop}
    {A : Ordinal.{u} → Ordinal.{u} → Prop} (hκ : IsRegular κ) (hI : Small κ I)
    (hA : ∀ i, I i → Small κ (A i)) : Small κ (fun z => ∃ i, I i ∧ A i z) := by
  classical
  cases hI with
  | intro βI hI =>
    cases hI.2 with
    | intro fI hfI =>
      let bnd : Ordinal.{u} → Ordinal.{u} := fun i =>
        if h : I i then Classical.choose (hA i h) else 0
      let enc : Ordinal.{u} → Ordinal.{u} → Ordinal.{u} := fun i =>
        if h : I i then Classical.choose (Classical.choose_spec (hA i h)).2 else fun _ => 0
      have hbnd : ∀ i, bnd i < κ := by
        intro i
        by_cases h : I i
        · have e : bnd i = Classical.choose (hA i h) := dite_eq_left h
          rw [e]
          exact (Classical.choose_spec (hA i h)).1
        · have e : bnd i = 0 := dite_eq_right h
          rw [e]
          exact hκ.pos
      have henc : ∀ i, I i → (∀ x, A i x → enc i x < bnd i) ∧
          ∀ x y, A i x → A i y → enc i x = enc i y → x = y := by
        intro i h
        have e1 : bnd i = Classical.choose (hA i h) := dite_eq_left h
        have e2 : enc i = Classical.choose (Classical.choose_spec (hA i h)).2 := dite_eq_left h
        rw [e1, e2]
        exact Classical.choose_spec (Classical.choose_spec (hA i h)).2
      let inv : Ordinal.{u} → Ordinal.{u} := fun y =>
        if h : ∃ i, I i ∧ fI i = y then Classical.choose h else 0
      have hinv : ∀ i, I i → inv (fI i) = i := by
        intro i hi
        have h : ∃ j, I j ∧ fI j = fI i := Exists.intro i (And.intro hi rfl)
        have e : inv (fI i) = Classical.choose h := dite_eq_left h
        rw [e]
        exact hfI.2 _ _ (Classical.choose_spec h).1 hi (Classical.choose_spec h).2
      let γ := supLt βI (fun y => bnd (inv y))
      have hγ : γ < κ := hκ.supLt_lt hI.1 (fun y _ => hbnd (inv y))
      have hbndγ : ∀ i, I i → bnd i ≤ γ := by
        intro i hi
        have := le_supLt βI (fun y => bnd (inv y)) (hfI.1 i hi)
        rw [hinv i hi] at this
        exact this
      let idx : Ordinal.{u} → Ordinal.{u} := fun z =>
        if h : ∃ i, I i ∧ A i z then Classical.choose h else 0
      have hidx : ∀ z, (∃ i, I i ∧ A i z) → I (idx z) ∧ A (idx z) z := by
        intro z h
        have e : idx z = Classical.choose h := dite_eq_left h
        rw [e]
        exact Classical.choose_spec h
      refine Exists.intro (mul γ βI) (And.intro (hκ.mul_lt hγ hI.1) ?_)
      refine Exists.intro (fun z => mul γ (fI (idx z)) + enc (idx z) z) (And.intro ?_ ?_)
      · intro z hz
        have hi := hidx z hz
        exact mul_pair_lt (hfI.1 _ hi.1)
          (lt_of_lt_of_le ((henc _ hi.1).1 z hi.2) (hbndγ _ hi.1))
      · intro z w hz hw e
        have hiz := hidx z hz
        have hiw := hidx w hw
        have hp := mul_pair_inj
          (lt_of_lt_of_le ((henc _ hiz.1).1 z hiz.2) (hbndγ _ hiz.1))
          (lt_of_lt_of_le ((henc _ hiw.1).1 w hiw.2) (hbndγ _ hiw.1)) e
        have ei : idx z = idx w := hfI.2 _ _ hiz.1 hiw.1 hp.1
        have he := hp.2
        rw [ei] at he
        rw [ei] at hiz
        exact (henc _ hiw.1).2 z w hiz.2 hiw.2 he

theorem not_small_self {κ : Ordinal.{u}} (hκ : IsRegular κ) : ¬ Small κ (fun x => x < κ) := by
  classical
  intro h
  cases h with
  | intro β hβ =>
    cases hβ.2 with
    | intro f hf =>
      let G : Ordinal.{u} → Ordinal.{u} := fun y =>
        if h : ∃ x, x < κ ∧ f x = y then Classical.choose h else 0
      have hG : ∀ x, x < κ → G (f x) = x := by
        intro x hx
        have h : ∃ z, z < κ ∧ f z = f x := Exists.intro x (And.intro hx rfl)
        have e : G (f x) = Classical.choose h := dite_eq_left h
        rw [e]
        exact hf.2 _ _ (Classical.choose_spec h).1 hx (Classical.choose_spec h).2
      have hGκ : ∀ y, y < β → G y < κ := by
        intro y _
        by_cases h : ∃ x, x < κ ∧ f x = y
        · have e : G y = Classical.choose h := dite_eq_left h
          rw [e]
          exact (Classical.choose_spec h).1
        · have e : G y = 0 := dite_eq_right h
          rw [e]
          exact hκ.pos
      have hs := hκ.supLt_lt hβ.1 hGκ
      have hsucc : succ (supLt β G) < κ := hκ.isLimit.succ_lt hs
      have hle : G (f (succ (supLt β G))) ≤ supLt β G := le_supLt β G (hf.1 _ hsucc)
      rw [hG _ hsucc] at hle
      exact not_lt_of_le hle (lt_succ_self _)

theorem exists_not_mem_of_small {κ : Ordinal.{u}} {A : Ordinal.{u} → Prop} (hκ : IsRegular κ)
    (h : Small κ A) : ∃ ξ, ξ < κ ∧ ¬ A ξ := by
  apply Classical.byContradiction
  intro hn
  apply not_small_self hκ
  apply h.mono
  intro x hx
  apply Classical.byContradiction
  intro hAx
  exact hn (Exists.intro x (And.intro hx hAx))

theorem small_natOrd {κ : Ordinal.{u}} (hω : omega < κ) :
    Small κ (fun x => ∃ n, x = ordNat n) :=
  (small_lt hω).mono (fun x hx => (lt_omega_iff x).mpr hx)

end
end OCF.Rathjen

namespace OCF.Rathjen

universe u

open Ordinal

noncomputable section

def listSum : List Ordinal.{u} → Ordinal.{u}
  | [] => 0
  | a :: l => a + listSum l

theorem listSum_nil : listSum ([] : List Ordinal.{u}) = 0 := rfl

theorem listSum_cons (a : Ordinal.{u}) (l : List Ordinal.{u}) :
    listSum (a :: l) = a + listSum l := rfl

theorem listSum_append (l₁ l₂ : List Ordinal.{u}) :
    listSum (l₁ ++ l₂) = listSum l₁ + listSum l₂ := by
  induction l₁ with
  | nil => exact (zero_add _).symm
  | cons a l ih =>
    show a + listSum (l ++ l₂) = (a + listSum l) + listSum l₂
    rw [ih, add_assoc]

theorem le_listSum_of_mem {l : List Ordinal.{u}} {p : Ordinal.{u}} (h : p ∈ l) :
    p ≤ listSum l := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons a l ih =>
    cases List.mem_cons.mp h with
    | inl h => rw [h]; exact le_add a _
    | inr h => exact le_trans (ih h) (right_le_add a _)

theorem listSum_lt {q : Ordinal.{u}} (hq : IsPrincipal q) {l : List Ordinal.{u}}
    (h : ∀ p, p ∈ l → p < q) : listSum l < q := by
  induction l with
  | nil => exact hq.pos
  | cons a l ih =>
    exact hq.2 a _ (h a (List.mem_cons_self))
      (ih (fun p hp => h p (List.mem_cons_of_mem a hp)))

def Nonincr (l : List Ordinal.{u}) : Prop := l.Pairwise (fun a b => b ≤ a)

def CNF (α : Ordinal.{u}) (l : List Ordinal.{u}) : Prop :=
  (∀ p, p ∈ l → IsPrincipal p) ∧ Nonincr l ∧ α = listSum l

def NFSum (α : Ordinal.{u}) (l : List Ordinal.{u}) : Prop := CNF α l ∧ ∀ p, p ∈ l → p < α

theorem cnf_zero : CNF (0 : Ordinal.{u}) [] :=
  And.intro (fun _ h => absurd h List.not_mem_nil) (And.intro List.Pairwise.nil rfl)

theorem cnf_single {p : Ordinal.{u}} (hp : IsPrincipal p) : CNF p [p] := by
  refine And.intro ?_ (And.intro (List.pairwise_singleton _ p) (add_zero p).symm)
  intro q hq
  rw [List.mem_singleton.mp hq]
  exact hp

theorem CNF.principal {α : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α l) {p : Ordinal.{u}}
    (hp : p ∈ l) : IsPrincipal p := h.1 p hp

theorem CNF.le {α : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α l) {p : Ordinal.{u}}
    (hp : p ∈ l) : p ≤ α := by
  rw [h.2.2]
  exact le_listSum_of_mem hp

theorem CNF.tail {α p : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α (p :: l)) :
    CNF (listSum l) l :=
  And.intro (fun q hq => h.1 q (List.mem_cons_of_mem p hq))
    (And.intro (List.pairwise_cons.mp h.2.1).2 rfl)

theorem CNF.head_principal {α p : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α (p :: l)) :
    IsPrincipal p := h.1 p List.mem_cons_self

theorem CNF.head_ge {α p : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α (p :: l))
    {q : Ordinal.{u}} (hq : q ∈ l) : q ≤ p := (List.pairwise_cons.mp h.2.1).1 q hq

theorem CNF.mem_le_head {α p : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α (p :: l))
    {q : Ordinal.{u}} (hq : q ∈ p :: l) : q ≤ p := by
  cases List.mem_cons.mp hq with
  | inl e => rw [e]; exact le_refl p
  | inr hq => exact h.head_ge hq

theorem CNF.head_le {α p : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α (p :: l)) : p ≤ α :=
  h.le List.mem_cons_self

theorem CNF.pos {α p : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α (p :: l)) : 0 < α :=
  lt_of_lt_of_le h.head_principal.pos h.head_le

theorem CNF.eq {α : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α l) : α = listSum l := h.2.2

theorem CNF.lt_of_head_lt {α p q : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α (p :: l))
    (hq : IsPrincipal q) (hpq : p < q) : α < q := by
  rw [h.eq]
  exact listSum_lt hq (fun x hx => lt_of_le_of_lt (h.mem_le_head hx) hpq)

theorem CNF.head_max {α p q : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α (p :: l))
    (hq : IsPrincipal q) (hqα : q ≤ α) : q ≤ p := by
  apply le_of_not_lt
  intro hpq
  exact not_lt_of_le hqα (h.lt_of_head_lt hq hpq)

theorem exists_largest_principal (α : Ordinal.{u}) (h : α ≠ 0) :
    ∃ p, IsPrincipal p ∧ p ≤ α ∧ ∀ q, IsPrincipal q → q ≤ α → q ≤ p := by
  classical
  let F : Ordinal.{u} → Ordinal.{u} := fun x => if IsPrincipal x then x else 0
  have hF1 : ∀ x, IsPrincipal x → F x = x := by
    intro x hx
    show (if IsPrincipal x then x else 0) = x
    simp only [hx, ↓reduceIte]
  have hF0 : ∀ x, ¬ IsPrincipal x → F x = 0 := by
    intro x hx
    show (if IsPrincipal x then x else 0) = 0
    simp only [hx, ↓reduceIte]
  have hmax : ∀ q, IsPrincipal q → q ≤ α → q ≤ supLt (succ α) F := by
    intro q hq hqα
    have := le_supLt (succ α) F (lt_succ_of_le hqα)
    rw [hF1 q hq] at this
    exact this
  have hle : supLt (succ α) F ≤ α := by
    apply (supLt_le_iff _ _ _).mpr
    intro ξ hξ
    by_cases hP : IsPrincipal ξ
    · rw [hF1 ξ hP]
      exact le_of_lt_succ hξ
    · rw [hF0 ξ hP]
      exact zero_le α
  have hmem : ∀ x, x < supLt (succ α) F → ∃ ξ, IsPrincipal ξ ∧ x < ξ ∧ ξ ≤ supLt (succ α) F := by
    intro x hx
    cases (lt_supLt_iff _ _ _).mp hx with
    | intro ξ hξ =>
      by_cases hP : IsPrincipal ξ
      · rw [hF1 ξ hP] at hξ
        exact Exists.intro ξ (And.intro hP (And.intro hξ.2
          (hmax ξ hP (le_of_lt_succ hξ.1))))
      · rw [hF0 ξ hP] at hξ
        exact absurd hξ.2 (not_lt_zero x)
  refine Exists.intro (supLt (succ α) F) (And.intro (And.intro ?_ ?_) (And.intro hle hmax))
  · have h1 := hmax _ isPrincipal_one (succ_le_of_lt (pos_of_ne_zero h))
    exact ne_of_gt (lt_of_lt_of_le (zero_lt_succ 0) h1)
  · apply addPrincipal_of_limit
    intro η hη
    cases hmem η hη with
    | intro ξ hξ => exact Exists.intro ξ (And.intro hξ.1.2 hξ.2)

theorem cnf_exists (α : Ordinal.{u}) : ∃ l, CNF α l := by
  induction α using lt_wellFounded.induction with
  | h α ih =>
    by_cases h0 : α = 0
    · rw [h0]
      exact Exists.intro [] cnf_zero
    · cases exists_largest_principal α h0 with
      | intro p hp =>
        cases exists_add_of_le p α hp.2.1 with
        | intro β hβ =>
          have hβα : β < α := by
            apply lt_of_le_of_ne (by rw [hβ]; exact right_le_add p β)
            intro e
            have hfix : p + α = α := by
              rw [e] at hβ
              exact hβ.symm
            have h1 : succ 0 + α = α := by
              apply le_antisymm
              · have := add_mono_left (succ_le_of_lt hp.1.pos) α
                rw [hfix] at this
                exact this
              · exact right_le_add _ _
            have hstage : ∀ n, principalStage p n + α = α := by
              intro n
              induction n with
              | zero =>
                show succ p + α = α
                rw [← add_one_eq_succ, add_assoc, h1, hfix]
              | succ n ih =>
                show (principalStage p n + principalStage p n) + α = α
                rw [add_assoc, ih, ih]
            have hhull : principalHull p ≤ α := by
              apply (sup_le_iff _ α).mpr
              intro n
              have := le_add (principalStage p n.down) α
              rw [hstage] at this
              exact this
            have hP : IsPrincipal (principalHull p) :=
              And.intro (ne_of_gt (lt_of_le_of_lt (zero_le p) (lt_principalHull p)))
                (principalHull_principal p)
            exact not_lt_of_le (hp.2.2 _ hP hhull) (lt_principalHull p)
          cases ih β hβα with
          | intro l hl =>
            refine Exists.intro (p :: l) (And.intro ?_ (And.intro ?_ ?_))
            · intro q hq
              cases List.mem_cons.mp hq with
              | inl e => rw [e]; exact hp.1
              | inr hq => exact hl.1 q hq
            · apply List.pairwise_cons.mpr
              apply And.intro _ hl.2.1
              intro q hq
              exact hp.2.2 q (hl.1 q hq) (le_trans (hl.le hq)
                (by rw [hβ]; exact right_le_add p β))
            · rw [listSum_cons, ← hl.eq]
              exact hβ

theorem cnf_unique {α : Ordinal.{u}} {l l' : List Ordinal.{u}} (h : CNF α l) (h' : CNF α l') :
    l = l' := by
  induction l generalizing α l' with
  | nil =>
    cases l' with
    | nil => rfl
    | cons q r =>
      have := h'.pos
      rw [h.eq, listSum_nil] at this
      exact absurd this (lt_irrefl 0)
  | cons p r ih =>
    cases l' with
    | nil =>
      have := h.pos
      rw [h'.eq, listSum_nil] at this
      exact absurd this (lt_irrefl 0)
    | cons q r' =>
      have hpq : p = q := le_antisymm (h'.head_max h.head_principal h.head_le)
        (h.head_max h'.head_principal h'.head_le)
      rw [← hpq] at h'
      have hs : listSum r = listSum r' := add_right_cancel (h.eq.symm.trans h'.eq)
      have ht := h'.tail
      rw [← hs] at ht
      rw [hpq, ih h.tail ht, ← hpq]

theorem cnf_of_principal {α : Ordinal.{u}} {l : List Ordinal.{u}} (hα : IsPrincipal α)
    (h : CNF α l) : l = [α] := cnf_unique h (cnf_single hα)

theorem nfSum_of_cnf {α : Ordinal.{u}} {l : List Ordinal.{u}} (h : CNF α l)
    (hP : ¬ IsPrincipal α) : NFSum α l := by
  apply And.intro h
  intro p hp
  apply lt_of_le_of_ne (h.le hp)
  intro e
  rw [← e] at hP
  exact hP (h.principal hp)

theorem NFSum.not_principal {α : Ordinal.{u}} {l : List Ordinal.{u}} (h : NFSum α l)
    (hα : IsPrincipal α) : False := by
  rw [cnf_of_principal hα h.1] at h
  exact lt_irrefl α (h.2 α List.mem_cons_self)

theorem NFSum.ne_zero {α : Ordinal.{u}} {l : List Ordinal.{u}} (h : NFSum α l) (hα : α ≠ 0) :
    2 ≤ l.length := by
  cases l with
  | nil =>
    rw [h.1.eq] at hα
    exact absurd rfl hα
  | cons p r =>
    cases r with
    | nil =>
      have e := h.1.eq
      rw [listSum_cons, listSum_nil, add_zero] at e
      exact absurd (e ▸ h.2 p List.mem_cons_self) (lt_irrefl p)
    | cons q r => exact Nat.le_add_left 2 r.length

theorem lemma_1_1 (α : Ordinal.{u}) (_h0 : α ≠ 0) (hP : ¬ IsPrincipal α) :
    ∃ l, NFSum α l ∧ ∀ l', NFSum α l' → l' = l := by
  cases cnf_exists α with
  | intro l hl =>
    exact Exists.intro l (And.intro (nfSum_of_cnf hl hP) (fun l' h' => cnf_unique h'.1 hl))

theorem cnf_add {y z : Ordinal.{u}} {ly lz : List Ordinal.{u}} (hy : CNF y ly) (hz : CNF z lz) :
    ∃ l, CNF (y + z) l ∧ ∀ p, p ∈ l → p ∈ ly ∨ p ∈ lz := by
  induction ly generalizing y with
  | nil =>
    refine Exists.intro lz (And.intro ?_ (fun p hp => Or.inr hp))
    rw [hy.eq, listSum_nil, zero_add]
    exact hz
  | cons p r ih =>
    cases lz with
    | nil =>
      refine Exists.intro (p :: r) (And.intro ?_ (fun q hq => Or.inl hq))
      rw [hz.eq, listSum_nil, add_zero]
      exact hy
    | cons q rz =>
      cases le_or_lt q p with
      | inl hqp =>
        cases ih hy.tail with
        | intro l0 hl0 =>
          refine Exists.intro (p :: l0) (And.intro (And.intro ?_ (And.intro ?_ ?_)) ?_)
          · intro x hx
            cases List.mem_cons.mp hx with
            | inl e => rw [e]; exact hy.head_principal
            | inr hx => exact hl0.1.principal hx
          · apply List.pairwise_cons.mpr
            apply And.intro _ hl0.1.2.1
            intro x hx
            cases hl0.2 x hx with
            | inl hr => exact hy.head_ge hr
            | inr hq => exact le_trans (hz.mem_le_head hq) hqp
          · rw [listSum_cons, ← hl0.1.eq, hy.eq, listSum_cons, add_assoc]
          · intro x hx
            cases List.mem_cons.mp hx with
            | inl e => rw [e]; exact Or.inl List.mem_cons_self
            | inr hx =>
              cases hl0.2 x hx with
              | inl hr => exact Or.inl (List.mem_cons_of_mem p hr)
              | inr hq => exact Or.inr hq
      | inr hpq =>
        have hyq : y < q := hy.lt_of_head_lt hz.head_principal hpq
        refine Exists.intro (q :: rz) (And.intro ?_ (fun x hx => Or.inr hx))
        have e : y + z = z := by
          rw [hz.eq, listSum_cons, ← add_assoc, hz.head_principal.2.absorb hyq]
        rw [e]
        exact hz

def IsComponent (α p : Ordinal.{u}) : Prop := ∃ l, CNF α l ∧ p ∈ l

theorem isComponent_add {y z p : Ordinal.{u}} (h : IsComponent (y + z) p) :
    IsComponent y p ∨ IsComponent z p := by
  cases h with
  | intro l hl =>
    cases cnf_exists y with
    | intro ly hy =>
      cases cnf_exists z with
      | intro lz hz =>
        cases cnf_add hy hz with
        | intro l' hl' =>
          rw [cnf_unique hl.1 hl'.1] at hl
          cases hl'.2 p hl.2 with
          | inl h => exact Or.inl (Exists.intro ly (And.intro hy h))
          | inr h => exact Or.inr (Exists.intro lz (And.intro hz h))

theorem isComponent_of_principal {α p : Ordinal.{u}} (hα : IsPrincipal α)
    (h : IsComponent α p) : p = α := by
  cases h with
  | intro l hl =>
    rw [cnf_of_principal hα hl.1] at hl
    exact List.mem_singleton.mp hl.2

theorem IsComponent.le {α p : Ordinal.{u}} (h : IsComponent α p) : p ≤ α := by
  cases h with
  | intro l hl => exact hl.1.le hl.2

theorem IsComponent.principal {α p : Ordinal.{u}} (h : IsComponent α p) : IsPrincipal p := by
  cases h with
  | intro l hl => exact hl.1.principal hl.2

theorem isComponent_zero {p : Ordinal.{u}} (h : IsComponent 0 p) : False := by
  cases h with
  | intro l hl =>
    rw [cnf_unique hl.1 cnf_zero] at hl
    exact List.not_mem_nil hl.2

theorem IsPrincipal.add_cases {x y : Ordinal.{u}} (h : IsPrincipal (x + y)) :
    (x + y = x ∧ y = 0) ∨ x + y = y := by
  cases h.add_eq rfl with
  | inl h' => exact Or.inl (And.intro h'.1.symm h'.2)
  | inr h' => exact Or.inr h'.symm

end
end OCF.Rathjen
