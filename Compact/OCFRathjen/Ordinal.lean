/-! Ordinals as well-order classes: order, suprema, Hartogs, arithmetic and principal ordinals.

Copied unchanged from the Subsp repository (`Subsp/OCF/Ordinal.lean`). -/

namespace OCF

universe u

structure WellOrder where
  Carrier : Type u
  lt : Carrier → Carrier → Prop
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ a b c, lt a b → lt b c → lt a c
  total : ∀ a b, lt a b ∨ a = b ∨ lt b a
  wellFounded : WellFounded lt

namespace WellOrder

structure Iso (A B : WellOrder.{u}) where
  toFun : A.Carrier → B.Carrier
  invFun : B.Carrier → A.Carrier
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b
  lt_iff : ∀ a b, B.lt (toFun a) (toFun b) ↔ A.lt a b

def Iso.refl (A : WellOrder.{u}) : Iso A A where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  lt_iff _ _ := Iff.intro (fun h => h) (fun h => h)

def Iso.trans {A B C : WellOrder.{u}} (e : Iso A B) (f : Iso B C) : Iso A C where
  toFun a := f.toFun (e.toFun a)
  invFun c := e.invFun (f.invFun c)
  left_inv a := by
    rw [f.left_inv, e.left_inv]
  right_inv c := by
    rw [e.right_inv, f.right_inv]
  lt_iff a b := Iff.trans (f.lt_iff (e.toFun a) (e.toFun b)) (e.lt_iff a b)

def Iso.symm {A B : WellOrder.{u}} (e : Iso A B) : Iso B A where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  lt_iff a b := by
    have h := e.lt_iff (e.invFun a) (e.invFun b)
    rw [e.right_inv a, e.right_inv b] at h
    exact h.symm

def below (A : WellOrder.{u}) (a : A.Carrier) : WellOrder.{u} where
  Carrier := { b : A.Carrier // A.lt b a }
  lt b c := A.lt b.1 c.1
  irrefl b := A.irrefl b.1
  trans b c d hbc hcd := A.trans b.1 c.1 d.1 hbc hcd
  total b c := by
    cases A.total b.1 c.1 with
    | inl h => exact Or.inl h
    | inr h =>
      cases h with
      | inl h => exact Or.inr (Or.inl (Subtype.ext h))
      | inr h => exact Or.inr (Or.inr h)
  wellFounded := InvImage.wf Subtype.val A.wellFounded

def Iso.below {A B : WellOrder.{u}} (e : Iso A B) (a : A.Carrier) :
    Iso (A.below a) (B.below (e.toFun a)) where
  toFun b := ⟨e.toFun b.1, (e.lt_iff b.1 a).mpr b.2⟩
  invFun b := ⟨e.invFun b.1, by
    apply (e.lt_iff (e.invFun b.1) a).mp
    rw [e.right_inv b.1]
    exact b.2⟩
  left_inv b := Subtype.ext (e.left_inv b.1)
  right_inv b := Subtype.ext (e.right_inv b.1)
  lt_iff b c := e.lt_iff b.1 c.1

def belowBelowIso (A : WellOrder.{u}) (a : A.Carrier) (b : (A.below a).Carrier) :
    Iso ((A.below a).below b) (A.below b.1) where
  toFun c := ⟨c.1.1, c.2⟩
  invFun c := ⟨⟨c.1, A.trans c.1 b.1 a c.2 b.2⟩, c.2⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv c := by
    apply Subtype.ext
    rfl
  lt_iff _ _ := Iff.intro (fun h => h) (fun h => h)

def Below (A B : WellOrder.{u}) : Prop :=
  ∃ b : B.Carrier, Nonempty (Iso A (B.below b))

theorem Below.iso_right {A B C : WellOrder.{u}} (e : Iso B C) (h : Below A B) :
    Below A C := by
  cases h with
  | intro b hb =>
    cases hb with
    | intro f =>
      exact Exists.intro (e.toFun b) (Nonempty.intro (f.trans (e.below b)))

theorem Below.iso_left {A B C : WellOrder.{u}} (e : Iso A B) (h : Below B C) :
    Below A C := by
  cases h with
  | intro c hc =>
    cases hc with
    | intro f => exact Exists.intro c (Nonempty.intro (e.trans f))

theorem acc_of_iso {A B : WellOrder.{u}} (e : Iso A B) (h : Acc Below B) :
    Acc Below A := by
  induction h generalizing A with
  | intro B _ ih =>
    apply Acc.intro
    intro C hC
    exact ih C (Below.iso_right e hC) (Iso.refl C)

theorem below_acc (A : WellOrder.{u}) (a : A.Carrier) : Acc Below (A.below a) := by
  induction a using A.wellFounded.induction with
  | h a ih =>
    apply Acc.intro
    intro B hB
    cases hB with
    | intro b hb =>
      cases hb with
      | intro e =>
        exact acc_of_iso (e.trans (belowBelowIso A a b)) (ih b.1 b.2)

theorem below_wellFounded : WellFounded Below.{u} := by
  apply WellFounded.intro
  intro A
  apply Acc.intro
  intro B hB
  cases hB with
  | intro a ha =>
    cases ha with
    | intro e => exact acc_of_iso e (below_acc A a)

theorem Below.irrefl (A : WellOrder.{u}) : ¬ Below A A := by
  have h := below_wellFounded.apply A
  induction h with
  | intro A _ ih =>
    intro hAA
    exact ih A hAA hAA

theorem Below.trans {A B C : WellOrder.{u}} (hAB : Below A B) (hBC : Below B C) :
    Below A C := by
  cases hBC with
  | intro c hc =>
    cases hc with
    | intro e =>
      cases Below.iso_right e hAB with
      | intro b hb =>
        cases hb with
        | intro f =>
          exact Exists.intro b.1 (Nonempty.intro (f.trans (belowBelowIso C c b)))

theorem Below.congr {A B C D : WellOrder.{u}} (e : Iso A B) (f : Iso C D) :
    Below A C ↔ Below B D := by
  apply Iff.intro
  · intro h
    exact Below.iso_right f (Below.iso_left e.symm h)
  · intro h
    exact Below.iso_right f.symm (Below.iso_left e h)

theorem not_below_of_iso {A B : WellOrder.{u}} (e : Iso A B) : ¬ Below A B := by
  intro h
  exact Below.irrefl A (Below.iso_right e.symm h)

theorem below_self (A : WellOrder.{u}) (a : A.Carrier) : Below (A.below a) A :=
  Exists.intro a (Nonempty.intro (Iso.refl (A.below a)))

theorem below_below_of_lt (A : WellOrder.{u}) (a b : A.Carrier) (h : A.lt a b) :
    Below (A.below a) (A.below b) :=
  Exists.intro ⟨a, h⟩ (Nonempty.intro (belowBelowIso A b ⟨a, h⟩).symm)

theorem lt_of_below_below (A : WellOrder.{u}) (a b : A.Carrier)
    (h : Below (A.below a) (A.below b)) : A.lt a b := by
  cases A.total a b with
  | inl hab => exact hab
  | inr hrest =>
    cases hrest with
    | inl hab =>
      cases hab
      exact False.elim (Below.irrefl (A.below a) h)
    | inr hba =>
      exact False.elim
        (Below.irrefl (A.below a) (Below.trans h (below_below_of_lt A b a hba)))

theorem eq_of_below_iso (A : WellOrder.{u}) (a b : A.Carrier)
    (e : Iso (A.below a) (A.below b)) : a = b := by
  cases A.total a b with
  | inl hab => exact False.elim (not_below_of_iso e (below_below_of_lt A a b hab))
  | inr hrest =>
    cases hrest with
    | inl hab => exact hab
    | inr hba =>
      exact False.elim (not_below_of_iso e.symm (below_below_of_lt A b a hba))

theorem exists_min (A : WellOrder.{u}) (P : A.Carrier → Prop) (h : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, A.lt b a → ¬ P b := by
  classical
  have descend : ∀ a, P a → ∃ c, P c ∧ ∀ b, A.lt b c → ¬ P b := by
    intro a
    induction a using A.wellFounded.induction with
    | h a ih =>
      intro ha
      by_cases hbelow : ∃ b, A.lt b a ∧ P b
      · cases hbelow with
        | intro b hb => exact ih b hb.1 hb.2
      · refine Exists.intro a (And.intro ha ?_)
        intro b hba hb
        exact hbelow (Exists.intro b (And.intro hba hb))
  cases h with
  | intro a ha => exact descend a ha

def Matches (A B : WellOrder.{u}) (a : A.Carrier) (b : B.Carrier) : Prop :=
  Nonempty (Iso (A.below a) (B.below b))

theorem Matches.unique_left {A B : WellOrder.{u}} {a c : A.Carrier} {b : B.Carrier}
    (h : Matches A B a b) (k : Matches A B c b) : a = c := by
  cases h with
  | intro e =>
    cases k with
    | intro f => exact eq_of_below_iso A a c (e.trans f.symm)

theorem Matches.unique_right {A B : WellOrder.{u}} {a : A.Carrier} {b d : B.Carrier}
    (h : Matches A B a b) (k : Matches A B a d) : b = d := by
  cases h with
  | intro e =>
    cases k with
    | intro f => exact eq_of_below_iso B b d (e.symm.trans f)

theorem Matches.lt_iff {A B : WellOrder.{u}} {a c : A.Carrier} {b d : B.Carrier}
    (h : Matches A B a b) (k : Matches A B c d) : B.lt b d ↔ A.lt a c := by
  cases h with
  | intro e =>
    cases k with
    | intro f =>
      apply Iff.intro
      · intro hbd
        exact lt_of_below_below A a c
          ((Below.congr e f).mpr (below_below_of_lt B b d hbd))
      · intro hac
        exact lt_of_below_below B b d
          ((Below.congr e f).mp (below_below_of_lt A a c hac))

theorem Matches.down {A B : WellOrder.{u}} {a : A.Carrier} {b : B.Carrier}
    (h : Matches A B a b) (d : B.Carrier) (hdb : B.lt d b) :
    ∃ c, A.lt c a ∧ Matches A B c d := by
  cases h with
  | intro e =>
    let c := e.invFun ⟨d, hdb⟩
    have f := ((belowBelowIso A a c).symm.trans (e.below c)).trans
      (belowBelowIso B b (e.toFun c))
    have he : (e.toFun c).1 = d := congrArg Subtype.val (e.right_inv ⟨d, hdb⟩)
    rw [he] at f
    exact Exists.intro c.1 (And.intro c.2 (Nonempty.intro f))

theorem Matches.below_right {A B : WellOrder.{u}} (b : B.Carrier)
    (a : A.Carrier) (c : (B.below b).Carrier) :
    Matches A (B.below b) a c ↔ Matches A B a c.1 := by
  apply Iff.intro
  · intro h
    cases h with
    | intro e => exact Nonempty.intro (e.trans (belowBelowIso B b c))
  · intro h
    cases h with
    | intro e => exact Nonempty.intro (e.trans (belowBelowIso B b c).symm)

theorem iso_of_matches {A B : WellOrder.{u}}
    (hA : ∀ a : A.Carrier, ∃ b : B.Carrier, Matches A B a b)
    (hB : ∀ b : B.Carrier, ∃ a : A.Carrier, Matches A B a b) : Nonempty (Iso A B) := by
  classical
  let f : A.Carrier → B.Carrier := fun a => Classical.choose (hA a)
  let g : B.Carrier → A.Carrier := fun b => Classical.choose (hB b)
  have hf : ∀ a, Matches A B a (f a) := fun a => Classical.choose_spec (hA a)
  have hg : ∀ b, Matches A B (g b) b := fun b => Classical.choose_spec (hB b)
  exact Nonempty.intro {
    toFun := f
    invFun := g
    left_inv := fun a => Matches.unique_left (hg (f a)) (hf a)
    right_inv := fun b => Matches.unique_right (hf (g b)) (hg b)
    lt_iff := fun a c => Matches.lt_iff (hf a) (hf c)
  }

theorem compare (A B : WellOrder.{u}) : Below A B ∨ Nonempty (Iso A B) ∨ Below B A := by
  classical
  induction A using below_wellFounded.induction generalizing B with
  | h A ih =>
    by_cases hBA : Below B A
    · exact Or.inr (Or.inr hBA)
    · have hA : ∀ a : A.Carrier, ∃ b : B.Carrier, Matches A B a b := by
        intro a
        cases ih (A.below a) (below_self A a) B with
        | inl h => exact h
        | inr h =>
          cases h with
          | inl h =>
            cases h with
            | intro e => exact False.elim (hBA (Exists.intro a (Nonempty.intro e.symm)))
          | inr h => exact False.elim (hBA (Below.trans h (below_self A a)))
      by_cases hB : ∀ b : B.Carrier, ∃ a : A.Carrier, Matches A B a b
      · exact Or.inr (Or.inl (iso_of_matches hA hB))
      · have hmissing : ∃ b : B.Carrier, ¬ ∃ a : A.Carrier, Matches A B a b :=
          Classical.not_forall.mp hB
        cases B.exists_min (fun b => ¬ ∃ a, Matches A B a b) hmissing with
        | intro b hb =>
          have hAc : ∀ a : A.Carrier, ∃ c : (B.below b).Carrier,
              Matches A (B.below b) a c := by
            intro a
            cases hA a with
            | intro c hc =>
              have hcb : B.lt c b := by
                cases B.total c b with
                | inl h => exact h
                | inr h =>
                  cases h with
                  | inl h =>
                    cases h
                    exact False.elim (hb.1 (Exists.intro a hc))
                  | inr h =>
                    cases Matches.down hc b h with
                    | intro d hd => exact False.elim (hb.1 (Exists.intro d hd.2))
              exact Exists.intro ⟨c, hcb⟩ ((Matches.below_right b a ⟨c, hcb⟩).mpr hc)
          have hBc : ∀ c : (B.below b).Carrier, ∃ a : A.Carrier,
              Matches A (B.below b) a c := by
            intro c
            have hc : ∃ a : A.Carrier, Matches A B a c.1 :=
              Classical.byContradiction (fun h => hb.2 c.1 c.2 h)
            cases hc with
            | intro a ha =>
              exact Exists.intro a ((Matches.below_right b a c).mpr ha)
          exact Or.inl (Exists.intro b (iso_of_matches hAc hBc))

end WellOrder
end OCF

namespace OCF

universe u

def WellOrder.isoSetoid : Setoid WellOrder.{u} where
  r A B := Nonempty (WellOrder.Iso A B)
  iseqv := {
    refl := fun A => Nonempty.intro (WellOrder.Iso.refl A)
    symm := fun h => by
      cases h with
      | intro e => exact Nonempty.intro e.symm
    trans := fun hAB hBC => by
      cases hAB with
      | intro e =>
        cases hBC with
        | intro f => exact Nonempty.intro (e.trans f)
  }

def Ordinal : Type (u + 1) := Quotient WellOrder.isoSetoid.{u}

namespace Ordinal

def type (A : WellOrder.{u}) : Ordinal.{u} := Quotient.mk WellOrder.isoSetoid A

def lt (a b : Ordinal.{u}) : Prop :=
  Quotient.liftOn₂ a b WellOrder.Below (by
    intro A B C D hAC hBD
    cases hAC with
    | intro e =>
      cases hBD with
      | intro f => exact propext (WellOrder.Below.congr e f))

instance : LT Ordinal.{u} where
  lt := lt

theorem type_eq_of_iso {A B : WellOrder.{u}} (e : WellOrder.Iso A B) :
    type A = type B := Quotient.sound (Nonempty.intro e)

theorem iso_of_type_eq {A B : WellOrder.{u}} (h : type A = type B) :
    Nonempty (WellOrder.Iso A B) := Quotient.exact h

theorem type_acc (A : WellOrder.{u}) : Acc (fun a b : Ordinal.{u} => a < b) (type A) := by
  have hA := WellOrder.below_wellFounded.apply A
  induction hA with
  | intro A _ ih =>
    apply Acc.intro
    intro b
    refine Quotient.inductionOn b ?_
    intro B hBA
    exact ih B hBA

theorem lt_wellFounded : WellFounded (fun a b : Ordinal.{u} => a < b) := by
  apply WellFounded.intro
  intro a
  refine Quotient.inductionOn a ?_
  intro A
  exact type_acc A

theorem lt_irrefl (a : Ordinal.{u}) : ¬ a < a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact WellOrder.Below.irrefl A

theorem lt_trans (a b c : Ordinal.{u}) : a < b → b < c → a < c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C hAB hBC
  exact WellOrder.Below.trans hAB hBC

theorem lt_asymm {a b : Ordinal.{u}} (hab : a < b) : ¬ b < a := by
  intro hba
  exact lt_irrefl a (lt_trans a b a hab hba)

theorem lt_total (a b : Ordinal.{u}) : a < b ∨ a = b ∨ b < a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  cases WellOrder.compare A B with
  | inl h => exact Or.inl h
  | inr h =>
    cases h with
    | inl h =>
      cases h with
      | intro e => exact Or.inr (Or.inl (type_eq_of_iso e))
    | inr h => exact Or.inr (Or.inr h)

instance : LE Ordinal.{u} where
  le a b := a < b ∨ a = b

theorem le_refl (a : Ordinal.{u}) : a ≤ a := Or.inr rfl

theorem le_trans {a b c : Ordinal.{u}} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases hab with
  | inl hab =>
    cases hbc with
    | inl hbc => exact Or.inl (lt_trans a b c hab hbc)
    | inr hbc =>
      cases hbc
      exact Or.inl hab
  | inr hab =>
    cases hab
    exact hbc

theorem le_antisymm {a b : Ordinal.{u}} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases hab with
  | inl hab =>
    cases hba with
    | inl hba => exact False.elim (lt_asymm hab hba)
    | inr hba => exact hba.symm
  | inr hab => exact hab

theorem not_lt_iff_le (a b : Ordinal.{u}) : (¬ a < b) ↔ b ≤ a := by
  apply Iff.intro
  · intro h
    cases lt_total a b with
    | inl hab => exact False.elim (h hab)
    | inr hrest =>
      cases hrest with
      | inl hab => exact Or.inr hab.symm
      | inr hba => exact Or.inl hba
  · intro h hab
    cases h with
    | inl hba => exact lt_asymm hab hba
    | inr hba =>
      cases hba
      exact lt_irrefl a hab

theorem lt_type_iff (a : Ordinal.{u}) (B : WellOrder.{u}) :
    a < type B ↔ ∃ b : B.Carrier, a = type (B.below b) := by
  refine Quotient.inductionOn a ?_
  intro A
  apply Iff.intro
  · intro h
    cases h with
    | intro b hb =>
      cases hb with
      | intro e => exact Exists.intro b (type_eq_of_iso e)
  · intro h
    cases h with
    | intro b hb => exact Exists.intro b (iso_of_type_eq hb)

theorem representative_exists (a : Ordinal.{u}) : ∃ A : WellOrder.{u}, type A = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Exists.intro A rfl

noncomputable def representative (a : Ordinal.{u}) : WellOrder.{u} :=
  Classical.choose (representative_exists a)

theorem type_representative (a : Ordinal.{u}) : type (representative a) = a :=
  Classical.choose_spec (representative_exists a)

theorem initial_lt (a : Ordinal.{u}) (x : (representative a).Carrier) :
    type ((representative a).below x) < a := by
  have h : type ((representative a).below x) < type (representative a) :=
    WellOrder.below_self (representative a) x
  rw [type_representative a] at h
  exact h

theorem initial_injective (a : Ordinal.{u}) (x y : (representative a).Carrier)
    (h : type ((representative a).below x) = type ((representative a).below y)) : x = y := by
  cases iso_of_type_eq h with
  | intro e => exact WellOrder.eq_of_below_iso (representative a) x y e

theorem initial_surjective (a b : Ordinal.{u}) (h : b < a) :
    ∃ x : (representative a).Carrier, b = type ((representative a).below x) := by
  apply (lt_type_iff b (representative a)).mp
  rw [type_representative a]
  exact h

theorem exists_min (P : Ordinal.{u} → Prop) (h : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, b < a → ¬ P b := by
  classical
  have descend : ∀ a, P a → ∃ c, P c ∧ ∀ b, b < c → ¬ P b := by
    intro a
    induction a using lt_wellFounded.induction with
    | h a ih =>
      intro ha
      by_cases hbelow : ∃ b, b < a ∧ P b
      · cases hbelow with
        | intro b hb => exact ih b hb.1 hb.2
      · refine Exists.intro a (And.intro ha ?_)
        intro b hba hb
        exact hbelow (Exists.intro b (And.intro hba hb))
  cases h with
  | intro a ha => exact descend a ha

end Ordinal
end OCF

namespace OCF.Ordinal

universe u

theorem initial_lt_iff (a : Ordinal.{u}) (x y : (representative a).Carrier) :
    type ((representative a).below x) < type ((representative a).below y) ↔
      (representative a).lt x y := by
  apply Iff.intro
  · intro h
    exact WellOrder.lt_of_below_below (representative a) x y h
  · intro h
    exact WellOrder.below_below_of_lt (representative a) x y h

def orderOn {X : Type u} (f : X → Ordinal.{u})
    (hf : ∀ x y, f x = f y → x = y) : WellOrder.{u} where
  Carrier := X
  lt x y := f x < f y
  irrefl x := lt_irrefl (f x)
  trans x y z hxy hyz := lt_trans (f x) (f y) (f z) hxy hyz
  total x y := by
    cases lt_total (f x) (f y) with
    | inl h => exact Or.inl h
    | inr h =>
      cases h with
      | inl h => exact Or.inr (Or.inl (hf x y h))
      | inr h => exact Or.inr (Or.inr h)
  wellFounded := InvImage.wf f lt_wellFounded

noncomputable def orderOnBelowIso {X : Type u} (f : X → Ordinal.{u})
    (hf : ∀ x y, f x = f y → x = y)
    (hd : ∀ x a, a < f x → ∃ y, f y = a) (x : X) :
    WellOrder.Iso ((orderOn f hf).below x) (representative (f x)) := by
  let F : ((orderOn f hf).below x).Carrier → (representative (f x)).Carrier :=
    fun y => Classical.choose (initial_surjective (f x) (f y.1) y.2)
  have hF : ∀ y, f y.1 = type ((representative (f x)).below (F y)) :=
    fun y => Classical.choose_spec (initial_surjective (f x) (f y.1) y.2)
  let G : (representative (f x)).Carrier → ((orderOn f hf).below x).Carrier :=
    fun b =>
      let y := Classical.choose (hd x _ (initial_lt (f x) b))
      have hy : f y = type ((representative (f x)).below b) :=
        Classical.choose_spec (hd x _ (initial_lt (f x) b))
      ⟨y, by
        change f y < f x
        rw [hy]
        exact initial_lt (f x) b⟩
  have hG : ∀ b, f (G b).1 = type ((representative (f x)).below b) :=
    fun b => Classical.choose_spec (hd x _ (initial_lt (f x) b))
  exact {
    toFun := F
    invFun := G
    left_inv := fun y => Subtype.ext (hf _ _ ((hG (F y)).trans (hF y).symm))
    right_inv := fun b => initial_injective (f x) _ _ ((hF (G b)).symm.trans (hG b))
    lt_iff := fun y z => by
      have h := initial_lt_iff (f x) (F y) (F z)
      rw [← hF y, ← hF z] at h
      exact h.symm
  }

theorem type_orderOn_below {X : Type u} (f : X → Ordinal.{u})
    (hf : ∀ x y, f x = f y → x = y)
    (hd : ∀ x a, a < f x → ∃ y, f y = a) (x : X) :
    type ((orderOn f hf).below x) = f x :=
  (type_eq_of_iso (orderOnBelowIso f hf hd x)).trans (type_representative (f x))

theorem lt_type_orderOn_iff {X : Type u} (f : X → Ordinal.{u})
    (hf : ∀ x y, f x = f y → x = y)
    (hd : ∀ x a, a < f x → ∃ y, f y = a) (a : Ordinal.{u}) :
    a < type (orderOn f hf) ↔ ∃ x, a = f x := by
  apply Iff.intro
  · intro h
    cases (lt_type_iff a (orderOn f hf)).mp h with
    | intro x hx => exact Exists.intro x (hx.trans (type_orderOn_below f hf hd x))
  · intro h
    cases h with
    | intro x hx =>
      apply (lt_type_iff a (orderOn f hf)).mpr
      exact Exists.intro x (hx.trans (type_orderOn_below f hf hd x).symm)

end OCF.Ordinal

namespace OCF.Ordinal

universe u

def SupPoint {I : Type u} (f : I → Ordinal.{u}) :=
  (i : I) × (representative (f i)).Carrier

noncomputable def supPointValue {I : Type u} (f : I → Ordinal.{u}) (p : SupPoint f) :
    Ordinal.{u} := type ((representative (f p.1)).below p.2)

def supSetoid {I : Type u} (f : I → Ordinal.{u}) : Setoid (SupPoint f) where
  r p q := supPointValue f p = supPointValue f q
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h k => h.trans k
  }

def SupCarrier {I : Type u} (f : I → Ordinal.{u}) := Quotient (supSetoid f)

noncomputable def supValue {I : Type u} (f : I → Ordinal.{u}) (x : SupCarrier f) :
    Ordinal.{u} := Quotient.liftOn x (supPointValue f) (fun _ _ h => h)

theorem supValue_injective {I : Type u} (f : I → Ordinal.{u}) (x y : SupCarrier f) :
    supValue f x = supValue f y → x = y := by
  refine Quotient.inductionOn₂ x y ?_
  intro p q h
  exact Quotient.sound h

theorem supValue_downward {I : Type u} (f : I → Ordinal.{u}) (x : SupCarrier f)
    (a : Ordinal.{u}) : a < supValue f x → ∃ y, supValue f y = a := by
  refine Quotient.inductionOn x ?_
  intro p h
  have ha : a < f p.1 := lt_trans a _ (f p.1) h (initial_lt (f p.1) p.2)
  cases initial_surjective (f p.1) a ha with
  | intro b hb =>
    exact Exists.intro (Quotient.mk (supSetoid f) ⟨p.1, b⟩) hb.symm

noncomputable def sup {I : Type u} (f : I → Ordinal.{u}) : Ordinal.{u} :=
  type (orderOn (supValue f) (supValue_injective f))

theorem lt_sup_iff {I : Type u} (f : I → Ordinal.{u}) (a : Ordinal.{u}) :
    a < sup f ↔ ∃ i, a < f i := by
  apply Iff.intro
  · intro h
    cases (lt_type_orderOn_iff (supValue f) (supValue_injective f)
        (supValue_downward f) a).mp h with
    | intro x hx =>
      revert hx
      refine Quotient.inductionOn x ?_
      intro p hp
      rw [hp]
      exact Exists.intro p.1 (initial_lt (f p.1) p.2)
  · intro h
    cases h with
    | intro i hi =>
      cases initial_surjective (f i) a hi with
      | intro b hb =>
        apply (lt_type_orderOn_iff (supValue f) (supValue_injective f)
          (supValue_downward f) a).mpr
        exact Exists.intro (Quotient.mk (supSetoid f) ⟨i, b⟩) hb

theorem le_sup {I : Type u} (f : I → Ordinal.{u}) (i : I) : f i ≤ sup f := by
  apply (not_lt_iff_le (sup f) (f i)).mp
  intro h
  exact lt_irrefl (sup f) ((lt_sup_iff f (sup f)).mpr (Exists.intro i h))

theorem sup_le_iff {I : Type u} (f : I → Ordinal.{u}) (b : Ordinal.{u}) :
    sup f ≤ b ↔ ∀ i, f i ≤ b := by
  apply Iff.intro
  · intro h i
    exact le_trans (le_sup f i) h
  · intro h
    apply (not_lt_iff_le b (sup f)).mp
    intro hb
    cases (lt_sup_iff f b).mp hb with
    | intro i hi => exact ((not_lt_iff_le b (f i)).mpr (h i)) hi

theorem sup_mono {I : Type u} (f g : I → Ordinal.{u}) (h : ∀ i, f i ≤ g i) :
    sup f ≤ sup g := by
  apply (sup_le_iff f (sup g)).mpr
  intro i
  exact le_trans (h i) (le_sup g i)

noncomputable def zero : Ordinal.{u} := sup (fun x : PEmpty.{u+1} => nomatch x)

noncomputable instance : OfNat Ordinal.{u} 0 where
  ofNat := zero

theorem not_lt_zero (a : Ordinal.{u}) : ¬ a < 0 := by
  intro h
  cases (lt_sup_iff (fun x : PEmpty.{u+1} => nomatch x) a).mp h with
  | intro x _ => exact PEmpty.elim x

theorem zero_le (a : Ordinal.{u}) : 0 ≤ a :=
  (not_lt_iff_le a 0).mp (not_lt_zero a)

theorem zero_lt_iff_ne_zero (a : Ordinal.{u}) : 0 < a ↔ a ≠ 0 := by
  apply Iff.intro
  · intro h heq
    cases heq
    exact lt_irrefl 0 h
  · intro h
    cases zero_le a with
    | inl hlt => exact hlt
    | inr heq => exact False.elim (h heq.symm)

noncomputable def succValue (a : Ordinal.{u}) : Option (representative a).Carrier → Ordinal.{u}
  | none => a
  | some x => type ((representative a).below x)

theorem succValue_injective (a : Ordinal.{u}) (x y : Option (representative a).Carrier) :
    succValue a x = succValue a y → x = y := by
  cases x with
  | none =>
    cases y with
    | none => intro _; rfl
    | some y =>
      intro h
      have hy := initial_lt a y
      change a = type ((representative a).below y) at h
      rw [← h] at hy
      exact False.elim (lt_irrefl a hy)
  | some x =>
    cases y with
    | none =>
      intro h
      have hx := initial_lt a x
      change type ((representative a).below x) = a at h
      rw [h] at hx
      exact False.elim (lt_irrefl a hx)
    | some y =>
      intro h
      exact congrArg Option.some (initial_injective a x y h)

theorem succValue_downward (a : Ordinal.{u}) (x : Option (representative a).Carrier)
    (b : Ordinal.{u}) (h : b < succValue a x) : ∃ y, succValue a y = b := by
  have hba : b < a := by
    cases x with
    | none => exact h
    | some x => exact lt_trans b _ a h (initial_lt a x)
  cases initial_surjective a b hba with
  | intro y hy => exact Exists.intro (some y) hy.symm

noncomputable def succ (a : Ordinal.{u}) : Ordinal.{u} :=
  type (orderOn (succValue a) (succValue_injective a))

theorem lt_succ_iff_le (a b : Ordinal.{u}) : a < succ b ↔ a ≤ b := by
  apply Iff.intro
  · intro h
    cases (lt_type_orderOn_iff (succValue b) (succValue_injective b)
        (succValue_downward b) a).mp h with
    | intro x hx =>
      cases x with
      | none => exact Or.inr hx
      | some x =>
        rw [hx]
        exact Or.inl (initial_lt b x)
  · intro h
    apply (lt_type_orderOn_iff (succValue b) (succValue_injective b)
      (succValue_downward b) a).mpr
    cases h with
    | inl h =>
      cases initial_surjective b a h with
      | intro x hx => exact Exists.intro (some x) hx
    | inr h => exact Exists.intro none h

theorem lt_succ_self (a : Ordinal.{u}) : a < succ a :=
  (lt_succ_iff_le a a).mpr (le_refl a)

theorem lt_of_le_of_lt {a b c : Ordinal.{u}} (hab : a ≤ b) (hbc : b < c) : a < c := by
  cases hab with
  | inl hab => exact lt_trans a b c hab hbc
  | inr hab =>
    cases hab
    exact hbc

theorem lt_of_lt_of_le {a b c : Ordinal.{u}} (hab : a < b) (hbc : b ≤ c) : a < c := by
  cases hbc with
  | inl hbc => exact lt_trans a b c hab hbc
  | inr hbc =>
    cases hbc
    exact hab

theorem succ_le_iff_lt (a b : Ordinal.{u}) : succ a ≤ b ↔ a < b := by
  apply Iff.intro
  · intro h
    exact lt_of_lt_of_le (lt_succ_self a) h
  · intro h
    apply (not_lt_iff_le b (succ a)).mp
    intro hb
    have hba := (lt_succ_iff_le b a).mp hb
    exact lt_irrefl b (lt_of_le_of_lt hba h)

theorem succ_mono {a b : Ordinal.{u}} (h : a ≤ b) : succ a ≤ succ b :=
  (succ_le_iff_lt a (succ b)).mpr ((lt_succ_iff_le a b).mpr h)

end OCF.Ordinal

namespace OCF

universe u

structure SubOrder (X : Type u) where
  domain : X → Prop
  lt : {x : X // domain x} → {x : X // domain x} → Prop
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ a b c, lt a b → lt b c → lt a c
  total : ∀ a b, lt a b ∨ a = b ∨ lt b a
  wellFounded : WellFounded lt

namespace SubOrder

def toWellOrder {X : Type u} (r : SubOrder X) : WellOrder.{u} where
  Carrier := {x : X // r.domain x}
  lt := r.lt
  irrefl := r.irrefl
  trans := r.trans
  total := r.total
  wellFounded := r.wellFounded

noncomputable def preimage {A X : Type u} (f : A → X) (x : {x : X // ∃ a, f a = x}) : A :=
  Classical.choose x.2

theorem preimage_spec {A X : Type u} (f : A → X) (x : {x : X // ∃ a, f a = x}) :
    f (preimage f x) = x.1 := Classical.choose_spec x.2

theorem preimage_image {A X : Type u} (f : A → X)
    (hf : ∀ a b, f a = f b → a = b) (a : A) :
    preimage f ⟨f a, Exists.intro a rfl⟩ = a :=
  hf _ a (preimage_spec f ⟨f a, Exists.intro a rfl⟩)

noncomputable def image {X : Type u} (A : WellOrder.{u}) (f : A.Carrier → X)
    (_hf : ∀ a b, f a = f b → a = b) : SubOrder X where
  domain x := ∃ a, f a = x
  lt x y := A.lt (preimage f x) (preimage f y)
  irrefl x := A.irrefl (preimage f x)
  trans x y z hxy hyz := A.trans _ _ _ hxy hyz
  total x y := by
    cases A.total (preimage f x) (preimage f y) with
    | inl h => exact Or.inl h
    | inr h =>
      cases h with
      | inl h =>
        apply Or.inr
        apply Or.inl
        apply Subtype.ext
        exact (preimage_spec f x).symm.trans ((congrArg f h).trans (preimage_spec f y))
      | inr h => exact Or.inr (Or.inr h)
  wellFounded := InvImage.wf (preimage f) A.wellFounded

noncomputable def imageIso {X : Type u} (A : WellOrder.{u}) (f : A.Carrier → X)
    (hf : ∀ a b, f a = f b → a = b) : WellOrder.Iso A (image A f hf).toWellOrder where
  toFun a := ⟨f a, Exists.intro a rfl⟩
  invFun := preimage f
  left_inv a := preimage_image f hf a
  right_inv x := Subtype.ext (preimage_spec f x)
  lt_iff a b := by
    change A.lt (preimage f ⟨f a, Exists.intro a rfl⟩)
      (preimage f ⟨f b, Exists.intro b rfl⟩) ↔ A.lt a b
    rw [preimage_image f hf a, preimage_image f hf b]

end SubOrder

namespace Ordinal

noncomputable def hartogs (X : Type u) : Ordinal.{u} :=
  sup (fun r : SubOrder X => succ (type r.toWellOrder))

theorem subOrder_type_lt_hartogs {X : Type u} (r : SubOrder X) :
    type r.toWellOrder < hartogs X :=
  lt_of_lt_of_le (lt_succ_self (type r.toWellOrder))
    (le_sup (fun s : SubOrder X => succ (type s.toWellOrder)) r)

theorem lt_hartogs_of_injective {X : Type u} (a : Ordinal.{u})
    (f : (representative a).Carrier → X) (hf : ∀ x y, f x = f y → x = y) :
    a < hartogs X := by
  have he := type_eq_of_iso (SubOrder.imageIso (representative a) f hf)
  have h := subOrder_type_lt_hartogs (SubOrder.image (representative a) f hf)
  rw [← he, type_representative a] at h
  exact h

theorem no_injection_hartogs (X : Type u) (f : (representative (hartogs X)).Carrier → X) :
    ¬ (∀ x y, f x = f y → x = y) := by
  intro hf
  exact lt_irrefl (hartogs X) (lt_hartogs_of_injective (hartogs X) f hf)

theorem exists_not_range_lt_hartogs {X : Type u} (f : X → Ordinal.{u}) :
    ∃ a, a < hartogs X ∧ ¬ ∃ x, f x = a := by
  classical
  apply Classical.byContradiction
  intro h
  have hit : ∀ a, a < hartogs X → ∃ x, f x = a := by
    intro a ha
    apply Classical.byContradiction
    intro hn
    exact h (Exists.intro a (And.intro ha hn))
  let g : (representative (hartogs X)).Carrier → X :=
    fun y => Classical.choose (hit _ (initial_lt (hartogs X) y))
  have hg : ∀ y, f (g y) = type ((representative (hartogs X)).below y) :=
    fun y => Classical.choose_spec (hit _ (initial_lt (hartogs X) y))
  apply no_injection_hartogs X g
  intro y z hyz
  apply initial_injective (hartogs X)
  exact (hg y).symm.trans ((congrArg f hyz).trans (hg z))

end Ordinal
end OCF

namespace OCF.Ordinal

universe u

theorem eq_of_lt_iff (a b : Ordinal.{u}) (h : ∀ c, c < a ↔ c < b) : a = b := by
  cases lt_total a b with
  | inl hab => exact False.elim (lt_irrefl a ((h a).mpr hab))
  | inr hrest =>
    cases hrest with
    | inl hab => exact hab
    | inr hba => exact False.elim (lt_irrefl b ((h b).mp hba))

noncomputable def add (a : Ordinal.{u}) : Ordinal.{u} → Ordinal.{u} :=
  lt_wellFounded.fix (fun b ih => sup (fun x : Option (representative b).Carrier =>
    match x with
    | none => a
    | some x => succ (ih (type ((representative b).below x)) (initial_lt b x))))

noncomputable instance : Add Ordinal.{u} where
  add := add

theorem add_eq (a b : Ordinal.{u}) :
    a + b = sup (fun x : Option (representative b).Carrier =>
      match x with
      | none => a
      | some x => succ (a + type ((representative b).below x))) :=
  WellFounded.fix_eq lt_wellFounded _ b

theorem lt_add_iff (a b c : Ordinal.{u}) :
    c < a + b ↔ c < a ∨ ∃ d, d < b ∧ c ≤ a + d := by
  rw [add_eq a b]
  apply Iff.intro
  · intro h
    cases (lt_sup_iff _ c).mp h with
    | intro x hx =>
      cases x with
      | none => exact Or.inl hx
      | some x =>
        exact Or.inr (Exists.intro (type ((representative b).below x))
          (And.intro (initial_lt b x) ((lt_succ_iff_le c _).mp hx)))
  · intro h
    apply (lt_sup_iff _ c).mpr
    cases h with
    | inl h => exact Exists.intro none h
    | inr h =>
      cases h with
      | intro d hd =>
        cases initial_surjective b d hd.1 with
        | intro x hx =>
          refine Exists.intro (some x) ?_
          apply (lt_succ_iff_le c _).mpr
          rw [← hx]
          exact hd.2

theorem le_add (a b : Ordinal.{u}) : a ≤ a + b := by
  rw [add_eq a b]
  exact le_sup _ none

theorem add_lt_add_right (a : Ordinal.{u}) {b c : Ordinal.{u}} (h : b < c) :
    a + b < a + c :=
  (lt_add_iff a c (a + b)).mpr (Or.inr (Exists.intro b (And.intro h (le_refl _))))

theorem add_mono_right (a : Ordinal.{u}) {b c : Ordinal.{u}} (h : b ≤ c) :
    a + b ≤ a + c := by
  cases h with
  | inl h => exact Or.inl (add_lt_add_right a h)
  | inr h =>
    cases h
    exact le_refl _

theorem add_zero (a : Ordinal.{u}) : a + 0 = a := by
  apply le_antisymm
  · rw [add_eq a 0]
    apply (sup_le_iff _ a).mpr
    intro x
    cases x with
    | none => exact le_refl a
    | some x => exact False.elim (not_lt_zero _ (initial_lt 0 x))
  · exact le_add a 0

theorem zero_add (b : Ordinal.{u}) : 0 + b = b := by
  induction b using lt_wellFounded.induction with
  | h b ih =>
    apply eq_of_lt_iff
    intro c
    apply Iff.intro
    · intro hcb
      cases (lt_add_iff 0 b c).mp hcb with
      | inl hc0 => exact False.elim (not_lt_zero c hc0)
      | inr hcd =>
        cases hcd with
        | intro d hd =>
          have hcd := hd.2
          rw [ih d hd.1] at hcd
          exact lt_of_le_of_lt hcd hd.1
    · intro hcb
      apply (lt_add_iff 0 b c).mpr
      apply Or.inr
      refine Exists.intro c (And.intro hcb ?_)
      rw [ih c hcb]
      exact le_refl c

theorem add_succ (a b : Ordinal.{u}) : a + succ b = succ (a + b) := by
  apply eq_of_lt_iff
  intro c
  apply Iff.intro
  · intro hc
    apply (lt_succ_iff_le c (a + b)).mpr
    cases (lt_add_iff a (succ b) c).mp hc with
    | inl hca => exact Or.inl (lt_of_lt_of_le hca (le_add a b))
    | inr hcd =>
      cases hcd with
      | intro d hd =>
        exact le_trans hd.2 (add_mono_right a ((lt_succ_iff_le d b).mp hd.1))
  · intro hc
    apply (lt_add_iff a (succ b) c).mpr
    exact Or.inr (Exists.intro b
      (And.intro (lt_succ_self b) ((lt_succ_iff_le c (a + b)).mp hc)))

theorem add_mono_left {a b : Ordinal.{u}} (hab : a ≤ b) (c : Ordinal.{u}) :
    a + c ≤ b + c := by
  induction c using lt_wellFounded.induction with
  | h c ih =>
    rw [add_eq a c, add_eq b c]
    apply sup_mono
    intro x
    cases x with
    | none => exact hab
    | some x => exact succ_mono (ih _ (initial_lt c x))

theorem right_le_add (a b : Ordinal.{u}) : b ≤ a + b := by
  have h := add_mono_left (zero_le a) b
  rw [zero_add b] at h
  exact h

theorem add_assoc (a b c : Ordinal.{u}) : (a + b) + c = a + (b + c) := by
  induction c using lt_wellFounded.induction with
  | h c ih =>
    apply eq_of_lt_iff
    intro x
    apply Iff.intro
    · intro hx
      cases (lt_add_iff (a + b) c x).mp hx with
      | inl hxab => exact lt_of_lt_of_le hxab (add_mono_right a (le_add b c))
      | inr hxd =>
        cases hxd with
        | intro d hd =>
          have hxd := hd.2
          rw [ih d hd.1] at hxd
          exact lt_of_le_of_lt hxd (add_lt_add_right a (add_lt_add_right b hd.1))
    · intro hx
      cases (lt_add_iff a (b + c) x).mp hx with
      | inl hxa => exact lt_of_lt_of_le hxa (le_trans (le_add a b) (le_add (a + b) c))
      | inr hxy =>
        cases hxy with
        | intro y hy =>
          cases (lt_add_iff b c y).mp hy.1 with
          | inl hyb =>
            exact lt_of_le_of_lt hy.2
              (lt_of_lt_of_le (add_lt_add_right a hyb) (le_add (a + b) c))
          | inr hyd =>
            cases hyd with
            | intro d hd =>
              have hxy := le_trans hy.2 (add_mono_right a hd.2)
              rw [← ih d hd.1] at hxy
              exact lt_of_le_of_lt hxy (add_lt_add_right (a + b) hd.1)

theorem add_right_cancel {a b c : Ordinal.{u}} (h : a + b = a + c) : b = c := by
  cases lt_total b c with
  | inl hbc =>
    have hlt := add_lt_add_right a hbc
    rw [h] at hlt
    exact False.elim (lt_irrefl (a + c) hlt)
  | inr hrest =>
    cases hrest with
    | inl hbc => exact hbc
    | inr hcb =>
      have hlt := add_lt_add_right a hcb
      rw [h] at hlt
      exact False.elim (lt_irrefl (a + c) hlt)

theorem lt_add_iff_eq (a b c : Ordinal.{u}) :
    c < a + b ↔ c < a ∨ ∃ d, d < b ∧ c = a + d := by
  apply Iff.intro
  · intro h
    cases (lt_add_iff a b c).mp h with
    | inl hca => exact Or.inl hca
    | inr hd =>
      cases Ordinal.exists_min (fun d => d < b ∧ c ≤ a + d) hd with
      | intro d hdmin =>
        cases hdmin.1.2 with
        | inr hcd => exact Or.inr (Exists.intro d (And.intro hdmin.1.1 hcd))
        | inl hcd =>
          cases (lt_add_iff a d c).mp hcd with
          | inl hca => exact Or.inl hca
          | inr he =>
            cases he with
            | intro e he =>
              exact False.elim
                (hdmin.2 e he.1 (And.intro (lt_trans e d b he.1 hdmin.1.1) he.2))
  · intro h
    apply (lt_add_iff a b c).mpr
    cases h with
    | inl h => exact Or.inl h
    | inr h =>
      cases h with
      | intro d hd => exact Or.inr (Exists.intro d (And.intro hd.1 (Or.inr hd.2)))

theorem le_add_cases (a b c : Ordinal.{u}) (h : c ≤ a + b) (hca : ¬ c < a) :
    ∃ d, d ≤ b ∧ c = a + d := by
  cases h with
  | inr h => exact Exists.intro b (And.intro (le_refl b) h)
  | inl h =>
    cases (lt_add_iff_eq a b c).mp h with
    | inl h => exact False.elim (hca h)
    | inr h =>
      cases h with
      | intro d hd => exact Exists.intro d (And.intro (Or.inl hd.1) hd.2)

theorem exists_add_of_le (a b : Ordinal.{u}) (h : a ≤ b) : ∃ c, b = a + c := by
  have hb : b < a + succ b := lt_of_lt_of_le (lt_succ_self b) (right_le_add a (succ b))
  cases (lt_add_iff_eq a (succ b) b).mp hb with
  | inl hba => exact False.elim (((not_lt_iff_le b a).mpr h) hba)
  | inr hc =>
    cases hc with
    | intro c hc => exact Exists.intro c hc.2

def AddPrincipal (k : Ordinal.{u}) : Prop :=
  ∀ a b, a < k → b < k → a + b < k

theorem AddPrincipal.absorb {k : Ordinal.{u}} (hk : AddPrincipal k)
    {a : Ordinal.{u}} (ha : a < k) : a + k = k := by
  apply le_antisymm
  · apply (not_lt_iff_le k (a + k)).mp
    intro h
    cases (lt_add_iff a k k).mp h with
    | inl hka => exact lt_asymm ha hka
    | inr hd =>
      cases hd with
      | intro d hd => exact lt_irrefl k (lt_of_le_of_lt hd.2 (hk a d ha hd.1))
  · exact right_le_add a k

theorem succ_zero_principal : AddPrincipal (succ (0 : Ordinal.{u})) := by
  intro a b ha hb
  have ea := le_antisymm ((lt_succ_iff_le a 0).mp ha) (zero_le a)
  have eb := le_antisymm ((lt_succ_iff_le b 0).mp hb) (zero_le b)
  rw [ea, eb, add_zero]
  exact lt_succ_self 0

end OCF.Ordinal

namespace OCF.Ordinal

universe u

noncomputable def principalStage (a : Ordinal.{u}) : Nat → Ordinal.{u}
  | 0 => succ a
  | n + 1 => principalStage a n + principalStage a n

theorem principalStage_pos (a : Ordinal.{u}) (n : Nat) : 0 < principalStage a n := by
  induction n with
  | zero => exact lt_of_le_of_lt (zero_le a) (lt_succ_self a)
  | succ n ih => exact lt_of_lt_of_le ih (le_add (principalStage a n) (principalStage a n))

theorem principalStage_lt_succ (a : Ordinal.{u}) (n : Nat) :
    principalStage a n < principalStage a (n + 1) := by
  have h := add_lt_add_right (principalStage a n) (principalStage_pos a n)
  rw [add_zero] at h
  exact h

theorem principalStage_mono (a : Ordinal.{u}) {n m : Nat} (h : n ≤ m) :
    principalStage a n ≤ principalStage a m := by
  induction h with
  | refl => exact le_refl _
  | @step m h ih => exact le_trans ih (Or.inl (principalStage_lt_succ a m))

noncomputable def principalHull (a : Ordinal.{u}) : Ordinal.{u} :=
  sup (fun n : ULift.{u} Nat => principalStage a n.down)

theorem principalStage_le_hull (a : Ordinal.{u}) (n : Nat) :
    principalStage a n ≤ principalHull a :=
  le_sup (fun k : ULift.{u} Nat => principalStage a k.down) (ULift.up n)

theorem lt_principalHull (a : Ordinal.{u}) : a < principalHull a :=
  lt_of_lt_of_le (lt_succ_self a) (principalStage_le_hull a 0)

theorem principalHull_principal (a : Ordinal.{u}) : AddPrincipal (principalHull a) := by
  intro x y hx hy
  cases (lt_sup_iff _ x).mp hx with
  | intro n hn =>
    cases (lt_sup_iff _ y).mp hy with
    | intro m hm =>
      have hxk := lt_of_lt_of_le hn (principalStage_mono a (Nat.le_max_left n.down m.down))
      have hyk := lt_of_lt_of_le hm (principalStage_mono a (Nat.le_max_right n.down m.down))
      have hxy := lt_of_le_of_lt (add_mono_left (Or.inl hxk) y)
        (add_lt_add_right (principalStage a (max n.down m.down)) hyk)
      exact lt_of_lt_of_le hxy (principalStage_le_hull a (max n.down m.down + 1))

end OCF.Ordinal
