import Compact.OCFRathjen.Enum

/-! 閉非有界集合と定常集合。

`κ` を非可算正則基数（`R κ`）とし、`κ` 未満の順序数のクラスについて

* `Unbounded κ X`：`X` は `κ` で非有界
* `ClosedBelow κ X`：`κ` 未満の `X` の極限点は `X` に入る
* `Club κ X`：その両方
* `Stationary κ S`：全ての `Club κ X` と交わる

を定める。主な結果は、二つの閉非有界集合の共通部分が閉非有界であること（`Club.inter`）と、
極限順序数・`η` より大きい順序数が閉非有界であること。 -/

namespace OCF.Rathjen

universe u

open Ordinal

noncomputable section

def Unbounded (κ : Ordinal.{u}) (X : Ordinal.{u} → Prop) : Prop :=
  ∀ η, η < κ → ∃ ξ, X ξ ∧ η < ξ ∧ ξ < κ

/-- A function from a regular ordinal into a smaller ordinal has an unbounded
fiber.  This form of the regularity argument will be used to thin sequences
of first-difference coordinates. -/
theorem exists_unbounded_fiber {κ δ : Ordinal.{u}} (hκ : IsRegular κ)
    (hδ : δ < κ) (f : Ordinal.{u} → Ordinal.{u})
    (hf : ∀ x, x < κ → f x < δ) :
    ∃ y, y < δ ∧ Unbounded κ (fun x => x < κ ∧ f x = y) := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hno : ∀ y, y < δ → ¬ Unbounded κ (fun x => x < κ ∧ f x = y) := by
    intro y hy hU
    exact hnone ⟨y, hy, hU⟩
  have hbound : ∀ y, y < δ →
      ∃ b, b < κ ∧ ∀ x, x < κ → f x = y → x ≤ b := by
    intro y hy
    apply Classical.byContradiction
    intro hn
    have hU : Unbounded κ (fun x => x < κ ∧ f x = y) := by
      intro b hb
      have hnot : ¬ (∀ x, x < κ → f x = y → x ≤ b) := by
        intro hle
        exact hn ⟨b, hb, hle⟩
      have hex : ∃ x, x < κ ∧ f x = y ∧ ¬ x ≤ b := by
        apply Classical.byContradiction
        intro h
        apply hnot
        intro x hx hxy
        by_cases hxb : x ≤ b
        · exact hxb
        · exact False.elim (h ⟨x, hx, hxy, hxb⟩)
      obtain ⟨x, hx, hxy, hxb⟩ := hex
      exact ⟨x, ⟨hx, hxy⟩, lt_of_not_le hxb, hx⟩
    exact hno y hy hU
  let bound : Ordinal.{u} → Ordinal.{u} := fun y =>
    if hy : y < δ then Classical.choose (hbound y hy) else 0
  have hbound_lt : ∀ y, bound y < κ := by
    intro y
    by_cases hy : y < δ
    · have heq : bound y = Classical.choose (hbound y hy) := dite_eq_left hy
      rw [heq]
      exact (Classical.choose_spec (hbound y hy)).1
    · have heq : bound y = 0 := dite_eq_right hy
      rw [heq]
      exact hκ.pos
  have hbound_spec : ∀ y, y < δ → ∀ x, x < κ → f x = y → x ≤ bound y := by
    intro y hy x hx hxy
    have heq : bound y = Classical.choose (hbound y hy) := dite_eq_left hy
    rw [heq]
    exact (Classical.choose_spec (hbound y hy)).2 x hx hxy
  let s := supLt δ bound
  have hs : s < κ := hκ.supLt_lt hδ (fun y _ => hbound_lt y)
  have hsucc : succ s < κ := hκ.1.2 s hs
  have hfs : f (succ s) < δ := hf (succ s) hsucc
  have hle₁ : succ s ≤ bound (f (succ s)) := hbound_spec _ hfs _ hsucc rfl
  have hle₂ : bound (f (succ s)) ≤ s := le_supLt δ bound hfs
  have hle : succ s ≤ s := le_trans hle₁ hle₂
  exact lt_irrefl s (lt_of_lt_of_le (lt_succ_self s) hle)

def ClosedBelow (κ : Ordinal.{u}) (X : Ordinal.{u} → Prop) : Prop :=
  ∀ l, l < κ → IsLimitPoint X l → X l

def Club (κ : Ordinal.{u}) (X : Ordinal.{u} → Prop) : Prop := Unbounded κ X ∧ ClosedBelow κ X

def Stationary (κ : Ordinal.{u}) (S : Ordinal.{u} → Prop) : Prop :=
  ∀ X, Club κ X → ∃ ξ, ξ < κ ∧ X ξ ∧ S ξ

/-! ### 正則基数の下の ω 列の上限 -/

/-- 狭義増加の ω 列の上限 -/
def omegaSup (s : Nat → Ordinal.{u}) : Ordinal.{u} := supLt omega (fun ζ => s (natOf ζ))

theorem lt_omegaSup {s : Nat → Ordinal.{u}} (hs : ∀ n, s n < s (n + 1)) (n : Nat) :
    s n < omegaSup s := by
  apply (lt_supLt_iff _ _ _).mpr
  refine Exists.intro (ordNat (n + 1)) (And.intro (ordNat_lt_omega _) ?_)
  rw [natOf_ordNat]
  exact hs n

theorem lt_omegaSup_iff {s : Nat → Ordinal.{u}} (ζ : Ordinal.{u}) :
    ζ < omegaSup s ↔ ∃ n, ζ < s n := by
  apply Iff.intro
  · intro h
    cases (lt_supLt_iff _ _ _).mp h with
    | intro ξ hξ => exact Exists.intro (natOf ξ) hξ.2
  · intro h
    cases h with
    | intro n hn =>
      apply (lt_supLt_iff _ _ _).mpr
      refine Exists.intro (ordNat n) (And.intro (ordNat_lt_omega _) ?_)
      rw [natOf_ordNat]
      exact hn

theorem omegaSup_lt {κ : Ordinal.{u}} (hκ : R κ) {s : Nat → Ordinal.{u}} (h : ∀ n, s n < κ) :
    omegaSup s < κ :=
  hκ.2.supLt_lt hκ.1 (fun ξ _ => h (natOf ξ))

/-- 狭義増加の ω 列の上限は極限順序数で、列の各項の極限点 -/
theorem omegaSup_isLimitPoint {s : Nat → Ordinal.{u}} (hs : ∀ n, s n < s (n + 1))
    {X : Ordinal.{u} → Prop} (hX : ∀ n, X (s (n + 1))) : IsLimitPoint X (omegaSup s) := by
  apply And.intro (lt_of_le_of_lt (zero_le _) (lt_omegaSup hs 0))
  intro η hη
  cases (lt_omegaSup_iff η).mp hη with
  | intro n hn =>
    exact Exists.intro (s (n + 1)) (And.intro (hX n)
      (And.intro (lt_trans _ _ _ hn (hs n)) (lt_omegaSup hs (n + 1))))

/-! ### 閉非有界集合 -/

/-- `X` が非有界なとき、`ζ` より大きい `X` の元を一つ選ぶ（`ζ ≥ κ` なら `0`） -/
def nextAbove (κ : Ordinal.{u}) (X : Ordinal.{u} → Prop) (h : Unbounded κ X) (ζ : Ordinal.{u}) :
    Ordinal.{u} :=
  open Classical in
  if hζ : ζ < κ then Classical.choose (h ζ hζ) else 0

theorem nextAbove_spec {κ : Ordinal.{u}} {X : Ordinal.{u} → Prop} (h : Unbounded κ X)
    {ζ : Ordinal.{u}} (hζ : ζ < κ) :
    X (nextAbove κ X h ζ) ∧ ζ < nextAbove κ X h ζ ∧ nextAbove κ X h ζ < κ := by
  unfold nextAbove
  rw [dite_eq_left hζ]
  exact Classical.choose_spec (h ζ hζ)

/-- 二つの非有界集合の元を交互にとる列 -/
def alternate (κ : Ordinal.{u}) (X Y : Ordinal.{u} → Prop) (hX : Unbounded κ X)
    (hY : Unbounded κ Y) (η : Ordinal.{u}) : Nat → Ordinal.{u}
  | 0 => η
  | n + 1 => nextAbove κ Y hY (nextAbove κ X hX (alternate κ X Y hX hY η n))

theorem alternate_spec {κ : Ordinal.{u}} {X Y : Ordinal.{u} → Prop} (hX : Unbounded κ X)
    (hY : Unbounded κ Y) {η : Ordinal.{u}} (hη : η < κ) (n : Nat) :
    alternate κ X Y hX hY η n < κ ∧
      X (nextAbove κ X hX (alternate κ X Y hX hY η n)) ∧
      alternate κ X Y hX hY η n < nextAbove κ X hX (alternate κ X Y hX hY η n) ∧
      nextAbove κ X hX (alternate κ X Y hX hY η n) < alternate κ X Y hX hY η (n + 1) ∧
      Y (alternate κ X Y hX hY η (n + 1)) ∧ alternate κ X Y hX hY η (n + 1) < κ := by
  induction n with
  | zero =>
    have h1 := nextAbove_spec hX hη
    have h2 := nextAbove_spec hY h1.2.2
    exact ⟨hη, h1.1, h1.2.1, h2.2.1, h2.1, h2.2.2⟩
  | succ n ih =>
    have h1 := nextAbove_spec hX ih.2.2.2.2.2
    have h2 := nextAbove_spec hY h1.2.2
    exact ⟨ih.2.2.2.2.2, h1.1, h1.2.1, h2.2.1, h2.1, h2.2.2⟩

theorem Club.inter {κ : Ordinal.{u}} (hκ : R κ) {X Y : Ordinal.{u} → Prop} (hX : Club κ X)
    (hY : Club κ Y) : Club κ (fun ξ => X ξ ∧ Y ξ) := by
  apply And.intro
  · intro η hη
    let s := alternate κ X Y hX.1 hY.1 η
    have hsp := alternate_spec hX.1 hY.1 hη
    have hs : ∀ n, s n < s (n + 1) := fun n =>
      lt_trans _ _ _ (hsp n).2.2.1 (hsp n).2.2.2.1
    have hlt : omegaSup s < κ := omegaSup_lt hκ (fun n => (hsp n).1)
    have hYl : IsLimitPoint Y (omegaSup s) :=
      omegaSup_isLimitPoint hs (fun n => (hsp n).2.2.2.2.1)
    have hXl : IsLimitPoint X (omegaSup s) := by
      apply And.intro hYl.1
      intro ζ hζ
      cases (lt_omegaSup_iff ζ).mp hζ with
      | intro n hn =>
        exact Exists.intro _ (And.intro (hsp n).2.1
          (And.intro (lt_trans _ _ _ hn (hsp n).2.2.1)
            (lt_trans _ _ _ (hsp n).2.2.2.1 (lt_omegaSup hs (n + 1)))))
    exact Exists.intro (omegaSup s) (And.intro (And.intro (hX.2 _ hlt hXl) (hY.2 _ hlt hYl))
      (And.intro (lt_omegaSup hs 0) hlt))
  · intro l hl hlp
    apply And.intro
    · apply hX.2 l hl
      apply And.intro hlp.1
      intro η hη
      cases hlp.2 η hη with
      | intro β hβ => exact Exists.intro β (And.intro hβ.1.1 hβ.2)
    · apply hY.2 l hl
      apply And.intro hlp.1
      intro η hη
      cases hlp.2 η hη with
      | intro β hβ => exact Exists.intro β (And.intro hβ.1.2 hβ.2)

/-- `η < κ` なら `η` より大きい順序数は閉非有界 -/
theorem club_gt {κ : Ordinal.{u}} (hκ : R κ) {η : Ordinal.{u}} (hηκ : η < κ) :
    Club κ (fun ξ => η < ξ) := by
  apply And.intro
  · intro ζ hζ
    cases lt_or_le ζ η with
    | inl h =>
      exact Exists.intro (succ η) (And.intro (lt_succ_self η)
        (And.intro (lt_trans _ _ _ h (lt_succ_self η)) (hκ.2.1.succ_lt hηκ)))
    | inr h =>
      exact Exists.intro (succ ζ) (And.intro (lt_of_le_of_lt h (lt_succ_self ζ))
        (And.intro (lt_succ_self ζ) (hκ.2.1.succ_lt hζ)))
  · intro l _ hlp
    cases hlp.2 0 hlp.1 with
    | intro β hβ => exact lt_trans _ _ _ hβ.1 hβ.2.2

/-- 極限順序数は閉非有界 -/
theorem club_isLimit {κ : Ordinal.{u}} (hκ : R κ) : Club κ IsLimit := by
  apply And.intro
  · intro η hη
    let s : Nat → Ordinal.{u} := fun n => η + ordNat n
    have hs : ∀ n, s n < s (n + 1) := fun n => by
      show η + ordNat n < η + ordNat (n + 1)
      exact (add_lt_add_iff_right η).mpr (ordNat_lt (Nat.lt_succ_self n))
    have hsκ : ∀ n, s n < κ := fun n => hκ.2.add_lt hη (lt_trans _ _ _ (ordNat_lt_omega n) hκ.1)
    refine Exists.intro (omegaSup s) (And.intro ?_ (And.intro ?_ (omegaSup_lt hκ hsκ)))
    · apply And.intro (lt_of_le_of_lt (zero_le _) (lt_omegaSup hs 0))
      intro β hβ
      cases (lt_omegaSup_iff β).mp hβ with
      | intro n hn =>
        exact lt_of_le_of_lt (succ_le_of_lt hn) (lt_omegaSup hs n)
    · have h0 : s 0 = η := add_zero η
      rw [← h0]
      exact lt_omegaSup hs 0
  · intro l _ hlp
    apply And.intro hlp.1
    intro β hβ
    cases hlp.2 β hβ with
    | intro γ hγ => exact lt_of_le_of_lt (succ_le_of_lt hγ.2.1) hγ.2.2

theorem Stationary.mono {κ : Ordinal.{u}} {S T : Ordinal.{u} → Prop} (h : Stationary κ S)
    (hST : ∀ ξ, ξ < κ → S ξ → T ξ) : Stationary κ T := by
  intro X hX
  cases h X hX with
  | intro ξ hξ => exact Exists.intro ξ (And.intro hξ.1 (And.intro hξ.2.1 (hST ξ hξ.1 hξ.2.2)))

/-- 定常集合は閉非有界集合との共通部分も定常 -/
theorem Stationary.inter_club {κ : Ordinal.{u}} (hκ : R κ) {S X : Ordinal.{u} → Prop}
    (h : Stationary κ S) (hX : Club κ X) : Stationary κ (fun ξ => S ξ ∧ X ξ) := by
  intro Y hY
  cases h _ (Club.inter hκ hX hY) with
  | intro ξ hξ => exact Exists.intro ξ (And.intro hξ.1 (And.intro hξ.2.1.2 (And.intro hξ.2.2 hξ.2.1.1)))

/-- 定常集合は非有界 -/
theorem Stationary.unbounded {κ : Ordinal.{u}} (hκ : R κ) {S : Ordinal.{u} → Prop}
    (h : Stationary κ S) : Unbounded κ S := by
  intro η hη
  cases h _ (club_gt hκ hη) with
  | intro ξ hξ => exact Exists.intro ξ (And.intro hξ.2.2 (And.intro hξ.2.1 hξ.1))

/-- 極限順序数全体は定常 -/
theorem stationary_isLimit {κ : Ordinal.{u}} (hκ : R κ) : Stationary κ IsLimit := by
  intro X hX
  cases (Club.inter hκ hX (club_isLimit hκ)).1 0 hκ.2.pos with
  | intro ξ hξ => exact Exists.intro ξ (And.intro hξ.2.2 (And.intro hξ.1.1 hξ.1.2))

/-! ### 二つの順序数の大きい方 -/

/-- 大きい方 -/
def omax (a b : Ordinal.{u}) : Ordinal.{u} :=
  open Classical in
  if a < b then b else a

theorem le_omax_left (a b : Ordinal.{u}) : a ≤ omax a b := by
  unfold omax
  split
  · exact Or.inl ‹_›
  · exact le_refl a

theorem le_omax_right (a b : Ordinal.{u}) : b ≤ omax a b := by
  unfold omax
  split
  · exact le_refl b
  · exact le_of_not_lt ‹_›

theorem omax_lt {a b c : Ordinal.{u}} (ha : a < c) (hb : b < c) : omax a b < c := by
  unfold omax
  split
  · exact hb
  · exact ha

end
end OCF.Rathjen
