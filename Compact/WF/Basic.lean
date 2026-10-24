import Compact.Additive

/-! 構成的な整列性証明（`Compact/WF`）の A 層：`cmp` の構文的な性質。

順序数・`Classical.choice`・大基数の仮定を使わず、項の大きさについての帰納法だけで示す。
各定理の公理は `Compact/WF/Axioms.lean` で `propext`・`Quot.sound` だけであることを検査する。

* `cmp_self`：`cmp t t = .eq`（全ての項）。 -/

namespace RTKA

open Tm

theorem cmpList_nil_nil : cmpList [] [] = .eq := by rw [cmpList]

theorem cmpList_nil_cons (y : Tm) (ys : List Tm) : cmpList [] (y :: ys) = .lt := by rw [cmpList]

theorem cmpList_cons_nil (x : Tm) (xs : List Tm) : cmpList (x :: xs) [] = .gt := by rw [cmpList]

theorem cmpList_cons_cons_eq {x y : Tm} (xs ys : List Tm) (h : cmpP x y = .eq) :
    cmpList (x :: xs) (y :: ys) = cmpList xs ys := by
  rw [cmpList, h]

theorem cmpList_cons_cons_ne {x y : Tm} (xs ys : List Tm) (h : cmpP x y ≠ .eq) :
    cmpList (x :: xs) (y :: ys) = cmpP x y := by
  rw [cmpList]
  cases e : cmpP x y with
  | eq => exact absurd e h
  | lt => rfl
  | gt => rfl

theorem cmp_eq (a b : Tm) : cmp a b = cmpList (summands a) (summands b) := by rw [cmp]

theorem cmpList_self : ∀ l : List Tm, (∀ x, x ∈ l → cmpP x x = .eq) → cmpList l l = .eq
  | [], _ => cmpList_nil_nil
  | x :: xs, h => by
    rw [cmpList_cons_cons_eq xs xs (h x List.mem_cons_self)]
    exact cmpList_self xs (fun y hy => h y (List.mem_cons_of_mem x hy))

theorem size_le_of_mem_summands : ∀ (t s : Tm), s ∈ summands t → s.size ≤ t.size
  | .zero, s, h => by simp [summands] at h
  | .plus a b, s, h => by
    rw [summands, List.mem_cons] at h
    cases h with
    | inl e => rw [e]; simp only [Tm.size]; omega
    | inr h => have := size_le_of_mem_summands b s h; simp only [Tm.size]; omega
  | .one, s, h | .K _, s, h | .Om _, s, h | .Xi _ _, s, h | .Psi _ _ _, s, h => by
    simp only [summands, List.mem_singleton] at h
    rw [h]
    exact Nat.le_refl _

theorem cmp_self_aux : ∀ n, ∀ t : Tm, t.size ≤ n → cmp t t = .eq ∧ cmpP t t = .eq := by
  intro n
  induction n with
  | zero => intro t h; exact absurd h (Nat.not_le.mpr (Tm.size_pos t))
  | succ n ih =>
    intro t ht
    have hP : ∀ x : Tm, x.size ≤ n + 1 → cmpP x x = .eq := by
      intro x hx
      rw [cmpP.eq_def]
      simp only [Nat.lt_irrefl, ↓reduceIte]
      cases x with
      | Om a =>
        have := (ih a (by simp only [Tm.size] at hx; omega)).1
        simpa using this
      | Xi m a => simp
      | Psi xi pi a => simp [cmpPsi.eq_def]
      | _ => rfl
    refine ⟨?_, hP t ht⟩
    rw [cmp_eq]
    exact cmpList_self _ (fun x hx => hP x (Nat.le_trans (size_le_of_mem_summands t x hx) ht))

/-- `cmp t t = .eq` -/
theorem cmp_self (t : Tm) : cmp t t = .eq := (cmp_self_aux t.size t (Nat.le_refl _)).1

theorem cmpP_self (t : Tm) : cmpP t t = .eq := (cmp_self_aux t.size t (Nat.le_refl _)).2

theorem lt_irrefl (t : Tm) : lt t t = false := by
  unfold lt
  rw [cmp_self]
  rfl

end RTKA
