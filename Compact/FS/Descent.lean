import Compact.FS.Class

/-! Bachmann 性の言い換え（基本列の具体形に依らない部分）。

`p b` を `b` の基本列の 0 番目（後者なら前者）とする。

* `InD p x b`：`x` は `b` から `p` をたどる降下列 `b, p b, p (p b), …` に現れる。
* `BP p x y`：区間 `(x, y]` の元 `b` は全て `x ≤ p b`。

`BP` は推移的で（`BP.trans`）、全ての `b` で `BP p (p b) b` なら、降下列に現れることから `BP` が
従う（`BP_of_InD`）。したがって `ω` 型の項 `a` の Bachmann 性は、梯子 `a[n] ∈ D(a[n+1])` と共終性から
従う（`bachmann_of_ladder`）。 -/

namespace FSDesc

variable {A : Type} [LT A] [Well_Order A]

theorem lt_irrefl' (a : A) : ¬ a < a := by
  intro h
  have key : ∀ b, Acc (fun x y : A => x < y) b → b ≠ a := by
    intro b hb
    induction hb with
    | intro b _ ih => intro e; subst e; exact ih b h rfl
  exact key a (Well_Order.lt_wf.apply a) rfl

theorem lt_asymm' {a b : A} (h : a < b) : ¬ b < a :=
  fun h' => lt_irrefl' a (Well_Order.lt_trans a b a h h')

theorem le_refl' (a : A) : a ≤ a := Or.inr rfl

theorem le_of_lt' {a b : A} (h : a < b) : a ≤ b := Or.inl h

theorem lt_of_lt_of_le' {a b c : A} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  rcases h2 with h2 | rfl
  · exact Well_Order.lt_trans a b c h1 h2
  · exact h1

theorem lt_of_le_of_lt' {a b c : A} (h1 : a ≤ b) (h2 : b < c) : a < c := by
  rcases h1 with h1 | rfl
  · exact Well_Order.lt_trans a b c h1 h2
  · exact h2

theorem le_trans' {a b c : A} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  rcases h1 with h1 | rfl
  · exact Or.inl (lt_of_lt_of_le' h1 h2)
  · exact h2

theorem not_lt_of_le' {a b : A} (h : a ≤ b) : ¬ b < a := by
  rcases h with h | rfl
  · exact lt_asymm' h
  · exact lt_irrefl' a

theorem le_of_not_lt' {a b : A} (h : ¬ a < b) : b ≤ a := by
  rcases Well_Order.lt_total a b with h' | h' | h'
  · exact absurd h' h
  · exact Or.inl h'
  · exact Or.inr h'.symm

variable (p : A → A)

/-- `x` は `b` から `p` をたどる降下列に現れる -/
inductive InD (x : A) : A → Prop
  | refl : InD x x
  | step {b : A} : InD x (p b) → InD x b

/-- 区間 `(x, y]` の元 `b` は全て `x ≤ p b` -/
def BP (x y : A) : Prop := ∀ b : A, x < b → b ≤ y → x ≤ p b

theorem BP.refl (x : A) : BP p x x :=
  fun _ h1 h2 => absurd h1 (not_lt_of_le' h2)

/-- `BP` の推移性 -/
theorem BP.trans {x y z : A} (hxy : x ≤ y) (h1 : BP p x y) (h2 : BP p y z) : BP p x z := by
  intro b hxb hbz
  by_cases hby : b ≤ y
  · exact h1 b hxb hby
  · have hyb : y < b := by
      rcases Well_Order.lt_total y b with h | h | h
      · exact h
      · exact absurd (Or.inl h) hby
      · exact absurd (Or.inr h.symm) hby
    exact le_trans' hxy (h2 b hyb hbz)

/-- 降下列は下がる -/
theorem InD.le (hp : ∀ b, p b ≤ b) {x y : A} (h : InD p x y) : x ≤ y := by
  induction h with
  | refl => exact le_refl' _
  | step _ ih => exact le_trans' ih (hp _)

/-- 各段で `BP p (p b) b` なら、降下列に現れる `x` について `BP p x y` -/
theorem BP_of_InD (hp : ∀ b, p b ≤ b) (hstep : ∀ b, BP p (p b) b) {x y : A} (h : InD p x y) :
    BP p x y := by
  induction h with
  | refl => exact BP.refl p x
  | step h' ih => exact BP.trans p (InD.le p hp h') ih (hstep _)

/-- `a` 未満の各段で `BP p (p c) c` なら、`a` 未満の `y` の降下列に現れる `x` について `BP p x y` -/
theorem BP_of_InD_lt {a : A} (hp : ∀ b, p b ≤ b) (hstep : ∀ c, c < a → BP p (p c) c) {x y : A}
    (hya : y < a) (h : InD p x y) : BP p x y := by
  induction h with
  | refl => exact BP.refl p _
  | step h' ih =>
    rename_i c
    exact BP.trans p (InD.le p hp h') (ih (lt_of_le_of_lt' (hp c) hya)) (hstep c hya)

/-- `ω` 型の Bachmann 性：単調で共終な `a` 未満の列 `f` で、梯子 `f n ∈ D(f (n+1))` があり、`a` 未満の
    全ての `c` で `BP p (p c) c` なら、`f n < b < a` のとき `f n ≤ p b` -/
theorem bachmann_of_ladder {a : A} (hp : ∀ b, p b ≤ b) (hstep : ∀ c, c < a → BP p (p c) c)
    (f : Nat → A) (hfa : ∀ n, f n < a)
    (hmono : ∀ n, f n < f (n + 1)) (hcof : ∀ x, x < a → ∃ m, x ≤ f m)
    (hlad : ∀ n, InD p (f n) (f (n + 1))) :
    ∀ n b, f n < b → b < a → f n ≤ p b := by
  -- f n から f (n + k) まで BP
  have chain : ∀ n k, BP p (f n) (f (n + k)) := by
    intro n k
    induction k with
    | zero => exact BP.refl p _
    | succ k ih =>
      have hle : f n ≤ f (n + k) := by
        clear ih
        induction k with
        | zero => exact le_refl' _
        | succ k ihk => exact le_trans' ihk (le_of_lt' (hmono _))
      exact BP.trans p hle ih (BP_of_InD_lt p hp hstep (hfa _) (hlad (n + k)))
  intro n b hnb hba
  obtain ⟨m, hbm⟩ := hcof b hba
  -- m > n
  have hnm : n < m := by
    rcases Nat.lt_or_ge n m with hc | hc
    · exact hc
    exfalso
    have hle : f m ≤ f n := by
      obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
      clear hbm hnb hc
      induction k with
      | zero => exact le_refl' _
      | succ k ihk => exact le_trans' ihk (le_of_lt' (hmono _))
    exact lt_irrefl' _ (lt_of_lt_of_le' (lt_of_lt_of_le' hnb hbm) hle)
  obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  exact chain n k b hnb hbm

/-- 共終数が大きい項の `BP`：添字 `ξ < σ` の列 `f` が共終で、0 番目 `f₀` が全ての `f ξ` の降下列に
    現れるなら、区間 `(f₀, a)` の元 `b` は全て `f₀ ≤ p b` -/
theorem bp0_of_big {a f₀ : A} (hp : ∀ b, p b ≤ b) (hstep : ∀ b, b < a → BP p (p b) b)
    (good : A → Prop) (f : A → A) (hcof : ∀ x, x < a → ∃ ξ, good ξ ∧ x ≤ f ξ)
    (hlt : ∀ ξ, good ξ → f ξ < a)
    (hlad : ∀ ξ, good ξ → InD p f₀ (f ξ)) :
    ∀ b, f₀ < b → b < a → f₀ ≤ p b := by
  intro b hb hba
  obtain ⟨ξ, hξ, hbξ⟩ := hcof b hba
  have key : ∀ {x y : A}, y < a → InD p x y → BP p x y := by
    intro x y hya h
    induction h with
    | refl => exact BP.refl p _
    | step h' ih =>
      rename_i c
      have hpc : p c < a := lt_of_le_of_lt' (hp c) hya
      exact BP.trans p (InD.le p hp h') (ih hpc) (hstep c hya)
  exact key (hlt ξ hξ) (hlad ξ hξ) b hb hbξ

end FSDesc
