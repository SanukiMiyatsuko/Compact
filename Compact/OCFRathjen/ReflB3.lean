import Compact.OCFRathjen.Collapse

/-! 構造補題 (B3')：`α ≤ Ω_{K_n+1}` のとき、`x ∈ C(α, K_n)` かつ `x < α` なら `x ∈ C(x, K_n)`。

`α > Ω_{K_n+1}` では成り立たない（`Ψ^0_{K_n^+}(K_n^+) ∈ C(α, K_n)` だが `C(Ψ^0_{K_n^+}(K_n^+), K_n)` には
入らない。`XiSuccK.lean`）。 -/

namespace OCF.Rathjen

universe u

open Ordinal

noncomputable section

variable [Setting.{u}]

/-- `K n` より大きい正則順序数は `Ω_{K n + 1}` 以上 -/
theorem Om_succ_le_of_R {n : Nat} (hn : 1 ≤ n) {π : Ordinal.{u}} (hπ : R π) (hlt : K n < π) :
    Om (K n + succ 0) ≤ π := by
  rw [add_one_eq_succ]
  apply enum_le_of (X := CardSet) (Or.inr (subset_closure hπ))
  intro γ hγ
  have hγle : γ ≤ K n := le_of_lt_succ hγ
  have h1 : Om γ ≤ K n := by
    cases hγle with
    | inl h =>
      have := Om_lt_Om h (K_lt_Λ n)
      rw [Om_K hn] at this
      exact Or.inl this
    | inr h => rw [h, Om_K hn]; exact le_refl _
  exact lt_of_le_of_lt h1 hlt

theorem K_add_one_lt_Λ (n : Nat) : K.{u} n + succ 0 < Λ := by
  rw [add_one_eq_succ]
  have hl : IsLimit (K.{u} (n + 1)) := (R_K (Nat.succ_le_succ (Nat.zero_le n))).2.1
  exact lt_trans _ _ _ (hl.succ_lt (K_lt_K_succ n)) (K_lt_Λ (n + 1))

/-- (B3')：`x ∈ C(α, K n)`、`x < α ≤ Ω_{K n + 1}` なら `x ∈ C(x, K n)` -/
theorem C_self_of_lt {n : Nat} (hn : 1 ≤ n) {α : Ordinal.{u}} (hα : α ≤ Om (K n + succ 0))
    {k : Nat} {x : Ordinal.{u}} (h : Cn α (K n) k x) : x < α → C x (K n) x := by
  unfold Cn at h
  induction h with
  | lt k γ hγ => intro _; exact C_lt hγ
  | one k => intro _; exact C_one _ _
  | kc k m => intro _; exact C_K _ _ m
  | add k y z hy hz ihy ihz =>
    intro hlt
    exact C_add (C_mono_arg (le_add y z) (ihy (lt_of_le_of_lt (le_add y z) hlt)))
      (C_mono_arg (right_le_add y z) (ihz (lt_of_le_of_lt (right_le_add y z) hlt)))
  | om k y hΛ hy ih =>
    intro hlt
    have hy' : y ≤ Om y := le_Om hΛ
    exact C_Om hΛ (C_mono_arg hy' (ih (lt_of_le_of_lt hy' hlt)))
  | xi k m y hpos hyα hy ih =>
    show Xi m y < α → C (Xi m y) (K n) (Xi m y)
    intro hlt
    cases Xi_le m y with
    | inr heq => rw [heq]; exact C_K _ _ m
    | inl hlt' =>
      have hsp := Xi_spec hlt'
      have hreg : IsReg (Xi m y) := ((M_pos_iff (ne_of_gt hpos) _).mp hsp.1).1
      by_cases hm : m ≤ n
      · exact C_lt (lt_of_lt_of_le hlt' (K_le hm))
      · exfalso
        have hnm : n ≤ m - 1 := by omega
        have h1 : K n < Xi m y := lt_of_le_of_lt (K_le hnm) hsp.2
        have h2 := Om_succ_le_of_R hn hreg.1 h1
        exact lt_irrefl _ (lt_of_lt_of_le (lt_of_lt_of_le hlt hα) h2)
  | psi k ξ π δ hδα hξδ hπ hξ hπC hδ ihξ ihπ ihδ =>
    show Psi ξ π δ < α → C (Psi ξ π δ) (K n) (Psi ξ π δ)
    intro hlt
    by_cases hX : Psi ξ π δ < K n
    · exact C_lt hX
    · have hKX : K n ≤ Psi ξ π δ := le_of_not_lt hX
      have hπR : R π := hπ.1
      cases Psi_le ξ π δ with
      | inr heq =>
        exfalso
        have hKπ : K n < π := by
          cases hKX with
          | inl h => rw [heq] at h; exact h
          | inr h => exact absurd (h.trans heq).symm (hπ.2.2 n)
        have h2 := Om_succ_le_of_R hn hπR hKπ
        have hπα : π < α := by rw [← heq]; exact hlt
        exact lt_irrefl π (lt_of_lt_of_le (lt_of_lt_of_le hπα hα) h2)
      | inl hlt' =>
        have hsp := Psi_spec hlt'
        have hKπ : K n < π := lt_of_le_of_lt hKX hlt'
        have h2 := Om_succ_le_of_R hn hπR hKπ
        have hπeq : π = Om (K n + succ 0) := by
          apply le_antisymm _ h2
          apply le_of_not_lt
          intro hlt2
          have hC : C δ (Psi ξ π δ) (Om (K n + succ 0)) :=
            C_Om (K_add_one_lt_Λ n) (C_add (C_K _ _ n) (C_one _ _))
          have := hsp.2.2.1 _ hC hlt2
          exact lt_irrefl _ (lt_of_lt_of_le (lt_trans _ _ _ this hlt) hα)
        have hδπ : δ < π := by rw [hπeq]; exact lt_of_lt_of_le hδα hα
        have hδX : δ < Psi ξ π δ := hsp.2.2.1 δ hsp.2.2.2.2 hδπ
        have hξα : ξ < α := lt_of_le_of_lt hξδ hδα
        have c1 : C (Psi ξ π δ) (K n) ξ :=
          C_mono_arg (le_trans hξδ (Or.inl hδX)) (ihξ hξα)
        have c2 : C (Psi ξ π δ) (K n) δ := C_mono_arg (Or.inl hδX) (ihδ hδα)
        have c3 : C (Psi ξ π δ) (K n) π := by
          rw [hπeq]; exact C_Om (K_add_one_lt_Λ n) (C_add (C_K _ _ n) (C_one _ _))
        exact C_Psi hδX hξδ hπ c1 c3 c2

theorem C_self_of_C {n : Nat} (hn : 1 ≤ n) {α x : Ordinal.{u}} (hα : α ≤ Om (K n + succ 0))
    (hx : C α (K n) x) (hxα : x < α) : C x (K n) x := by
  cases hx with
  | intro k hk => exact C_self_of_lt hn hα hk hxα

end
end OCF.Rathjen
