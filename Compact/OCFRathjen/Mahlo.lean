import Compact.OCFRathjen.Collapse

/-! `M^ξ` の定常性から `M^ξ` への所属を得る（Lemma 4.11 (vi)(vii)）。

* `M_of_stationary`（4.11 (vii)）：`π ∈ Reg` で `M^ξ` が `π` で定常なら `π ∈ M^ξ`。
* `M_of_M`（4.11 (vi)）：`π ∈ M^α` で `ξ ∈ C(α, π) ∩ α` なら `π ∈ M^ξ`。
* `Psi_not_stationary`, `Psi_not_M`（Prop. 4.16 後半）：`ξ > 0` で `Ψ^ξ_π(α) < π` なら、
  `M^ξ` は `Ψ^ξ_π(α)` で定常でなく、`β > ξ` について `Ψ^ξ_π(α) ∉ M^β`。

準備として、`K(ρ)` が `(K_{n-1}, K_n)` で一定であることと、閉非有界集合の極限点の集合が閉非有界であることを示す。 -/

namespace OCF.Rathjen

universe u

open Ordinal

noncomputable section

/-! ### 閉非有界集合の極限点 -/

/-- 閉非有界集合の極限点全体は閉非有界 -/
theorem Club.limitPoints {κ : Ordinal.{u}} (hκ : R κ) {U : Ordinal.{u} → Prop} (hU : Club κ U) :
    Club κ (IsLimitPoint U) := by
  apply And.intro
  · intro η hη
    let s : Nat → Ordinal.{u} := fun n => Nat.rec η (fun _ δ => nextAbove κ U hU.1 δ) n
    have hsS : ∀ n, s (n + 1) = nextAbove κ U hU.1 (s n) := fun _ => rfl
    have hsp : ∀ n, s n < κ ∧ U (s (n + 1)) ∧ s n < s (n + 1) := by
      intro n
      induction n with
      | zero =>
        have h := nextAbove_spec hU.1 hη
        exact ⟨hη, h.1, h.2.1⟩
      | succ n ih =>
        have h1 : s (n + 1) < κ := by rw [hsS n]; exact (nextAbove_spec hU.1 ih.1).2.2
        have h2 := nextAbove_spec hU.1 h1
        rw [hsS (n + 1)]
        exact ⟨h1, h2.1, h2.2.1⟩
    have hs : ∀ n, s n < s (n + 1) := fun n => (hsp n).2.2
    refine Exists.intro (omegaSup s) (And.intro (omegaSup_isLimitPoint hs (fun n => (hsp n).2.1))
      (And.intro (lt_omegaSup hs 0) (omegaSup_lt hκ (fun n => (hsp n).1))))
  · intro l _ hlp
    apply And.intro hlp.1
    intro η hη
    cases hlp.2 η hη with
    | intro ρ hρ =>
      cases hρ.1.2 η hρ.2.1 with
      | intro ζ hζ => exact Exists.intro ζ (And.intro hζ.1 (And.intro hζ.2.1 (lt_trans _ _ _ hζ.2.2 hρ.2.2)))

/-- `ρ` が `U` の極限点で `U` が `κ` で閉なら、`U` は `ρ` で閉非有界 -/
theorem Club.below {κ ρ : Ordinal.{u}} {U : Ordinal.{u} → Prop} (hU : Club κ U) (hρκ : ρ < κ)
    (hρ : IsLimitPoint U ρ) : Club ρ U := by
  apply And.intro
  · intro η hη
    cases hρ.2 η hη with
    | intro ζ hζ => exact Exists.intro ζ hζ
  · intro l hl hlp
    exact hU.2 l (lt_trans _ _ _ hl hρκ) hlp

variable [Setting.{u}]

/-! ### `K(ρ)` -/

theorem exists_level_aux (π : Ordinal.{u}) :
    ∀ N, π < K N → ∃ n, π < K n ∧ ∀ m, m < n → K m ≤ π := by
  intro N
  induction N with
  | zero => intro h; exact absurd h (not_lt_zero π)
  | succ N ih =>
    intro h
    cases lt_or_le π (K N) with
    | inl h' => exact ih h'
    | inr h' =>
      refine Exists.intro (N + 1) (And.intro h ?_)
      intro m hm
      exact le_trans (K_le (Nat.le_of_lt_succ hm)) h'

/-- `π < Λ` なら `π < K_n` となる最小の `n` がある -/
theorem exists_level {π : Ordinal.{u}} (hπ : π < Λ) : ∃ n, π < K n ∧ ∀ m, m < n → K m ≤ π := by
  cases (lt_Λ_iff π).mp hπ with
  | intro N hN => exact exists_level_aux π N hN

theorem Kabove_eq {π : Ordinal.{u}} {n : Nat} (h1 : π < K n) (h2 : ∀ m, m < n → K m ≤ π) :
    Kabove π = K n := by
  have hP : (∃ k, K n = K k) ∧ π < K n := And.intro (Exists.intro n rfl) h1
  apply le_antisymm (least_le _ hP)
  apply le_of_not_lt
  intro hlt
  have hs := (least_spec (fun κ => (∃ k, κ = K k) ∧ π < κ) (Exists.intro _ hP)).1
  cases hs.1 with
  | intro k hk =>
    have hltk : K k < K n := by rw [← hk]; exact hlt
    have hπk : π < K k := by rw [← hk]; exact hs.2
    exact absurd hπk (not_lt_of_le (h2 k (K_lt_iff.mp hltk)))

/-- `π ∈ Reg` なら `K_{n-1} < π < K_n`（`1 ≤ n`）となる `n` があり、`K(π) = K_n` -/
theorem IsReg.level {π : Ordinal.{u}} (hπ : IsReg π) :
    ∃ n, 1 ≤ n ∧ K (n - 1) < π ∧ π < K n ∧ Kabove π = K n := by
  cases exists_level hπ.2.1 with
  | intro n hn =>
    cases n with
    | zero => exact absurd hn.1 (not_lt_zero π)
    | succ n =>
      have hle : K n ≤ π := hn.2 n (Nat.lt_succ_self n)
      have hlt : K n < π := lt_of_le_of_ne hle (fun e => hπ.2.2 n e.symm)
      exact ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), hlt, hn.1, Kabove_eq hn.1 hn.2⟩

/-- `K_{n-1} ≤ ρ < K_n` なら `K(ρ) = K_n` -/
theorem Kabove_eq_of_between {ρ : Ordinal.{u}} {n : Nat} (h1 : K (n - 1) ≤ ρ)
    (h2 : ρ < K n) : Kabove ρ = K n := by
  apply Kabove_eq h2
  intro m hm
  exact le_trans (K_le (Nat.le_sub_one_of_lt hm)) h1

/-! ### Lemma 4.11 (vi)(vii) -/

/-- Lemma 4.11 (vii)：`π ∈ Reg` で `M^ξ` が `π` で定常なら `π ∈ M^ξ` -/
theorem M_of_stationary {ξ π : Ordinal.{u}} (hπ : IsReg π) (hstat : Stationary π (M ξ)) :
    M ξ π := by
  have hR := hπ.1
  cases eq_zero_or_pos ξ with
  | inl h0 =>
    subst h0
    exact (M_zero_iff π).mpr (And.intro hR.2.1 hπ.2.1)
  | inr hpos =>
    have hξ0 : ξ ≠ 0 := ne_of_gt hpos
    cases hπ.level with
    | intro n hn =>
      have hunb := hstat.unbounded hR
      -- `M^ξ ∩ (η, π)` の元は `M^ξ` の性質をもつ
      have hMρ : ∀ ρ, M ξ ρ → IsReg ρ ∧ (∀ x, C ξ ρ x → x < Kabove ρ → x < ρ) ∧ C ξ ρ ξ ∧
          ∀ η, η < ξ → C ξ ρ η → Stationary ρ (M η) := fun ρ h => (M_pos_iff hξ0 ρ).mp h
      apply (M_pos_iff hξ0 π).mpr
      refine ⟨hπ, ?_, ?_, ?_⟩
      · intro x hx hxK
        cases C_limit hR.2.1 hx with
        | intro η hη =>
          cases hunb (omax η (K (n - 1))) (omax_lt hη.1 hn.2.1) with
          | intro ρ hρ =>
            have hKρ : Kabove ρ = K n :=
              Kabove_eq_of_between (le_trans (le_omax_right _ _) (Or.inl hρ.2.1))
                (lt_trans _ _ _ hρ.2.2 hn.2.2.1)
            have hxρ := (hMρ ρ hρ.1).2.1 x
              (C_mono_base (le_trans (le_omax_left _ _) (Or.inl hρ.2.1)) hη.2)
              (by rw [hKρ, ← hn.2.2.2]; exact hxK)
            exact lt_trans _ _ _ hxρ hρ.2.2
      · cases hunb 0 hR.2.pos with
        | intro ρ hρ => exact C_mono_base (Or.inl hρ.2.2) (hMρ ρ hρ.1).2.2.1
      · intro η hηξ hηC U hU
        cases C_limit hR.2.1 hηC with
        | intro ε hε =>
          cases hstat _ (Club.inter hR (Club.limitPoints hR hU) (club_gt hR hε.1)) with
          | intro ρ hρ =>
            have hρM := hMρ ρ hρ.2.2
            have hstatρ := hρM.2.2.2 η hηξ (C_mono_base (Or.inl hρ.2.1.2) hε.2)
            cases hstatρ U (Club.below hU hρ.1 hρ.2.1.1) with
            | intro ζ hζ => exact Exists.intro ζ (And.intro (lt_trans _ _ _ hζ.1 hρ.1) hζ.2)

/-- Lemma 4.11 (vi)：`π ∈ M^α` で `ξ ∈ C(α, π) ∩ α` なら `π ∈ M^ξ` -/
theorem M_of_M {α ξ π : Ordinal.{u}} (h : M α π) (hξα : ξ < α) (hξ : C α π ξ) : M ξ π := by
  have hα0 : α ≠ 0 := ne_of_gt (lt_of_le_of_lt (zero_le ξ) hξα)
  have hM := (M_pos_iff hα0 π).mp h
  exact M_of_stationary hM.1 (hM.2.2.2 ξ hξα hξ)

/-! ### Prop. 4.16（後半） -/

/-- Prop. 4.16（後半）：`ξ > 0` で `Ψ^ξ_π(α) < π` なら `M^ξ` は `Ψ^ξ_π(α)` で定常でない -/
theorem Psi_not_stationary {ξ π α : Ordinal.{u}} (hξ0 : 0 < ξ) (hlt : Psi ξ π α < π) :
    ¬ Stationary (Psi ξ π α) (M ξ) := by
  intro hstat
  have hsp := Psi_spec hlt
  have hMp := (M_pos_iff (ne_of_gt hξ0) _).mp hsp.2.1
  have hR : R (Psi ξ π α) := hMp.1.1
  have hl := hR.2.1
  have hξC : C α (Psi ξ π α) ξ := C_mono_arg hsp.1 hMp.2.2.1
  cases C_limit hl hξC with
  | intro η₁ h₁ =>
    cases C_limit hl hsp.2.2.2.1 with
    | intro η₂ h₂ =>
      cases C_limit hl hsp.2.2.2.2 with
      | intro η₃ h₃ =>
        let μ₀ := omax η₁ (omax η₂ η₃)
        have hμ₀ : μ₀ < Psi ξ π α := omax_lt h₁.1 (omax_lt h₂.1 h₃.1)
        cases hstat _ (club_closedC hR α hμ₀) with
        | intro ν hν =>
          have hle : ∀ η, η ≤ μ₀ → η ≤ ν := fun η h => le_trans h (Or.inl hν.2.1.1)
          have hνπ : ν < π := lt_trans _ _ _ hν.1 hlt
          have hCν : ∀ x, C α ν x → x < π → x < ν := by
            intro x hx hxπ
            exact hν.2.1.2 x hx (hsp.2.2.1 x (C_mono_base (Or.inl hν.1) hx) hxπ)
          have hψν : Psi ξ π α ≤ ν := Psi_le_of hsp.1 hν.2.2 hνπ hCν
            (C_mono_base (hle _ (le_trans (le_omax_left η₂ η₃) (le_omax_right _ _))) h₂.2)
            (C_mono_base (hle _ (le_trans (le_omax_right η₂ η₃) (le_omax_right _ _))) h₃.2)
          exact absurd hν.1 (not_lt_of_le hψν)

/-- Prop. 4.16（後半）：`ξ > 0`、`Ψ^ξ_π(α) < π`、`ξ < β` なら `Ψ^ξ_π(α) ∉ M^β` -/
theorem Psi_not_M {ξ π α β : Ordinal.{u}} (hξ0 : 0 < ξ) (hlt : Psi ξ π α < π) (hξβ : ξ < β) :
    ¬ M β (Psi ξ π α) := by
  intro hM
  have hsp := Psi_spec hlt
  have hMξ := (M_pos_iff (ne_of_gt hξ0) _).mp hsp.2.1
  have hMβ := (M_pos_iff (ne_of_gt (lt_trans _ _ _ hξ0 hξβ)) _).mp hM
  exact Psi_not_stationary hξ0 hlt
    (hMβ.2.2.2 ξ hξβ (C_mono_arg (Or.inl hξβ) hMξ.2.2.1))

end
end OCF.Rathjen
