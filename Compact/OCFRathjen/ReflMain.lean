import Compact.OCFRathjen.Mahlo
import Compact.OCFRathjen.WeakCompact
import Compact.OCFRathjen.Grl
import Compact.OCFRathjen.ReflIdx

/-! `K n`（`n ≥ 1`）が分割性を持つなら `StageReflectionAt n` が成り立つ。

`C(α, K n)` から `K n` への単射 `j`（`|C(α, K n)| < Ω_{K n + 1}`、`exists_inj_C`）で
`C(α, K n) ∩ α` を `K n` 個の定常集合 `M^β` の族として並べ、反射補題 `grl` を、四つの club
（`E`、`C(α,ρ) ∩ K n ⊆ ρ`、`j[C(α,ρ) ∩ α] ⊆ ρ`、`ρ > max(K(n-1), η₀)`）の共通部分に適用する。
`α ≤ Ω_{K n + 1}` は (B3')（`C_self_of_C`）で `C(α, K n) ∩ α` の元に帰納法の仮定を使うためだけに要る。 -/

namespace OCF.Rathjen

universe u

open Ordinal

set_option linter.unusedSectionVars false

noncomputable section

variable [Setting.{u}]

theorem stageReflectionAt_of_partition {n : Nat} (hn : 1 ≤ n) (hpart : PartitionProp (K.{u} n)) :
    StageReflectionAt.{u} n := by
  intro α hα0 hαΩ hCα hIH E hE
  have hκ : R (K.{u} n) := R_K hn
  obtain ⟨j, hjκ, hjinj⟩ := exists_inj_C hn α
  let S : Ordinal.{u} → Ordinal.{u} → Prop := fun c ρ =>
    ∀ β, β < α → 0 < β → C α (K n) β → j β = c → M β ρ
  have hS : ∀ c, c < K n → Stationary (K n) (S c) := by
    intro c _
    by_cases hex : ∃ β, β < α ∧ 0 < β ∧ C α (K n) β ∧ j β = c
    · obtain ⟨β₀, hβ₀α, hβ₀pos, hβ₀C, hβ₀c⟩ := hex
      have hst : Stationary (K n) (M β₀) :=
        hIH β₀ hβ₀α hβ₀pos (Or.inl (lt_of_lt_of_le hβ₀α hαΩ)) (C_self_of_C hn hαΩ hβ₀C hβ₀α)
      refine hst.mono ?_
      intro ρ _ hρ β _ _ hβC hβc
      have e : β = β₀ := hjinj β β₀ hβC hβ₀C (hβc.trans hβ₀c.symm)
      rw [e]
      exact hρ
    · refine (stationary_isLimit hκ).mono ?_
      intro ρ _ _ β hβα hβpos hβC hβc
      exact absurd ⟨β, hβα, hβpos, hβC, hβc⟩ hex
  obtain ⟨η₀, hη₀κ, hη₀⟩ := C_limit hκ.2.1 hCα
  have hn' : n - 1 < n := by omega
  have hK1 : K (n - 1) < K n := K_lt hn'
  have hμ₀ : omax (K (n - 1)) η₀ < K n := omax_lt hK1 hη₀κ
  have hE2 := club_closedC hκ α hμ₀
  have hE3 := club_j hn (α := α) (fun β _ => hjκ β) hμ₀
  have hEall := Club.inter hκ (Club.inter hκ hE hE2) hE3
  obtain ⟨τ, hτκ, ⟨⟨hτE, hτμ, hτcl⟩, _, hτj⟩, hτR, hτS⟩ := grl hκ hpart hEall hS
  have hτpos : K (n - 1) < τ := lt_of_le_of_lt (le_omax_left _ _) hτμ
  have hη₀τ : η₀ ≤ τ := le_trans (le_omax_right _ _) (Or.inl hτμ)
  have hτΛ : τ < Λ := lt_trans _ _ _ hτκ (K_lt_Λ n)
  refine ⟨τ, hτκ, hτE, ?_, C_mono_base hη₀τ hη₀, ?_, ?_⟩
  · refine ⟨hτR, hτΛ, ?_⟩
    intro m hm
    by_cases hmn : m ≤ n - 1
    · have h1 : K m ≤ K (n - 1) := K_le hmn
      rw [hm] at hτpos
      exact lt_irrefl _ (lt_of_le_of_lt h1 hτpos)
    · have h1 : K n ≤ K m := K_le (by omega)
      rw [hm] at hτκ
      exact lt_irrefl _ (lt_of_lt_of_le hτκ h1)
  · intro x hx hxK
    rw [Kabove_eq_of_between (Or.inl hτpos) hτκ] at hxK
    exact hτcl x hx hxK
  · intro β hβα hβC
    by_cases hβ0 : β = 0
    · subst hβ0
      intro X hX
      cases stationary_isLimit hτR X hX with
      | intro ξ hξ =>
        exact ⟨ξ, hξ.1, hξ.2.1,
          (M_zero_iff ξ).mpr ⟨hξ.2.2, lt_trans _ _ _ hξ.1 hτΛ⟩⟩
    · have hβpos : 0 < β := by
        cases zero_le β with
        | inl h => exact h
        | inr h => exact absurd h.symm hβ0
      have hβC' : C α (K n) β := C_mono_base (Or.inl hτκ) hβC
      have hjβ : j β < τ := hτj β hβC hβα
      intro X hX
      cases hτS (j β) hjβ X hX with
      | intro ξ hξ => exact ⟨ξ, hξ.1, hξ.2.1, hξ.2.2 β hβα hβpos hβC' rfl⟩

end
end OCF.Rathjen
