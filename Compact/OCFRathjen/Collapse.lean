import Compact.OCFRathjen.Stage

/-! `|C(α, β)| < π`（Lemma 4.11 (ii)）と、`Ψ^ξ_π(α) ∈ M^ξ ∩ π`（Prop. 4.16 の前半）。

* `C_small`：`π` が非可算正則で `β < π` なら `C(α, β)` は `π` 未満の個数。
* `C_bounded`：さらに `C(α, β) ∩ π` は `π` 未満の順序数で抑えられる。
* `Psi_lt`：`M^ξ` が `π` で定常で、`ξ ≤ α`、`ξ, π, α ∈ C(α, π)` なら `Ψ^ξ_π(α) < π`
  （`Psi_spec` と合わせて `Ψ^ξ_π(α) ∈ M^ξ ∩ π`）。 -/

namespace OCF.Rathjen

universe u

open Ordinal

noncomputable section

/-- 正則基数 `κ` 未満の小さい集合は `κ` 未満で抑えられる -/
theorem Small.bounded {κ : Ordinal.{u}} (hκ : IsRegular κ) {A : Ordinal.{u} → Prop}
    (h : Small κ A) (hA : ∀ x, A x → x < κ) : ∃ γ, γ < κ ∧ ∀ x, A x → x < γ := by
  classical
  cases h with
  | intro β hβ =>
    cases hβ.2 with
    | intro f hf =>
      let pre : Ordinal.{u} → Ordinal.{u} := fun ζ =>
        if h : ∃ x, A x ∧ f x = ζ then Classical.choose h else 0
      have hpre : ∀ x, A x → pre (f x) = x := by
        intro x hx
        have h : ∃ y, A y ∧ f y = f x := Exists.intro x (And.intro hx rfl)
        have e : pre (f x) = Classical.choose h := dite_eq_left h
        rw [e]
        have hs := Classical.choose_spec h
        exact hf.2 _ _ hs.1 hx hs.2
      have hpreκ : ∀ ζ, pre ζ < κ := by
        intro ζ
        by_cases h : ∃ x, A x ∧ f x = ζ
        · have e : pre ζ = Classical.choose h := dite_eq_left h
          rw [e]
          exact hA _ (Classical.choose_spec h).1
        · have e : pre ζ = 0 := dite_eq_right h
          rw [e]
          exact hκ.pos
      refine Exists.intro (supLt β (fun ζ => succ (pre ζ)))
        (And.intro (hκ.supLt_lt hβ.1 (fun ζ _ => hκ.1.succ_lt (hpreκ ζ))) ?_)
      intro x hx
      apply (lt_supLt_iff _ _ _).mpr
      refine Exists.intro (f x) (And.intro (hf.1 x hx) ?_)
      show x < succ (pre (f x))
      rw [hpre x hx]
      exact lt_succ_self x

variable [Setting.{u}]

/-! ### Lemma 4.11 (ii) -/

theorem Cn_zero_cases {α β x : Ordinal.{u}} (h : Cn α β 0 x) :
    x < β ∨ x = succ 0 ∨ ∃ m, x = K m := by
  unfold Cn at h
  cases h with
  | lt _ _ h => exact Or.inl h
  | one _ => exact Or.inr (Or.inl rfl)
  | kc _ m => exact Or.inr (Or.inr (Exists.intro m rfl))

theorem Cn_succ_cases {α β x : Ordinal.{u}} {n : Nat} (h : Cn α β (n + 1) x) :
    Cn α β n x ∨ (∃ y z, Cn α β n y ∧ Cn α β n z ∧ x = y + z) ∨
      (∃ y, Cn α β n y ∧ x = Om y) ∨
      (∃ y m, Cn α β n y ∧ x = Xi m y) ∨
      (∃ ξ π δ, Cn α β n ξ ∧ Cn α β n π ∧ Cn α β n δ ∧ x = Psi ξ π δ) := by
  unfold Cn at h
  cases h with
  | lt _ _ h => exact Or.inl (StageC.lt n x h)
  | one _ => exact Or.inl (StageC.one n)
  | kc _ m => exact Or.inl (StageC.kc n m)
  | add _ y z hy hz => exact Or.inr (Or.inl ⟨y, z, hy, hz, rfl⟩)
  | om _ y _ hy => exact Or.inr (Or.inr (Or.inl ⟨y, hy, rfl⟩))
  | xi _ m y _ _ hy => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨y, m, hy, rfl⟩)))
  | psi _ ξ π δ _ _ _ hξ hπ hδ => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ξ, π, δ, hξ, hπ, hδ, rfl⟩)))

theorem small_K {κ : Ordinal.{u}} (hω : omega < κ) : Small κ (fun x => ∃ m, x = K m) := by
  apply ((small_natOrd hω).image (fun y => K (natOf y))).mono
  intro x hx
  cases hx with
  | intro m hm =>
    refine Exists.intro (ordNat m) (And.intro (Exists.intro m rfl) ?_)
    rw [natOf_ordNat]
    exact hm

theorem Cn_small {π β : Ordinal.{u}} (hπ : R π) (hβ : β < π) (α : Ordinal.{u}) :
    ∀ n, Small π (Cn α β n) := by
  have hreg := hπ.2
  have hω := hπ.1
  intro n
  induction n with
  | zero =>
    have h1 : Small π (fun x => x = succ (0 : Ordinal.{u})) := by
      apply (small_natOrd hω).mono
      intro x hx
      exact Exists.intro 1 hx
    apply ((Small.union hreg (small_lt hβ) (Small.union hreg h1 (small_K hω)))).mono
    intro x hx
    exact Cn_zero_cases hx
  | succ n ih =>
    have hadd := Small.image2 hreg ih ih (fun y z => y + z)
    have hom := Small.image ih Om
    have hxi := Small.image2 hreg ih (small_natOrd hω) (fun y m => Xi (natOf m) y)
    have hpsi : Small π (fun x => ∃ ξ, Cn α β n ξ ∧
        (fun ξ x => ∃ p d, Cn α β n p ∧ Cn α β n d ∧ x = Psi ξ p d) ξ x) :=
      Small.iUnion hreg ih (fun ξ _ => Small.image2 hreg ih ih (fun p d => Psi ξ p d))
    apply (Small.union hreg ih (Small.union hreg hadd (Small.union hreg hom
      (Small.union hreg hxi hpsi)))).mono
    intro x hx
    cases Cn_succ_cases hx with
    | inl h => exact Or.inl h
    | inr h =>
      cases h with
      | inl h => exact Or.inr (Or.inl h)
      | inr h =>
        cases h with
        | inl h =>
          cases h with
          | intro y hy => exact Or.inr (Or.inr (Or.inl ⟨y, hy.1, hy.2⟩))
        | inr h =>
          cases h with
          | inl h =>
            cases h with
            | intro y hy =>
              cases hy with
              | intro m hm =>
                refine Or.inr (Or.inr (Or.inr (Or.inl ⟨y, ordNat m, hm.1, Exists.intro m rfl, ?_⟩)))
                rw [natOf_ordNat]
                exact hm.2
          | inr h =>
            cases h with
            | intro ξ h =>
              cases h with
              | intro p h =>
                cases h with
                | intro d h =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ξ, h.1, p, d, h.2.1, h.2.2.1, h.2.2.2⟩)))

/-- Lemma 4.11 (ii)：`|C(α, β)| < π` -/
theorem C_small {π β : Ordinal.{u}} (hπ : R π) (hβ : β < π) (α : Ordinal.{u}) :
    Small π (C α β) := by
  apply (Small.iUnion hπ.2 (small_natOrd hπ.1) (A := fun i x => Cn α β (natOf i) x)
    (fun i _ => Cn_small hπ hβ α (natOf i))).mono
  intro x hx
  cases hx with
  | intro n hn =>
    refine Exists.intro (ordNat n) (And.intro (Exists.intro n rfl) ?_)
    show Cn α β (natOf (ordNat n)) x
    rw [natOf_ordNat]
    exact hn

/-- `C(α, β) ∩ π` は `π` 未満で抑えられる -/
theorem C_bounded {π β : Ordinal.{u}} (hπ : R π) (hβ : β < π) (α : Ordinal.{u}) :
    ∃ γ, γ < π ∧ ∀ x, C α β x → x < π → x < γ := by
  cases Small.bounded hπ.2 ((C_small hπ hβ α).mono (A := fun x => C α β x ∧ x < π)
      (fun _ h => h.1)) (fun _ h => h.2) with
  | intro γ hγ => exact Exists.intro γ (And.intro hγ.1 (fun x hx hxπ => hγ.2 x (And.intro hx hxπ)))

/-! ### Prop. 4.16（前半） -/

/-- `C(α, ρ) ∩ π ⊆ ρ` となる `ρ`（`μ₀ < ρ < π`）は `π` で閉非有界 -/
theorem club_closedC {π : Ordinal.{u}} (hπ : R π) (α : Ordinal.{u}) {μ₀ : Ordinal.{u}}
    (hμ₀ : μ₀ < π) :
    Club π (fun ρ => μ₀ < ρ ∧ ∀ x, C α ρ x → x < π → x < ρ) := by
  classical
  apply And.intro
  · intro η hη
    -- `δ₀ = max(η, μ₀) + 1`、`δ_{n+1} = max(δ_n + 1, sup(C(α, δ_n) ∩ π))`
    let bnd : Ordinal.{u} → Ordinal.{u} := fun δ =>
      if h : δ < π then Classical.choose (C_bounded hπ h α) else 0
    have hbnd : ∀ δ, δ < π → bnd δ < π ∧ ∀ x, C α δ x → x < π → x < bnd δ := by
      intro δ hδ
      have e : bnd δ = Classical.choose (C_bounded hπ hδ α) := dite_eq_left hδ
      rw [e]
      exact Classical.choose_spec (C_bounded hπ hδ α)
    let s : Nat → Ordinal.{u} := fun n =>
      Nat.rec (succ (omax η μ₀)) (fun _ δ => omax (succ δ) (bnd δ)) n
    have hs0 : s 0 = succ (omax η μ₀) := rfl
    have hsS : ∀ n, s (n + 1) = omax (succ (s n)) (bnd (s n)) := fun _ => rfl
    have hsπ : ∀ n, s n < π := by
      intro n
      induction n with
      | zero => rw [hs0]; exact hπ.2.1.succ_lt (omax_lt hη hμ₀)
      | succ n ih =>
        rw [hsS]
        exact omax_lt (hπ.2.1.succ_lt ih) (hbnd _ ih).1
    have hs : ∀ n, s n < s (n + 1) := by
      intro n
      rw [hsS]
      exact lt_of_lt_of_le (lt_succ_self _) (le_omax_left _ _)
    let δs := omegaSup s
    have hδsπ : δs < π := omegaSup_lt hπ hsπ
    have hδslim : IsLimit δs := by
      apply And.intro (lt_of_le_of_lt (zero_le _) (lt_omegaSup hs 0))
      intro β hβ
      cases (lt_omegaSup_iff β).mp hβ with
      | intro n hn => exact lt_of_le_of_lt (succ_le_of_lt hn) (lt_omegaSup hs n)
    have hlt0 : omax η μ₀ < δs := lt_trans _ _ _ (lt_succ_self _) (lt_omegaSup hs 0)
    refine Exists.intro δs (And.intro (And.intro
      (lt_of_le_of_lt (le_omax_right η μ₀) hlt0) ?_)
      (And.intro (lt_of_le_of_lt (le_omax_left η μ₀) hlt0) hδsπ))
    intro x hx hxπ
    cases C_limit hδslim hx with
    | intro ζ hζ =>
      cases (lt_omegaSup_iff ζ).mp hζ.1 with
      | intro n hn =>
        have hxn : x < bnd (s n) := (hbnd _ (hsπ n)).2 x (C_mono_base (Or.inl hn) hζ.2) hxπ
        exact lt_trans _ _ _ hxn (lt_of_le_of_lt (by rw [hsS n]; exact le_omax_right _ _)
          (lt_omegaSup hs (n + 1)))
  · intro l hlπ hlp
    have hl : IsLimit l := by
      apply And.intro hlp.1
      intro β hβ
      cases hlp.2 β hβ with
      | intro γ hγ => exact lt_of_le_of_lt (succ_le_of_lt hγ.2.1) hγ.2.2
    apply And.intro
    · cases hlp.2 0 hlp.1 with
      | intro γ hγ => exact lt_trans _ _ _ hγ.1.1 hγ.2.2
    · intro x hx hxπ
      cases C_limit hl hx with
      | intro ζ hζ =>
        cases hlp.2 ζ hζ.1 with
        | intro ρ hρ =>
          exact lt_trans _ _ _ (hρ.1.2 x (C_mono_base (Or.inl hρ.2.1) hζ.2) hxπ) hρ.2.2

/-- Prop. 4.16（前半）：`M^ξ` が `π` で定常、`ξ ≤ α`、`ξ, π, α ∈ C(α, π)` なら `Ψ^ξ_π(α) < π` -/
theorem Psi_lt {ξ π α : Ordinal.{u}} (hπ : R π) (hstat : Stationary π (M ξ)) (hξα : ξ ≤ α)
    (hξ : C α π ξ) (hπC : C α π π) (hα : C α π α) : Psi ξ π α < π := by
  have hl := hπ.2.1
  cases C_limit hl hξ with
  | intro η₁ h₁ =>
    cases C_limit hl hπC with
    | intro η₂ h₂ =>
      cases C_limit hl hα with
      | intro η₃ h₃ =>
        let μ₀ := omax η₁ (omax η₂ η₃)
        have hμ₀ : μ₀ < π := omax_lt h₁.1 (omax_lt h₂.1 h₃.1)
        cases hstat _ (club_closedC hπ α hμ₀) with
        | intro ν hν =>
          have hle : ∀ η, η ≤ μ₀ → η ≤ ν := fun η h => le_trans h (Or.inl hν.2.1.1)
          apply lt_of_le_of_lt _ hν.1
          exact Psi_le_of hξα hν.2.2 hν.1 hν.2.1.2
            (C_mono_base (hle _ (le_trans (le_omax_left η₂ η₃) (le_omax_right _ _))) h₂.2)
            (C_mono_base (hle _ (le_trans (le_omax_right η₂ η₃) (le_omax_right _ _))) h₃.2)

end
end OCF.Rathjen
