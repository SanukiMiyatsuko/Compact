import Compact.OCFRathjen.Values

/-! 生成子の値の一意性と `Ψ` どうしの比較（Rathjen Lemma 4.17・4.19 (i)(ii)、Prop. 4.20 の加法版）。

* `M_fixed`（Lemma 4.19 (i)）：`α > 0`、`π ∈ M^α` なら `Ω_π = π`。
* `Psi_fixed`（Lemma 4.19 (ii)）：`Ω_π = π`、`Ψ^ξ_π(α) < π` なら `Ω_Ψ = Ψ`。
* `Xi_ne_Psi`・`Psi_inj`（Prop. 4.17）、ほか生成子の値が互いに異なること。
* `GenRep_Om`・`GenRep_Xi`・`GenRep_Psi`：本物の生成子の値の表示は引数まで一意。
* `transfer`：`z ∈ C(σ, x) ∩ C(β, y)`、`y < x ≤ π`、`C(β, y) ∩ π ⊆ y` なら `z ∈ C(σ, y)`。
* `Psi_le_of_stationary`：Prop. 4.16 の議論の一般形。
* `Psi_lt_Psi_iff`（Prop. 4.20）。 -/

namespace OCF.Rathjen

universe u

open Ordinal

noncomputable section

variable [Setting.{u}]

omit [Setting] in
theorem one_lt_of_R {ρ : Ordinal.{u}} (h : R ρ) : succ 0 < ρ :=
  lt_trans _ _ _ (ordNat_lt_omega 1) h.1

theorem M_isLimit {ξ ρ : Ordinal.{u}} (h : M ξ ρ) : IsLimit ρ := by
  cases eq_zero_or_pos ξ with
  | inl h0 => subst h0; exact ((M_zero_iff ρ).mp h).1
  | inr hpos => exact (M_reg hpos h).1.2.1

/-! ### Lemma 4.19 (i)(ii) -/

/-- `Ω` で閉じた極限 `π < Λ` は `Ω` の不動点 -/
theorem Om_fixed_of_closed {π : Ordinal.{u}} (hl : IsLimit π) (hΛ : π < Λ)
    (h : ∀ w, w < π → Om w < π) : Om π = π := by
  apply le_antisymm _ (le_Om hΛ)
  rw [Om_limit hl hΛ]
  exact (supLt_le_iff π Om π).mpr (fun w hw => Or.inl (h w hw))

/-- Lemma 4.19 (i)：`α > 0`、`π ∈ M^α` なら `Ω_π = π` -/
theorem M_fixed {α π : Ordinal.{u}} (hα : 0 < α) (h : M α π) : Om π = π := by
  have hM := (M_pos_iff (ne_of_gt hα) π).mp h
  cases hM.1.level with
  | intro n hn =>
    apply Om_fixed_of_closed hM.1.1.2.1 hM.1.2.1
    intro w hw
    have hwK : w < K n := lt_trans _ _ _ hw hn.2.2.1
    apply hM.2.1 _ (C_Om (lt_trans _ _ _ hwK (K_lt_Λ n)) (C_lt hw))
    rw [hn.2.2.2]
    exact Om_lt_K hn.1 hwK

/-- Lemma 4.19 (ii)：`Ω_π = π`、`Ψ^ξ_π(α) < π` なら `Ω_Ψ = Ψ` -/
theorem Psi_fixed {ξ π α : Ordinal.{u}} (hψ : Psi ξ π α < π) (hπ : Om π = π) (hΛ : π < Λ) :
    Om (Psi ξ π α) = Psi ξ π α := by
  have sp := Psi_spec hψ
  apply Om_fixed_of_closed (M_isLimit sp.2.1) (lt_trans _ _ _ hψ hΛ)
  intro w hw
  have hwπ : w < π := lt_trans _ _ _ hw hψ
  apply sp.2.2.1 _ (C_Om (lt_trans _ _ _ hwπ hΛ) (C_lt hw))
  have h := Om_lt_Om hwπ hΛ
  rw [hπ] at h
  exact h

/-! ### `Ψ` の基本的な所属 -/

/-- `Ψ^ξ_π(α) < π` なら `ξ ∈ C(ξ, Ψ^ξ_π(α))` -/
theorem Psi_C_xi {ξ π α : Ordinal.{u}} (hψ : Psi ξ π α < π) : C ξ (Psi ξ π α) ξ := by
  cases eq_zero_or_pos ξ with
  | inl h0 => rw [h0]; exact C_zero _ _
  | inr hpos => exact ((M_pos_iff (ne_of_gt hpos) _).mp (Psi_spec hψ).2.1).2.2.1

theorem Psi_C_xi' {ξ π α : Ordinal.{u}} (hψ : Psi ξ π α < π) : C α (Psi ξ π α) ξ :=
  C_mono_arg (Psi_spec hψ).1 (Psi_C_xi hψ)

/-- Prop. 4.16 の議論の一般形：`ρ` 正則、`ρ ≤ π`、`C(α, ρ) ∩ π ⊆ ρ`、`π, α ∈ C(α, ρ)`、`ξ ≤ α`、
    `M^ξ` が `ρ` で定常なら `Ψ^ξ_π(α) < ρ` -/
theorem Psi_le_of_stationary {ξ π α ρ : Ordinal.{u}} (hR : R ρ) (hρπ : ρ ≤ π)
    (hC : ∀ x, C α ρ x → x < π → x < ρ) (hπC : C α ρ π) (hαC : C α ρ α) (hξα : ξ ≤ α)
    (hstat : Stationary ρ (M ξ)) : Psi ξ π α < ρ := by
  have hl := hR.2.1
  cases C_limit hl hπC with
  | intro η₂ h₂ =>
    cases C_limit hl hαC with
    | intro η₃ h₃ =>
      cases hstat _ (club_closedC hR α (omax_lt h₂.1 h₃.1)) with
      | intro ν hν =>
        have hle : ∀ η, η ≤ omax η₂ η₃ → η ≤ ν := fun η h => le_trans h (Or.inl hν.2.1.1)
        apply lt_of_le_of_lt _ hν.1
        apply Psi_le_of hξα hν.2.2 (lt_of_lt_of_le hν.1 hρπ)
        · intro x hx hxπ
          exact hν.2.1.2 x hx (hC x (C_mono_base (Or.inl hν.1) hx) hxπ)
        · exact C_mono_base (hle _ (le_omax_left η₂ η₃)) h₂.2
        · exact C_mono_base (hle _ (le_omax_right η₂ η₃)) h₃.2

/-! ### 生成子の値が互いに異なること（Prop. 4.17 ほか） -/

omit [Setting] in
theorem Om_ne_one {w : Ordinal.{u}} (hlt : w < Om w) : Om w ≠ succ 0 := by
  intro e
  rw [e] at hlt
  have hw0 : w = 0 := (le_zero_iff w).mp (le_of_lt_succ hlt)
  rw [hw0, Om_zero] at e
  exact succ_ne_zero 0 e.symm

theorem Om_ne_K {w : Ordinal.{u}} {m : Nat} (hΛ : w < Λ) (hlt : w < Om w) : Om w ≠ K m := by
  intro e
  cases m with
  | zero =>
    rw [e] at hlt
    exact not_lt_of_le (zero_le w) hlt
  | succ m =>
    have hK := Om_K (Nat.succ_le_succ (Nat.zero_le m))
    rw [← hK] at e
    have hw := Om_inj hΛ (K_lt_Λ _) e
    rw [hw, hK] at hlt
    exact lt_irrefl _ hlt

theorem Xi_good_of_lt {m : Nat} {x : Ordinal.{u}} (hX : Xi m x < K m) : XiGood m x :=
  ⟨(Xi_spec hX).1, (Xi_spec hX).2, hX⟩

theorem Xi_reg {m : Nat} {x : Ordinal.{u}} (hpos : 0 < x) (hX : Xi m x < K m) : IsReg (Xi m x) :=
  M_reg hpos (Xi_spec hX).1

theorem Xi_fixed {m : Nat} {x : Ordinal.{u}} (hpos : 0 < x) (hX : Xi m x < K m) :
    Om (Xi m x) = Xi m x :=
  M_fixed hpos (Xi_spec hX).1

theorem Xi_level {m : Nat} {x : Ordinal.{u}} (hX : Xi m x < K m) : 1 ≤ m := by
  cases m with
  | zero => exact absurd hX (not_lt_of_le (zero_le _))
  | succ m => exact Nat.succ_le_succ (Nat.zero_le m)

theorem Om_ne_Xi {w x : Ordinal.{u}} {m : Nat} (hΛ : w < Λ) (hlt : w < Om w) (hpos : 0 < x)
    (hX : Xi m x < K m) : Om w ≠ Xi m x := by
  intro e
  have hf := Xi_fixed hpos hX
  rw [← hf] at e
  have hw := Om_inj hΛ (lt_trans _ _ _ hX (K_lt_Λ m)) e
  rw [hw, hf] at hlt
  exact lt_irrefl _ hlt

theorem Om_ne_Psi {w ξ π β : Ordinal.{u}} (hΛ : w < Λ) (hlt : w < Om w) (hψ : Psi ξ π β < π) :
    Om w ≠ Psi ξ π β := by
  intro e
  have sp := Psi_spec hψ
  have hw : w < Psi ξ π β := by rw [← e]; exact hlt
  have h := sp.2.2.1 _ (C_Om hΛ (C_lt hw)) (by rw [e]; exact hψ)
  rw [e] at h
  exact lt_irrefl _ h

theorem Xi_ne_one {m : Nat} {x : Ordinal.{u}} (hpos : 0 < x) (hX : Xi m x < K m) :
    Xi m x ≠ succ 0 :=
  ne_of_gt (one_lt_of_R (Xi_reg hpos hX).1)

theorem Xi_ne_K {m m' : Nat} {x : Ordinal.{u}} (hX : Xi m x < K m) : Xi m x ≠ K m' := by
  intro e
  have h1 := (Xi_spec hX).2
  rw [e] at h1 hX
  have a := K_lt_iff.mp h1
  have b := K_lt_iff.mp hX
  omega

theorem Xi_inj' {m m' : Nat} {x x' : Ordinal.{u}} (hpos : 0 < x) (hpos' : 0 < x')
    (hX : Xi m x < K m) (hX' : Xi m' x' < K m') (e : Xi m x = Xi m' x') : m = m' ∧ x = x' := by
  have h1 := (Xi_spec hX).2
  have h1' := (Xi_spec hX').2
  have hm : m = m' := by
    rw [e] at h1 hX
    have a := K_lt_iff.mp (lt_trans _ _ _ h1 hX')
    have b := K_lt_iff.mp (lt_trans _ _ _ h1' hX)
    omega
  subst hm
  exact And.intro rfl (Xi_inj hpos hpos' (Xi_good_of_lt hX) (Xi_good_of_lt hX') e)

/-- Prop. 4.17 (i) -/
theorem Xi_ne_Psi {n : Nat} {ξ π α β : Ordinal.{u}} (hpos : 0 < β) (hX : Xi n β < K n)
    (hψ : Psi ξ π α < π) (hπ : IsReg π) : Psi ξ π α ≠ Xi n β := by
  intro e
  have sp := Psi_spec hψ
  have sx := (Xi_good_of_lt hX).spec hpos
  have hπK : π < K n := by
    cases lt_or_le π (K n) with
    | inl h => exact h
    | inr h =>
      cases h with
      | inl hKπ =>
        have h' := sp.2.2.1 _ (C_K α _ n) hKπ
        rw [e] at h'
        exact absurd (lt_trans _ _ _ h' hX) (lt_irrefl _)
      | inr e' => exact absurd e'.symm (hπ.2.2 n)
  cases le_or_lt α β with
  | inl hαβ =>
    have hC : C β (Xi n β) π := by rw [← e]; exact C_mono_arg hαβ sp.2.2.2.1
    have h' := sx.2 π hC hπK
    rw [← e] at h'
    exact lt_asymm h' hψ
  | inr hβα =>
    have hC : C α (Psi ξ π α) β := by rw [e]; exact C_mono_arg (Or.inl hβα) sx.1
    have h' := sp.2.2.1 _ (C_Xi n hpos hβα hC) (by rw [← e]; exact hψ)
    rw [← e] at h'
    exact lt_irrefl _ h'

theorem Psi_ne_one {ξ π α : Ordinal.{u}} (hψ : Psi ξ π α < π) (hπ : R π) :
    Psi ξ π α ≠ succ 0 := by
  intro e
  have h := (Psi_spec hψ).2.2.1 _ (C_one α _) (one_lt_of_R hπ)
  rw [e] at h
  exact lt_irrefl _ h

theorem Psi_ne_K {ξ π α : Ordinal.{u}} {m : Nat} (hψ : Psi ξ π α < π) : Psi ξ π α ≠ K m := by
  intro e
  have h := (Psi_spec hψ).2.2.1 _ (C_K α _ m) (by rw [← e]; exact hψ)
  rw [e] at h
  exact lt_irrefl _ h

/-- Prop. 4.17 (ii) -/
theorem Psi_inj {ξ π α σ κ β : Ordinal.{u}} (hψ : Psi ξ π α < π) (hψ' : Psi σ κ β < κ)
    (hπ : IsReg π) (hκ : IsReg κ) (e : Psi ξ π α = Psi σ κ β) : ξ = σ ∧ π = κ ∧ α = β := by
  -- `α = β`
  have kα : ∀ {ξ π α σ κ β : Ordinal.{u}}, Psi ξ π α < π → Psi σ κ β < κ → IsReg π →
      Psi ξ π α = Psi σ κ β → ¬ α < β := by
    intro ξ π α σ κ β hψ hψ' hπ e hαβ
    have sp := Psi_spec hψ
    have mono : ∀ z, C α (Psi ξ π α) z → C β (Psi σ κ β) z := fun z hz => by
      rw [← e]; exact C_mono_arg (Or.inl hαβ) hz
    have h := (Psi_spec hψ').2.2.1 _ (C_Psi hαβ sp.1 hπ (mono _ (Psi_C_xi' hψ)) (mono _ sp.2.2.2.1)
      (mono _ sp.2.2.2.2)) (by rw [e]; exact hψ')
    rw [e] at h
    exact lt_irrefl _ h
  have hαβ : α = β := by
    cases lt_total α β with
    | inl h => exact absurd h (kα hψ hψ' hπ e)
    | inr h =>
      cases h with
      | inl h => exact h
      | inr h => exact absurd h (kα hψ' hψ hκ e.symm)
  subst hαβ
  -- `π = κ`
  have kπ : ∀ {ξ π σ κ : Ordinal.{u}}, Psi ξ π α < π → Psi σ κ α < κ →
      Psi ξ π α = Psi σ κ α → ¬ π < κ := by
    intro ξ π σ κ hψ hψ' e hπκ
    have hC : C α (Psi σ κ α) π := by rw [← e]; exact (Psi_spec hψ).2.2.2.1
    have h := (Psi_spec hψ').2.2.1 _ hC hπκ
    rw [← e] at h
    exact lt_asymm h hψ
  have hπκ : π = κ := by
    cases lt_total π κ with
    | inl h => exact absurd h (kπ hψ hψ' e)
    | inr h =>
      cases h with
      | inl h => exact h
      | inr h => exact absurd h (kπ hψ' hψ e.symm)
  subst hπκ
  -- `ξ = σ`
  have kξ : ∀ {ξ σ : Ordinal.{u}}, Psi ξ π α < π → Psi σ π α < π →
      Psi ξ π α = Psi σ π α → ¬ ξ < σ := by
    intro ξ σ hψ hψ' e hξσ
    have sp := Psi_spec hψ
    have sp' := Psi_spec hψ'
    have hσ0 : σ ≠ 0 := ne_of_gt (lt_of_le_of_lt (zero_le ξ) hξσ)
    have hM := (M_pos_iff hσ0 _).mp sp'.2.1
    have hC : C σ (Psi σ π α) ξ := by rw [← e]; exact C_mono_arg (Or.inl hξσ) (Psi_C_xi hψ)
    have h := Psi_le_of_stationary hM.1.1 (Or.inl hψ') sp'.2.2.1 sp'.2.2.2.1 sp'.2.2.2.2 sp.1
      (hM.2.2.2 ξ hξσ hC)
    rw [e] at h
    exact lt_irrefl _ h
  have hξσ : ξ = σ := by
    cases lt_total ξ σ with
    | inl h => exact absurd h (kξ hψ hψ' e)
    | inr h =>
      cases h with
      | inl h => exact h
      | inr h => exact absurd h (kξ hψ' hψ e.symm)
  exact ⟨hξσ, rfl, rfl⟩

/-! ### 表示の一意性 -/

theorem GenRep_Om {S : Ordinal.{u} → Prop} {γ w : Ordinal.{u}} (h : GenRep S γ (Om w))
    (hΛ : w < Λ) (hlt : w < Om w) : S w := by
  rcases h with h | ⟨m, h⟩ | ⟨w', hw', hΛ', _, h⟩ | ⟨m, x, _, hpos, _, hX, h⟩ |
      ⟨ξ, π, β, _, _, _, _, _, _, hψ, h⟩
  · exact absurd h (Om_ne_one hlt)
  · exact absurd h (Om_ne_K hΛ hlt)
  · rw [Om_inj hΛ hΛ' h]; exact hw'
  · exact absurd h (Om_ne_Xi hΛ hlt hpos hX)
  · exact absurd h (Om_ne_Psi hΛ hlt hψ)

theorem GenRep_Xi {S : Ordinal.{u} → Prop} {γ x : Ordinal.{u}} {m : Nat}
    (h : GenRep S γ (Xi m x)) (hpos : 0 < x) (hX : Xi m x < K m) : S x ∧ x < γ := by
  rcases h with h | ⟨m', h⟩ | ⟨w, _, hΛ, hlt, h⟩ | ⟨m', x', hx', hpos', hxγ, hX', h⟩ |
      ⟨ξ, π, β, _, _, _, _, _, hπ, hψ, h⟩
  · exact absurd h (Xi_ne_one hpos hX)
  · exact absurd h (Xi_ne_K hX)
  · exact absurd h.symm (Om_ne_Xi hΛ hlt hpos hX)
  · rw [(Xi_inj' hpos hpos' hX hX' h).2]; exact And.intro hx' hxγ
  · exact absurd h.symm (Xi_ne_Psi hpos hX hψ hπ)

theorem GenRep_Psi {S : Ordinal.{u} → Prop} {γ ξ π β : Ordinal.{u}}
    (h : GenRep S γ (Psi ξ π β)) (hπ : IsReg π) (hψ : Psi ξ π β < π) :
    S ξ ∧ S π ∧ S β ∧ β < γ := by
  rcases h with h | ⟨m, h⟩ | ⟨w, _, hΛ, hlt, h⟩ | ⟨m, x, _, hpos, _, hX, h⟩ |
      ⟨ξ', π', β', hξ', hπ', hβ', hβγ, _, hπR', hψ', h⟩
  · exact absurd h (Psi_ne_one hψ hπ.1)
  · exact absurd h (Psi_ne_K hψ)
  · exact absurd h.symm (Om_ne_Psi hΛ hlt hψ)
  · exact absurd h (Xi_ne_Psi hpos hX hψ hπ)
  · have e := Psi_inj hψ hψ' hπ hπR' h
    rw [e.1, e.2.1, e.2.2]
    exact ⟨hξ', hπ', hβ', hβγ⟩

/-! ### 推移補題 -/

/-- `z ∈ C(σ, x) ∩ C(β, y)`、`y < x ≤ π`、`C(β, y) ∩ π ⊆ y` なら `z ∈ C(σ, y)` -/
theorem transfer {σ x β y π : Ordinal.{u}} (hyx : y < x) (hxπ : x ≤ π)
    (hy : ∀ w, C β y w → w < π → w < y) :
    ∀ n z, Cn σ x n z → C β y z → C σ y z := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro z hz hzC
    have ihb : ∀ w, Below σ x n w → C β y w → C σ y w := by
      intro w hw hwC
      cases hw with
      | intro k hk => exact ih k hk.1 w hk.2 hwC
    cases cnf_exists z with
    | intro l hl =>
      apply C_of_cnf hl
      intro p hp
      have hpn := Cn_cnf hz hl p hp
      have hpC := C_cnf hzC hl hp
      have hP := hl.principal hp
      cases lt_or_le p x with
      | inl hpx =>
        cases lt_or_le p y with
        | inl hpy => exact C_lt hpy
        | inr hyp => exact absurd (hy p hpC (lt_of_lt_of_le hpx hxπ)) (not_lt_of_le hyp)
      | inr hxp =>
        have hrep' := C_gen hpC hP (le_trans (Or.inl hyx) hxp)
        rcases Cn_gen hpn hP hxp with h | ⟨m, h⟩ | ⟨w, hw, hΛ, hlt, h⟩ |
            ⟨m, t, ht, hpos, htσ, hX, h⟩ | ⟨ξ', π', β', hξ', hπ', hβ', hβσ, hξβ, hπR, hψ, h⟩
        · rw [h]; exact C_one σ y
        · rw [h]; exact C_K σ y m
        · rw [h] at hrep' ⊢
          exact C_Om hΛ (ihb w hw (GenRep_Om hrep' hΛ hlt))
        · rw [h] at hrep' ⊢
          exact C_Xi m hpos htσ (ihb t ht (GenRep_Xi hrep' hpos hX).1)
        · rw [h] at hrep' ⊢
          have g := GenRep_Psi hrep' hπR hψ
          exact C_Psi hβσ hξβ hπR (ihb ξ' hξ' g.1) (ihb π' hπ' g.2.1) (ihb β' hβ' g.2.2.1)

/-! ### Prop. 4.20 -/

/-- Prop. 4.20 の場合 (3)：`ξ < σ`、`ξ ∈ C(α, Ψ^σ_π(α))` なら `Ψ^ξ_π(α) < Ψ^σ_π(α)` -/
theorem Psi_lt_Psi_of_case3 {ξ σ π α : Ordinal.{u}} (hπ : IsReg π) (hx : Psi ξ π α < π)
    (hy : Psi σ π α < π) (hξσ : ξ < σ) (hξC : C α (Psi σ π α) ξ) :
    Psi ξ π α < Psi σ π α := by
  apply lt_of_not_le
  intro hle
  cases hle with
  | inr e => exact absurd (Psi_inj hy hx hπ hπ e).1 (ne_of_gt hξσ)
  | inl hyx =>
    have sp := Psi_spec hx
    have sp' := Psi_spec hy
    have hσ0 : σ ≠ 0 := ne_of_gt (lt_of_le_of_lt (zero_le ξ) hξσ)
    have hM := (M_pos_iff hσ0 _).mp sp'.2.1
    cases C_mono_arg (Or.inl hξσ) (Psi_C_xi hx) with
    | intro n hn =>
      have hξy := transfer hyx (Or.inl hx) sp'.2.2.1 n ξ hn hξC
      have h := Psi_le_of_stationary hM.1.1 (Or.inl hy) sp'.2.2.1 sp'.2.2.2.1 sp'.2.2.2.2 sp.1
        (hM.2.2.2 ξ hξσ hξy)
      exact lt_asymm h hyx

/-- Prop. 4.20：同じ階の `Ψ` どうしの比較（`Ψ^ξ_π(α) < κ`、`Ψ^σ_κ(β) < π` のとき） -/
theorem Psi_lt_Psi_iff {ξ π α σ κ β : Ordinal.{u}} (hπ : IsReg π) (hκ : IsReg κ)
    (hx : Psi ξ π α < π) (hy : Psi σ κ β < κ) (hyπ : Psi σ κ β < π) (hxκ : Psi ξ π α < κ) :
    Psi ξ π α < Psi σ κ β ↔
      (α < β ∧ C β (Psi σ κ β) α ∧ C β (Psi σ κ β) ξ ∧ C β (Psi σ κ β) π) ∨
      (β ≤ α ∧ ¬ (C α (Psi ξ π α) β ∧ C α (Psi ξ π α) σ ∧ C α (Psi ξ π α) κ)) ∨
      (α = β ∧ κ = π ∧ ξ < σ ∧ C β (Psi σ κ β) ξ) ∨
      (σ < ξ ∧ ¬ C ξ (Psi ξ π α) σ) := by
  have sp := Psi_spec hx
  have sp' := Psi_spec hy
  apply Iff.intro
  · intro hlt
    have mono : ∀ z, C α (Psi ξ π α) z → C α (Psi σ κ β) z := fun z hz =>
      C_mono_base (Or.inl hlt) hz
    cases lt_total α β with
    | inl hαβ =>
      have mono' : ∀ z, C α (Psi ξ π α) z → C β (Psi σ κ β) z := fun z hz =>
        C_mono_arg (Or.inl hαβ) (mono z hz)
      exact Or.inl ⟨hαβ, mono' _ sp.2.2.2.2, mono' _ (Psi_C_xi' hx), mono' _ sp.2.2.2.1⟩
    | inr h =>
      cases h with
      | inr hβα =>
        refine Or.inr (Or.inl (And.intro (Or.inl hβα) ?_))
        intro hC
        have h' := sp.2.2.1 _ (C_Psi hβα sp'.1 hκ hC.2.1 hC.2.2 hC.1) hyπ
        exact lt_asymm hlt h'
      | inl e =>
        subst e
        cases lt_total κ π with
        | inl hκπ =>
          refine Or.inr (Or.inl (And.intro (le_refl α) ?_))
          intro hC
          have h' := sp.2.2.1 _ hC.2.2 hκπ
          exact lt_asymm (lt_trans _ _ _ hlt hy) h'
        | inr h =>
          cases h with
          | inr hπκ =>
            have h' := sp'.2.2.1 _ (mono _ sp.2.2.2.1) hπκ
            exact absurd (lt_trans _ _ _ h' hyπ) (lt_irrefl _)
          | inl e =>
            subst e
            by_cases hσ : C α (Psi ξ κ α) σ
            · cases lt_total ξ σ with
              | inl hξσ => exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hξσ, mono _ (Psi_C_xi' hx)⟩))
              | inr h =>
                cases h with
                | inl e => subst e; exact absurd hlt (lt_irrefl _)
                | inr hσξ =>
                  exact absurd (Psi_lt_Psi_of_case3 hπ hy hx hσξ hσ) (lt_asymm hlt)
            · exact Or.inr (Or.inl (And.intro (le_refl α) (fun hC => hσ hC.2.1)))
  · intro h
    rcases h with h | h | h | h
    · exact sp'.2.2.1 _ (C_Psi h.1 sp.1 hπ h.2.2.1 h.2.2.2 h.2.1) hxκ
    · apply lt_of_not_le
      intro hle
      have mono : ∀ z, C β (Psi σ κ β) z → C α (Psi ξ π α) z := fun z hz =>
        C_mono_arg h.1 (C_mono_base hle hz)
      exact h.2 ⟨mono _ sp'.2.2.2.2, mono _ (Psi_C_xi' hy), mono _ sp'.2.2.2.1⟩
    · obtain ⟨e1, e2, hξσ, hC⟩ := h
      subst e1
      subst e2
      exact Psi_lt_Psi_of_case3 hπ hx hy hξσ hC
    · apply lt_of_not_le
      intro hle
      exact h.2 (C_mono_arg (Or.inl h.1) (C_mono_base hle (Psi_C_xi hy)))

end
end OCF.Rathjen
