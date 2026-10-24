import Compact.OCFRathjen.Setting

/-! 比較の補題（Rathjen §4 の Lemma 4.14, Prop. 4.21 の加法版）。

同じ階 `m`（`K_{m-1} < · < K_m`）の項どうしの比較で、記法系 `T⁺` の `xiLtXi`・`psiLtXi` がそのまま使う形。

* `Xi_lt_Xi_iff`（Lemma 4.14）：`Ξ_m(α) < Ξ_m(β)` ⟺ `α < β ∧ α ∈ C(β, Ξ_m(β))` または `β < α ∧ β ∉ C(α, Ξ_m(α))`。
* `Xi_inj`（Cor. 4.15）：`α ≠ β` なら `Ξ_m(α) ≠ Ξ_m(β)`。
* `Psi_lt_Xi_iff`（Prop. 4.21）：`Ψ^ξ_π(α) < Ξ_m(β)` ⟺ `π ≤ Ξ_m(β)` または `β < α ∧ β ∉ C(α, Ψ^ξ_π(α))`。

`Ξ_m(α)` については、`Ξ_m(α) ∈ M^α` かつ `K_{m-1} < Ξ_m(α) < K_m`（`XiGood`）を仮定する。
`StationaryHyp` のもとで、標準形の項の値はこれを満たす（`Xi_mem`）。 -/

namespace OCF.Rathjen

universe u

open Ordinal

noncomputable section

variable [Setting.{u}]

/-- `Ξ_m(α) ∈ M^α` かつ `K_{m-1} < Ξ_m(α) < K_m` -/
def XiGood (m : Nat) (α : Ordinal.{u}) : Prop :=
  M α (Xi m α) ∧ K (m - 1) < Xi m α ∧ Xi m α < K m

/-- `XiGood` から `α ∈ C(α, Ξ_m(α))` と `C(α, Ξ_m(α)) ∩ K_m ⊆ Ξ_m(α)` -/
theorem XiGood.spec {m : Nat} {α : Ordinal.{u}} (hα0 : 0 < α) (h : XiGood m α) :
    C α (Xi m α) α ∧ ∀ x, C α (Xi m α) x → x < K m → x < Xi m α := by
  have hM := (M_pos_iff (ne_of_gt hα0) _).mp h.1
  have hK : Kabove (Xi m α) = K m := Kabove_eq_of_between (Or.inl h.2.1) h.2.2
  refine And.intro hM.2.2.1 ?_
  intro x hx hxK
  exact hM.2.1 x hx (by rw [hK]; exact hxK)

/-- Lemma 4.14 -/
theorem Xi_lt_Xi_iff {m : Nat} {α β : Ordinal.{u}} (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα : XiGood m α) (hβ : XiGood m β) :
    Xi m α < Xi m β ↔ (α < β ∧ C β (Xi m β) α) ∨ (β < α ∧ ¬ C α (Xi m α) β) := by
  have sα := hα.spec hα0
  have sβ := hβ.spec hβ0
  apply Iff.intro
  · intro hlt
    cases lt_total α β with
    | inl hαβ =>
      exact Or.inl (And.intro hαβ (C_mono_base (Or.inl hlt) (C_mono_arg (Or.inl hαβ) sα.1)))
    | inr h =>
      cases h with
      | inl e => rw [e] at hlt; exact absurd hlt (lt_irrefl _)
      | inr hβα =>
        refine Or.inr (And.intro hβα ?_)
        intro hC
        have hXi : Xi m β < Xi m α := sα.2 _ (C_Xi m hβ0 hβα hC) hβ.2.2
        exact lt_asymm hlt hXi
  · intro h
    cases h with
    | inl h => exact sβ.2 _ (C_Xi m hα0 h.1 h.2) hα.2.2
    | inr h =>
      apply lt_of_not_le
      intro hle
      exact h.2 (C_mono_arg (Or.inl h.1) (C_mono_base hle sβ.1))

/-- Cor. 4.15 -/
theorem Xi_inj {m : Nat} {α β : Ordinal.{u}} (hα0 : 0 < α) (hβ0 : 0 < β)
    (hα : XiGood m α) (hβ : XiGood m β) (e : Xi m α = Xi m β) : α = β := by
  have sα := hα.spec hα0
  have sβ := hβ.spec hβ0
  cases lt_total α β with
  | inl hαβ =>
    have hC : C β (Xi m β) α := by rw [← e]; exact C_mono_arg (Or.inl hαβ) sα.1
    have hlt := sβ.2 _ (C_Xi m hα0 hαβ hC) hα.2.2
    rw [e] at hlt
    exact absurd hlt (lt_irrefl _)
  | inr h =>
    cases h with
    | inl h => exact h
    | inr hβα =>
      have hC : C α (Xi m α) β := by rw [e]; exact C_mono_arg (Or.inl hβα) sβ.1
      have hlt := sα.2 _ (C_Xi m hβ0 hβα hC) hβ.2.2
      rw [e] at hlt
      exact absurd hlt (lt_irrefl _)

/-- Prop. 4.21：同じ階 `m` の `Ψ^ξ_π(α)`（`π < K_m`）と `Ξ_m(β)` の比較 -/
theorem Psi_lt_Xi_iff {m : Nat} {ξ π α β : Ordinal.{u}} (hβ0 : 0 < β) (hβ : XiGood m β)
    (hψ : Psi ξ π α < π) (hπK : π < K m) :
    Psi ξ π α < Xi m β ↔ π ≤ Xi m β ∨ (β < α ∧ ¬ C α (Psi ξ π α) β) := by
  have sβ := hβ.spec hβ0
  have sψ := Psi_spec hψ
  apply Iff.intro
  · intro hlt
    cases le_or_lt π (Xi m β) with
    | inl h => exact Or.inl h
    | inr hXπ =>
      refine Or.inr ?_
      cases lt_or_le β α with
      | inr hαβ =>
        have hπC : C β (Xi m β) π := C_mono_base (Or.inl hlt) (C_mono_arg hαβ sψ.2.2.2.1)
        exact absurd (sβ.2 π hπC hπK) (not_lt_of_le (Or.inl hXπ))
      | inl hβα =>
        refine And.intro hβα ?_
        intro hC
        have hXψ : Xi m β < Psi ξ π α := sψ.2.2.1 _ (C_Xi m hβ0 hβα hC) hXπ
        exact lt_asymm hlt hXψ
  · intro h
    cases h with
    | inl h => exact lt_of_lt_of_le hψ h
    | inr h =>
      apply lt_of_not_le
      intro hle
      cases hle with
      | inl hlt =>
        exact h.2 (C_mono_arg (Or.inl h.1) (C_mono_base (Or.inl hlt) sβ.1))
      | inr e =>
        exact h.2 (C_mono_arg (Or.inl h.1) (by rw [← e]; exact sβ.1))

end

/-! ## 生成子の値と `C(γ, δ)` の元の分解。

* 生成子の値（`1`、`K_m`、`Ω_w`、`Ξ_m(x)`（`x > 0`）、`Ψ^ξ_π(β)`（`π ∈ Reg`））は加法的主数か `0`。
* `Cn_cnf`：`z ∈ C(γ, δ)` の Cantor 標準形の項は、同じ段階で `C(γ, δ)` に入る（Lemma 4.18 (i) の加法版）。
* `Cn_gen`：加法的主数 `z ∈ C(γ, δ)` で `z ≥ δ` のものは、本物の生成子の値（`Ω_w` で `w < Ω_w`、
  `Ξ_m(x) < K_m`、`Ψ^ξ_π(β) < π`）か `1`・`K_m` で、その引数はより前の段階で `C(γ, δ)` に入る。 -/

noncomputable section

/-- 非可算正則基数の閉包の元は加法的主数 -/
theorem principal_of_closure_R {ξ : Ordinal.{u}} (h : closure R ξ) : IsPrincipal ξ := by
  cases (closure_iff R ξ).mp h with
  | inl hR => exact hR.2.isPrincipal
  | inr hlp =>
    refine And.intro (ne_of_gt hlp.1) (addPrincipal_of_limit ?_)
    intro η hη
    cases hlp.2 η hη with
    | intro ρ hρ => exact Exists.intro ρ (And.intro hρ.1.2.addPrincipal (And.intro hρ.2.1 (Or.inl hρ.2.2)))

/-- `0` か加法的主数の Cantor 標準形は、自分自身だけからなる -/
theorem cnf_mem_eq_of_principal_or_zero {z : Ordinal.{u}} (hz : z = 0 ∨ IsPrincipal z)
    {l : List Ordinal.{u}} (h : CNF z l) {p : Ordinal.{u}} (hp : p ∈ l) : p = z := by
  cases hz with
  | inl h0 =>
    rw [h0] at h
    rw [cnf_unique h cnf_zero] at hp
    exact absurd hp List.not_mem_nil
  | inr hP =>
    rw [cnf_of_principal hP h] at hp
    exact List.mem_singleton.mp hp

theorem C_of_cnf {γ δ z : Ordinal.{u}} [Setting.{u}] {l : List Ordinal.{u}} (h : CNF z l)
    (hl : ∀ p, p ∈ l → C γ δ p) : C γ δ z := by
  rw [h.eq]
  clear h
  induction l with
  | nil => exact C_zero γ δ
  | cons a l ih =>
    rw [listSum_cons]
    exact C_add (hl a List.mem_cons_self) (ih (fun p hp => hl p (List.mem_cons_of_mem a hp)))

variable [Setting.{u}]

theorem M_pos_of_mem {ξ ρ : Ordinal.{u}} (h : M ξ ρ) : 0 < ρ := by
  cases eq_zero_or_pos ξ with
  | inl h0 => subst h0; exact ((M_zero_iff ρ).mp h).1.1
  | inr hpos => exact ((M_pos_iff (ne_of_gt hpos) ρ).mp h).1.1.2.pos

theorem M_reg {ξ ρ : Ordinal.{u}} (hξ : 0 < ξ) (h : M ξ ρ) : IsReg ρ :=
  ((M_pos_iff (ne_of_gt hξ) ρ).mp h).1

theorem IsReg.principal {π : Ordinal.{u}} (h : IsReg π) : IsPrincipal π := h.1.2.isPrincipal

theorem Om_principal_or_zero {x : Ordinal.{u}} (hx : x < Λ) : Om x = 0 ∨ IsPrincipal (Om x) := by
  cases cardSet_Om hx with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr (principal_of_closure_R h)

theorem K_principal_or_zero (m : Nat) : K.{u} m = 0 ∨ IsPrincipal (K m) := by
  cases m with
  | zero => exact Or.inl rfl
  | succ m => exact Or.inr (R_K (Nat.succ_le_succ (Nat.zero_le m))).2.isPrincipal

theorem Xi_eq_K_of_not_lt {m : Nat} {x : Ordinal.{u}} (h : ¬ Xi m x < K m) : Xi m x = K m :=
  le_antisymm (Xi_le m x) (le_of_not_lt h)

theorem Xi_principal_or_zero (m : Nat) {x : Ordinal.{u}} (hx : 0 < x) :
    Xi m x = 0 ∨ IsPrincipal (Xi m x) := by
  by_cases h : Xi m x < K m
  · exact Or.inr (M_reg hx (Xi_spec h).1).principal
  · rw [Xi_eq_K_of_not_lt h]; exact K_principal_or_zero m

theorem Psi_eq_of_not_lt {ξ π β : Ordinal.{u}} (h : ¬ Psi ξ π β < π) : Psi ξ π β = π :=
  le_antisymm (Psi_le ξ π β) (le_of_not_lt h)

/-- `Ψ^ξ_π(β) < π` なら加法的主数 -/
theorem Psi_principal_of_lt {ξ π β : Ordinal.{u}} (hπ : R π) (h : Psi ξ π β < π) :
    IsPrincipal (Psi ξ π β) := by
  have hs := Psi_spec h
  refine And.intro (ne_of_gt (M_pos_of_mem hs.2.1)) ?_
  intro a b ha hb
  exact hs.2.2.1 _ (C_add (C_lt ha) (C_lt hb))
    (hπ.2.add_lt (lt_trans _ _ _ ha h) (lt_trans _ _ _ hb h))

theorem Psi_principal {ξ π β : Ordinal.{u}} (hπ : IsReg π) : IsPrincipal (Psi ξ π β) := by
  by_cases h : Psi ξ π β < π
  · exact Psi_principal_of_lt hπ.1 h
  · rw [Psi_eq_of_not_lt h]; exact hπ.principal

/-! ### Lemma 4.18 (i)：Cantor 標準形の項 -/

theorem Cn_cnf {γ δ : Ordinal.{u}} : ∀ {n : Nat} {z : Ordinal.{u}}, Cn γ δ n z →
    ∀ {l : List Ordinal.{u}}, CNF z l → ∀ p, p ∈ l → Cn γ δ n p := by
  intro n z h
  unfold Cn at h ⊢
  induction h with
  | lt n w hw =>
    intro l hl p hp
    exact StageC.lt n p (lt_of_le_of_lt (hl.le hp) hw)
  | one n =>
    intro l hl p hp
    rw [cnf_mem_eq_of_principal_or_zero (Or.inr isPrincipal_one) hl hp]
    exact StageC.one n
  | kc n m =>
    intro l hl p hp
    rw [cnf_mem_eq_of_principal_or_zero (K_principal_or_zero m) hl hp]
    exact StageC.kc n m
  | add n x y _ _ ihx ihy =>
    intro l hl p hp
    cases cnf_exists x with
    | intro lx hx =>
      cases cnf_exists y with
      | intro ly hy =>
        cases cnf_add hx hy with
        | intro l' hl' =>
          rw [cnf_unique hl hl'.1] at hp
          cases hl'.2 p hp with
          | inl h => exact Cn_succ (ihx hx p h)
          | inr h => exact Cn_succ (ihy hy p h)
  | om n x hΛ hx _ =>
    intro l hl p hp
    rw [cnf_mem_eq_of_principal_or_zero (Om_principal_or_zero hΛ) hl hp]
    exact StageC.om n x hΛ hx
  | xi n m x hpos hα hx _ =>
    intro l hl p hp
    rw [cnf_mem_eq_of_principal_or_zero (Xi_principal_or_zero m hpos) hl hp]
    exact StageC.xi n m x hpos hα hx
  | psi n ξ π β hβ hξβ hπ hξ hπC hβC _ _ _ =>
    intro l hl p hp
    rw [cnf_mem_eq_of_principal_or_zero (Or.inr (Psi_principal hπ)) hl hp]
    exact StageC.psi n ξ π β hβ hξβ hπ hξ hπC hβC

theorem C_cnf {γ δ z : Ordinal.{u}} (h : C γ δ z) {l : List Ordinal.{u}} (hl : CNF z l)
    {p : Ordinal.{u}} (hp : p ∈ l) : C γ δ p := by
  cases h with
  | intro n hn => exact Exists.intro n (Cn_cnf hn hl p hp)

/-- `z ∈ C(γ, δ)` ⟺ `z` の Cantor 標準形の項が全て `C(γ, δ)` に入る -/
theorem C_iff_cnf {γ δ z : Ordinal.{u}} {l : List Ordinal.{u}} (hl : CNF z l) :
    C γ δ z ↔ ∀ p, p ∈ l → C γ δ p :=
  Iff.intro (fun h _ hp => C_cnf h hl hp) (C_of_cnf hl)

/-! ### 生成子への分解（Def. 5.1 (T1)–(T6) の一意性の前半） -/

/-- 本物の生成子による表示（引数は `S` に入る） -/
def GenRep (S : Ordinal.{u} → Prop) (γ z : Ordinal.{u}) : Prop :=
  z = succ 0 ∨ (∃ m, z = K m) ∨
    (∃ w, S w ∧ w < Λ ∧ w < Om w ∧ z = Om w) ∨
    (∃ m x, S x ∧ 0 < x ∧ x < γ ∧ Xi m x < K m ∧ z = Xi m x) ∨
    (∃ ξ π β, S ξ ∧ S π ∧ S β ∧ β < γ ∧ ξ ≤ β ∧ IsReg π ∧ Psi ξ π β < π ∧ z = Psi ξ π β)

theorem GenRep.mono {S T : Ordinal.{u} → Prop} (hST : ∀ x, S x → T x) {γ z : Ordinal.{u}}
    (h : GenRep S γ z) : GenRep T γ z := by
  rcases h with h | h | ⟨w, hw, h⟩ | ⟨m, x, hx, h⟩ | ⟨ξ, π, β, hξ, hπ, hβ, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ⟨w, hST w hw, h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, x, hST x hx, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ξ, π, β, hST ξ hξ, hST π hπ, hST β hβ, h⟩)))
/-- `n` より前の段階で `C(γ, δ)` に入る -/
def Below (γ δ : Ordinal.{u}) (n : Nat) (x : Ordinal.{u}) : Prop := ∃ k, k < n ∧ Cn γ δ k x

theorem Below.mono {γ δ : Ordinal.{u}} {n m : Nat} (h : n ≤ m) {x : Ordinal.{u}}
    (hx : Below γ δ n x) : Below γ δ m x := by
  cases hx with
  | intro k hk => exact Exists.intro k (And.intro (Nat.lt_of_lt_of_le hk.1 h) hk.2)

/-- 加法的主数 `z ∈ C_n(γ, δ)` で `δ ≤ z` なら、`n` より前の段階の引数による本物の生成子の表示がある -/
theorem Cn_gen {γ δ : Ordinal.{u}} : ∀ {n : Nat} {z : Ordinal.{u}}, Cn γ δ n z →
    IsPrincipal z → δ ≤ z → GenRep (Below γ δ n) γ z := by
  intro n z h
  unfold Cn at h
  induction h with
  | lt n w hw => intro _ hle; exact absurd hw (not_lt_of_le hle)
  | one n => intro _ _; exact Or.inl rfl
  | kc n m => intro _ _; exact Or.inr (Or.inl ⟨m, rfl⟩)
  | add n x y _ _ ihx ihy =>
    intro hP hle
    cases hP.add_cases with
    | inl h =>
      rw [h.1] at hP hle ⊢
      exact (ihx hP hle).mono (fun _ hb => hb.mono (Nat.le_succ n))
    | inr h =>
      rw [h] at hP hle ⊢
      exact (ihy hP hle).mono (fun _ hb => hb.mono (Nat.le_succ n))
  | om n x hΛ hx ih =>
    intro hP hle
    by_cases hlt : x < Om x
    · exact Or.inr (Or.inr (Or.inl ⟨x, ⟨n, Nat.lt_succ_self n, hx⟩, hΛ, hlt, rfl⟩))
    · have he : Om x = x := le_antisymm (le_of_not_lt hlt) (le_Om hΛ)
      rw [he] at hP hle ⊢
      exact (ih hP hle).mono (fun _ hb => hb.mono (Nat.le_succ n))
  | xi n m x hpos hα hx _ =>
    intro _ _
    show GenRep _ _ (Xi m x)
    by_cases hlt : Xi m x < K m
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨m, x, ⟨n, Nat.lt_succ_self n, hx⟩, hpos, hα, hlt, rfl⟩)))
    · rw [Xi_eq_K_of_not_lt hlt]
      exact Or.inr (Or.inl ⟨m, rfl⟩)
  | psi n ξ π β hβ hξβ hπ hξ hπC hβC _ ihπ _ =>
    intro hP hle
    show GenRep _ _ (Psi ξ π β)
    by_cases hlt : Psi ξ π β < π
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ξ, π, β, ⟨n, Nat.lt_succ_self n, hξ⟩,
        ⟨n, Nat.lt_succ_self n, hπC⟩, ⟨n, Nat.lt_succ_self n, hβC⟩, hβ, hξβ, hπ, hlt, rfl⟩)))
    · have he := Psi_eq_of_not_lt hlt
      have hP' : IsPrincipal π := by rw [← he]; exact hP
      have hle' : δ ≤ π := by rw [← he]; exact hle
      rw [he]
      exact (ihπ hP' hle').mono (fun _ hb => hb.mono (Nat.le_succ n))

theorem C_gen {γ δ z : Ordinal.{u}} (h : C γ δ z) (hP : IsPrincipal z) (hle : δ ≤ z) :
    GenRep (C γ δ) γ z := by
  cases h with
  | intro n hn =>
    exact (Cn_gen hn hP hle).mono (fun x hx => by
      cases hx with
      | intro k hk => exact Exists.intro k hk.2)

/-! ## 生成子の値の一意性と `Ψ` どうしの比較（Rathjen Lemma 4.17・4.19 (i)(ii)、Prop. 4.20 の加法版）。

* `M_fixed`（Lemma 4.19 (i)）：`α > 0`、`π ∈ M^α` なら `Ω_π = π`。
* `Psi_fixed`（Lemma 4.19 (ii)）：`Ω_π = π`、`Ψ^ξ_π(α) < π` なら `Ω_Ψ = Ψ`。
* `Xi_ne_Psi`・`Psi_inj`（Prop. 4.17）、ほか生成子の値が互いに異なること。
* `GenRep_Om`・`GenRep_Xi`・`GenRep_Psi`：本物の生成子の値の表示は引数まで一意。
* `transfer`：`z ∈ C(σ, x) ∩ C(β, y)`、`y < x ≤ π`、`C(β, y) ∩ π ⊆ y` なら `z ∈ C(σ, y)`。
* `Psi_le_of_stationary`：Prop. 4.16 の議論の一般形。
* `Psi_lt_Psi_iff`（Prop. 4.20）。 -/

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

/-! ## 標準形の意味論版 `Good` と、その値の性質。

`Good` は `RTKA.isNF` と同じ形の帰納的述語で、`isNF` が `cmp`・`inC` で調べる条件を順序数の条件
（`val a < Ω_{val a}`、`val a ∈ C(val a, K_n)` など）に置き換えたもの。

* `Good.inv`：`StationaryHyp` のもとで、`Good` な項の値は良い性質（`Inv`）をもつ。
  加法的主数・階・Cantor 標準形、正則な項の定常性（Lemma 5.2）、`Ω` の不動点（Lemma 4.19）など。
* `val_inj`：`Good` な項の上で `val` は単射（Lemma 5.2 (iii)）。 -/

noncomputable section

open RTKA (Tm)

/-! ### 項の構文についての補題 -/

theorem summands_eq_nil {t : Tm} : RTKA.summands t = [] ↔ t = .zero := by
  cases t <;> simp [RTKA.summands]

theorem ne_zero_of_isPrincipal {t : Tm} (h : RTKA.isPrincipal t = true) : t ≠ .zero := by
  intro e; subst e; simp [RTKA.isPrincipal] at h

theorem ne_zero_of_isRegTerm {t : Tm} (h : RTKA.isRegTerm t = true) : t ≠ .zero := by
  intro e; subst e; simp [RTKA.isRegTerm] at h

theorem omegaFixed_of_isInacc {t : Tm} (h : RTKA.isInacc t = true) : RTKA.omegaFixed t = true := by
  cases t <;> simp_all [RTKA.isInacc, RTKA.omegaFixed]

theorem CNF.append_left {α : Ordinal.{u}} {l₁ l₂ : List Ordinal.{u}} (h : CNF α (l₁ ++ l₂)) :
    CNF (listSum l₁) l₁ :=
  ⟨fun p hp => h.1 p (List.mem_append_left l₂ hp), (List.pairwise_append.mp h.2.1).1, rfl⟩

variable [Setting.{u}]

/-- 標準形の意味論版（`RTKA.isNF` の条件を順序数の条件にしたもの） -/
inductive Good : Tm → Prop
  | zero : Good .zero
  | one : Good .one
  | kc (n : Nat) (hn : 1 ≤ n) : Good (.K n)
  | plus (a b : Tm) (ha : Good a) (hb : Good b) (hap : RTKA.isPrincipal a = true)
      (hb0 : b ≠ .zero) (hle : ∀ h, (RTKA.summands b).head? = some h → val.{u} h ≤ val a) :
      Good (.plus a b)
  | om (a : Tm) (ha : Good a) (ha0 : a ≠ .zero) (hlt : val.{u} a < Om (val a)) : Good (.Om a)
  | xi (n : Nat) (a : Tm) (hn : 1 ≤ n) (ha : Good a) (ha0 : a ≠ .zero)
      (hle : val.{u} a ≤ Om (K n + succ 0)) (hC : C (val.{u} a) (K n) (val a)) : Good (.Xi n a)
  | psi (xi pi a m : Tm) (hxi : Good xi) (hpi : Good pi) (ha : Good a)
      (hreg : RTKA.isRegTerm pi = true) (hle : val.{u} xi ≤ val a)
      (hCa : C (val.{u} a) (val pi) (val a)) (hCxi : C (val.{u} a) (val pi) (val xi))
      (hCpi : C (val.{u} a) (val pi) (val pi)) (hm : RTKA.mOf pi = some m)
      (hxim : val.{u} xi < val m) (hCm : C (val.{u} m) (val pi) (val xi)) : Good (.Psi xi pi a)

/-- `Good` な項の値の性質 -/
structure Inv (t : Tm) : Prop where
  lt_Λ : val.{u} t < Λ
  cnf : CNF (val.{u} t) ((RTKA.summands t).map val)
  bounds : t ≠ .zero →
    1 ≤ RTKA.lev t ∧ K (RTKA.lev t - 1) ≤ val.{u} t ∧ val.{u} t < K (RTKA.lev t)
  strict : RTKA.isPrincipal t = true → (∀ n, t ≠ .K n) → K (RTKA.lev t - 1) < val.{u} t
  one_lt : RTKA.isPrincipal t = true → t ≠ .one → succ 0 < val.{u} t
  reg : RTKA.isRegTerm t = true → IsReg (val.{u} t) ∧ ∀ m, RTKA.mOf t = some m →
    ∀ ξ, ξ < val.{u} m → C (val m) (val t) ξ → Stationary (val t) (M ξ)
  fixed : RTKA.omegaFixed t = true → Om (val.{u} t) = val t
  om : ∀ a, t = .Om a → val.{u} a < Om (val a) ∧ (RTKA.isSucc a = true →
    ∃ ζ, val.{u} a = succ ζ ∧ ∀ γ δ, C γ δ (val a) → C γ δ ζ)
  xi : ∀ n a, t = .Xi n a → 0 < val.{u} a ∧ XiGood n (val.{u} a)
  psi : ∀ xi pi a, t = .Psi xi pi a →
    Psi (val.{u} xi) (val pi) (val a) < val pi ∧ IsReg (val.{u} pi)
  psi0 : ∀ c a, t = .Psi .zero (.Om c) a → ∀ w, w < val.{u} c → Om w < val t

theorem Inv.pos {t : Tm} (h : Inv.{u} t) (ht : t ≠ .zero) : 0 < val.{u} t := by
  have hc := h.cnf
  cases hs : RTKA.summands t with
  | nil => exact absurd (summands_eq_nil.mp hs) ht
  | cons p l =>
    rw [hs, List.map_cons] at hc
    exact hc.pos

theorem Inv.principal {t : Tm} (h : Inv.{u} t) (hp : RTKA.isPrincipal t = true) :
    IsPrincipal (val.{u} t) := by
  have hc := h.cnf
  rw [RTKA.summands_principal hp, List.map_cons, List.map_nil] at hc
  exact hc.head_principal

/-- `c` の最後の項が `1` なら `val c = ζ + 1` で、`val c ∈ C(γ, δ)` から `ζ ∈ C(γ, δ)` -/
theorem Inv.isSucc {c : Tm} (h : Inv.{u} c) (hs : RTKA.isSucc c = true) :
    ∃ ζ, val.{u} c = succ ζ ∧ ∀ γ δ, C γ δ (val c) → C γ δ ζ := by
  have hl : (RTKA.summands c).getLast? = some .one := by
    simpa [RTKA.isSucc] using hs
  cases List.getLast?_eq_some_iff.mp hl with
  | intro ys hys =>
    have hc := h.cnf
    rw [hys, List.map_append, List.map_cons, List.map_nil] at hc
    have hζ := CNF.append_left hc
    refine Exists.intro (listSum (ys.map val)) (And.intro ?_ ?_)
    · rw [hc.eq, listSum_append, listSum_cons, listSum_nil, add_zero]
      exact add_one_eq_succ _
    · intro γ δ hC
      apply C_of_cnf hζ
      intro p hp
      exact (C_iff_cnf hc).mp hC p (List.mem_append_left _ hp)

theorem K_isPrincipal {n : Nat} (hn : 1 ≤ n) : IsPrincipal (K.{u} n) := (R_K hn).2.isPrincipal

theorem Om_succ_isReg {ζ : Ordinal.{u}} (hΛ : succ ζ < Λ) : IsReg (Om (succ ζ)) := by
  have hR := Om_succ_R hΛ
  refine ⟨hR, Om_lt_Λ hΛ, ?_⟩
  intro n e
  cases n with
  | zero => exact absurd e (ne_of_gt hR.2.pos)
  | succ n =>
    have hK := Om_K (Nat.succ_le_succ (Nat.zero_le n))
    rw [← hK] at e
    have e' := Om_inj hΛ (K_lt_Λ _) e
    exact (R_K (Nat.succ_le_succ (Nat.zero_le n))).2.1.ne_succ ζ e'.symm

/-- `Good` な項の値の性質（Lemma 4.19、5.2 など） -/
theorem Good.inv (hS : StationaryHyp.{u}) {t : Tm} (h : Good.{u} t) : Inv.{u} t := by
  induction h with
  | zero =>
    exact {
      lt_Λ := lt_of_le_of_lt (zero_le _) (K_lt_Λ 0)
      cnf := cnf_zero
      bounds := fun h => absurd rfl h
      strict := fun h => by simp [RTKA.isPrincipal] at h
      one_lt := fun h => by simp [RTKA.isPrincipal] at h
      reg := fun h => by simp [RTKA.isRegTerm] at h
      fixed := fun h => by simp [RTKA.omegaFixed] at h
      om := fun _ h => by cases h
      xi := fun _ _ h => by cases h
      psi := fun _ _ _ h => by cases h
      psi0 := fun _ _ h => by cases h }
  | one =>
    have h1 : succ (0 : Ordinal.{u}) < K 1 := one_lt_of_R (R_K (Nat.le_refl 1))
    exact {
      lt_Λ := lt_trans _ _ _ h1 (K_lt_Λ 1)
      cnf := cnf_single isPrincipal_one
      bounds := fun _ => ⟨Nat.le_refl 1, Or.inl (zero_lt_succ 0), h1⟩
      strict := fun _ _ => zero_lt_succ 0
      one_lt := fun _ h => absurd rfl h
      reg := fun h => by simp [RTKA.isRegTerm] at h
      fixed := fun h => by simp [RTKA.omegaFixed] at h
      om := fun _ h => by cases h
      xi := fun _ _ h => by cases h
      psi := fun _ _ _ h => by cases h
      psi0 := fun _ _ h => by cases h }
  | kc n hn =>
    exact {
      lt_Λ := K_lt_Λ n
      cnf := cnf_single (K_isPrincipal hn)
      bounds := fun _ => by
        refine ⟨Nat.le_add_left 1 n, ?_, K_lt (Nat.lt_succ_self n)⟩
        show K (n + 1 - 1) ≤ K n
        rw [Nat.add_sub_cancel]
        exact le_refl _
      strict := fun _ h => absurd rfl (h n)
      one_lt := fun _ _ => one_lt_of_R (R_K hn)
      reg := fun h => by simp [RTKA.isRegTerm] at h
      fixed := fun _ => Om_K hn
      om := fun _ h => by cases h
      xi := fun _ _ h => by cases h
      psi := fun _ _ _ h => by cases h
      psi0 := fun _ _ h => by cases h }
  | plus a b _ _ hap hb0 hle iha ihb =>
    have ha0 := ne_zero_of_isPrincipal hap
    have hcnf : CNF (val.{u} (.plus a b)) ((RTKA.summands (.plus a b)).map val) := by
      rw [RTKA.summands_plus, List.map_cons]
      have hb := ihb.cnf
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        cases List.mem_cons.mp hp with
        | inl e => rw [e]; exact iha.principal hap
        | inr hp => exact hb.principal hp
      · apply List.pairwise_cons.mpr (And.intro ?_ hb.2.1)
        intro q hq
        cases hs : RTKA.summands b with
        | nil => exact absurd (summands_eq_nil.mp hs) hb0
        | cons h l =>
          rw [hs, List.map_cons] at hq hb
          exact le_trans (hb.mem_le_head hq) (hle h (by rw [hs]; rfl))
      · show val a + val b = _
        rw [listSum_cons, ← hb.eq]
    have hbd := iha.bounds ha0
    have hlt : val.{u} (.plus a b) < K (RTKA.lev (.plus a b)) := by
      have hc := hcnf
      rw [RTKA.summands_plus, List.map_cons] at hc
      exact hc.lt_of_head_lt (K_isPrincipal hbd.1) hbd.2.2
    exact {
      lt_Λ := lt_trans _ _ _ hlt (K_lt_Λ _)
      cnf := hcnf
      bounds := fun _ => ⟨hbd.1, le_trans hbd.2.1 (le_add _ _), hlt⟩
      strict := fun h => by simp [RTKA.isPrincipal] at h
      one_lt := fun h => by simp [RTKA.isPrincipal] at h
      reg := fun h => by simp [RTKA.isRegTerm] at h
      fixed := fun h => by simp [RTKA.omegaFixed] at h
      om := fun _ h => by cases h
      xi := fun _ _ h => by cases h
      psi := fun _ _ _ h => by cases h
      psi0 := fun _ _ h => by cases h }
  | om a _ ha0 hlt iha =>
    have hΛ := iha.lt_Λ
    have hva0 := iha.pos ha0
    have hP : IsPrincipal (Om (val.{u} a)) := by
      cases Om_principal_or_zero hΛ with
      | inl h0 => rw [h0] at hlt; exact absurd hlt (not_lt_of_le (zero_le _))
      | inr h => exact h
    have hbd := iha.bounds ha0
    exact {
      lt_Λ := Om_lt_Λ hΛ
      cnf := cnf_single hP
      bounds := fun _ => ⟨hbd.1, le_trans hbd.2.1 (Or.inl hlt), Om_lt_K hbd.1 hbd.2.2⟩
      strict := fun _ _ => lt_of_le_of_lt hbd.2.1 hlt
      one_lt := fun _ _ => lt_of_le_of_lt (succ_le_of_lt hva0) hlt
      reg := fun hr => by
        have hs : RTKA.isSucc a = true := by simpa [RTKA.isRegTerm] using hr
        cases iha.isSucc hs with
        | intro ζ hζ =>
          have hΛ' : succ ζ < Λ := by rw [← hζ.1]; exact hΛ
          have hreg : IsReg (Om (val.{u} a)) := by rw [hζ.1]; exact Om_succ_isReg hΛ'
          refine And.intro hreg ?_
          intro m hm ξ hξ _
          have hm1 : m = .one := by simp [RTKA.mOf] at hm; exact hm.symm
          subst hm1
          have hξ0 : ξ = 0 := (le_zero_iff ξ).mp (le_of_lt_succ hξ)
          subst hξ0
          exact Stationary.mono (stationary_isLimit hreg.1)
            (fun ρ hρ hl => (M_zero_iff ρ).mpr ⟨hl, lt_trans _ _ _ hρ hreg.2.1⟩)
      fixed := fun h => by simp [RTKA.omegaFixed] at h
      om := fun a' h => by cases h; exact ⟨hlt, iha.isSucc⟩
      xi := fun _ _ h => by cases h
      psi := fun _ _ _ h => by cases h
      psi0 := fun _ _ h => by cases h }
  | xi n a hn _ ha0 hle hC iha =>
    have hva0 := iha.pos ha0
    have good : XiGood n (val.{u} a) := Xi_mem hn (hS n hn (val a) hva0 hle hC)
    have hX : Xi n (val.{u} a) < K n := good.2.2
    have hreg := Xi_reg hva0 hX
    exact {
      lt_Λ := lt_trans _ _ _ hX (K_lt_Λ n)
      cnf := cnf_single hreg.principal
      bounds := fun _ => ⟨hn, Or.inl good.2.1, hX⟩
      strict := fun _ _ => good.2.1
      one_lt := fun _ _ => one_lt_of_R hreg.1
      reg := fun _ => by
        refine And.intro hreg ?_
        intro m hm ξ hξ hξC
        have hma : m = a := by simp [RTKA.mOf] at hm; exact hm.symm
        subst hma
        exact ((M_pos_iff (ne_of_gt hva0) _).mp good.1).2.2.2 ξ hξ hξC
      fixed := fun _ => Xi_fixed hva0 hX
      om := fun _ h => by cases h
      xi := fun _ _ h => by cases h; exact ⟨hva0, good⟩
      psi := fun _ _ _ h => by cases h
      psi0 := fun _ _ h => by cases h }
  | psi xi pi a m _ _ _ hreg hle hCa hCxi hCpi hm hxim hCm ihxi ihpi _ =>
    have hπ := (ihpi.reg hreg).1
    have hψ : Psi (val.{u} xi) (val pi) (val a) < val pi :=
      Psi_lt hπ.1 ((ihpi.reg hreg).2 m hm _ hxim hCm) hle hCxi hCpi hCa
    have sp := Psi_spec hψ
    have hbd := ihpi.bounds (ne_zero_of_isRegTerm hreg)
    have hKψ : K (RTKA.lev pi - 1) < Psi (val.{u} xi) (val pi) (val a) := by
      apply sp.2.2.1 _ (C_K _ _ _)
      cases hbd.2.1 with
      | inl h => exact h
      | inr e => exact absurd e.symm (hπ.2.2 _)
    exact {
      lt_Λ := lt_trans _ _ _ hψ ihpi.lt_Λ
      cnf := cnf_single (Psi_principal_of_lt hπ.1 hψ)
      bounds := fun _ => ⟨hbd.1, Or.inl hKψ, lt_trans _ _ _ hψ hbd.2.2⟩
      strict := fun _ _ => hKψ
      one_lt := fun _ _ => sp.2.2.1 _ (C_one _ _) (one_lt_of_R hπ.1)
      reg := fun hr => by
        have hxi0 : xi ≠ .zero := by simpa [RTKA.isRegTerm] using hr
        have hξ0 := ihxi.pos hxi0
        refine And.intro (M_reg hξ0 sp.2.1) ?_
        intro m' hm' ξ hξ hξC
        have hmx : m' = xi := by simp [RTKA.mOf] at hm'; exact hm'.symm
        subst hmx
        exact ((M_pos_iff (ne_of_gt hξ0) _).mp sp.2.1).2.2.2 ξ hξ hξC
      fixed := fun hf => by
        have hf' : xi ≠ .zero ∨ RTKA.isInacc pi = true := by
          simpa [RTKA.omegaFixed] using hf
        cases hf' with
        | inl hxi0 => exact M_fixed (ihxi.pos hxi0) sp.2.1
        | inr hi => exact Psi_fixed hψ (ihpi.fixed (omegaFixed_of_isInacc hi)) hπ.2.1
      om := fun _ h => by cases h
      xi := fun _ _ h => by cases h
      psi := fun _ _ _ h => by cases h; exact ⟨hψ, hπ⟩
      psi0 := fun c a' h w hw => by
        injection h with e1 e2 e3
        subst e1 e2 e3
        have ho := ihpi.om c rfl
        have hs : RTKA.isSucc c = true := by simpa [RTKA.isRegTerm] using hreg
        cases ho.2 hs with
        | intro ζ hζ =>
          have hcΛ : val.{u} c < Λ := lt_of_le_of_lt (le_Om (lt_trans _ _ _ ho.1 ihpi.lt_Λ))
            ihpi.lt_Λ
          have hrep := C_gen sp.2.2.2.1 hπ.principal (Or.inl hψ)
          have hcC := GenRep_Om hrep hcΛ ho.1
          have hζC := hζ.2 _ _ hcC
          have hsΛ : succ ζ < Λ := by rw [← hζ.1]; exact hcΛ
          have hζΛ : ζ < Λ := lt_trans _ _ _ (lt_succ_self ζ) hsΛ
          have hOπ : Om ζ < Om (val.{u} c) := by
            rw [hζ.1]
            exact Om_lt_Om (lt_succ_self ζ) hsΛ
          have hOζ := sp.2.2.1 (Om ζ) (C_Om hζΛ hζC) hOπ
          have hwζ : w ≤ ζ := by rw [hζ.1] at hw; exact le_of_lt_succ hw
          cases hwζ with
          | inl h => exact lt_trans _ _ _ (Om_lt_Om h hζΛ) hOζ
          | inr e => rw [e]; exact hOζ }

/-! ### `val` の単射性（Lemma 5.2 (iii)） -/

theorem summands_val_eq {a b : Tm} (ha : Inv.{u} a) (hb : Inv.{u} b) (e : val.{u} a = val b) :
    (RTKA.summands a).map val.{u} = (RTKA.summands b).map val := by
  have h := hb.cnf
  rw [← e] at h
  exact cnf_unique ha.cnf h

/-- 和でない項と値が等しい項は和でない -/
theorem isPrincipal_of_val_eq (hS : StationaryHyp.{u}) {a b : Tm} (ha : Good.{u} a)
    (hb : Good.{u} b) (hap : RTKA.isPrincipal a = true) (e : val.{u} a = val b) :
    RTKA.isPrincipal b = true := by
  have hs := summands_val_eq (ha.inv hS) (hb.inv hS) e
  rw [RTKA.summands_principal hap, List.map_cons, List.map_nil] at hs
  cases hb with
  | zero => simp [RTKA.summands] at hs
  | plus b₁ b₂ _ _ _ hb0 _ =>
    rw [RTKA.summands_plus, List.map_cons] at hs
    have h2 := (List.cons.inj hs).2
    exact absurd (summands_eq_nil.mp (List.map_eq_nil_iff.mp h2.symm)) hb0
  | _ => simp [RTKA.isPrincipal]

/-- `Good` な項の上で `val` は単射 -/
theorem val_inj (hS : StationaryHyp.{u}) :
    ∀ (a b : Tm), Good.{u} a → Good.{u} b → val.{u} a = val b → a = b := by
  intro a
  induction a with
  | zero =>
    intro b _ hb e
    have hs := summands_val_eq (Good.zero.inv hS) (hb.inv hS) e
    simp only [RTKA.summands, List.map_nil] at hs
    exact (summands_eq_nil.mp (List.map_eq_nil_iff.mp hs.symm)).symm
  | plus a₁ a₂ ih₁ ih₂ =>
    intro b ha hb e
    have hs := summands_val_eq (ha.inv hS) (hb.inv hS) e
    by_cases hbp : RTKA.isPrincipal b = true
    · have h := isPrincipal_of_val_eq hS hb ha hbp e.symm
      simp [RTKA.isPrincipal] at h
    cases ha with
    | plus _ _ ha₁ ha₂ _ ha0 _ =>
      cases hb with
      | plus b₁ b₂ hb₁ hb₂ _ _ _ =>
        rw [RTKA.summands_plus, RTKA.summands_plus, List.map_cons, List.map_cons] at hs
        have e₁ := (List.cons.inj hs).1
        have e₂ : val.{u} a₂ = val b₂ := by
          rw [(ha₂.inv hS).cnf.eq, (hb₂.inv hS).cnf.eq, (List.cons.inj hs).2]
        rw [ih₁ b₁ ha₁ hb₁ e₁, ih₂ b₂ ha₂ hb₂ e₂]
      | zero => simp [RTKA.summands] at hs
      | _ => simp [RTKA.isPrincipal] at hbp
  | one =>
    intro b ha hb e
    have hbp := isPrincipal_of_val_eq hS ha hb rfl e
    have ib := hb.inv hS
    cases hb with
    | one => rfl
    | kc m hm => exact absurd e (ne_of_lt (one_lt_of_R (R_K hm)))
    | om c _ _ hlt => exact absurd e.symm (Om_ne_one hlt)
    | xi m c _ _ _ _ _ =>
      have hx := ib.xi m c rfl
      exact absurd e.symm (Xi_ne_one hx.1 hx.2.2.2)
    | psi ξ π β _ _ _ _ _ _ _ _ _ _ _ _ =>
      have hp := ib.psi ξ π β rfl
      exact absurd e.symm (Psi_ne_one hp.1 hp.2.1)
    | _ => simp [RTKA.isPrincipal] at hbp
  | K n =>
    intro b ha hb e
    have hbp := isPrincipal_of_val_eq hS ha hb rfl e
    have ib := hb.inv hS
    cases ha with
    | kc _ hn =>
      cases hb with
      | one => exact absurd e.symm (ne_of_lt (one_lt_of_R (R_K hn)))
      | kc m _ => rw [K_inj e]
      | om c hc _ hlt => exact absurd e.symm (Om_ne_K (hc.inv hS).lt_Λ hlt)
      | xi m c _ _ _ _ _ => exact absurd e.symm (Xi_ne_K (ib.xi m c rfl).2.2.2)
      | psi ξ π β _ _ _ _ _ _ _ _ _ _ _ _ => exact absurd e.symm (Psi_ne_K (ib.psi ξ π β rfl).1)
      | _ => simp [RTKA.isPrincipal] at hbp
  | Om a ih =>
    intro b ha hb e
    have hbp := isPrincipal_of_val_eq hS ha hb rfl e
    have ib := hb.inv hS
    cases ha with
    | om _ ha' _ hlt =>
      have hΛ := (ha'.inv hS).lt_Λ
      cases hb with
      | one => exact absurd e (Om_ne_one hlt)
      | kc m _ => exact absurd e (Om_ne_K hΛ hlt)
      | om c hc _ _ => rw [ih c ha' hc (Om_inj hΛ (hc.inv hS).lt_Λ e)]
      | xi m c _ _ _ _ _ =>
        have hx := ib.xi m c rfl
        exact absurd e (Om_ne_Xi hΛ hlt hx.1 hx.2.2.2)
      | psi ξ π β _ _ _ _ _ _ _ _ _ _ _ _ => exact absurd e (Om_ne_Psi hΛ hlt (ib.psi ξ π β rfl).1)
      | _ => simp [RTKA.isPrincipal] at hbp
  | Xi n a ih =>
    intro b ha hb e
    have hbp := isPrincipal_of_val_eq hS ha hb rfl e
    have ia := ha.inv hS
    have ib := hb.inv hS
    have hx := ia.xi n a rfl
    cases ha with
    | xi _ _ _ ha' _ _ _ =>
      cases hb with
      | one => exact absurd e (Xi_ne_one hx.1 hx.2.2.2)
      | kc m _ => exact absurd e (Xi_ne_K hx.2.2.2)
      | om c hc _ hlt => exact absurd e.symm (Om_ne_Xi (hc.inv hS).lt_Λ hlt hx.1 hx.2.2.2)
      | xi m c _ hc _ _ _ =>
        have hy := ib.xi m c rfl
        have h := Xi_inj' hx.1 hy.1 hx.2.2.2 hy.2.2.2 e
        rw [h.1, ih c ha' hc h.2]
      | psi ξ π β _ _ _ _ _ _ _ _ _ _ _ _ =>
        have hp := ib.psi ξ π β rfl
        exact absurd e.symm (Xi_ne_Psi hx.1 hx.2.2.2 hp.1 hp.2)
      | _ => simp [RTKA.isPrincipal] at hbp
  | Psi xi pi a ihxi ihpi iha =>
    intro b ha hb e
    have hbp := isPrincipal_of_val_eq hS ha hb rfl e
    have ia := ha.inv hS
    have ib := hb.inv hS
    have hp := ia.psi xi pi a rfl
    cases ha with
    | psi _ _ _ _ hxi hpi ha' _ _ _ _ _ _ _ _ =>
      cases hb with
      | one => exact absurd e (Psi_ne_one hp.1 hp.2.1)
      | kc m _ => exact absurd e (Psi_ne_K hp.1)
      | om c hc _ hlt => exact absurd e.symm (Om_ne_Psi (hc.inv hS).lt_Λ hlt hp.1)
      | xi m c _ _ _ _ _ =>
        have hy := ib.xi m c rfl
        exact absurd e (Xi_ne_Psi hy.1 hy.2.2.2 hp.1 hp.2)
      | psi ξ π β _ hξ hπ hβ _ _ _ _ _ _ _ _ =>
        have hq := ib.psi ξ π β rfl
        have h := Psi_inj hp.1 hq.1 hp.2 hq.2 e
        rw [ihxi ξ hxi hξ h.1, ihpi π hpi hπ h.2.1, iha β ha' hβ h.2.2]
      | _ => simp [RTKA.isPrincipal] at hbp

end

/-! ## `cmp`・`inC` の正しさ（Rathjen Lemma 5.4、Prop. 4.20・4.21 などを `T⁺` の比較の各節に当てはめる）。

`Good` な項について、`RTKA.cmp a b = ocmp (val a) (val b)` と
`RTKA.inC a g d = true ↔ val a ∈ C(val g, val d)` を、`cmp`・`inC` の停止性の測度
（`8 ·（大きさの和）+ 段`）についての帰納法で同時に示す（`CmpOK`）。 -/

noncomputable section

open RTKA (Tm)

/-! ### 順序数の比較 -/

open Classical in
/-- 順序数の比較 -/
def ocmp (x y : Ordinal.{u}) : Ordering :=
  if x < y then .lt else if x = y then .eq else .gt

theorem ocmp_of_lt {x y : Ordinal.{u}} (h : x < y) : ocmp x y = .lt := by
  unfold ocmp; simp [h]

theorem ocmp_of_eq {x y : Ordinal.{u}} (h : x = y) : ocmp x y = .eq := by
  unfold ocmp; subst h; simp [lt_irrefl]

theorem ocmp_of_gt {x y : Ordinal.{u}} (h : y < x) : ocmp x y = .gt := by
  unfold ocmp; simp [lt_asymm h, ne_of_gt h]

theorem ocmp_eq_lt_iff {x y : Ordinal.{u}} : ocmp x y = .lt ↔ x < y := by
  rcases lt_total x y with h | h | h
  · simp [ocmp_of_lt h, h]
  · subst h; simp [ocmp_of_eq rfl, lt_irrefl]
  · simp [ocmp_of_gt h, lt_asymm h]

theorem ocmp_eq_eq_iff {x y : Ordinal.{u}} : ocmp x y = .eq ↔ x = y := by
  rcases lt_total x y with h | h | h
  · simp [ocmp_of_lt h, ne_of_lt h]
  · subst h; simp [ocmp_of_eq rfl]
  · simp [ocmp_of_gt h, ne_of_gt h]

theorem ocmp_eq_gt_iff {x y : Ordinal.{u}} : ocmp x y = .gt ↔ y < x := by
  rcases lt_total x y with h | h | h
  · simp [ocmp_of_lt h, lt_asymm h]
  · subst h; simp [ocmp_of_eq rfl, lt_irrefl]
  · simp [ocmp_of_gt h, h]

theorem ocmp_swap (x y : Ordinal.{u}) : (ocmp x y).swap = ocmp y x := by
  rcases lt_total x y with h | h | h
  · rw [ocmp_of_lt h, ocmp_of_gt h]; rfl
  · subst h; rw [ocmp_of_eq rfl]; rfl
  · rw [ocmp_of_gt h, ocmp_of_lt h]; rfl

/-- 大小が同じなら比較も同じ -/
theorem ocmp_congr {x y x' y' : Ordinal.{u}} (h1 : x < y ↔ x' < y') (h2 : y < x ↔ y' < x') :
    ocmp x y = ocmp x' y' := by
  rcases lt_total x y with h | h | h
  · rw [ocmp_of_lt h, ocmp_of_lt (h1.mp h)]
  · subst h
    rw [ocmp_of_eq rfl]
    rcases lt_total x' y' with h' | h' | h'
    · exact absurd (h1.mpr h') (lt_irrefl _)
    · rw [ocmp_of_eq h']
    · exact absurd (h2.mpr h') (lt_irrefl _)
  · rw [ocmp_of_gt h, ocmp_of_gt (h2.mp h)]

theorem ocmp_add_left (a x y : Ordinal.{u}) : ocmp (a + x) (a + y) = ocmp x y :=
  ocmp_congr (add_lt_add_iff_right a) (add_lt_add_iff_right a)

variable [Setting.{u}]

theorem ocmp_Om {x y : Ordinal.{u}} (hx : x < Λ) (hy : y < Λ) : ocmp (Om x) (Om y) = ocmp x y :=
  ocmp_congr (Om_lt_Om_iff hx hy) (Om_lt_Om_iff hy hx)

theorem Om_le_Om {x y : Ordinal.{u}} (h : x ≤ y) (hy : y < Λ) : Om x ≤ Om y := by
  cases h with
  | inl h => exact Or.inl (Om_lt_Om h hy)
  | inr e => rw [e]; exact le_refl _

omit [Setting] in
theorem bnot_iff {b : Bool} {P : Prop} (h : b = true ↔ P) : (!b) = true ↔ ¬ P := by
  cases b <;> simp_all

/-! ### 和の項 -/

theorem summands_good : ∀ (t : Tm), Good.{u} t →
    ∀ s, s ∈ RTKA.summands t → Good.{u} s ∧ RTKA.isPrincipal s = true := by
  intro t
  induction t with
  | zero => intro _ s hs; simp [RTKA.summands] at hs
  | plus a b _ ihb =>
    intro h s hs
    cases h with
    | plus _ _ ha hb hap _ _ =>
      rw [RTKA.summands_plus] at hs
      cases List.mem_cons.mp hs with
      | inl e => rw [e]; exact ⟨ha, hap⟩
      | inr hs => exact ihb hb s hs
  | _ =>
    intro h s hs
    simp only [RTKA.summands, List.mem_singleton] at hs
    rw [hs]
    exact ⟨h, rfl⟩

/-! ### 帰納法の仮定 -/

/-- 測度 `N` 未満の `cmp`・`inC` の呼び出しが正しい -/
def CmpOK (N : Nat) : Prop :=
  (∀ a b : Tm, 8 * (a.size + b.size) + 3 < N → Good.{u} a → Good.{u} b →
    RTKA.cmp a b = ocmp (val.{u} a) (val b)) ∧
  (∀ a g d : Tm, 8 * (a.size + g.size) + 5 < N → 8 * (a.size + d.size) + 5 < N →
    Good.{u} a → Good.{u} g → Good.{u} d →
    (RTKA.inC a g d = true ↔ C (val.{u} g) (val d) (val a)))

/-! ### `inC`（Lemma 5.4） -/

theorem inC_ok (hS : StationaryHyp.{u}) {N : Nat} (hN : CmpOK.{u} N) {a g d : Tm}
    (hm1 : 8 * (a.size + g.size) + 5 ≤ N) (hm2 : 8 * (a.size + d.size) + 5 ≤ N)
    (ha : Good.{u} a) (hg : Good.{u} g) (hd : Good.{u} d) :
    RTKA.inC a g d = true ↔ C (val.{u} g) (val d) (val a) := by
  have ia := ha.inv hS
  have ha' := ha
  cases ha with
  | zero => rw [RTKA.inC]; exact ⟨fun _ => C_zero _ _, fun _ => rfl⟩
  | one => rw [RTKA.inC]; exact ⟨fun _ => C_one _ _, fun _ => rfl⟩
  | kc n _ => rw [RTKA.inC]; exact ⟨fun _ => C_K _ _ n, fun _ => rfl⟩
  | plus x y hx hy _ _ _ =>
    simp only [RTKA.Tm.size] at hm1 hm2
    rw [RTKA.inC, Bool.and_eq_true, hN.2 x g d (by omega) (by omega) hx hg hd,
      hN.2 y g d (by omega) (by omega) hy hg hd]
    have hc := ia.cnf
    rw [RTKA.summands_plus, List.map_cons] at hc
    show _ ↔ C _ _ (val x + val y)
    apply Iff.intro
    · intro h; exact C_add h.1 h.2
    · intro h
      have hall := (C_iff_cnf hc).mp h
      refine And.intro (hall _ List.mem_cons_self) ?_
      exact (C_iff_cnf (hy.inv hS).cnf).mpr (fun p hp => hall p (List.mem_cons_of_mem _ hp))
  | om x hx _ hlt =>
    simp only [RTKA.Tm.size] at hm1 hm2
    rw [RTKA.inC, hN.2 x g d (by omega) (by omega) hx hg hd]
    have hΛ := (hx.inv hS).lt_Λ
    apply Iff.intro
    · intro h; exact C_Om hΛ h
    · intro h
      cases lt_or_le (Om (val.{u} x)) (val d) with
      | inl h' => exact C_lt (lt_of_le_of_lt (le_Om hΛ) h')
      | inr h' => exact GenRep_Om (C_gen h (ia.principal rfl) h') hΛ hlt
  | xi n b _ hb _ _ _ =>
    simp only [RTKA.Tm.size] at hm1 hm2
    have e1 := hN.1 _ d (by simp only [RTKA.Tm.size]; omega) ha' hd
    have e2 := hN.2 b g d (by omega) (by omega) hb hg hd
    have e3 := hN.1 b g (by omega) hb hg
    rw [RTKA.inC, e1, e3]
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, ocmp_eq_lt_iff, e2]
    have hx := ia.xi n b rfl
    apply Iff.intro
    · intro h
      cases h with
      | inl h => exact C_lt h
      | inr h => exact C_Xi n hx.1 h.2 h.1
    · intro h
      cases lt_or_le (val.{u} (.Xi n b)) (val d) with
      | inl h' => exact Or.inl h'
      | inr h' =>
        have g' := GenRep_Xi (C_gen h (ia.principal rfl) h') hx.1 hx.2.2.2
        exact Or.inr ⟨g'.1, g'.2⟩
  | psi sg ka b _ hsg hka hb _ hle _ _ _ _ _ _ =>
    simp only [RTKA.Tm.size] at hm1 hm2
    have e1 := hN.1 _ d (by simp only [RTKA.Tm.size]; omega) ha' hd
    have eka := hN.2 ka g d (by omega) (by omega) hka hg hd
    have esg := hN.2 sg g d (by omega) (by omega) hsg hg hd
    have eb := hN.2 b g d (by omega) (by omega) hb hg hd
    have e3 := hN.1 b g (by omega) hb hg
    rw [RTKA.inC, e1, e3]
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, ocmp_eq_lt_iff, eka, esg, eb]
    have hp := ia.psi sg ka b rfl
    apply Iff.intro
    · intro h
      cases h with
      | inl h => exact C_lt h
      | inr h => exact C_Psi h.2 hle hp.2 h.1.1.2 h.1.1.1 h.1.2
    · intro h
      cases lt_or_le (val.{u} (.Psi sg ka b)) (val d) with
      | inl h' => exact Or.inl h'
      | inr h' =>
        have g' := GenRep_Psi (C_gen h (ia.principal rfl) h') hp.2 hp.1
        exact Or.inr ⟨⟨⟨g'.2.1, g'.1⟩, g'.2.2.1⟩, g'.2.2.2⟩

/-! ### `cmpOmX`（Lemma 4.19） -/

theorem cmpOmX_ok (hS : StationaryHyp.{u}) {N : Nat} (hN : CmpOK.{u} N) {a X : Tm}
    (hm : 8 * (a.size + X.size) + 4 ≤ N) (ha : Good.{u} a) (hX : Good.{u} X)
    (hXk : (∃ n b, X = .Xi n b) ∨ (∃ xi pi b, X = .Psi xi pi b)) :
    RTKA.cmpOmX a X = ocmp (Om (val.{u} a)) (val X) := by
  have ia := ha.inv hS
  have iX := hX.inv hS
  rw [RTKA.cmpOmX.eq_def]
  by_cases hf : RTKA.omegaFixed X = true
  · simp only [hf, ↓reduceIte]
    rw [hN.1 a X (by omega) ha hX]
    have e := ocmp_Om ia.lt_Λ iX.lt_Λ
    rw [iX.fixed hf] at e
    exact e.symm
  · simp only [hf, Bool.false_eq_true, ↓reduceIte]
    rcases hXk with ⟨n, b, rfl⟩ | ⟨xi, pi, b, rfl⟩
    · simp [RTKA.omegaFixed] at hf
    · have hf' : xi = .zero ∧ RTKA.isInacc pi = false := by simpa [RTKA.omegaFixed] using hf
      obtain ⟨rfl, hpi⟩ := hf'
      have hX' := hX
      cases hX with
      | psi _ _ _ _ _ hpi' _ hreg _ _ _ _ _ _ _ =>
        cases pi with
        | Om c =>
          cases hpi' with
          | om _ hc _ _ =>
            dsimp only
            simp only [RTKA.Tm.size] at hm
            rw [hN.1 a c (by omega) ha hc]
            have hp := iX.psi .zero (.Om c) b rfl
            split
            · rename_i h
              exact (ocmp_of_lt (iX.psi0 c b rfl _ (ocmp_eq_lt_iff.mp (beq_iff_eq.mp h)))).symm
            · rename_i h
              have hca : val.{u} c ≤ val a :=
                le_of_not_lt (fun h' => h (beq_iff_eq.mpr (ocmp_of_lt h')))
              exact (ocmp_of_gt (lt_of_lt_of_le hp.1 (Om_le_Om hca ia.lt_Λ))).symm
        | Xi _ _ => simp [RTKA.isInacc] at hpi
        | Psi _ _ _ => simp [RTKA.isInacc, RTKA.isRegTerm] at hpi hreg; exact absurd hpi hreg
        | _ => simp [RTKA.isRegTerm] at hreg

/-! ### `xiLtXi`（Lemma 4.14） -/

theorem xiLtXi_ok (hS : StationaryHyp.{u}) {N : Nat} (hN : CmpOK.{u} N) {n : Nat} {a b : Tm}
    (hm : 8 * (a.size + b.size + 2) ≤ N) (ha : Good.{u} (.Xi n a)) (hb : Good.{u} (.Xi n b)) :
    RTKA.xiLtXi (.Xi n a) (.Xi n b) = true ↔ val.{u} (.Xi n a) < val (.Xi n b) := by
  have hxa := (ha.inv hS).xi n a rfl
  have hxb := (hb.inv hS).xi n b rfl
  have ha' := ha
  have hb' := hb
  cases ha with
  | xi _ _ _ ha _ _ _ =>
    cases hb with
    | xi _ _ _ hb _ _ _ =>
      have e2 := hN.2 a b (.Xi n b) (by omega) (by simp only [RTKA.Tm.size]; omega) ha hb hb'
      have e4 := hN.2 b a (.Xi n a) (by omega) (by simp only [RTKA.Tm.size]; omega) hb ha ha'
      rw [RTKA.xiLtXi, hN.1 a b (by omega) ha hb, hN.1 b a (by omega) hb ha]
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, ocmp_eq_lt_iff, e2, bnot_iff e4]
      exact (Xi_lt_Xi_iff hxa.1 hxb.1 hxa.2 hxb.2).symm

/-! ### `psiLtXi`（Prop. 4.21） -/

theorem psiLtXi_ok (hS : StationaryHyp.{u}) {N : Nat} (hN : CmpOK.{u} N) {xi pi a b : Tm}
    {m : Nat} (hm : 8 * (xi.size + pi.size + a.size + b.size + 2) ≤ N)
    (hx : Good.{u} (.Psi xi pi a)) (hy : Good.{u} (.Xi m b)) (hlev : RTKA.lev pi = m) :
    RTKA.psiLtXi (.Psi xi pi a) (.Xi m b) = true ↔ val.{u} (.Psi xi pi a) < val (.Xi m b) := by
  have hp := (hx.inv hS).psi xi pi a rfl
  have hxb := (hy.inv hS).xi m b rfl
  have hx' := hx
  have hy' := hy
  cases hx with
  | psi _ _ _ _ _ hpi ha hreg _ _ _ _ _ _ _ =>
    cases hy with
    | xi _ _ _ hb _ _ _ =>
      have hπK : val.{u} pi < K m := by
        rw [← hlev]; exact ((hpi.inv hS).bounds (ne_zero_of_isRegTerm hreg)).2.2
      have e3 := hN.2 b a (.Psi xi pi a) (by omega) (by simp only [RTKA.Tm.size]; omega) hb ha hx'
      rw [RTKA.psiLtXi, hN.1 pi _ (by simp only [RTKA.Tm.size]; omega) hpi hy',
        hN.1 b a (by omega) hb ha]
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, ocmp_eq_lt_iff,
        ocmp_eq_gt_iff, bnot_iff e3]
      rw [not_lt_iff_le]
      exact (Psi_lt_Xi_iff hxb.1 hxb.2 hp.1 hπK).symm

/-! ### `cmpPsi`（Prop. 4.17・4.20） -/

theorem cmpPsi_ok (hS : StationaryHyp.{u}) {N : Nat} (hN : CmpOK.{u} N) {xi pi a sg ka b : Tm}
    (hm : 8 * (xi.size + pi.size + a.size + sg.size + ka.size + b.size + 2) ≤ N)
    (hx : Good.{u} (.Psi xi pi a)) (hy : Good.{u} (.Psi sg ka b)) :
    RTKA.cmpPsi (.Psi xi pi a) (.Psi sg ka b) = ocmp (val.{u} (.Psi xi pi a)) (val (.Psi sg ka b)) := by
  have px := (hx.inv hS).psi xi pi a rfl
  have py := (hy.inv hS).psi sg ka b rfl
  have hx' := hx
  have hy' := hy
  cases hx with
  | psi _ _ _ _ hxi hpi ha _ _ _ _ _ _ _ _ =>
    cases hy with
    | psi _ _ _ _ hsg hka hb _ _ _ _ _ _ _ _ =>
      rw [RTKA.cmpPsi]
      split
      · rename_i h
        rw [beq_iff_eq.mp h]
        exact (ocmp_of_eq rfl).symm
      rename_i hne
      have hne' : val.{u} (.Psi xi pi a) ≠ val (.Psi sg ka b) := fun e =>
        hne (beq_iff_eq.mpr (val_inj hS _ _ hx' hy' e))
      rw [hN.1 _ pi (by simp only [RTKA.Tm.size]; omega) hy' hpi]
      split
      · rename_i h
        have h' : val.{u} pi ≤ val (.Psi sg ka b) :=
          le_of_not_lt (fun h' => (bne_iff_ne.mp h) (ocmp_of_lt h'))
        exact (ocmp_of_lt (lt_of_lt_of_le px.1 h')).symm
      rename_i hyπ
      have hyπ' : val.{u} (.Psi sg ka b) < val pi := by
        simp only [bne_iff_ne, ne_eq, ocmp_eq_lt_iff] at hyπ
        exact Classical.not_not.mp hyπ
      rw [hN.1 _ ka (by simp only [RTKA.Tm.size]; omega) hx' hka]
      split
      · rename_i h
        have h' : val.{u} ka ≤ val (.Psi xi pi a) :=
          le_of_not_lt (fun h' => (bne_iff_ne.mp h) (ocmp_of_lt h'))
        exact (ocmp_of_gt (lt_of_lt_of_le py.1 h')).symm
      rename_i hxκ
      have hxκ' : val.{u} (.Psi xi pi a) < val ka := by
        simp only [bne_iff_ne, ne_eq, ocmp_eq_lt_iff] at hxκ
        exact Classical.not_not.mp hxκ
      have key := Psi_lt_Psi_iff px.2 py.2 px.1 py.1 hyπ' hxκ'
      have e_ab := hN.1 a b (by omega) ha hb
      have e_ba := hN.1 b a (by omega) hb ha
      have e_xs := hN.1 xi sg (by omega) hxi hsg
      have e_sx := hN.1 sg xi (by omega) hsg hxi
      have i1 := hN.2 a b _ (by omega) (by simp only [RTKA.Tm.size]; omega) ha hb hy'
      have i2 := hN.2 xi b _ (by omega) (by simp only [RTKA.Tm.size]; omega) hxi hb hy'
      have i3 := hN.2 pi b _ (by omega) (by simp only [RTKA.Tm.size]; omega) hpi hb hy'
      have i4 := hN.2 b a _ (by omega) (by simp only [RTKA.Tm.size]; omega) hb ha hx'
      have i5 := hN.2 sg a _ (by omega) (by simp only [RTKA.Tm.size]; omega) hsg ha hx'
      have i6 := hN.2 ka a _ (by omega) (by simp only [RTKA.Tm.size]; omega) hka ha hx'
      have i7 := hN.2 sg xi _ (by omega) (by simp only [RTKA.Tm.size]; omega) hsg hxi hx'
      have i456 : (RTKA.inC b a (.Psi xi pi a) && RTKA.inC sg a (.Psi xi pi a) &&
          RTKA.inC ka a (.Psi xi pi a)) = true ↔
          (C (val.{u} a) (val (.Psi xi pi a)) (val b) ∧ C (val a) (val (.Psi xi pi a)) (val sg) ∧
            C (val a) (val (.Psi xi pi a)) (val ka)) := by
        rw [Bool.and_eq_true, Bool.and_eq_true, i4, i5, i6, and_assoc]
      have hkp : ka = pi ↔ val.{u} ka = val pi :=
        ⟨fun e => by rw [e], fun e => val_inj hS _ _ hka hpi e⟩
      rw [e_ab, e_ba, e_xs, e_sx]
      dsimp only
      split
      · rename_i hc
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
          ocmp_eq_lt_iff, ocmp_eq_gt_iff, ocmp_eq_eq_iff, i1, i2, i3, bnot_iff i456, bnot_iff i7,
          hkp] at hc
        apply Eq.symm
        apply ocmp_of_lt
        apply key.mpr
        rcases hc with ((h | h) | h) | h
        · exact Or.inl ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2⟩
        · exact Or.inr (Or.inl ⟨le_of_not_lt h.1, h.2⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩))
        · exact Or.inr (Or.inr (Or.inr h))
      · rename_i hc
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
          ocmp_eq_lt_iff, ocmp_eq_gt_iff, ocmp_eq_eq_iff, i1, i2, i3, bnot_iff i456, bnot_iff i7,
          hkp, not_or] at hc
        apply Eq.symm
        apply ocmp_of_gt
        have hnlt : ¬ val.{u} (.Psi xi pi a) < val (.Psi sg ka b) := by
          intro hlt
          rcases key.mp hlt with h | h | h | h
          · exact hc.1.1.1 ⟨⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩, hxκ'⟩
          · exact hc.1.1.2 ⟨not_lt_of_le h.1, h.2⟩
          · exact hc.1.2 ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩
          · exact hc.2 h
        rcases lt_total (val.{u} (.Psi xi pi a)) (val (.Psi sg ka b)) with h | h | h
        · exact absurd h hnlt
        · exact absurd h hne'
        · exact h

/-! ### `cmpP`：和でない項どうしの比較 -/

theorem cmpP_ok (hS : StationaryHyp.{u}) {N : Nat} (hN : CmpOK.{u} N) {x y : Tm}
    (hm : 8 * (x.size + y.size) + 1 ≤ N) (hx : Good.{u} x) (hy : Good.{u} y)
    (hxp : RTKA.isPrincipal x = true) (hyp : RTKA.isPrincipal y = true) :
    RTKA.cmpP x y = ocmp (val.{u} x) (val y) := by
  have ix := hx.inv hS
  have iy := hy.inv hS
  have bx := ix.bounds (ne_zero_of_isPrincipal hxp)
  have bY := iy.bounds (ne_zero_of_isPrincipal hyp)
  rw [RTKA.cmpP.eq_def]
  by_cases hl : RTKA.lev x < RTKA.lev y
  · simp only [hl, ↓reduceIte]
    exact (ocmp_of_lt (lt_of_lt_of_le bx.2.2 (le_trans (K_le (by omega)) bY.2.1))).symm
  by_cases hl' : RTKA.lev y < RTKA.lev x
  · simp only [hl, hl', ↓reduceIte]
    exact (ocmp_of_gt (lt_of_lt_of_le bY.2.2 (le_trans (K_le (by omega)) bx.2.1))).symm
  simp only [hl, hl', ↓reduceIte]
  have hlev : RTKA.lev x = RTKA.lev y := by omega
  -- `K_{lev - 1}` との比較
  have kx : ∀ n, RTKA.lev x = n + 1 → (∀ m, x ≠ .K m) → K n < val.{u} x := by
    intro n hn hK
    have h := ix.strict hxp hK
    rw [hn, Nat.add_sub_cancel] at h
    exact h
  have ky : ∀ n, RTKA.lev y = n + 1 → (∀ m, y ≠ .K m) → K n < val.{u} y := by
    intro n hn hK
    have h := iy.strict hyp hK
    rw [hn, Nat.add_sub_cancel] at h
    exact h
  have hx' := hx
  have hy' := hy
  cases hx with
  | zero => simp [RTKA.isPrincipal] at hxp
  | plus => simp [RTKA.isPrincipal] at hxp
  | one =>
    cases hy with
    | zero => simp [RTKA.isPrincipal] at hyp
    | plus => simp [RTKA.isPrincipal] at hyp
    | one => exact (ocmp_of_eq rfl).symm
    | _ => dsimp only; exact (ocmp_of_lt (iy.one_lt rfl (by intro h; cases h))).symm
  | kc n hn =>
    cases hy with
    | zero => simp [RTKA.isPrincipal] at hyp
    | plus => simp [RTKA.isPrincipal] at hyp
    | one => dsimp only; exact (ocmp_of_gt (ix.one_lt rfl (by intro h; cases h))).symm
    | kc m _ =>
      dsimp only
      simp only [RTKA.lev] at hlev
      have e : n = m := by omega
      subst e
      exact (ocmp_of_eq rfl).symm
    | om b _ _ _ =>
      dsimp only
      have hK := ky n (by simp only [RTKA.lev] at hlev ⊢; omega) (fun _ h => by cases h)
      have hne : ¬ (b == Tm.K n) = true := by
        rw [beq_iff_eq]
        intro e
        subst e
        have h := hK
        rw [show val.{u} (Tm.Om (Tm.K n)) = Om (K n) from rfl, Om_K hn] at h
        exact lt_irrefl _ h
      simp only [hne]
      exact (ocmp_of_lt hK).symm
    | xi m c _ _ _ _ _ =>
      dsimp only
      exact (ocmp_of_lt (ky n (by simp only [RTKA.lev] at hlev ⊢; omega)
        (fun _ h => by cases h))).symm
    | psi _ pi _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      dsimp only
      exact (ocmp_of_lt (ky n (by simp only [RTKA.lev] at hlev ⊢; omega)
        (fun _ h => by cases h))).symm
  | om a ha _ _ =>
    cases hy with
    | zero => simp [RTKA.isPrincipal] at hyp
    | plus => simp [RTKA.isPrincipal] at hyp
    | one => dsimp only; exact (ocmp_of_gt (ix.one_lt rfl (by intro h; cases h))).symm
    | kc m hm' =>
      dsimp only
      have hK := kx m (by simp only [RTKA.lev] at hlev ⊢; omega) (fun _ h => by cases h)
      have hne : ¬ (a == Tm.K m) = true := by
        rw [beq_iff_eq]
        intro e
        subst e
        have h := hK
        rw [show val.{u} (Tm.Om (Tm.K m)) = Om (K m) from rfl, Om_K hm'] at h
        exact lt_irrefl _ h
      simp only [hne]
      exact (ocmp_of_gt hK).symm
    | om b hb _ _ =>
      dsimp only
      simp only [RTKA.Tm.size] at hm
      rw [hN.1 a b (by omega) ha hb]
      exact (ocmp_Om (ha.inv hS).lt_Λ (hb.inv hS).lt_Λ).symm
    | xi m c _ _ _ _ _ =>
      dsimp only
      simp only [RTKA.Tm.size] at hm
      exact cmpOmX_ok hS hN (by simp only [RTKA.Tm.size]; omega) ha hy' (Or.inl ⟨m, c, rfl⟩)
    | psi sg ka c _ _ _ _ _ _ _ _ _ _ _ _ =>
      dsimp only
      simp only [RTKA.Tm.size] at hm
      exact cmpOmX_ok hS hN (by simp only [RTKA.Tm.size]; omega) ha hy'
        (Or.inr ⟨sg, ka, c, rfl⟩)
  | xi n a _ ha _ _ _ =>
    have hxa := ix.xi n a rfl
    cases hy with
    | zero => simp [RTKA.isPrincipal] at hyp
    | plus => simp [RTKA.isPrincipal] at hyp
    | one => dsimp only; exact (ocmp_of_gt (ix.one_lt rfl (by intro h; cases h))).symm
    | kc m _ =>
      dsimp only
      exact (ocmp_of_gt (kx m (by simp only [RTKA.lev] at hlev ⊢; omega)
        (fun _ h => by cases h))).symm
    | om b hb _ _ =>
      dsimp only
      simp only [RTKA.Tm.size] at hm
      rw [cmpOmX_ok hS hN (by simp only [RTKA.Tm.size]; omega) hb hx' (Or.inl ⟨n, a, rfl⟩),
        ocmp_swap]
      rfl
    | xi m b _ hb _ _ _ =>
      dsimp only
      simp only [RTKA.lev] at hlev
      subst hlev
      have hxb := iy.xi n b rfl
      by_cases hab : a = b
      · subst hab
        simp only [beq_self_eq_true, ↓reduceIte]
        exact (ocmp_of_eq rfl).symm
      · have hab' : ¬ (a == b) = true := by rw [beq_iff_eq]; exact hab
        simp only [hab', Bool.false_eq_true, ↓reduceIte]
        have hiff := xiLtXi_ok hS hN (by simp only [RTKA.Tm.size] at hm; omega) hx' hy'
        split
        · rename_i h
          exact (ocmp_of_lt (hiff.mp h)).symm
        · rename_i h
          apply Eq.symm
          apply ocmp_of_gt
          have hne : val.{u} (.Xi n a) ≠ val (.Xi n b) := fun e =>
            hab (val_inj hS _ _ ha hb (Xi_inj hxa.1 hxb.1 hxa.2 hxb.2 e))
          rcases lt_total (val.{u} (.Xi n a)) (val (.Xi n b)) with h' | h' | h'
          · exact absurd (hiff.mpr h') h
          · exact absurd h' hne
          · exact h'
    | psi xi pi c _ _ _ _ _ _ _ _ _ _ _ _ =>
      dsimp only
      simp only [RTKA.lev] at hlev
      have hp := iy.psi xi pi c rfl
      have hiff := psiLtXi_ok hS hN (by simp only [RTKA.Tm.size] at hm; omega) hy' hx' hlev.symm
      split
      · rename_i h
        exact (ocmp_of_gt (hiff.mp h)).symm
      · rename_i h
        apply Eq.symm
        apply ocmp_of_lt
        have hne : val.{u} (.Psi xi pi c) ≠ val (.Xi n a) := Xi_ne_Psi hxa.1 hxa.2.2.2 hp.1 hp.2
        rcases lt_total (val.{u} (.Psi xi pi c)) (val (.Xi n a)) with h' | h' | h'
        · exact absurd (hiff.mpr h') h
        · exact absurd h' hne
        · exact h'
  | psi xi pi a _ _ _ _ _ _ _ _ _ _ _ _ =>
    have hp := ix.psi xi pi a rfl
    cases hy with
    | zero => simp [RTKA.isPrincipal] at hyp
    | plus => simp [RTKA.isPrincipal] at hyp
    | one => dsimp only; exact (ocmp_of_gt (ix.one_lt rfl (by intro h; cases h))).symm
    | kc m _ =>
      dsimp only
      exact (ocmp_of_gt (kx m (by simp only [RTKA.lev] at hlev ⊢; omega)
        (fun _ h => by cases h))).symm
    | om b hb _ _ =>
      dsimp only
      simp only [RTKA.Tm.size] at hm
      rw [cmpOmX_ok hS hN (by simp only [RTKA.Tm.size]; omega) hb hx' (Or.inr ⟨xi, pi, a, rfl⟩),
        ocmp_swap]
      rfl
    | xi m b _ _ _ _ _ =>
      dsimp only
      simp only [RTKA.lev] at hlev
      have hxb := iy.xi m b rfl
      have hiff := psiLtXi_ok hS hN (by simp only [RTKA.Tm.size] at hm; omega) hx' hy' hlev
      split
      · rename_i h
        exact (ocmp_of_lt (hiff.mp h)).symm
      · rename_i h
        apply Eq.symm
        apply ocmp_of_gt
        have hne : val.{u} (.Psi xi pi a) ≠ val (.Xi m b) := Xi_ne_Psi hxb.1 hxb.2.2.2 hp.1 hp.2
        rcases lt_total (val.{u} (.Psi xi pi a)) (val (.Xi m b)) with h' | h' | h'
        · exact absurd (hiff.mpr h') h
        · exact absurd h' hne
        · exact h'
    | psi sg ka b _ _ _ _ _ _ _ _ _ _ _ _ =>
      dsimp only
      exact cmpPsi_ok hS hN (by simp only [RTKA.Tm.size] at hm; omega) hx' hy'

/-! ### 和の比較（辞書式） -/

theorem cmpList_ok (hS : StationaryHyp.{u}) {N : Nat} (hN : CmpOK.{u} N) :
    ∀ (xs ys : List Tm), 8 * (RTKA.lsize xs + RTKA.lsize ys) + 2 ≤ N →
    (∀ t, t ∈ xs → Good.{u} t ∧ RTKA.isPrincipal t = true) →
    (∀ t, t ∈ ys → Good.{u} t ∧ RTKA.isPrincipal t = true) →
    CNF (listSum (xs.map val.{u})) (xs.map val) → CNF (listSum (ys.map val.{u})) (ys.map val) →
    RTKA.cmpList xs ys = ocmp (listSum (xs.map val.{u})) (listSum (ys.map val)) := by
  intro xs
  induction xs with
  | nil =>
    intro ys _ _ _ _ hy
    cases ys with
    | nil => rw [RTKA.cmpList]; exact (ocmp_of_eq rfl).symm
    | cons y ys =>
      rw [RTKA.cmpList]
      rw [List.map_cons] at hy
      exact (ocmp_of_lt hy.pos).symm
  | cons x xs ih =>
    intro ys hm hxs hys hx hy
    cases ys with
    | nil =>
      rw [RTKA.cmpList]
      rw [List.map_cons] at hx
      exact (ocmp_of_gt hx.pos).symm
    | cons y ys =>
      simp only [RTKA.lsize] at hm
      have hx0 := hxs x List.mem_cons_self
      have hy0 := hys y List.mem_cons_self
      rw [RTKA.cmpList, cmpP_ok hS hN (by omega) hx0.1 hy0.1 hx0.2 hy0.2]
      simp only [List.map_cons] at hx hy ⊢
      rcases lt_total (val.{u} x) (val y) with h | h | h
      · rw [ocmp_of_lt h]
        exact (ocmp_of_lt (lt_of_lt_of_le (hx.lt_of_head_lt ((hy0.1.inv hS).principal hy0.2) h)
          hy.head_le)).symm
      · rw [ocmp_of_eq h]
        dsimp only
        rw [ih ys (by omega) (fun t ht => hxs t (List.mem_cons_of_mem _ ht))
          (fun t ht => hys t (List.mem_cons_of_mem _ ht)) hx.tail hy.tail,
          listSum_cons, listSum_cons, h, ocmp_add_left]
      · rw [ocmp_of_gt h]
        exact (ocmp_of_gt (lt_of_lt_of_le (hy.lt_of_head_lt ((hx0.1.inv hS).principal hx0.2) h)
          hx.head_le)).symm

theorem cmp_ok (hS : StationaryHyp.{u}) {N : Nat} (hN : CmpOK.{u} N) {a b : Tm}
    (hm : 8 * (a.size + b.size) + 3 ≤ N) (ha : Good.{u} a) (hb : Good.{u} b) :
    RTKA.cmp a b = ocmp (val.{u} a) (val b) := by
  have ia := ha.inv hS
  have ib := hb.inv hS
  have la := RTKA.lsize_summands_le a
  have lb := RTKA.lsize_summands_le b
  rw [RTKA.cmp, cmpList_ok hS hN _ _ (by omega) (summands_good a ha) (summands_good b hb)
    ⟨ia.cnf.1, ia.cnf.2.1, rfl⟩ ⟨ib.cnf.1, ib.cnf.2.1, rfl⟩, ← ia.cnf.eq, ← ib.cnf.eq]

/-! ### 帰納法 -/

theorem cmpOK_succ (hS : StationaryHyp.{u}) {N : Nat} (hN : CmpOK.{u} N) : CmpOK.{u} (N + 1) :=
  ⟨fun _ _ _ ha hb => cmp_ok hS hN (by omega) ha hb,
   fun _ _ _ _ _ ha hg hd => inC_ok hS hN (by omega) (by omega) ha hg hd⟩

theorem cmpOK_all (hS : StationaryHyp.{u}) : ∀ N, CmpOK.{u} N
  | 0 => ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | N + 1 => cmpOK_succ hS (cmpOK_all hS N)

/-- `Good` な項について `cmp` は値の比較と一致する -/
theorem cmp_correct (hS : StationaryHyp.{u}) {a b : Tm} (ha : Good.{u} a) (hb : Good.{u} b) :
    RTKA.cmp a b = ocmp (val.{u} a) (val b) :=
  (cmpOK_all hS _).1 a b (Nat.lt_succ_self _) ha hb

/-- `Good` な項について `inC a g d` は `val a ∈ C(val g, val d)` と一致する（Lemma 5.4） -/
theorem inC_correct (hS : StationaryHyp.{u}) {a g d : Tm} (ha : Good.{u} a) (hg : Good.{u} g)
    (hd : Good.{u} d) : RTKA.inC a g d = true ↔ C (val.{u} g) (val d) (val a) :=
  (cmpOK_all hS (8 * (a.size + g.size + d.size) + 6)).2 a g d (by omega) (by omega) ha hg hd

end

/-! ## 主定理：`StationaryHyp → CmpCorrect`。

標準形の項（`RTKA.isNF`）は `Good` で（`good_of_isNF`）、`Good` な項について `cmp` は値の比較と
一致する（`cmp_correct`）。`good_of_isNF` は項の構造についての帰納法で、`isNF` が調べる `cmp`・`inC` の
条件を、部分項について `cmp_correct`・`inC_correct` で順序数の条件に読み替える。逆向きの `isNF_of_good` と
合わせて `isNF_iff_good`。

`StationaryHyp` は `Complete.lean` で弱コンパクト基数の列から導く（`cmpCorrect_of_weaklyCompact`）。 -/

noncomputable section

open RTKA (Tm)

/-- 非可算正則基数の閉包の元は `ω` より大きい -/
theorem omega_lt_of_closure_R {ξ : Ordinal.{u}} (h : closure R ξ) : omega < ξ := by
  cases (closure_iff R ξ).mp h with
  | inl hR => exact hR.1
  | inr hlp =>
    cases hlp.2 0 hlp.1 with
    | intro ρ hρ => exact lt_trans _ _ _ hρ.1.1 hρ.2.2

variable [Setting.{u}]

/-- `K_n^+ = Ω_{K_n + 1}` は `Good` -/
theorem good_succK {n : Nat} (hn : 1 ≤ n) : Good.{u} (RTKA.succK n) := by
  have hKn : K.{u} n < K (n + 1) := K_lt (Nat.lt_succ_self n)
  have hsΛ : succ (K.{u} n) < Λ :=
    lt_trans _ _ _ ((R_K (Nat.succ_le_succ (Nat.zero_le n))).2.1.succ_lt hKn) (K_lt_Λ _)
  have hR := Om_succ_R hsΛ
  have hK : K.{u} n < Om (succ (K n)) := by
    have h := Om_lt_Om (lt_succ_self (K.{u} n)) hsΛ
    rw [Om_K hn] at h
    exact h
  apply Good.om _ (Good.plus _ _ (Good.kc n hn) Good.one rfl (by intro h; cases h) ?_)
    (by intro h; cases h)
  · show K n + succ 0 < Om (K n + succ 0)
    have h := hR.2.isPrincipal.2 _ _ hK (one_lt_of_R hR)
    rw [add_one_eq_succ] at h ⊢
    exact h
  · intro h hh
    simp only [RTKA.summands, List.head?_cons, Option.some.injEq] at hh
    subst hh
    exact Or.inl (one_lt_of_R (R_K hn))

theorem good_mOf {pi m : Tm} (h : Good.{u} pi) (hm : RTKA.mOf pi = some m) : Good.{u} m := by
  cases h with
  | om _ _ _ _ => simp [RTKA.mOf] at hm; subst hm; exact Good.one
  | xi _ _ _ ha _ _ _ => simp [RTKA.mOf] at hm; subst hm; exact ha
  | psi _ _ _ _ hxi _ _ _ _ _ _ _ _ _ _ => simp [RTKA.mOf] at hm; subst hm; exact hxi
  | _ => simp [RTKA.mOf] at hm

/-- `isNF (Ω_a)` の条件 `a < Ω_a`（`cmp` で調べる）から `val a < Ω_{val a}` -/
theorem lt_Om_of_lt (hS : StationaryHyp.{u}) {a : Tm} (ha : Good.{u} a) (ha0 : a ≠ .zero)
    (h : RTKA.lt a (.Om a) = true) : val.{u} a < Om (val a) := by
  have ia := ha.inv hS
  apply lt_of_le_of_ne (le_Om ia.lt_Λ)
  intro e
  have hfix : Om (val.{u} a) = val a := e.symm
  have hP : IsPrincipal (val.{u} a) := by
    cases Om_principal_or_zero ia.lt_Λ with
    | inl h0 => rw [hfix] at h0; exact absurd h0 (ne_of_gt (ia.pos ha0))
    | inr hp => rw [hfix] at hp; exact hp
  have hap : RTKA.isPrincipal a = true := by
    cases ha with
    | zero => exact absurd rfl ha0
    | plus a₁ a₂ _ _ _ hb0 _ =>
      have hc := ia.cnf
      rw [RTKA.summands_plus, List.map_cons] at hc
      have h2 := (List.cons.inj (cnf_of_principal hP hc)).2
      exact absurd (summands_eq_nil.mp (List.map_eq_nil_iff.mp h2)) hb0
    | _ => rfl
  -- `cmpP a (Ω_a) = .eq`
  have hcmpP : RTKA.cmpP a (.Om a) = .eq := by
    have ha' := ha
    rw [RTKA.cmpP.eq_def]
    simp only [show RTKA.lev (.Om a) = RTKA.lev a from rfl, Nat.lt_irrefl, ↓reduceIte]
    cases ha with
    | zero => simp [RTKA.isPrincipal] at hap
    | plus => simp [RTKA.isPrincipal] at hap
    | one =>
      exfalso
      cases cardSet_Om ia.lt_Λ with
      | inl h0 => rw [hfix] at h0; exact succ_ne_zero 0 h0
      | inr hc =>
        rw [hfix] at hc
        exact lt_asymm (omega_lt_of_closure_R hc) (ordNat_lt_omega 1)
    | kc m _ => simp
    | om b hb _ hlt =>
      exfalso
      have hbΛ := (hb.inv hS).lt_Λ
      have e' := Om_inj (Om_lt_Λ hbΛ) hbΛ hfix
      rw [e'] at hlt
      exact lt_irrefl _ hlt
    | xi n b _ _ _ _ _ =>
      dsimp only
      rw [cmpOmX_ok hS (cmpOK_all hS _) (Nat.le_refl _) ha' ha' (Or.inl ⟨n, b, rfl⟩), hfix,
        ocmp_of_eq rfl]
      rfl
    | psi xi pi c _ _ _ _ _ _ _ _ _ _ _ _ =>
      dsimp only
      rw [cmpOmX_ok hS (cmpOK_all hS _) (Nat.le_refl _) ha' ha' (Or.inr ⟨xi, pi, c, rfl⟩), hfix,
        ocmp_of_eq rfl]
      rfl
  unfold RTKA.lt at h
  rw [RTKA.cmp, RTKA.summands_principal hap, RTKA.summands_principal (t := .Om a) rfl, RTKA.cmpList,
    hcmpP] at h
  simp [RTKA.cmpList] at h

/-- 標準形の項は `Good` -/
theorem good_of_isNF (hS : StationaryHyp.{u}) : ∀ t : Tm, RTKA.isNF t = true → Good.{u} t := by
  intro t
  induction t with
  | zero => intro _; exact Good.zero
  | one => intro _; exact Good.one
  | K n =>
    intro h
    simp only [RTKA.isNF, decide_eq_true_eq] at h
    exact Good.kc n h
  | plus a b iha ihb =>
    intro h
    simp only [RTKA.isNF, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨⟨hap, hb0⟩, hna⟩, hnb⟩, hm⟩ := h
    have ga := iha hna
    have gb := ihb hnb
    refine Good.plus a b ga gb hap hb0 ?_
    intro hd hhd
    cases hs : RTKA.summands b with
    | nil => rw [hs] at hhd; cases hhd
    | cons h' l =>
      rw [hs] at hhd hm
      simp only [List.head?_cons, Option.some.injEq] at hhd
      subst hhd
      simp only [bne_iff_ne, ne_eq] at hm
      have gh := (summands_good b gb h' (by rw [hs]; exact List.mem_cons_self)).1
      rw [cmp_correct hS gh ga, ocmp_eq_gt_iff] at hm
      exact le_of_not_lt hm
  | Om a iha =>
    intro h
    simp only [RTKA.isNF, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hna, ha0⟩, hlt⟩ := h
    have ga := iha hna
    exact Good.om a ga ha0 (lt_Om_of_lt hS ga ha0 hlt)
  | Xi n a iha =>
    intro h
    simp only [RTKA.isNF, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hn, hna⟩, ha0⟩, hle⟩, hC⟩ := h
    have ga := iha hna
    have hle' : val.{u} a ≤ val (RTKA.succK n) := by
      rw [cmp_correct hS ga (good_succK hn), ocmp_eq_gt_iff] at hle
      exact le_of_not_lt hle
    rw [val_succK] at hle'
    exact Good.xi n a hn ga ha0 hle' ((inC_correct hS ga ga (Good.kc n hn)).mp hC)
  | Psi xi pi a ihxi ihpi iha =>
    intro h
    simp only [RTKA.isNF, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hnxi, hnpi⟩, hna⟩, hreg⟩, hle⟩, hCa⟩, hCxi⟩, hCpi⟩, hm⟩ := h
    have gxi := ihxi hnxi
    have gpi := ihpi hnpi
    have ga := iha hna
    have hle' : val.{u} xi ≤ val a := by
      rw [cmp_correct hS gxi ga, ocmp_eq_gt_iff] at hle
      exact le_of_not_lt hle
    cases hmo : RTKA.mOf pi with
    | none => rw [hmo] at hm; simp at hm
    | some m =>
      rw [hmo] at hm
      simp only [Bool.and_eq_true] at hm
      obtain ⟨hlt, hCm⟩ := hm
      have gm := good_mOf gpi hmo
      have hlt' : val.{u} xi < val m := by
        unfold RTKA.lt at hlt
        rw [cmp_correct hS gxi gm, beq_iff_eq, ocmp_eq_lt_iff] at hlt
        exact hlt
      exact Good.psi xi pi a m gxi gpi ga hreg hle' ((inC_correct hS ga ga gpi).mp hCa)
        ((inC_correct hS gxi ga gpi).mp hCxi) ((inC_correct hS gpi ga gpi).mp hCpi) hmo hlt'
        ((inC_correct hS gxi gm gpi).mp hCm)

/-- 逆向き：`Good` な項は標準形（`isNF` が調べる `cmp`・`inC` の条件を `cmp_correct`・`inC_correct` で戻す） -/
theorem isNF_of_good (hS : StationaryHyp.{u}) : ∀ t : Tm, Good.{u} t → RTKA.isNF t = true := by
  intro t ht
  induction ht with
  | zero => rfl
  | one => rfl
  | kc n hn => simp [RTKA.isNF, hn]
  | plus a b ha hb hap hb0 hle iha ihb =>
    simp only [RTKA.isNF, Bool.and_eq_true, bne_iff_ne, ne_eq]
    refine ⟨⟨⟨⟨hap, hb0⟩, iha⟩, ihb⟩, ?_⟩
    cases hs : RTKA.summands b with
    | nil => exact absurd (summands_eq_nil.mp hs) hb0
    | cons h l =>
      simp only [bne_iff_ne, ne_eq]
      have gh := (summands_good b hb h (by rw [hs]; exact List.mem_cons_self)).1
      rw [cmp_correct hS gh ha, ocmp_eq_gt_iff]
      exact not_lt_of_le (hle h (by rw [hs]; rfl))
  | om a ha ha0 hlt iha =>
    simp only [RTKA.isNF, Bool.and_eq_true, bne_iff_ne, ne_eq]
    refine ⟨⟨iha, ha0⟩, ?_⟩
    unfold RTKA.lt
    rw [cmp_correct hS ha (Good.om a ha ha0 hlt), beq_iff_eq, ocmp_eq_lt_iff]
    exact hlt
  | xi n a hn ha ha0 hle hC iha =>
    simp only [RTKA.isNF, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    refine ⟨⟨⟨⟨hn, iha⟩, ha0⟩, ?_⟩, (inC_correct hS ha ha (Good.kc n hn)).mpr hC⟩
    rw [cmp_correct hS ha (good_succK hn), ocmp_eq_gt_iff, val_succK]
    exact not_lt_of_le hle
  | psi xi pi a m hxi hpi ha hreg hle hCa hCxi hCpi hm hxim hCm ihxi ihpi iha =>
    simp only [RTKA.isNF, Bool.and_eq_true, bne_iff_ne, ne_eq, hm]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨ihxi, ihpi⟩, iha⟩, hreg⟩, ?_⟩, (inC_correct hS ha ha hpi).mpr hCa⟩,
      (inC_correct hS hxi ha hpi).mpr hCxi⟩, (inC_correct hS hpi ha hpi).mpr hCpi⟩, ?_, ?_⟩
    · rw [cmp_correct hS hxi ha, ocmp_eq_gt_iff]
      exact not_lt_of_le hle
    · unfold RTKA.lt
      rw [cmp_correct hS hxi (good_mOf hpi hm), beq_iff_eq, ocmp_eq_lt_iff]
      exact hxim
    · exact (inC_correct hS hxi (good_mOf hpi hm) hpi).mpr hCm

/-- `isNF` は `Good` のちょうどの判定（Def. 5.1 の加法版の条件を過不足なく調べる） -/
theorem isNF_iff_good (hS : StationaryHyp.{u}) (t : Tm) : RTKA.isNF t = true ↔ Good.{u} t :=
  ⟨good_of_isNF hS t, isNF_of_good hS t⟩

/-- 主定理：`M^α` が `K_n` で定常（`StationaryHyp`）なら、標準形の項について `cmp` は値の大小・相等と一致する -/
theorem cmpCorrect_of_stationaryHyp (hS : StationaryHyp.{u}) : CmpCorrect.{u} := by
  intro a b ha hb
  have e := cmp_correct hS (good_of_isNF hS a ha) (good_of_isNF hS b hb)
  refine And.intro ?_ ?_
  · unfold RTKA.lt
    rw [e, beq_iff_eq]
    exact ocmp_eq_lt_iff
  · rw [e]
    exact ocmp_eq_eq_iff

/-- 系：標準形の項の上で `cmp a b = .eq` なら `a = b` -/
theorem eq_of_cmp_eq (hS : StationaryHyp.{u}) {a b : Tm} (ha : RTKA.isNF a = true)
    (hb : RTKA.isNF b = true) (h : RTKA.cmp a b = .eq) : a = b :=
  val_inj.{u} hS a b (good_of_isNF hS a ha) (good_of_isNF hS b hb)
    (((cmpCorrect_of_stationaryHyp.{u} hS) a b ha hb).2.mp h)

end
end OCF.Rathjen
