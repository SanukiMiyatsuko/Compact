import Compact.OCFRathjen.Compare

/-! 生成子の値と `C(γ, δ)` の元の分解。

* 生成子の値（`1`、`K_m`、`Ω_w`、`Ξ_m(x)`（`x > 0`）、`Ψ^ξ_π(β)`（`π ∈ Reg`））は加法的主数か `0`。
* `Cn_cnf`：`z ∈ C(γ, δ)` の Cantor 標準形の項は、同じ段階で `C(γ, δ)` に入る（Lemma 4.18 (i) の加法版）。
* `Cn_gen`：加法的主数 `z ∈ C(γ, δ)` で `z ≥ δ` のものは、本物の生成子の値（`Ω_w` で `w < Ω_w`、
  `Ξ_m(x) < K_m`、`Ψ^ξ_π(β) < π`）か `1`・`K_m` で、その引数はより前の段階で `C(γ, δ)` に入る。 -/

namespace OCF.Rathjen

universe u

open Ordinal

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

end
end OCF.Rathjen
