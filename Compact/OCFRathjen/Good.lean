import Compact.OCFRathjen.Unique
import Compact.OCFRathjen.Eval
import Compact.OCFRathjen.WeakCompact

/-! 標準形の意味論版 `Good` と、その値の性質。

`Good` は `RTKA.isNF` と同じ形の帰納的述語で、`isNF` が `cmp`・`inC` で調べる条件を順序数の条件
（`val a < Ω_{val a}`、`val a ∈ C(val a, K_n)` など）に置き換えたもの。

* `Good.inv`：`Good` な項の値は良い性質（`Inv`）をもつ
  （弱コンパクト性から導いた定常性仮定 (S) `stationaryHyp` を用いる）。
  加法的主数・階・Cantor 標準形、正則な項の定常性（Lemma 5.2）、`Ω` の不動点（Lemma 4.19）など。
* `val_inj`：`Good` な項の上で `val` は単射（Lemma 5.2 (iii)）。 -/

namespace OCF.Rathjen

universe u

open Ordinal

noncomputable section

open RTKA (Tm)

/-! ### 項の構文についての補題 -/

theorem summands_principal {t : Tm} (h : RTKA.isPrincipal t = true) : RTKA.summands t = [t] := by
  cases t <;> simp_all [RTKA.isPrincipal, RTKA.summands]

theorem summands_plus (a b : Tm) : RTKA.summands (.plus a b) = a :: RTKA.summands b := by
  simp [RTKA.summands]

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
      (hlt : val.{u} a < Om (K n + succ 0)) (hC : C (val.{u} a) (K n) (val a)) : Good (.Xi n a)
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
  rw [summands_principal hp, List.map_cons, List.map_nil] at hc
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
theorem Good.inv {t : Tm} (h : Good.{u} t) : Inv.{u} t := by
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
      rw [summands_plus, List.map_cons]
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
      rw [summands_plus, List.map_cons] at hc
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
  | xi n a hn _ ha0 hlt hC iha =>
    have hva0 := iha.pos ha0
    have good : XiGood n (val.{u} a) := Xi_mem hn (stationaryHyp n hn (val a) hva0 hlt hC)
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
theorem isPrincipal_of_val_eq {a b : Tm} (ha : Good.{u} a)
    (hb : Good.{u} b) (hap : RTKA.isPrincipal a = true) (e : val.{u} a = val b) :
    RTKA.isPrincipal b = true := by
  have hs := summands_val_eq ha.inv hb.inv e
  rw [summands_principal hap, List.map_cons, List.map_nil] at hs
  cases hb with
  | zero => simp [RTKA.summands] at hs
  | plus b₁ b₂ _ _ _ hb0 _ =>
    rw [summands_plus, List.map_cons] at hs
    have h2 := (List.cons.inj hs).2
    exact absurd (summands_eq_nil.mp (List.map_eq_nil_iff.mp h2.symm)) hb0
  | _ => simp [RTKA.isPrincipal]

/-- `Good` な項の上で `val` は単射 -/
theorem val_inj :
    ∀ (a b : Tm), Good.{u} a → Good.{u} b → val.{u} a = val b → a = b := by
  intro a
  induction a with
  | zero =>
    intro b _ hb e
    have hs := summands_val_eq (Good.zero.inv) (hb.inv) e
    simp only [RTKA.summands, List.map_nil] at hs
    exact (summands_eq_nil.mp (List.map_eq_nil_iff.mp hs.symm)).symm
  | plus a₁ a₂ ih₁ ih₂ =>
    intro b ha hb e
    have hs := summands_val_eq ha.inv hb.inv e
    by_cases hbp : RTKA.isPrincipal b = true
    · have h := isPrincipal_of_val_eq hb ha hbp e.symm
      simp [RTKA.isPrincipal] at h
    cases ha with
    | plus _ _ ha₁ ha₂ _ ha0 _ =>
      cases hb with
      | plus b₁ b₂ hb₁ hb₂ _ _ _ =>
        rw [summands_plus, summands_plus, List.map_cons, List.map_cons] at hs
        have e₁ := (List.cons.inj hs).1
        have e₂ : val.{u} a₂ = val b₂ := by
          rw [ha₂.inv.cnf.eq, hb₂.inv.cnf.eq, (List.cons.inj hs).2]
        rw [ih₁ b₁ ha₁ hb₁ e₁, ih₂ b₂ ha₂ hb₂ e₂]
      | zero => simp [RTKA.summands] at hs
      | _ => simp [RTKA.isPrincipal] at hbp
  | one =>
    intro b ha hb e
    have hbp := isPrincipal_of_val_eq ha hb rfl e
    have ib := hb.inv
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
    have hbp := isPrincipal_of_val_eq ha hb rfl e
    have ib := hb.inv
    cases ha with
    | kc _ hn =>
      cases hb with
      | one => exact absurd e.symm (ne_of_lt (one_lt_of_R (R_K hn)))
      | kc m _ => rw [K_inj e]
      | om c hc _ hlt => exact absurd e.symm (Om_ne_K hc.inv.lt_Λ hlt)
      | xi m c _ _ _ _ _ => exact absurd e.symm (Xi_ne_K (ib.xi m c rfl).2.2.2)
      | psi ξ π β _ _ _ _ _ _ _ _ _ _ _ _ => exact absurd e.symm (Psi_ne_K (ib.psi ξ π β rfl).1)
      | _ => simp [RTKA.isPrincipal] at hbp
  | Om a ih =>
    intro b ha hb e
    have hbp := isPrincipal_of_val_eq ha hb rfl e
    have ib := hb.inv
    cases ha with
    | om _ ha' _ hlt =>
      have hΛ := ha'.inv.lt_Λ
      cases hb with
      | one => exact absurd e (Om_ne_one hlt)
      | kc m _ => exact absurd e (Om_ne_K hΛ hlt)
      | om c hc _ _ => rw [ih c ha' hc (Om_inj hΛ hc.inv.lt_Λ e)]
      | xi m c _ _ _ _ _ =>
        have hx := ib.xi m c rfl
        exact absurd e (Om_ne_Xi hΛ hlt hx.1 hx.2.2.2)
      | psi ξ π β _ _ _ _ _ _ _ _ _ _ _ _ => exact absurd e (Om_ne_Psi hΛ hlt (ib.psi ξ π β rfl).1)
      | _ => simp [RTKA.isPrincipal] at hbp
  | Xi n a ih =>
    intro b ha hb e
    have hbp := isPrincipal_of_val_eq ha hb rfl e
    have ia := ha.inv
    have ib := hb.inv
    have hx := ia.xi n a rfl
    cases ha with
    | xi _ _ _ ha' _ _ _ =>
      cases hb with
      | one => exact absurd e (Xi_ne_one hx.1 hx.2.2.2)
      | kc m _ => exact absurd e (Xi_ne_K hx.2.2.2)
      | om c hc _ hlt => exact absurd e.symm (Om_ne_Xi hc.inv.lt_Λ hlt hx.1 hx.2.2.2)
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
    have hbp := isPrincipal_of_val_eq ha hb rfl e
    have ia := ha.inv
    have ib := hb.inv
    have hp := ia.psi xi pi a rfl
    cases ha with
    | psi _ _ _ _ hxi hpi ha' _ _ _ _ _ _ _ _ =>
      cases hb with
      | one => exact absurd e (Psi_ne_one hp.1 hp.2.1)
      | kc m _ => exact absurd e (Psi_ne_K hp.1)
      | om c hc _ hlt => exact absurd e.symm (Om_ne_Psi hc.inv.lt_Λ hlt hp.1)
      | xi m c _ _ _ _ _ =>
        have hy := ib.xi m c rfl
        exact absurd e (Xi_ne_Psi hy.1 hy.2.2.2 hp.1 hp.2)
      | psi ξ π β _ hξ hπ hβ _ _ _ _ _ _ _ _ =>
        have hq := ib.psi ξ π β rfl
        have h := Psi_inj hp.1 hq.1 hp.2 hq.2 e
        rw [ihxi ξ hxi hξ h.1, ihpi π hpi hπ h.2.1, iha β ha' hβ h.2.2]
      | _ => simp [RTKA.isPrincipal] at hbp

end
end OCF.Rathjen
