import Compact.FS.CofMain
import Compact.FS.Order
import Compact.FS.Descent

/-! 標準形の型 `NF` 上の基本列：`fund`・`dom` を `NF` に移し、Bachmann 以外の FS の性質を示す。

* `big_cof` には閉じた点 `β` の存在が要る（`exists_closed`）：目標 `σ` なら `Ψ^0_σ(K_M)`（`M` を部分項の階より
  大きく取ると、`σ` 未満の項は `C(K_M, ·)` に入る）、`σ = K_m` なら仮想の K 点 `virtK`。
* Bachmann は梯子（`ω` 型の `a[n] ∈ D(a[n+1])`、`big` 型の `a[0] ∈ D(a[ξ])`）に帰着する：各項の `BP (p c) c` を
  整礎帰納で示す（`bach0`、帰納の一歩は `Descent.lean` の `bachmann_of_ladder`・`bp0_of_big`）。 -/

namespace RTKA.Fund

open Tm W

/-! ### 閉じた点の存在 -/

/-- 項の並びの部分項の階の最大 -/
def maxLevS : List Tm → Nat
  | [] => 0
  | u :: l => max ((subs u).foldr (fun v n => max (lev v) n) 0) (maxLevS l)

theorem lev_le_foldr : ∀ {l : List Tm} {v : Tm}, v ∈ l → lev v ≤ l.foldr (fun v n => max (lev v) n) 0
  | u :: l, v, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (lev_le_foldr h) (Nat.le_max_right _ _)

theorem lev_le_maxLevS : ∀ {l : List Tm} {u v : Tm}, u ∈ l → v ∈ subs u → lev v ≤ maxLevS l
  | u :: l, u', v, hu, hv => by
    simp only [maxLevS]
    rcases List.mem_cons.mp hu with rfl | hu
    · exact Nat.le_trans (lev_le_foldr hv) (Nat.le_max_left _ _)
    · exact Nat.le_trans (lev_le_maxLevS hu hv) (Nat.le_max_right _ _)

/-- 節点の引数が全て `g` 未満なら `C(g, d)` に入る -/
theorem inC_of_args {g d : Tm} : ∀ {x : Tm}, (∀ s k a, Tm.Psi s k a ∈ subs x → Lt a g) →
    (∀ m b, Tm.Xi m b ∈ subs x → Lt b g) → inC x g d = true
  | .zero, _, _ => inC_zero _ _
  | .one, _, _ => inC_one _ _
  | .K _, _, _ => inC_K _ _ _
  | .plus a b, h1, h2 => by
    rw [inC_plus, Bool.and_eq_true]
    exact ⟨inC_of_args (fun s k c hs => h1 s k c (subs_plus_l hs)) (fun m e hs => h2 m e (subs_plus_l hs)),
      inC_of_args (fun s k c hs => h1 s k c (subs_plus_r hs)) (fun m e hs => h2 m e (subs_plus_r hs))⟩
  | .Om e, h1, h2 => by
    rw [inC_om]
    exact inC_of_args (fun s k c hs => h1 s k c (subs_om hs)) (fun m e' hs => h2 m e' (subs_om hs))
  | .Xi m b, h1, h2 =>
    inC_xi_iff.mpr (Or.inr ⟨inC_of_args (fun s k c hs => h1 s k c (subs_xi hs))
      (fun m' e hs => h2 m' e (subs_xi hs)), h2 m b (self_mem_subs _)⟩)
  | .Psi s k a, h1, h2 =>
    inC_psi_iff.mpr (Or.inr ⟨inC_of_args (fun s' k' c hs => h1 s' k' c (subs_psi_p hs))
        (fun m e hs => h2 m e (subs_psi_p hs)),
      inC_of_args (fun s' k' c hs => h1 s' k' c (subs_psi_s hs)) (fun m e hs => h2 m e (subs_psi_s hs)),
      inC_of_args (fun s' k' c hs => h1 s' k' c (subs_psi_a hs)) (fun m e hs => h2 m e (subs_psi_a hs)),
      h1 s k a (self_mem_subs _)⟩)

/-- 正則項 `σ` 未満の有限個の元の上に、`σ` の中で閉じた点がある -/
theorem exists_closed {σ : Tm} (hσF : WNF σ) (hreg : RegTerm σ) (l : List Tm)
    (hl : ∀ f, f ∈ l → WNF f ∧ Lt f σ) :
    ∃ β, WNF β ∧ Lt β σ ∧ Cl σ β ∧ ∀ f, f ∈ l → Lt f β := by
  rcases hreg with hσt | ⟨m, rfl⟩
  · -- 目標：`β = Ψ^0_σ(K_M)`
    have hM : 1 ≤ maxLevS (σ :: l) + 1 := Nat.le_add_left 1 _
    have hKF : WNF (.K (maxLevS (σ :: l) + 1)) := WNF.K' hM
    have hlt : ∀ u, u ∈ σ :: l → ∀ v, v ∈ subs u → WNF v → Lt v (.K (maxLevS (σ :: l) + 1)) :=
      fun u hu v hv hvF => (lt_K_iffY hvF hM).mpr (Nat.le_trans (lev_le_maxLevS hu hv) (Nat.le_succ _))
    have hβ : WNF (.Psi .zero σ (.K (maxLevS (σ :: l) + 1))) :=
      wnf_psi0 hσF hσt hKF (inC_K _ _ _) fun r hr =>
        hlt σ List.mem_cons_self r (mem_subs_arg hr) (wnf_of_argR hσF hr)
    refine ⟨_, hβ, lt_psi_targetY hβ, Cl.of_psi hβ, fun f hf => ?_⟩
    have hfF := (hl f hf).1
    have hfl : f ∈ σ :: l := List.mem_cons_of_mem _ hf
    have hC : inC f (.K (maxLevS (σ :: l) + 1)) (.Psi .zero σ (.K (maxLevS (σ :: l) + 1))) = true :=
      inC_of_args (fun s k a hs => hlt f hfl a (subs_trans hs (subs_psi_a (self_mem_subs a)))
          ((hfF.of_mem_subs hs).psi.aF))
        fun j b hs => hlt f hfl b (subs_trans hs (subs_xi (self_mem_subs b))) (hfF.of_mem_subs hs).xi.2.1
    exact coll_psiY hβ f hfF hC (hl f hf).2
  · -- `σ = K_m`：仮想の K 点
    have hm : 1 ≤ m := hσF.k
    obtain ⟨N, hN⟩ := exists_bound (P := fun _ => True) (wnf_virtK hm) (virtK_mono hm) l
      (fun f hf => (hl f hf).1) fun f hf _ => virt_all hm f (hl f hf).1 (hl f hf).2
    exact ⟨virtK m N, wnf_virtK hm N, (lt_K_iffY (wnf_virtK hm N) hm).mpr (Nat.le_refl _),
      Cl.of_xi (wnf_virtK hm N), fun f hf => hN f hf trivial⟩

/-! ### 項の上の基本列の性質 -/

theorem seqI_dom_nat {t : Tm} (ht : WNF t) (h : dom t = .omega) : NatInv t (info t).seq := by
  have hI := seqI_all t ht
  unfold SeqI at hI
  rw [show (info t).seq.dom = dom t from rfl, h] at hI
  exact hI

theorem seqI_dom_big {t σ : Tm} (ht : WNF t) (h : dom t = .big σ) :
    BigUB t σ (info t).seq ∧ RegTerm σ := by
  have hI := seqI_all t ht
  unfold SeqI at hI
  rw [show (info t).seq.dom = dom t from rfl, h] at hI
  exact ⟨hI.1.1, hI.2.2⟩

theorem natOf_ofNatT (n : Nat) : natOf (ofNatT n) = n := by
  unfold natOf ofNatT
  rw [summands_mulNat (x := one) rfl]
  simp

theorem fund_omega {t : Tm} (h : dom t = .omega) (n : Nat) : fund t (ofNatT n) = (info t).seq.nat n := by
  rw [fund_eq, h]
  show fundNat t (natOf (ofNatT n)) = _
  rw [natOf_ofNatT]
  rfl

theorem fund_big {t σ ξ : Tm} (h : dom t = .big σ) (hξ : Lt ξ σ) : fund t ξ = (info t).seq.big ξ := by
  rw [fund_eq, h]
  show fundBig t (if ltB ξ σ = true then ξ else zero) = _
  rw [ite_eq_left (ltB_iff.mpr hξ)]
  rfl

theorem fund_wnf {t ξ : Tm} (ht : WNF t) (hξ : WNF ξ) : WNF (fund t ξ) := by
  rw [fund_eq]
  cases hd : dom t with
  | zero => exact WNF.zero
  | one => exact wnf_pred ht
  | omega => exact ((seqI_dom_nat ht hd).1.good _).1
  | big σ =>
    obtain ⟨hU, hreg⟩ := seqI_dom_big ht hd
    show WNF (fundBig t (if ltB ξ σ = true then ξ else zero))
    by_cases h : ltB ξ σ = true
    · rw [ite_eq_left h]
      exact (hU.good.1 ξ hξ (ltB_iff.mp h)).1
    · rw [ite_eq_right h]
      exact (hU.good.1 .zero WNF.zero (zero_lt hreg.ne_zero)).1

theorem dom_big_wnf {t σ : Tm} (ht : WNF t) (h : dom t = .big σ) : WNF σ := (seqI_dom_big ht h).1.hσF

end RTKA.Fund

namespace RTKA

open Fund Tm W FSDesc

/-! ### `NF` の上の基本列 -/

/-- 共終数 -/
def domNF (a : NF) : Cof NF :=
  match h : dom a.1 with
  | .zero => .zero
  | .one => .one
  | .omega => .omega
  | .big σ => .big ⟨σ, dom_big_wnf a.2 h⟩

/-- 基本列 -/
def fundNF (a ξ : NF) : NF := ⟨fund a.1 ξ.1, fund_wnf a.2 ξ.2⟩

/-- 自然数 -/
def ofNatNF (n : Nat) : NF := ⟨ofNatT n, wnf_ofNatT n⟩

def zeroNF : NF := ⟨.zero, rfl⟩

theorem domNF_zero {a : NF} : domNF a = .zero ↔ dom a.1 = .zero := by
  unfold domNF
  split <;> simp_all

theorem domNF_one {a : NF} : domNF a = .one ↔ dom a.1 = .one := by
  unfold domNF
  split <;> simp_all

theorem domNF_omega {a : NF} : domNF a = .omega ↔ dom a.1 = .omega := by
  unfold domNF
  split <;> simp_all

theorem domNF_big {a σ : NF} : domNF a = .big σ ↔ dom a.1 = .big σ.1 := by
  obtain ⟨σv, hσv⟩ := σ
  unfold domNF
  split
  · rename_i h
    simp [h]
  · rename_i h
    simp [h]
  · rename_i h
    simp [h]
  · rename_i σ' h
    constructor
    · intro e
      have e' : σ' = σv := congrArg Subtype.val (Cof.big.inj e)
      rw [h, e']
    · intro e
      rw [h] at e
      have e' := Cof.big.inj e
      subst e'
      rfl

theorem nf_lt {a b : NF} : a < b ↔ Lt a.1 b.1 := Iff.rfl

theorem nf_le {a b : NF} : a ≤ b ↔ Le a.1 b.1 := by
  show a < b ∨ a = b ↔ _
  constructor
  · rintro (h | rfl)
    · exact Or.inr h
    · exact Or.inl rfl
  · rintro (h | h)
    · exact Or.inr (Subtype.ext h)
    · exact Or.inl h

/-! ### Bachmann 以外の FS の性質 -/

theorem nf_ofNat_zero : ofNatNF 0 = zeroNF := rfl

theorem nf_ofNat_dom (n : Nat) : domNF (ofNatNF (n + 1)) = .one := domNF_one.mpr (dom_ofNatT n)

theorem nf_ofNat_fund (n : Nat) (m : NF) : fundNF (ofNatNF (n + 1)) m = ofNatNF n :=
  Subtype.ext (fund_ofNatT n m.1)

theorem nf_zero_dom : domNF zeroNF = .zero := domNF_zero.mpr dom_zero

theorem nf_zero_unique (a : NF) (h : domNF a = .zero) : a = zeroNF :=
  Subtype.ext ((dom_eq_zero_iff a.2).mp (domNF_zero.mp h))

theorem nf_zero_fund (n : NF) : fundNF zeroNF n = zeroNF := Subtype.ext (fund_zero n.1)

theorem nf_succ_md (a n : NF) (h : domNF a = .one) : fundNF a n < a := by
  have hd := domNF_one.mp h
  show Lt (fund a.1 n.1) a.1
  rw [fund_of_dom_one _ hd]
  exact pred_lt a.2 ((dom_eq_one_iff a.2).mp hd)

theorem nf_succ_cof (a n x : NF) (h : domNF a = .one) (hx : x < a) : x ≤ fundNF a n := by
  have hd := domNF_one.mp h
  rw [nf_le]
  show Le x.1 (fund a.1 n.1)
  rw [fund_of_dom_one _ hd]
  exact le_pred a.2 ((dom_eq_one_iff a.2).mp hd) x.2 hx

theorem nf_omega_lt (a : NF) (n : Nat) (h : domNF a = .omega) : fundNF a (ofNatNF n) < a := by
  have hd := domNF_omega.mp h
  show Lt (fund a.1 (ofNatT n)) a.1
  rw [fund_omega hd]
  exact ((seqI_dom_nat a.2 hd).1.good n).2.1

theorem nf_omega_mono (a : NF) (n : Nat) (h : domNF a = .omega) :
    fundNF a (ofNatNF n) < fundNF a (ofNatNF (n + 1)) := by
  have hd := domNF_omega.mp h
  show Lt (fund a.1 (ofNatT n)) (fund a.1 (ofNatT (n + 1)))
  rw [fund_omega hd, fund_omega hd]
  exact ((seqI_dom_nat a.2 hd).1.good n).2.2

theorem nf_omega_cof (a x : NF) (h : domNF a = .omega) (hx : x < a) : ∃ n, x ≤ fundNF a (ofNatNF n) := by
  have hd := domNF_omega.mp h
  have hC := seqC_all a.1 a.2
  unfold SeqC at hC
  rw [show (info a.1).seq.dom = dom a.1 from rfl, hd] at hC
  obtain ⟨n, hn⟩ := hC x.1 x.2 hx
  refine ⟨n, (nf_le).mpr (Or.inr ?_)⟩
  show Lt x.1 (fund a.1 (ofNatT n))
  rw [fund_omega hd]
  exact hn

theorem nf_big_lt (a σ ξ : NF) (h : domNF a = .big σ) (hξ : ξ < σ) : fundNF a ξ < a := by
  have hd := domNF_big.mp h
  show Lt (fund a.1 ξ.1) a.1
  rw [fund_big hd hξ]
  exact ((seqI_dom_big a.2 hd).1.good.1 ξ.1 ξ.2 hξ).2

theorem nf_big_mono (a σ ξ η : NF) (h : domNF a = .big σ) (hξη : ξ < η) (hησ : η < σ) :
    fundNF a ξ < fundNF a η := by
  have hd := domNF_big.mp h
  have hξσ : Lt ξ.1 σ.1 := W.lt_transY ξ.2 η.2 σ.2 hξη hησ
  show Lt (fund a.1 ξ.1) (fund a.1 η.1)
  rw [fund_big hd hξσ, fund_big hd hησ]
  exact (seqI_dom_big a.2 hd).1.good.2 ξ.1 η.1 ξ.2 η.2 hξη hησ

theorem nf_big_cof (a σ x : NF) (h : domNF a = .big σ) (hx : x < a) : ∃ ξ, ξ < σ ∧ x ≤ fundNF a ξ := by
  have hd := domNF_big.mp h
  obtain ⟨hU, hreg⟩ := seqI_dom_big a.2 hd
  have hC := seqC_all a.1 a.2
  unfold SeqC at hC
  rw [show (info a.1).seq.dom = dom a.1 from rfl, hd] at hC
  obtain ⟨β, hβF, hβσ, hCl, hβ⟩ := exists_closed σ.2 hreg (fr σ.1 x.1)
    fun f hf => ⟨(show WNF x.1 from x.2).of_mem_subs (fr_spec hf).1, (fr_spec hf).2⟩
  refine ⟨⟨β, hβF⟩, hβσ, (nf_le).mpr (Or.inr ?_)⟩
  show Lt x.1 (fund a.1 β)
  rw [fund_big hd hβσ]
  exact hC x.1 β x.2 hx hβF hβσ hCl hβ

/-! ### Bachmann の梯子への帰着 -/

/-- `p b = b[0]`（後者なら前者） -/
def p0 (b : NF) : NF := fundNF b (ofNatNF 0)

theorem p0_le (b : NF) : p0 b ≤ b := by
  cases hd : domNF b with
  | zero =>
    have e := nf_zero_unique b hd
    subst e
    exact Or.inr (nf_zero_fund _)
  | one => exact Or.inl (nf_succ_md b _ hd)
  | omega => exact Or.inl (nf_omega_lt b 0 hd)
  | big σ =>
    have hσ0 : ofNatNF 0 < σ := by
      show Lt Tm.zero σ.1
      exact zero_lt (seqI_dom_big b.2 (domNF_big.mp hd)).2.ne_zero
    exact Or.inl (nf_big_lt b σ _ hd hσ0)

/-- 梯子：`ω` 型の項 `a` で、`a[n]` は `a[n+1]` からの降下列に現れる -/
def LadderOmega : Prop :=
  ∀ a : NF, domNF a = .omega → ∀ n, InD p0 (fundNF a (ofNatNF n)) (fundNF a (ofNatNF (n + 1)))

/-- 梯子：`big` 型の項 `a` で、`a[0]` は `a[ξ]` からの降下列に現れる -/
def LadderBig : Prop :=
  ∀ a σ : NF, domNF a = .big σ → ∀ ξ, ξ < σ → InD p0 (fundNF a (ofNatNF 0)) (fundNF a ξ)

/-- 梯子があれば、全ての項 `c` で区間 `(c[0], c]` の元 `b` は `c[0] ≤ b[0]` -/
theorem bach0 (hL1 : LadderOmega) (hL2 : LadderBig) : ∀ c : NF, BP p0 (p0 c) c := by
  intro c
  refine WellFounded.induction (C := fun c => BP p0 (p0 c) c) (Well_Order.lt_wf (A := NF)) c ?_
  intro c ih b hb hbc
  rcases hbc with hbc | rfl
  rotate_left
  · exact le_refl' _
  cases hd : domNF c with
  | zero =>
    exfalso
    have e := nf_zero_unique c hd
    subst e
    have h1 : p0 zeroNF = zeroNF := nf_zero_fund _
    rw [h1] at hb
    exact lt_asymm' hb hbc
  | one =>
    exfalso
    exact not_lt_of_le' (nf_succ_cof c (ofNatNF 0) b hd hbc) hb
  | omega =>
    exact bachmann_of_ladder p0 p0_le (fun c' hc' => ih c' hc') (fun n => fundNF c (ofNatNF n))
      (fun n => nf_omega_lt c n hd) (fun n => nf_omega_mono c n hd) (fun x hx => nf_omega_cof c x hd hx)
      (hL1 c hd) 0 b hb hbc
  | big σ =>
    exact bp0_of_big p0 p0_le (fun b' hb' => ih b' hb') (fun ξ => ξ < σ) (fun ξ => fundNF c ξ)
      (fun x hx => nf_big_cof c σ x hd hx) (fun ξ hξ => nf_big_lt c σ ξ hd hξ) (fun ξ hξ => hL2 c σ hd ξ hξ)
      b hb hbc

/-- Bachmann 性（梯子から） -/
theorem nf_omega_bachmann (hL1 : LadderOmega) (hL2 : LadderBig) (a b : NF) (n : Nat)
    (hd : domNF a = .omega) (h1 : fundNF a (ofNatNF n) < b) (h2 : b < a) :
    fundNF a (ofNatNF n) ≤ fundNF b (ofNatNF 0) :=
  bachmann_of_ladder p0 p0_le (fun c _ => bach0 hL1 hL2 c) (fun n => fundNF a (ofNatNF n))
    (fun n => nf_omega_lt a n hd) (fun n => nf_omega_mono a n hd) (fun x hx => nf_omega_cof a x hd hx)
    (hL1 a hd) n b h1 h2

/-- 梯子があれば `NF` は基本列の公理を満たす -/
def fsNF (hL1 : LadderOmega) (hL2 : LadderBig) : FS NF where
  fund := fundNF
  dom := domNF
  Z := zeroNF
  ofNat := ofNatNF
  ofNat_zero := nf_ofNat_zero
  ofNat_dom := nf_ofNat_dom
  ofNat_fund := nf_ofNat_fund
  zero_dom := nf_zero_dom
  zero_unique := nf_zero_unique
  zero_fund := nf_zero_fund
  succ_md := nf_succ_md
  succ_cof := nf_succ_cof
  omega_lt := nf_omega_lt
  omega_mono := nf_omega_mono
  omega_bachmann := fun a b n hd h1 h2 => nf_omega_bachmann hL1 hL2 a b n hd h1 h2
  omega_cof := nf_omega_cof
  big_lt := nf_big_lt
  big_mono := nf_big_mono
  big_cof := nf_big_cof

end RTKA
