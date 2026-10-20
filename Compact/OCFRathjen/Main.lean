import Compact.OCFRathjen.Correct
import Compact.OCFRathjen.WeakCompact

/-! 主定理：`StationaryHyp → CmpCorrect`。

標準形の項（`RTKA.isNF`）は `Good` で（`good_of_isNF`）、`Good` な項について `cmp` は値の比較と
一致する（`cmp_correct`）。`good_of_isNF` は項の構造についての帰納法で、`isNF` が調べる `cmp`・`inC` の
条件を、部分項について `cmp_correct`・`inC_correct` で順序数の条件に読み替える。 -/

namespace OCF.Rathjen

universe u

open Ordinal

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
      rw [summands_plus, List.map_cons] at hc
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
  rw [RTKA.cmp, summands_principal hap, summands_principal (t := .Om a) rfl, RTKA.cmpList,
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
    obtain ⟨⟨⟨⟨hn, hna⟩, ha0⟩, hlt⟩, hC⟩ := h
    have ga := iha hna
    have hlt' : val.{u} a < val (RTKA.succK n) := by
      unfold RTKA.lt at hlt
      rw [cmp_correct hS ga (good_succK hn), beq_iff_eq, ocmp_eq_lt_iff] at hlt
      exact hlt
    rw [val_succK] at hlt'
    exact Good.xi n a hn ga ha0 hlt' ((inC_correct hS ga ga (Good.kc n hn)).mp hC)
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

/-- 系：標準形の項の上の `lt` は整礎 -/
theorem lt_wf_of_stationaryHyp (hS : StationaryHyp.{u}) :
    WellFounded (fun a b : {t : Tm // RTKA.isNF t = true} => RTKA.lt a.1 b.1 = true) := by
  refine Subrelation.wf (fun {a b} hab => ?_)
    (InvImage.wf (fun t : {t : Tm // RTKA.isNF t = true} => val.{u} t.1) lt_wellFounded)
  exact ((cmpCorrect_of_stationaryHyp hS) a.1 b.1 a.2 b.2).1.mp hab

end
end OCF.Rathjen
