import Compact.WF.FZCmp

/-! 断片 `FY` の次の正則項 `nrY`（順序の仮定 `FZOrder` の下で）。

正則項（崩壊の添字）は `Ω_c`（`c` は後者）、`K_n`、`Ξ_n(p)`。`Ψ^0_{Ξ_n(p)}(a)` は `Ω` の不動点で正則でないので、
次の正則項は `Ω_{Ψ+1}`。 -/

namespace RTKA.Z

open Tm

/-! ### 後者 -/

theorem FZNF.mk_plus {a b : Tm} (ha : FZNF a) (hb : FZNF b) (hap : isPrincipal a = true)
    (hb0 : b ≠ .zero) (hh : ∀ h rest, summands b = h :: rest → cmp h a ≠ .gt) :
    FZNF (.plus a b) := by
  refine ⟨?_, ?_⟩
  · simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq]
    refine ⟨⟨⟨⟨hap, hb0⟩, ha.1⟩, hb.1⟩, ?_⟩
    cases hs : summands b with
    | nil => exact absurd hs (summands_ne_nil hb0)
    | cons h rest =>
      have := hh h rest hs
      simpa using this
  · simp only [isFZ, Bool.and_eq_true]
    exact ⟨ha.2, hb.2⟩

theorem succT_FZNF : ∀ {z : Tm}, FZNF z → FZNF (succT z)
  | .zero, _ => FZNF.one
  | .plus a b, hz => by
    obtain ⟨ha, hb, hap, hb0⟩ := hz.plus
    refine FZNF.mk_plus ha (succT_FZNF hb) hap (succT_ne_zero b) ?_
    intro h rest hs
    rw [summands_succT] at hs
    cases hs' : summands b with
    | nil => exact absurd hs' (summands_ne_nil hb0)
    | cons h' rest' =>
      rw [hs', List.cons_append, List.cons.injEq] at hs
      rw [← hs.1]
      exact hz.plus_head hs'
  | .one, hz | .K _, hz | .Om _, hz | .Xi _ _, hz | .Psi _ _ _, hz => by
    refine FZNF.mk_plus hz FZNF.one rfl (by intro e; cases e) ?_
    intro h rest hs
    simp only [summands, List.cons.injEq] at hs
    rw [← hs.1, cmp_principal rfl rfl]
    exact cmpP_one_ne_gtY hz rfl

theorem cmpList_succ_ne_gtY : ∀ (l m : List Tm), (∀ y, y ∈ m → FZNF y ∧ isPrincipal y = true) →
    cmpList l m = .lt → cmpList (l ++ [.one]) m ≠ .gt
  | [], [], _, h => by rw [cmpList_nil_nil] at h; cases h
  | [], y :: ys, hm, _ => by
    have hy := hm y List.mem_cons_self
    rw [List.nil_append]
    cases e : cmpP .one y with
    | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]; decide
    | eq =>
      rw [cmpList_cons_cons_eq _ _ e]
      cases ys with
      | nil => rw [cmpList_nil_nil]; decide
      | cons _ _ => rw [cmpList_nil_cons]; decide
    | gt => exact absurd e (cmpP_one_ne_gtY hy.1 hy.2)
  | _ :: _, [], _, h => by rw [cmpList_cons_nil] at h; cases h
  | x :: xs, y :: ys, hm, h => by
    rw [List.cons_append]
    rcases cmpList_lt_cases h with e | ⟨e, e'⟩
    · rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]; decide
    · rw [cmpList_cons_cons_eq _ _ e]
      exact cmpList_succ_ne_gtY xs ys (fun y hy => hm y (List.mem_cons_of_mem _ hy)) e'

/-- 正則項：`Ψ` の目標 `Ω_c`（`c` は後者）と `Ξ_n(p)`、`Ξ_n` の添字 `K_n` -/
def IsRegY (σ : Tm) : Prop :=
  (∃ c, σ = .Om c ∧ isSucc c = true) ∨ (∃ n, σ = .K n) ∨ ∃ n p, σ = .Xi n p

/-- 次の正則項：`t` より大きい最小の正則項 -/
def nrY : Tm → Tm
  | .plus a _ => nrY a
  | .Psi _ (.Om c) _ => .Om c
  | .Psi s p a => .Om (succT (.Psi s p a))
  | .K n => .Om (succT (.K n))
  | .Om a => .Om (succT a)
  | .Xi n a => .Om (succT (.Xi n a))
  | _ => .Om .one

theorem IsRegY.K (n : Nat) : IsRegY (.K n) := Or.inr (Or.inl ⟨n, rfl⟩)

theorem IsRegY.tgt {ξ π a : Tm} (h : FZNF (.Psi ξ π a)) : IsRegY π := by
  rcases h.psi.tgt with ⟨c, rfl, hs⟩ | ⟨n, p, rfl⟩
  · exact Or.inl ⟨c, rfl, hs⟩
  · exact Or.inr (Or.inr ⟨n, p, rfl⟩)

theorem lev_nrY : ∀ {t : Tm}, FZNF t → t ≠ .zero → lev (nrY t) = lev t
  | .zero, _, h => absurd rfl h
  | .one, _, _ => rfl
  | .K _, _, _ => rfl
  | .plus a _, ht, _ => by
    obtain ⟨ha, -, hap, -⟩ := ht.plus
    have : a ≠ .zero := by intro e; subst e; simp [isPrincipal] at hap
    have h := lev_nrY ha this
    exact h
  | .Om _, ht, _ => lev_succT ht.om.2.1
  | .Xi _ _, _, _ => rfl
  | .Psi _ p _, ht, _ => by
    rcases ht.psi.tgt with ⟨c, rfl, -⟩ | ⟨n, q, rfl⟩ <;> rfl

section Order

variable [FZOrder]

/-- `z < c` なら `z + 1 ≤ c` -/
theorem succT_leY {z c : Tm} (hz : FZNF z) (hc : FZNF c) (h : Lt z c) : Le (succT z) c := by
  have hne : cmp (succT z) c ≠ .gt := by
    rw [cmp_eq, summands_succT]
    unfold Lt at h
    rw [cmp_eq] at h
    exact cmpList_succ_ne_gtY _ _ (summands_FZNF c hc) h
  exact le_of_ne_gtY (succT_FZNF hz) hc hne

omit [FZOrder] in
theorem succT_ne_principal (z : Tm) {X : Tm} (hX : isPrincipal X = true) (hX1 : X ≠ .one) :
    succT z ≠ X := by
  intro e
  subst e
  cases z <;> simp_all [succT, isPrincipal]

/-- `Ω` の不動点 `X` より小さい `z` について `z + 1 < X` -/
theorem succT_lt_OF {z X : Tm} (hX : IsOF X) (hz : FZNF z) (hXF : FZNF X) (h : Lt z X) :
    Lt (succT z) X := by
  rcases succT_leY hz hXF h with e | h'
  · exact absurd e (succT_ne_principal z hX.principal
      (by rcases hX with ⟨n, a, rfl⟩ | ⟨ξ, n, p, a, rfl⟩ <;> intro e <;> cases e))
  · exact h'

omit [FZOrder] in
/-- 先頭の項は和以下 -/
theorem head_leY {t h : Tm} {rest : List Tm} (ht : FZNF t) (hs : summands t = h :: rest) :
    Le h t := by
  cases t with
  | zero => simp [summands] at hs
  | plus a b =>
    rw [summands_plus, List.cons.injEq] at hs
    rw [← hs.1]
    exact Or.inr (lt_plus_leftY ht)
  | _ =>
    simp only [summands, List.cons.injEq] at hs
    rw [hs.1]
    exact Le.refl _

/-! ### `Ω_z` の標準形 -/

/-- `0`・`K_m`・`Ω` の不動点でない標準形 `z` について `Ω_z` は標準形 -/
theorem FZNF.om_ofY {z : Tm} (hz : FZNF z) (h0 : z ≠ .zero) (hK : ∀ m, z ≠ .K m)
    (hX : ¬ IsOF z) : FZNF (.Om z) := by
  have hlt : Lt z (.Om z) := by
    cases hs : summands z with
    | nil => exact absurd hs (summands_ne_nil h0)
    | cons h rest =>
      have hh := summands_FZNF z hz h (by rw [hs]; exact List.mem_cons_self)
      have hle := head_leY hz hs
      have : Lt h (.Om z) := by
        cases h with
        | zero => simp [isPrincipal] at hh
        | plus _ _ => simp [isPrincipal] at hh
        | K m =>
          rcases hle with e | e
          · exact absurd e.symm (hK m)
          · exact (lt_K_omY hh.1.k hz).mpr e
        | Xi n a =>
          rcases hle with e | e
          · exact absurd (e ▸ Or.inl ⟨n, a, rfl⟩) hX
          · exact (lt_OF_omG (Or.inl ⟨n, a, rfl⟩) hh.1 hz).mpr e
        | one =>
          have hl : 1 ≤ lev z := lev_posY hz h0
          rcases Nat.lt_or_eq_of_le hl with hl | hl
          · rw [lt_principal_iff rfl rfl, cmpP_of_lev_lt (by simp only [lev]; exact hl)]
          · rw [lt_principal_iff rfl rfl, cmpP.eq_def]
            simp only [lev, ← hl, Nat.lt_irrefl, ↓reduceIte]
        | Om x =>
          have hx := hh.1.om
          rw [lt_om_iffY hx.1 hz]
          exact lt_of_lt_of_leY hx.1 hh.1 hz hx.2.2 hle
        | Psi s p β =>
          rcases hh.1.psi.m with ⟨c, rfl, rfl⟩ | ⟨n, q, rfl, -, -⟩
          · exact (lt_psi_omY hh.1 hz).mpr
              (Or.inr (lt_of_lt_of_leY hh.1.psiOm.1 hh.1 hz (FZOrder.cx hh.1) hle))
          · rcases hle with e | e
            · exact absurd (e ▸ Or.inr ⟨s, n, q, β, rfl⟩) hX
            · exact (lt_OF_omG (Or.inr ⟨s, n, q, β, rfl⟩) hh.1 hz).mpr e
      exact lt_of_head_lt rfl hs ((lt_principal_iff hh.2 rfl).mp this)
  refine ⟨?_, hz.2⟩
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq]
  refine ⟨⟨hz.1, h0⟩, ?_⟩
  unfold lt
  unfold Lt at hlt
  simp [hlt]

theorem FZNF.om_succT {z : Tm} (hz : FZNF z) : FZNF (.Om (succT z)) :=
  FZNF.om_ofY (succT_FZNF hz) (succT_ne_zero z) (succT_ne_K z)
    (by rintro (⟨n, a, e⟩ | ⟨ξ, n, p, a, e⟩) <;> cases z <;> simp [succT] at e)

theorem FZNF.om_one : FZNF (.Om .one) :=
  FZNF.om_ofY FZNF.one (by intro e; cases e) (fun _ e => by cases e)
    (by rintro (⟨n, a, e⟩ | ⟨ξ, n, p, a, e⟩) <;> cases e)

/-! ### 次の正則項 -/

theorem nr_specY : ∀ t : Tm, FZNF t → FZNF (nrY t) ∧ IsRegY (nrY t) ∧ Lt t (nrY t)
  | .zero, _ => ⟨FZNF.om_one, Or.inl ⟨.one, rfl, rfl⟩, zero_lt (by intro e; cases e)⟩
  | .one, _ => ⟨FZNF.om_one, Or.inl ⟨.one, rfl, rfl⟩, FZNF.om_one.om.2.2⟩
  | .K _, ht => ⟨FZNF.om_succT ht, Or.inl ⟨_, rfl, isSucc_succT _⟩,
      (lt_K_omY ht.k (succT_FZNF ht)).mpr (lt_succT _)⟩
  | .plus a _, ht => by
    obtain ⟨ha, -, -, -⟩ := ht.plus
    obtain ⟨h1, h2, h3⟩ := nr_specY a ha
    refine ⟨h1, h2, (lt_plus_prin_iffY ht ?_).mpr h3⟩
    show isPrincipal (nrY a) = true
    rcases h2 with ⟨c, e, -⟩ | ⟨n, e⟩ | ⟨n, p, e⟩ <;> rw [e] <;> rfl
  | .Om a, ht => ⟨FZNF.om_succT ht.om.1, Or.inl ⟨_, rfl, isSucc_succT _⟩,
      (lt_om_iffY ht.om.1 (succT_FZNF ht.om.1)).mpr (lt_succT _)⟩
  | .Xi n a, ht => ⟨FZNF.om_succT ht, Or.inl ⟨_, rfl, isSucc_succT _⟩,
      (lt_OF_omG (Or.inl ⟨n, a, rfl⟩) ht (succT_FZNF ht)).mpr (lt_succT _)⟩
  | .Psi ξ p a, ht => by
    rcases ht.psi.m with ⟨c, rfl, rfl⟩ | ⟨n, q, rfl, -, -⟩
    · exact ⟨ht.psi.piF, Or.inl ⟨c, rfl, ht.psiOm.2.2.1⟩, lt_psi_om_self c a⟩
    · exact ⟨FZNF.om_succT ht, Or.inl ⟨_, rfl, isSucc_succT _⟩,
        (lt_OF_omG (Or.inr ⟨ξ, n, q, a, rfl⟩) ht (succT_FZNF ht)).mpr (lt_succT _)⟩

theorem nr_lt_KY {t : Tm} {m : Nat} (ht : FZNF t) (hm : 1 ≤ m) (h : Lt t (.K m)) :
    Lt (nrY t) (.K m) := by
  rw [lt_K_iffY (nr_specY t ht).1 hm]
  by_cases h0 : t = .zero
  · subst h0
    show 1 ≤ m
    exact hm
  · rw [lev_nrY ht h0]
    exact (lt_K_iffY ht hm).mp h

theorem nr_le_omY : ∀ t : Tm, FZNF t → ∀ c : Tm, FZNF (.Om c) → Lt t (.Om c) →
    Le (nrY t) (.Om c)
  | .zero, _, _, hc, _ | .one, _, _, hc, _ =>
    le_om_of_leY FZNF.one hc.om.1 (one_leY hc.om.1 hc.om.2.1)
  | .K _, ht, _, hc, h =>
    le_om_of_leY (succT_FZNF ht) hc.om.1 (succT_leY ht hc.om.1 ((lt_K_omY ht.k hc.om.1).mp h))
  | .plus a _, ht, c, hc, h => by
    obtain ⟨ha, -, -, -⟩ := ht.plus
    exact nr_le_omY a ha c hc (lt_transY ha ht hc (lt_plus_leftY ht) h)
  | .Om _, ht, _, hc, h =>
    le_om_of_leY (succT_FZNF ht.om.1) hc.om.1
      (succT_leY ht.om.1 hc.om.1 ((lt_om_iffY ht.om.1 hc.om.1).mp h))
  | .Xi n a, ht, _, hc, h =>
    le_om_of_leY (succT_FZNF ht) hc.om.1
      (succT_leY ht hc.om.1 ((lt_OF_omG (Or.inl ⟨n, a, rfl⟩) ht hc.om.1).mp h))
  | .Psi ξ p a, ht, _, hc, h => by
    rcases ht.psi.m with ⟨c', rfl, rfl⟩ | ⟨n, q, rfl, -, -⟩
    · exact le_om_of_leY ht.psiOm.1 hc.om.1 ((lt_psi_omY ht hc.om.1).mp h)
    · exact le_om_of_leY (succT_FZNF ht) hc.om.1
        (succT_leY ht hc.om.1 ((lt_OF_omG (Or.inr ⟨ξ, n, q, a, rfl⟩) ht hc.om.1).mp h))

theorem nr_lt_xiY : ∀ t : Tm, FZNF t → ∀ {m : Nat} {q : Tm}, FZNF (.Xi m q) → Lt t (.Xi m q) →
    Lt (nrY t) (.Xi m q)
  | .zero, _, m, q, hX, _ | .one, _, m, q, hX, _ => by
    have h1 : Lt .one (.Xi m q) := by
      rcases one_leY hX (by intro e; cases e) with e | h
      · cases e
      · exact h
    exact (lt_om_OFG (Or.inl ⟨m, q, rfl⟩)).mpr h1
  | .K n, ht, m, q, hX, h =>
    (lt_om_OFG (Or.inl ⟨m, q, rfl⟩)).mpr (succT_lt_OF (Or.inl ⟨m, q, rfl⟩) ht hX h)
  | .plus a _, ht, _, _, hX, h => by
    obtain ⟨ha, -, -, -⟩ := ht.plus
    exact nr_lt_xiY a ha hX (lt_transY ha ht hX (lt_plus_leftY ht) h)
  | .Om a, ht, m, q, hX, h =>
    (lt_om_OFG (Or.inl ⟨m, q, rfl⟩)).mpr (succT_lt_OF (Or.inl ⟨m, q, rfl⟩) ht.om.1 hX
      ((lt_om_OFG (Or.inl ⟨m, q, rfl⟩)).mp h))
  | .Xi n a, ht, m, q, hX, h =>
    (lt_om_OFG (Or.inl ⟨m, q, rfl⟩)).mpr (succT_lt_OF (Or.inl ⟨m, q, rfl⟩) ht hX h)
  | .Psi ξ p a, ht, m, q, hX, h => by
    rcases ht.psi.m with ⟨c, rfl, rfl⟩ | ⟨n, r, rfl, -, -⟩
    · -- `Ψ_c(a) < Ξ` なら `c < Ξ`
      have hs := ht.psiOm.2.2.1
      have hcF := ht.psiOm.1
      have hc : Lt c (.Xi m q) := by
        rcases triY hcF hX with h' | e | h'
        · exact h'
        · subst e; simp [isSucc, summands] at hs
        · exact absurd ((lt_OF_psiOm (Or.inl ⟨m, q, rfl⟩) hX ht).mpr h') (Lt.asymmY ht hX h)
      exact (lt_om_OFG (Or.inl ⟨m, q, rfl⟩)).mpr hc
    · exact (lt_om_OFG (Or.inl ⟨m, q, rfl⟩)).mpr (succT_lt_OF (Or.inl ⟨m, q, rfl⟩) ht hX h)

/-- 次の正則項は `t` より大きい正則項の中で最小 -/
theorem nr_leastY (t : Tm) (ht : FZNF t) (σ : Tm) (hσ : FZNF σ) (hR : IsRegY σ) (h : Lt t σ) :
    Le (nrY t) σ := by
  rcases hR with ⟨c, rfl, -⟩ | ⟨m, rfl⟩ | ⟨m, q, rfl⟩
  · exact nr_le_omY t ht c hσ h
  · exact Or.inr (nr_lt_KY ht hσ.k h)
  · exact Or.inr (nr_lt_xiY t ht hσ h)

/-! ### 前線の元は項以下 -/

theorem fr_leY {R : Tm} (hR : FZNF R) : ∀ {x w : Tm}, FZNF x → w ∈ fr R x → Le w x
  | .zero, _, _, h | .one, _, _, h | .K _, _, _, h => by simp [fr] at h
  | .plus a b, w, hx, h => by
    obtain ⟨ha, hb, -, -⟩ := hx.plus
    have hw : FZNF w := hx.of_mem_subs (fr_spec h).1
    rw [fr, List.mem_append] at h
    rcases h with h | h
    · exact Or.inr (lt_of_le_of_ltY hw ha hx (fr_leY hR ha h) (lt_plus_leftY hx))
    · exact Or.inr (lt_of_le_of_ltY hw hb hx (fr_leY hR hb h) (lt_plus_rightY hx))
  | .Om a, w, hx, h => by
    have hw : FZNF w := hx.of_mem_subs (fr_spec h).1
    rw [fr] at h
    exact Or.inr (lt_of_le_of_ltY hw hx.om.1 hx (fr_leY hR hx.om.1 h) hx.om.2.2)
  | .Xi m a, w, hx, h => by
    have hw : FZNF w := hx.of_mem_subs (fr_spec h).1
    have hwR := (fr_spec h).2
    rw [fr] at h
    by_cases hl : Lt (.Xi m a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      exact Or.inl h
    · exact Or.inr (lt_of_lt_of_leY hw hR hx hwR (le_of_not_ltY hx hR hl))
  | .Psi s p a, w, hx, h => by
    have hw : FZNF w := hx.of_mem_subs (fr_spec h).1
    have hwR := (fr_spec h).2
    rw [fr] at h
    by_cases hl : Lt (.Psi s p a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      exact Or.inl h
    · exact Or.inr (lt_of_lt_of_leY hw hR hx hwR (le_of_not_ltY hx hR hl))

end Order

end RTKA.Z
