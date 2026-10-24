import Compact.WF.FWCmp

/-! 体系全体の次の正則項 `nrY`（順序の仮定 `FWOrder` の下で）。

正則項（崩壊の添字）は `Ω_c`（`c` は後者）、`K_n`、`Ξ_n(p)`、Mahlo 添字が `0` でない `Ψ^ζ_κ(b)`。
`Ψ^0_π(a)`（`π` は `Ω_c` 以外）は `Ω` の不動点で正則でないので、次の正則項は `Ω_{Ψ+1}`。 -/

namespace RTKA.W

open Tm

/-! ### 後者 -/

theorem WNF.mk_plus {a b : Tm} (ha : WNF a) (hb : WNF b) (hap : isPrincipal a = true)
    (hb0 : b ≠ .zero) (hh : ∀ h rest, summands b = h :: rest → cmp h a ≠ .gt) :
    WNF (.plus a b) := by
  show isNF (.plus a b) = true
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq]
  refine ⟨⟨⟨⟨hap, hb0⟩, ha⟩, hb⟩, ?_⟩
  cases hs : summands b with
  | nil => exact absurd hs (summands_ne_nil hb0)
  | cons h rest =>
    have := hh h rest hs
    simpa using this

theorem succT_WNF : ∀ {z : Tm}, WNF z → WNF (succT z)
  | .zero, _ => WNF.one
  | .plus a b, hz => by
    obtain ⟨ha, hb, hap, hb0⟩ := hz.plus
    refine WNF.mk_plus ha (succT_WNF hb) hap (succT_ne_zero b) ?_
    intro h rest hs
    rw [summands_succT] at hs
    cases hs' : summands b with
    | nil => exact absurd hs' (summands_ne_nil hb0)
    | cons h' rest' =>
      rw [hs', List.cons_append, List.cons.injEq] at hs
      rw [← hs.1]
      exact hz.plus_head hs'
  | .one, hz | .K _, hz | .Om _, hz | .Xi _ _, hz | .Psi _ _ _, hz => by
    refine WNF.mk_plus hz WNF.one rfl (by intro e; cases e) ?_
    intro h rest hs
    simp only [summands, List.cons.injEq] at hs
    rw [← hs.1, cmp_principal rfl rfl]
    exact cmpP_one_ne_gtY hz rfl

theorem cmpList_succ_ne_gtY : ∀ (l m : List Tm), (∀ y, y ∈ m → WNF y ∧ isPrincipal y = true) →
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

/-- 正則項：`Ψ` の目標と `Ξ_n` の添字 `K_n` -/
def IsRegY (σ : Tm) : Prop :=
  (∃ c, σ = .Om c ∧ isSucc c = true) ∨ (∃ n, σ = .K n) ∨ (∃ n p, σ = .Xi n p) ∨
    ∃ ζ κ b, σ = .Psi ζ κ b ∧ ζ ≠ .zero

/-- 次の正則項：`t` より大きい最小の正則項 -/
def nrY : Tm → Tm
  | .plus a _ => nrY a
  | .Psi _ (.Om c) _ => .Om c
  | .Psi s p a => .Om (succT (.Psi s p a))
  | .K n => .Om (succT (.K n))
  | .Om a => .Om (succT a)
  | .Xi n a => .Om (succT (.Xi n a))
  | _ => .Om .one

theorem nrY_psi {s p a : Tm} (hp : ∀ c, p ≠ .Om c) :
    nrY (.Psi s p a) = .Om (succT (.Psi s p a)) := by
  cases p with
  | Om c => exact absurd rfl (hp c)
  | _ => rfl

theorem IsRegY.K (n : Nat) : IsRegY (.K n) := Or.inr (Or.inl ⟨n, rfl⟩)

theorem IsRegY.tgt {ξ π a : Tm} (h : WNF (.Psi ξ π a)) : IsRegY π := by
  rcases h.psi.tgt with ⟨c, rfl, hs⟩ | ⟨n, p, rfl⟩ | ⟨ζ, κ, b, rfl, hζ⟩
  · exact Or.inl ⟨c, rfl, hs⟩
  · exact Or.inr (Or.inr (Or.inl ⟨n, p, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ζ, κ, b, rfl, hζ⟩))

theorem lev_nrY : ∀ {t : Tm}, WNF t → t ≠ .zero → lev (nrY t) = lev t
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
    rcases ht.psi.tgt with ⟨c, rfl, -⟩ | ⟨n, q, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩ <;> rfl

section Order

variable [FWOrder]

/-- `z < c` なら `z + 1 ≤ c` -/
theorem succT_leY {z c : Tm} (hz : WNF z) (hc : WNF c) (h : Lt z c) : Le (succT z) c := by
  have hne : cmp (succT z) c ≠ .gt := by
    rw [cmp_eq, summands_succT]
    unfold Lt at h
    rw [cmp_eq] at h
    exact cmpList_succ_ne_gtY _ _ (summands_WNF c hc) h
  exact le_of_ne_gtY (succT_WNF hz) hc hne

omit [FWOrder] in
theorem succT_ne_principal (z : Tm) {X : Tm} (hX : isPrincipal X = true) (hX1 : X ≠ .one) :
    succT z ≠ X := by
  intro e
  subst e
  cases z <;> simp_all [succT, isPrincipal]

/-- `Ω` の不動点 `X` より小さい `z` について `z + 1 < X` -/
theorem succT_lt_OF {z X : Tm} (hX : IsOF X) (hz : WNF z) (hXF : WNF X) (h : Lt z X) :
    Lt (succT z) X := by
  rcases succT_leY hz hXF h with e | h'
  · exact absurd e (succT_ne_principal z hX.principal
      (by rcases hX with ⟨n, a, rfl⟩ | ⟨ξ, π, a, rfl, -, -⟩ <;> intro e <;> cases e))
  · exact h'

omit [FWOrder] in
/-- 先頭の項は和以下 -/
theorem head_leY {t h : Tm} {rest : List Tm} (ht : WNF t) (hs : summands t = h :: rest) :
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
theorem WNF.om_ofY {z : Tm} (hz : WNF z) (h0 : z ≠ .zero) (hK : ∀ m, z ≠ .K m)
    (hX : ¬ IsOF z) : WNF (.Om z) := by
  have hlt : Lt z (.Om z) := by
    cases hs : summands z with
    | nil => exact absurd hs (summands_ne_nil h0)
    | cons h rest =>
      have hh := summands_WNF z hz h (by rw [hs]; exact List.mem_cons_self)
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
          rcases hh.1.shape with ⟨c, rfl, rfl⟩ | hsh
          · exact (lt_psi_omY hh.1 hz).mpr
              (Or.inr (lt_of_lt_of_leY hh.1.psiOm.1 hh.1 hz (FWOrder.cx hh.1) hle))
          · rcases hle with e | e
            · exact absurd (e ▸ IsOF.psi hh.1 (notOm_of_shape hsh)) hX
            · exact (lt_OF_omG (IsOF.psi hh.1 (notOm_of_shape hsh)) hh.1 hz).mpr e
      exact lt_of_head_lt rfl hs ((lt_principal_iff hh.2 rfl).mp this)
  show isNF (.Om z) = true
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq]
  refine ⟨⟨hz, h0⟩, ?_⟩
  unfold lt
  unfold Lt at hlt
  simp [hlt]

theorem WNF.om_succT {z : Tm} (hz : WNF z) : WNF (.Om (succT z)) :=
  WNF.om_ofY (succT_WNF hz) (succT_ne_zero z) (succT_ne_K z)
    (by rintro (⟨n, a, e⟩ | ⟨ξ, π, a, e, -, -⟩) <;> cases z <;> simp [succT] at e)

theorem WNF.om_one : WNF (.Om .one) :=
  WNF.om_ofY WNF.one (by intro e; cases e) (fun _ e => by cases e)
    (by rintro (⟨n, a, e⟩ | ⟨ξ, π, a, e, -, -⟩) <;> cases e)

/-! ### 次の正則項 -/

theorem nr_specY : ∀ t : Tm, WNF t → WNF (nrY t) ∧ IsRegY (nrY t) ∧ Lt t (nrY t)
  | .zero, _ => ⟨WNF.om_one, Or.inl ⟨.one, rfl, rfl⟩, zero_lt (by intro e; cases e)⟩
  | .one, _ => ⟨WNF.om_one, Or.inl ⟨.one, rfl, rfl⟩, WNF.om_one.om.2.2⟩
  | .K _, ht => ⟨WNF.om_succT ht, Or.inl ⟨_, rfl, isSucc_succT _⟩,
      (lt_K_omY ht.k (succT_WNF ht)).mpr (lt_succT _)⟩
  | .plus a _, ht => by
    obtain ⟨ha, -, -, -⟩ := ht.plus
    obtain ⟨h1, h2, h3⟩ := nr_specY a ha
    refine ⟨h1, h2, (lt_plus_prin_iffY ht ?_).mpr h3⟩
    show isPrincipal (nrY a) = true
    rcases h2 with ⟨c, e, -⟩ | ⟨n, e⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, -⟩ <;> rw [e] <;> rfl
  | .Om a, ht => ⟨WNF.om_succT ht.om.1, Or.inl ⟨_, rfl, isSucc_succT _⟩,
      (lt_om_iffY ht.om.1 (succT_WNF ht.om.1)).mpr (lt_succT _)⟩
  | .Xi n a, ht => ⟨WNF.om_succT ht, Or.inl ⟨_, rfl, isSucc_succT _⟩,
      (lt_OF_omG (Or.inl ⟨n, a, rfl⟩) ht (succT_WNF ht)).mpr (lt_succT _)⟩
  | .Psi ξ p a, ht => by
    rcases ht.shape with ⟨c, rfl, rfl⟩ | hsh
    · exact ⟨ht.psi.piF, Or.inl ⟨c, rfl, ht.psiOm.2.2.1⟩, lt_psi_om_self c a⟩
    · rw [nrY_psi (notOm_of_shape hsh)]
      exact ⟨WNF.om_succT ht, Or.inl ⟨_, rfl, isSucc_succT _⟩,
        (lt_OF_omG (IsOF.psi ht (notOm_of_shape hsh)) ht (succT_WNF ht)).mpr (lt_succT _)⟩

theorem nr_lt_KY {t : Tm} {m : Nat} (ht : WNF t) (hm : 1 ≤ m) (h : Lt t (.K m)) :
    Lt (nrY t) (.K m) := by
  rw [lt_K_iffY (nr_specY t ht).1 hm]
  by_cases h0 : t = .zero
  · subst h0
    show 1 ≤ m
    exact hm
  · rw [lev_nrY ht h0]
    exact (lt_K_iffY ht hm).mp h

theorem nr_le_omY : ∀ t : Tm, WNF t → ∀ c : Tm, WNF (.Om c) → Lt t (.Om c) →
    Le (nrY t) (.Om c)
  | .zero, _, _, hc, _ | .one, _, _, hc, _ =>
    le_om_of_leY WNF.one hc.om.1 (one_leY hc.om.1 hc.om.2.1)
  | .K _, ht, _, hc, h =>
    le_om_of_leY (succT_WNF ht) hc.om.1 (succT_leY ht hc.om.1 ((lt_K_omY ht.k hc.om.1).mp h))
  | .plus a _, ht, c, hc, h => by
    obtain ⟨ha, -, -, -⟩ := ht.plus
    exact nr_le_omY a ha c hc (lt_transY ha ht hc (lt_plus_leftY ht) h)
  | .Om _, ht, _, hc, h =>
    le_om_of_leY (succT_WNF ht.om.1) hc.om.1
      (succT_leY ht.om.1 hc.om.1 ((lt_om_iffY ht.om.1 hc.om.1).mp h))
  | .Xi n a, ht, _, hc, h =>
    le_om_of_leY (succT_WNF ht) hc.om.1
      (succT_leY ht hc.om.1 ((lt_OF_omG (Or.inl ⟨n, a, rfl⟩) ht hc.om.1).mp h))
  | .Psi ξ p a, ht, _, hc, h => by
    rcases ht.shape with ⟨c', rfl, rfl⟩ | hsh
    · exact le_om_of_leY ht.psiOm.1 hc.om.1 ((lt_psi_omY ht hc.om.1).mp h)
    · rw [nrY_psi (notOm_of_shape hsh)]
      exact le_om_of_leY (succT_WNF ht) hc.om.1
          (succT_leY ht hc.om.1 ((lt_OF_omG (IsOF.psi ht (notOm_of_shape hsh)) ht hc.om.1).mp h))

theorem nr_lt_OFY : ∀ t : Tm, WNF t → ∀ {X : Tm}, IsOF X → WNF X → Lt t X → Lt (nrY t) X
  | .zero, _, X, hO, hX, _ | .one, _, X, hO, hX, _ => by
    have h1 : Lt .one X := by
      rcases one_leY hX (by rintro rfl; rcases hO with ⟨n, a, e⟩ | ⟨ξ, π, a, e, -, -⟩ <;> cases e)
        with e | h
      · rw [← e] at hO; rcases hO with ⟨n, a, e⟩ | ⟨ξ, π, a, e, -, -⟩ <;> cases e
      · exact h
    exact (lt_om_OFG hO).mpr h1
  | .K n, ht, X, hO, hX, h => (lt_om_OFG hO).mpr (succT_lt_OF hO ht hX h)
  | .plus a _, ht, _, hO, hX, h => by
    obtain ⟨ha, -, -, -⟩ := ht.plus
    exact nr_lt_OFY a ha hO hX (lt_transY ha ht hX (lt_plus_leftY ht) h)
  | .Om a, ht, X, hO, hX, h =>
    (lt_om_OFG hO).mpr (succT_lt_OF hO ht.om.1 hX ((lt_om_OFG hO).mp h))
  | .Xi n a, ht, X, hO, hX, h => (lt_om_OFG hO).mpr (succT_lt_OF hO ht hX h)
  | .Psi ξ p a, ht, X, hO, hX, h => by
    rcases ht.shape with ⟨c, rfl, rfl⟩ | hsh
    · -- `Ψ_c(a) < X` なら `c < X`
      have hs := ht.psiOm.2.2.1
      have hcF := ht.psiOm.1
      have hc : Lt c X := by
        rcases triY hcF hX with h' | e | h'
        · exact h'
        · subst e
          rcases hO with ⟨n, a, rfl⟩ | ⟨ξ, π, a, rfl, -, -⟩ <;> simp [isSucc, summands] at hs
        · exact absurd ((lt_OF_psiOm hO hX ht).mpr h') (Lt.asymmY ht hX h)
      exact (lt_om_OFG hO).mpr hc
    · rw [nrY_psi (notOm_of_shape hsh)]
      exact (lt_om_OFG hO).mpr (succT_lt_OF hO ht hX h)

/-- 次の正則項は `t` より大きい正則項の中で最小 -/
theorem nr_leastY (t : Tm) (ht : WNF t) (σ : Tm) (hσ : WNF σ) (hR : IsRegY σ) (h : Lt t σ) :
    Le (nrY t) σ := by
  rcases hR with ⟨c, rfl, -⟩ | ⟨m, rfl⟩ | ⟨m, q, rfl⟩ | ⟨ζ, κ, b, rfl, hζ⟩
  · exact nr_le_omY t ht c hσ h
  · exact Or.inr (nr_lt_KY ht hσ.k h)
  · exact Or.inr (nr_lt_OFY t ht (Or.inl ⟨m, q, rfl⟩) hσ h)
  · refine Or.inr (nr_lt_OFY t ht (IsOF.psi hσ ?_) hσ h)
    rcases hσ.shape with ⟨c, rfl, rfl⟩ | hsh
    · exact absurd rfl hζ
    · exact notOm_of_shape hsh

/-! ### 前線の元は項以下 -/

theorem fr_leY {R : Tm} (hR : WNF R) : ∀ {x w : Tm}, WNF x → w ∈ fr R x → Le w x
  | .zero, _, _, h | .one, _, _, h | .K _, _, _, h => by simp [fr] at h
  | .plus a b, w, hx, h => by
    obtain ⟨ha, hb, -, -⟩ := hx.plus
    have hw : WNF w := hx.of_mem_subs (fr_spec h).1
    rw [fr, List.mem_append] at h
    rcases h with h | h
    · exact Or.inr (lt_of_le_of_ltY hw ha hx (fr_leY hR ha h) (lt_plus_leftY hx))
    · exact Or.inr (lt_of_le_of_ltY hw hb hx (fr_leY hR hb h) (lt_plus_rightY hx))
  | .Om a, w, hx, h => by
    have hw : WNF w := hx.of_mem_subs (fr_spec h).1
    rw [fr] at h
    exact Or.inr (lt_of_le_of_ltY hw hx.om.1 hx (fr_leY hR hx.om.1 h) hx.om.2.2)
  | .Xi m a, w, hx, h => by
    have hw : WNF w := hx.of_mem_subs (fr_spec h).1
    have hwR := (fr_spec h).2
    rw [fr] at h
    by_cases hl : Lt (.Xi m a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      exact Or.inl h
    · exact Or.inr (lt_of_lt_of_leY hw hR hx hwR (le_of_not_ltY hx hR hl))
  | .Psi s p a, w, hx, h => by
    have hw : WNF w := hx.of_mem_subs (fr_spec h).1
    have hwR := (fr_spec h).2
    rw [fr] at h
    by_cases hl : Lt (.Psi s p a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      exact Or.inl h
    · exact Or.inr (lt_of_lt_of_leY hw hR hx hwR (le_of_not_ltY hx hR hl))

end Order

end RTKA.W
