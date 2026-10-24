import Compact.WF.FZ

/-! 断片 `FZ` の比較の道具（順序の仮定 `FZOrder` の下で）。

* 和・階・`1`・`K_n`・`Ω` との比較（`FY` の同名の補題の `FZ` 版）。
* `Ψ^ξ` どうしの比較の展開（`lt_psi_psiY`、Prop. 4.20 の (1)〜(4)）と、`Ψ^ξ` と `Ξ` の比較の展開。
* `Ω` の不動点（`Ξ_n(a)` と `Ψ^ξ_{Ξ_n(p)}(a)`）と `Ω_e`・`Ψ^0_{Ω_c}(β)` の比較。
* 崩壊の性質（`coll_psiY`・`coll_xiY`）と、比較から前線の証人を取り出す補題（`wit_c2`・`wit_c4`・`wit_psi_xi`）。 -/

namespace RTKA.Z

open Tm

/-! ### 和 -/

theorem FZNF.plus_head {a b : Tm} (h : FZNF (.plus a b)) {h' : Tm} {rest : List Tm}
    (hs : summands b = h' :: rest) : cmp h' a ≠ .gt := by
  have hn := h.1
  simp only [isNF, Bool.and_eq_true] at hn
  have h2 := hn.2
  rw [hs] at h2
  simpa using h2

theorem lt_plus_leftY {a b : Tm} (h : FZNF (.plus a b)) : Lt a (.plus a b) := by
  obtain ⟨-, -, hap, hb0⟩ := h.plus
  unfold Lt
  rw [cmp_eq, summands_principal' hap, summands_plus, cmpList_cons_cons_eq _ _ (cmpP_self a)]
  cases hs : summands b with
  | nil => exact absurd hs (summands_ne_nil hb0)
  | cons _ _ => exact cmpList_nil_cons _ _

/-- 主要項 `y` について `a + b < y` ⟺ `a < y` -/
theorem lt_plus_prin_iffY {a b y : Tm} (h : FZNF (.plus a b)) (hyp : isPrincipal y = true) :
    Lt (.plus a b) y ↔ Lt a y := by
  obtain ⟨-, -, hap, hb0⟩ := h.plus
  rw [lt_principal_iff hap hyp]
  unfold Lt
  rw [cmp_eq, summands_principal' hyp, summands_plus]
  cases e : cmpP a y with
  | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]
  | eq =>
    rw [cmpList_cons_cons_eq _ _ e]
    cases hs : summands b with
    | nil => exact absurd hs (summands_ne_nil hb0)
    | cons _ _ => rw [cmpList_cons_nil]; simp
  | gt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]

/-- 底（同じ階の最小元）より小さい同じ階の項はない -/
theorem not_lt_isBotY {x y : Tm} (hl : lev x = lev y) (hy : isBot y = true) (hx : FZNF x)
    (hyF : FZNF y) : cmpP x y ≠ .lt := by
  rw [cmpP.eq_def]
  simp only [hl, Nat.lt_irrefl, ↓reduceIte]
  cases x <;> cases y <;> simp_all [isBot]
  all_goals first
    | (split <;> simp)
    | (have := hyF.k; simp only [lev] at hl; omega)

theorem lev_posY : ∀ {t : Tm}, FZNF t → t ≠ .zero → 1 ≤ lev t
  | .zero, _, h => absurd rfl h
  | .one, _, _ => Nat.le_refl _
  | .K _, _, _ => by simp only [lev]; omega
  | .plus a _, ht, _ => by
    obtain ⟨ha, -, hap, -⟩ := ht.plus
    have : a ≠ .zero := by intro e; subst e; simp [isPrincipal] at hap
    show 1 ≤ lev a
    exact lev_posY ha this
  | .Om a, ht, _ => by show 1 ≤ lev a; exact lev_posY ht.om.1 ht.om.2.1
  | .Xi _ _, ht, _ => ht.xi.1
  | .Psi _ pi _, ht, _ => by
    have hP := ht.psi
    show 1 ≤ lev pi
    exact lev_posY hP.piF (by rcases hP.tgt with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ <;> intro e <;> cases e)

/-- `x < K_m` なら `x` の階は `m` 以下 -/
theorem lev_le_of_lt_KY {z : Tm} {n : Nat} (hn : 1 ≤ n) (hz : FZNF z) (h : Lt z (.K n)) :
    lev z ≤ n := by
  cases hs : summands z with
  | nil =>
    have : z = .zero := by cases z <;> simp_all [summands]
    subst this
    simp [lev]
  | cons x xs =>
    have hx := summands_FZNF z hz x (by rw [hs]; exact List.mem_cons_self)
    unfold Lt at h
    rw [cmp_eq, hs, show summands (Tm.K n) = [.K n] from rfl] at h
    have hl := lev_head hs
    rcases cmpList_lt_cases h with e | ⟨-, e'⟩
    · have := lev_le_of_cmpP_lt e
      simp only [lev] at this
      rcases Nat.lt_or_eq_of_le this with h1 | h1
      · rw [← hl]; omega
      · exact absurd e (not_lt_isBotY (by simp only [lev]; exact h1) rfl hx.1 (FZNF.K' hn))
    · cases xs with
      | nil => rw [cmpList_nil_nil] at e'; cases e'
      | cons _ _ => rw [cmpList_cons_nil] at e'; cases e'

/-- `x < K_m` ⟺ `x` の階が `m` 以下 -/
theorem lt_K_iffY {x : Tm} {m : Nat} (hx : FZNF x) (hm : 1 ≤ m) : Lt x (.K m) ↔ lev x ≤ m :=
  ⟨lev_le_of_lt_KY hm hx, fun h => lt_of_lev_lt' (by simp only [lev]; omega)⟩

theorem cmpP_one_ne_gtY {h : Tm} (hF : FZNF h) (hp : isPrincipal h = true) :
    cmpP .one h ≠ .gt := by
  have hl : 1 ≤ lev h := lev_posY hF (by intro e; subst e; simp [isPrincipal] at hp)
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · rw [cmpP_of_lev_lt (by simp only [lev]; exact hl)]; decide
  · rw [cmpP.eq_def]
    simp only [lev, ← hl, Nat.lt_irrefl, ↓reduceIte]
    cases h <;> simp

theorem lt_oneY {u : Tm} (hu : FZNF u) (h : Lt u .one) : u = .zero := by
  cases hs : summands u with
  | nil => cases u <;> simp_all [summands]
  | cons x xs =>
    exfalso
    unfold Lt at h
    rw [cmp_eq, hs, show summands Tm.one = [.one] from rfl] at h
    have hx := summands_FZNF u hu x (by rw [hs]; exact List.mem_cons_self)
    have hl : 1 ≤ lev x := lev_posY hx.1 (by intro e; subst e; simp [isPrincipal] at hx)
    rcases cmpList_lt_cases h with e | ⟨e, e'⟩
    · rcases Nat.lt_or_eq_of_le hl with hl | hl
      · rw [cmpP_of_lev_gt (by simp only [lev]; exact hl)] at e; cases e
      · exact not_lt_isBotY (by simp only [lev]; exact hl.symm) rfl hx.1 FZNF.one e
    · cases xs with
      | nil => rw [cmpList_nil_nil] at e'; cases e'
      | cons _ _ => rw [cmpList_cons_nil] at e'; cases e'

section Order

variable [FZOrder]

theorem lt_plus_rightY : ∀ {a b : Tm}, FZNF (.plus a b) → Lt b (.plus a b)
  | a, b, h => by
    obtain ⟨-, hb, hap, hb0⟩ := h.plus
    cases hs : summands b with
    | nil => exact absurd hs (summands_ne_nil hb0)
    | cons x xs =>
      have hxa := h.plus_head hs
      have hx := summands_FZNF b hb x (by rw [hs]; exact List.mem_cons_self)
      have hxa' : cmpP x a ≠ .gt := by rwa [← cmp_principal hx.2 hap]
      unfold Lt
      rw [cmp_eq, hs, summands_plus, hs]
      cases e : cmpP x a with
      | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]
      | gt => exact absurd e hxa'
      | eq =>
        rw [cmpList_cons_cons_eq _ _ e]
        have hxe : x = a :=
          eq_of_cmpP_eqY hx.1 (summands_FZNF _ h a (by simp [summands])).1 hx.2 hap e
        subst hxe
        cases b with
        | zero => exact absurd rfl hb0
        | plus p q =>
          rw [summands_plus, List.cons.injEq] at hs
          obtain ⟨rfl, hq⟩ := hs
          have := lt_plus_rightY hb
          unfold Lt at this
          rw [cmp_eq, summands_plus] at this
          rwa [← hq]
        | _ =>
          simp only [summands, List.cons.injEq] at hs
          rw [← hs.2]
          exact cmpList_nil_cons _ _

/-- 主要項 `x` について `x < a + b` ⟺ `x ≤ a` -/
theorem lt_prin_plus_iffY {x a b : Tm} (hx : FZNF x) (hxp : isPrincipal x = true)
    (h : FZNF (.plus a b)) : Lt x (.plus a b) ↔ Le x a := by
  obtain ⟨ha, -, hap, hb0⟩ := h.plus
  have hL : Lt x (.plus a b) ↔ cmpP x a ≠ .gt := by
    unfold Lt
    rw [cmp_eq, summands_principal' hxp, summands_plus]
    cases e : cmpP x a with
    | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]; simp
    | eq =>
      rw [cmpList_cons_cons_eq _ _ e]
      cases hs : summands b with
      | nil => exact absurd hs (summands_ne_nil hb0)
      | cons _ _ => rw [cmpList_nil_cons]; simp
    | gt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]; simp
  rw [hL]
  constructor
  · intro h'
    exact le_of_ne_gtY hx ha (by rwa [cmp_principal hxp hap])
  · intro h'
    rw [← cmp_principal hxp hap]
    exact ne_gt_of_le h'

theorem lt_plus_plus_neY {a b a' b' : Tm} (h : FZNF (.plus a b)) (h' : FZNF (.plus a' b'))
    (hne : a ≠ a') : Lt (.plus a b) (.plus a' b') ↔ Lt a a' := by
  obtain ⟨ha, -, hap, -⟩ := h.plus
  obtain ⟨ha', -, hap', -⟩ := h'.plus
  have e : cmpP a a' ≠ .eq := fun e => hne (eq_of_cmpP_eqY ha ha' hap hap' e)
  rw [lt_principal_iff hap hap']
  unfold Lt
  rw [cmp_eq, summands_plus, summands_plus, cmpList_cons_cons_ne _ _ e]

theorem one_leY {c : Tm} (hc : FZNF c) (h0 : c ≠ .zero) : Le .one c := by
  rcases triY FZNF.one hc with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact absurd (lt_oneY hc h) h0

/-! ### `Ω` -/

theorem lt_om_iffY {a b : Tm} (ha : FZNF a) (hb : FZNF b) : Lt (.Om a) (.Om b) ↔ Lt a b := by
  rcases Nat.lt_trichotomy (lev a) (lev b) with h | h | h
  · constructor
    · intro _; exact lt_of_lev_lt' h
    · intro _
      rw [lt_principal_iff rfl rfl, cmpP_of_lev_lt (by simp only [lev]; exact h)]
  · exact lt_om_om a b h
  · constructor
    · intro h'
      rw [lt_principal_iff rfl rfl, cmpP_of_lev_gt (by simp only [lev]; exact h)] at h'
      cases h'
    · intro h'; exact absurd (lt_of_lev_lt' h) (Lt.asymmY ha hb h')

theorem le_om_of_leY {a b : Tm} (ha : FZNF a) (hb : FZNF b) (h : Le a b) :
    Le (.Om a) (.Om b) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr ((lt_om_iffY ha hb).mpr h)

omit [FZOrder] in
theorem FZNF.psiOm {ξ c a : Tm} (h : FZNF (.Psi ξ (.Om c) a)) :
    FZNF c ∧ FZNF (.Om c) ∧ isSucc c = true ∧ FZNF a ∧ inC a a (.Om c) = true ∧ ξ = .zero := by
  have hP := h.psi
  rcases hP.m with ⟨c', e, hξ⟩ | ⟨n, p, e, -⟩
  · cases e
    exact ⟨hP.piF.om.1, hP.piF, by rcases hP.tgt with ⟨c'', e', hs⟩ | ⟨n, p, e'⟩ <;> cases e'; exact hs, hP.aF, hP.Ca, hξ⟩
  · cases e

theorem lt_psi_omY {c β e : Tm} (hψ : FZNF (.Psi .zero (.Om c) β)) (he : FZNF e) :
    Lt (.Psi .zero (.Om c) β) (.Om e) ↔ Le c e := by
  have hc := hψ.psiOm.1
  rcases Nat.lt_trichotomy (lev e) (lev c) with hl | hl | hl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · rintro (rfl | h)
      · exact absurd hl (Nat.lt_irrefl _)
      · exact absurd (lev_le_of_lt_gen h) (by omega)
  · rw [lt_psi_om e c β hl]
    constructor
    · intro h; exact le_of_not_ltY he hc h
    · intro h; exact not_lt_of_leY hc he h
  · constructor
    · intro _; exact Or.inr (lt_of_lev_lt' hl)
    · intro _; exact lt_of_lev_lt' (by simp only [lev]; exact hl)

omit [FZOrder] in
theorem lt_om_psiY {e c β : Tm} (hψ : FZNF (.Psi .zero (.Om c) β)) :
    Lt (.Om e) (.Psi .zero (.Om c) β) ↔ Lt e c := by
  have hc := hψ.psiOm.1
  rcases Nat.lt_trichotomy (lev e) (lev c) with hl | hl | hl
  · constructor
    · intro _; exact lt_of_lev_lt' hl
    · intro _; exact lt_of_lev_lt' (by simp only [lev]; exact hl)
  · exact lt_om_psi e c β hl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · intro h; have := lev_le_of_lt_gen h; exfalso; omega

theorem lt_K_omY {m : Nat} {e : Tm} (hm : 1 ≤ m) (he : FZNF e) :
    Lt (.K m) (.Om e) ↔ Lt (.K m) e := by
  rcases Nat.lt_trichotomy (lev e) (m + 1) with hl | hl | hl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
  · by_cases hek : e = .K m
    · subst hek
      constructor
      · intro h
        rw [lt_principal_iff rfl rfl, cmpP.eq_def] at h
        simp only [lev, Nat.lt_irrefl, ↓reduceIte] at h
        simp at h
      · intro h; exact absurd h (Lt.irrefl _)
    · constructor
      · intro _
        rcases triY (FZNF.K' hm) he with h | h | h
        · exact h
        · exact absurd h.symm hek
        · have := (lt_K_iffY he hm).mp h; exfalso; omega
      · intro _
        rw [lt_principal_iff rfl rfl, cmpP.eq_def]
        simp only [lev, hl, Nat.lt_irrefl, ↓reduceIte]
        simp [hek]
  · constructor
    · intro _; exact lt_of_lev_lt' (by simp only [lev]; omega)
    · intro _; exact lt_of_lev_lt' (by simp only [lev]; omega)

end Order

/-! ### `Ψ^ξ` と目標・`Ξ` の比較の展開（順序の仮定なし） -/

theorem lt_psi_targetY {ξ π a : Tm} (h : FZNF (.Psi ξ π a)) : Lt (.Psi ξ π a) π := by
  rcases h.psi.m with ⟨c, rfl, rfl⟩ | ⟨n, p, rfl, -, -⟩
  · exact lt_psi_om_self c a
  · rw [lt_principal_iff rfl rfl, cmpP_psi_xi (pi := .Xi n p) (m := n) rfl, psiLtXi_eq, cmp_self]
    simp

/-- 同じ階の `Ψ^ξ_π(a)` と `Ξ_n(b)` の比較（Prop. 4.21） -/
theorem lt_psi_xiY {ξ π a b : Tm} {n : Nat} (hl : lev π = n) :
    Lt (.Psi ξ π a) (.Xi n b) ↔
      cmp π (.Xi n b) ≠ .gt ∨ (Lt b a ∧ inC b a (.Psi ξ π a) = false) := by
  rw [lt_principal_iff rfl rfl, cmpP_psi_xi hl, psiLtXi_eq, ite_lt_gt_eq_lt]
  unfold Lt
  cases cmp π (Tm.Xi n b) <;> cases cmp b a <;> cases inC b a (Tm.Psi ξ π a) <;> simp

theorem lt_xi_psiY {ξ π a b : Tm} {n : Nat} (hl : lev π = n) :
    Lt (.Xi n b) (.Psi ξ π a) ↔ ¬ Lt (.Psi ξ π a) (.Xi n b) := by
  rw [lt_principal_iff rfl rfl, lt_principal_iff rfl rfl, cmpP_xi_psi hl, cmpP_psi_xi hl]
  cases psiLtXi (Tm.Psi ξ π a) (.Xi n b) <;> simp

/-- 同じ階の `Ψ` どうしの比較の展開（`cmpPsi`、Prop. 4.20 の (1)〜(4)） -/
theorem lt_psi_psiY {ξ π a σ κ b : Tm} (hl : lev π = lev κ)
    (hne : Tm.Psi ξ π a ≠ .Psi σ κ b) :
    Lt (.Psi ξ π a) (.Psi σ κ b) ↔
      ¬ Lt (.Psi σ κ b) π ∨
        (Lt (.Psi σ κ b) π ∧ Lt (.Psi ξ π a) κ ∧
          ((Lt a b ∧ inC a b (.Psi σ κ b) = true ∧ inC ξ b (.Psi σ κ b) = true ∧
              inC π b (.Psi σ κ b) = true) ∨
            (cmp b a ≠ .gt ∧ ¬ (inC b a (.Psi ξ π a) = true ∧ inC σ a (.Psi ξ π a) = true ∧
              inC κ a (.Psi ξ π a) = true)) ∨
            (cmp a b = .eq ∧ κ = π ∧ Lt ξ σ ∧ inC ξ b (.Psi σ κ b) = true) ∨
            (Lt σ ξ ∧ inC σ ξ (.Psi ξ π a) = false))) := by
  rw [lt_principal_iff rfl rfl, cmpP_psi_psi hl, cmpPsi.eq_def]
  simp only []
  unfold Lt
  by_cases h1 : cmp (Tm.Psi σ κ b) π = .lt
  · by_cases h2 : cmp (Tm.Psi ξ π a) κ = .lt
    · have hne' : (Tm.Psi ξ π a == Tm.Psi σ κ b) = false := by simpa using hne
      simp only [hne', h1, h2, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        ite_lt_gt_eq_lt, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
        Bool.not_eq_true', and_true, not_true_eq_false, false_or, true_and]
      constructor
      · rintro (((h | h) | h) | h)
        · exact Or.inl ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
        · refine Or.inr (Or.inl ⟨h.1, fun ⟨e1, e2, e3⟩ => ?_⟩)
          rw [e1, e2, e3] at h
          simp at h
        · exact Or.inr (Or.inr (Or.inl ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩))
        · exact Or.inr (Or.inr (Or.inr h))
      · rintro (h | ⟨h, hn⟩ | h | h)
        · exact Or.inl (Or.inl (Or.inl ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩))
        · refine Or.inl (Or.inl (Or.inr ⟨h, ?_⟩))
          cases e1 : inC b a (Tm.Psi ξ π a) <;> cases e2 : inC σ a (Tm.Psi ξ π a) <;>
            cases e3 : inC κ a (Tm.Psi ξ π a) <;> simp_all
        · exact Or.inl (Or.inr ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩)
        · exact Or.inr h
    · simp [hne, h1, h2]
  · simp [hne, h1]

section Order

variable [FZOrder]

/-! ### `Ω` の不動点 -/

/-- `Ω` の不動点になる主要項（`Ξ_n(a)` と `Ψ^ξ_{Ξ_n(p)}(a)`） -/
def IsOF (X : Tm) : Prop := (∃ n a, X = .Xi n a) ∨ ∃ ξ n p a, X = .Psi ξ (.Xi n p) a

omit [FZOrder] in
theorem IsOF.principal {X : Tm} (h : IsOF X) : isPrincipal X = true := by
  rcases h with ⟨n, a, rfl⟩ | ⟨ξ, n, p, a, rfl⟩ <;> rfl

omit [FZOrder] in
theorem cmpP_om_OF {e X : Tm} (hX : IsOF X) (hl : lev e = lev X) :
    cmpP (.Om e) X = cmp e X := by
  rcases hX with ⟨n, a, rfl⟩ | ⟨ξ, n, p, a, rfl⟩
  · exact cmpP_om_xi hl
  · rw [cmpP.eq_def]
    have hl' : lev e = n := hl
    simp only [lev, hl', Nat.lt_irrefl, ↓reduceIte]
    rw [cmpOmX.eq_def]
    simp [omegaFixed, isInacc]

omit [FZOrder] in
theorem cmpP_OF_om {e X : Tm} (hX : IsOF X) (hl : lev e = lev X) :
    cmpP X (.Om e) = (cmp e X).swap := by
  rcases hX with ⟨n, a, rfl⟩ | ⟨ξ, n, p, a, rfl⟩
  · exact cmpP_xi_om hl
  · rw [cmpP.eq_def]
    have hl' : lev e = n := hl
    simp only [lev, hl', Nat.lt_irrefl, ↓reduceIte]
    rw [cmpOmX.eq_def]
    simp [omegaFixed, isInacc]

omit [FZOrder] in
theorem lt_om_OFG {e X : Tm} (hX : IsOF X) :
    Lt (.Om e) X ↔ Lt e X := by
  rcases Nat.lt_trichotomy (lev e) (lev X) with hl | hl | hl
  · exact ⟨fun _ => lt_of_lev_lt' hl, fun _ => lt_of_lev_lt' (by simp only [lev]; exact hl)⟩
  · rw [lt_principal_iff rfl hX.principal, cmpP_om_OF hX hl]; rfl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · intro h; have := lev_le_of_lt_gen h; exfalso; omega

theorem lt_OF_omG {e X : Tm} (hX : IsOF X) (hXF : FZNF X) (he : FZNF e) :
    Lt X (.Om e) ↔ Lt X e := by
  rcases Nat.lt_trichotomy (lev e) (lev X) with hl | hl | hl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · intro h; have := lev_le_of_lt_gen h; exfalso; omega
  · rw [lt_principal_iff hX.principal rfl, cmpP_OF_om hX hl]
    unfold Lt
    rw [FZOrder.swap hXF he]
    cases cmp X e <;> simp
  · exact ⟨fun _ => lt_of_lev_lt' hl, fun _ => lt_of_lev_lt' (by simp only [lev]; exact hl)⟩

/-- `Ω` の不動点 `X` と `Ψ^0_{Ω_c}(β)`：`X < Ψ_c(β)` ⟺ `X < c`（KL） -/
theorem lt_OF_psiOm {X c β : Tm} (hX : IsOF X) (hXF : FZNF X)
    (hψ : FZNF (.Psi .zero (.Om c) β)) :
    Lt X (.Psi .zero (.Om c) β) ↔ Lt X c := by
  obtain ⟨hc, hσ, -⟩ := hψ.psiOm
  constructor
  · intro h
    exact (lt_OF_omG hX hXF hc).mp (lt_transY hXF hψ hσ h (lt_psi_om_self c β))
  · intro h
    exact lt_transY hXF hc hψ h (FZOrder.cx hψ)

/-! ### `Ξ` どうし -/

/-- 同じ階の `Ξ` どうしの比較（Lemma 4.14） -/
theorem lt_xi_xi_sameY {n : Nat} {α β : Tm} (hα : FZNF α) (hβ : FZNF β) (hne : α ≠ β) :
    Lt (.Xi n α) (.Xi n β) ↔
      (Lt α β ∧ inC α β (.Xi n β) = true) ∨ (Lt β α ∧ inC β α (.Xi n α) = false) := by
  rw [lt_principal_iff rfl rfl, cmpP_xi_xi, xiLtXi_eq]
  simp only [hne, ↓reduceIte]
  rw [ite_lt_gt_eq_lt]
  rcases triY hα hβ with h | h | h
  · have h' : cmp β α = .gt := by unfold Lt at h; rw [FZOrder.swap hα hβ, h]; rfl
    unfold Lt at h
    simp [h, h', Lt]
  · exact absurd h hne
  · have h' : cmp α β = .gt := by unfold Lt at h; rw [FZOrder.swap hβ hα, h]; rfl
    unfold Lt at h
    cases inC β α (Tm.Xi n α) <;> simp [h, h', Lt]

/-! ### 崩壊の性質 -/

/-- `Ψ^ξ_π(γ)` の崩壊の性質：`z ∈ C(γ, Ψ^ξ_π(γ))` で `z < π` なら `z < Ψ^ξ_π(γ)` -/
theorem coll_psiY {ξ π γ : Tm} (ht : FZNF (.Psi ξ π γ)) :
    ∀ z, FZNF z → inC z γ (.Psi ξ π γ) = true → Lt z π → Lt z (.Psi ξ π γ) := by
  have hπ := ht.psi.piF
  have hm := ht.psi.m
  intro z
  induction z with
  | zero => intros; exact zero_lt (by intro e; cases e)
  | one =>
    intro _ _ _
    rcases one_leY ht (by intro e; cases e) with e | h
    · cases e
    · exact h
  | K m =>
    intro hz _ hlt
    rcases triY hz ht with h | e | h
    · exact h
    · cases e
    · exfalso
      have h1 := (lt_K_iffY ht hz.k).mp h
      have h2 := lev_le_of_lt_gen hlt
      simp only [lev] at h1 h2
      omega
  | plus a b iha _ =>
    intro hz hin hlt
    rw [inC_plus, Bool.and_eq_true] at hin
    obtain ⟨haF, -, -, -⟩ := hz.plus
    have hao : Lt a π := lt_transY haF hz hπ (lt_plus_leftY hz) hlt
    exact (lt_plus_prin_iffY hz rfl).mpr (iha haF hin.1 hao)
  | Om e ihe =>
    intro hz hin hlt
    rw [inC_om] at hin
    have heF := hz.om.1
    rcases hm with ⟨c, rfl, rfl⟩ | ⟨n, p, rfl, -, -⟩
    · exact (lt_om_psiY ht).mpr ((lt_om_iffY heF hπ.om.1).mp hlt)
    · exact (lt_om_OFG (Or.inr ⟨ξ, n, p, γ, rfl⟩)).mpr
        (ihe heF hin (lt_transY heF hz hπ hz.om.2.2 hlt))
  | Xi m f _ =>
    intro hz hin hlt
    rcases inC_xi_iff.mp hin with h | ⟨hf, -⟩
    · exact h
    rcases hm with ⟨c, rfl, rfl⟩ | ⟨n, p, rfl, -, -⟩
    · exact (lt_OF_psiOm (Or.inl ⟨m, f, rfl⟩) hz ht).mpr
        ((lt_OF_omG (Or.inl ⟨m, f, rfl⟩) hz hπ.om.1).mp hlt)
    · have hl := lev_le_of_lt_gen hlt
      simp only [lev] at hl
      rcases Nat.lt_or_eq_of_le hl with hl | hl
      · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
      · subst hl
        have hgt : cmp (.Xi m p) (.Xi m f) = .gt := by
          unfold Lt at hlt; rw [FZOrder.swap hz hπ, hlt]; rfl
        rw [lt_xi_psiY (π := .Xi m p) (n := m) rfl, lt_psi_xiY (π := .Xi m p) (n := m) rfl]
        rintro (h | ⟨-, h⟩)
        · exact h hgt
        · rw [hf] at h; cases h
  | Psi s κ β _ _ _ =>
    intro hz hin hlt
    rcases inC_psi_iff.mp hin with h | ⟨hκ, hs, hβ, hβγ⟩
    · exact h
    have hl := lev_le_of_lt_gen hlt
    simp only [lev] at hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · have hne : Tm.Psi s κ β ≠ .Psi ξ π γ := by
        intro e; cases e; exact Lt.irrefl _ hβγ
      rw [lt_psi_psiY hl hne]
      by_cases h1 : Lt (.Psi ξ π γ) κ
      · exact Or.inr ⟨h1, hlt, Or.inl ⟨hβγ, hβ, hs, hκ⟩⟩
      · exact Or.inl h1

/-- `Ξ_n(γ)` の崩壊の性質：`z ∈ C(γ, Ξ_n(γ))` で `z < K_n` なら `z < Ξ_n(γ)` -/
theorem coll_xiY {n : Nat} {γ : Tm} (ht : FZNF (.Xi n γ)) :
    ∀ z, FZNF z → inC z γ (.Xi n γ) = true → Lt z (.K n) → Lt z (.Xi n γ) := by
  obtain ⟨hn, hγF, -, -, -⟩ := ht.xi
  have hK := FZNF.K' hn
  intro z
  induction z with
  | zero => intros; exact zero_lt (by intro e; cases e)
  | one =>
    intro _ _ _
    rcases one_leY ht (by intro e; cases e) with e | h
    · cases e
    · exact h
  | K m =>
    intro hz _ hlt
    rcases triY hz ht with h | e | h
    · exact h
    · cases e
    · exfalso
      have h1 := (lt_K_iffY hz hn).mp hlt
      have h2 := (lt_K_iffY ht hz.k).mp h
      simp only [lev] at h1 h2
      omega
  | plus a b iha _ =>
    intro hz hin hlt
    rw [inC_plus, Bool.and_eq_true] at hin
    obtain ⟨haF, -, -, -⟩ := hz.plus
    have hao : Lt a (.K n) := lt_transY haF hz hK (lt_plus_leftY hz) hlt
    exact (lt_plus_prin_iffY hz rfl).mpr (iha haF hin.1 hao)
  | Om g ihg =>
    intro hz hin hlt
    rw [inC_om] at hin
    have hgF := hz.om.1
    exact (lt_om_OFG (Or.inl ⟨n, γ, rfl⟩)).mpr
      (ihg hgF hin (lt_transY hgF hz hK hz.om.2.2 hlt))
  | Xi m f _ =>
    intro hz hin hlt
    rcases inC_xi_iff.mp hin with h | ⟨hf, hfγ⟩
    · exact h
    have hl := (lt_K_iffY hz hn).mp hlt
    simp only [lev] at hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · subst hl
      have hne : f ≠ γ := fun e => by subst e; exact Lt.irrefl _ hfγ
      exact (lt_xi_xi_sameY hz.xi.2.1 hγF hne).mpr (Or.inl ⟨hfγ, hf⟩)
  | Psi s κ β _ ihκ _ =>
    intro hz hin hlt
    have hκF := hz.psi.piF
    rcases inC_psi_iff.mp hin with h | ⟨hκ, -, -, -⟩
    · exact h
    have hl := (lt_K_iffY hz hn).mp hlt
    simp only [lev] at hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · have hκK : Lt κ (.K n) := (lt_K_iffY hκF hn).mpr (by omega)
      have hκX := ihκ hκF hκ hκK
      refine (lt_psi_xiY hl).mpr (Or.inl ?_)
      unfold Lt at hκX
      rw [hκX]
      decide

/-! ### 前線による言い換え -/

theorem inC_frY {R g0 g d x : Tm} (hx : FZNF x) (hR : FZNF R) (hd : FZNF d) (hg0 : FZNF g0)
    (hg : FZNF g) (h0 : inC x g0 R = true) (hdR : Le d R) (hgg : Le g0 g) :
    inC x g d = true ↔ ∀ w, w ∈ fr R x → inC w g d = true :=
  inC_fr x h0 (fun _ hw hn hwd => hn (lt_of_lt_of_leY (hx.of_mem_subs hw) hd hR hwd hdR))
    (fun _ hv hvg => lt_of_lt_of_leY (hx.of_mem_subs hv) hg0 hg hvg hgg)

/-- `a ∈ C(a, Ψ^ξ_π(a))` -/
theorem inC_arg_own {ξ π a : Tm} (h : FZNF (.Psi ξ π a)) :
    inC a a (.Psi ξ π a) = true := by
  have hP := h.psi
  exact (inC_frY hP.aF hP.piF h hP.aF hP.aF hP.Ca (Or.inr (lt_psi_targetY h)) (Or.inl rfl)).mpr
    (fun w hw => inC_of_lt_node (fr_node hw) (FZOrder.k2 h w hw))

/-- `π ∈ C(a, Ψ^ξ_π(a))` -/
theorem inC_tgt_own {ξ π a : Tm} (h : FZNF (.Psi ξ π a)) :
    inC π a (.Psi ξ π a) = true := by
  have hP := h.psi
  exact (inC_frY hP.piF hP.piF h hP.aF hP.aF hP.Cpi (Or.inr (lt_psi_targetY h)) (Or.inl rfl)).mpr
    (fun w hw => inC_of_lt_node (fr_node hw) (FZOrder.k2t h w hw))

/-- `ξ ∈ C(a, Ψ^ξ_π(a))` -/
theorem inC_mahlo_own {ξ π a : Tm} (h : FZNF (.Psi ξ π a)) :
    inC ξ a (.Psi ξ π a) = true := by
  have hP := h.psi
  exact (inC_frY hP.xiF hP.piF h hP.aF hP.aF hP.Cxi (Or.inr (lt_psi_targetY h)) (Or.inl rfl)).mpr
    (fun w hw => inC_of_lt_node (fr_node hw) (FZOrder.k2s h w hw))

/-- 同じ階の `Ξ_n` どうしの比較の前線による言い換え -/
theorem ff_xiY {n : Nat} {α β : Tm} (hx : FZNF (.Xi n α)) (hy : FZNF (.Xi n β)) (hne : α ≠ β) :
    Lt (.Xi n α) (.Xi n β) ↔
      (Lt α β ∧ ∀ w, w ∈ fr (.K n) α → Lt w (.Xi n β)) ∨
        (Lt β α ∧ ∃ w, w ∈ fr (.K n) β ∧ ¬ Lt w (.Xi n α)) := by
  obtain ⟨hn, hαF, -, -, hαC⟩ := hx.xi
  obtain ⟨-, hβF, -, -, hβC⟩ := hy.xi
  have hK := FZNF.K' hn
  have hxK : Lt (.Xi n α) (.K n) := (lt_K_iffY hx hn).mpr (Nat.le_refl _)
  have hyK : Lt (.Xi n β) (.K n) := (lt_K_iffY hy hn).mpr (Nat.le_refl _)
  have collx : ∀ w, w ∈ fr (.K n) β → inC w α (.Xi n α) = true → Lt w (.Xi n α) :=
    fun w hw h => coll_xiY hx w (hβF.of_mem_subs (fr_spec hw).1) h (fr_spec hw).2
  have colly : ∀ w, w ∈ fr (.K n) α → inC w β (.Xi n β) = true → Lt w (.Xi n β) :=
    fun w hw h => coll_xiY hy w (hαF.of_mem_subs (fr_spec hw).1) h (fr_spec hw).2
  rw [lt_xi_xi_sameY hαF hβF hne]
  constructor
  · rintro (⟨hab, h⟩ | ⟨hba, h⟩)
    · exact Or.inl ⟨hab, (fr_inC_iff colly).mp
        ((inC_frY hαF hK hy hαF hβF hαC (Or.inr hyK) (Or.inr hab)).mp h)⟩
    · refine Or.inr ⟨hba, (fr_inC_false_iff collx).mp ?_⟩
      intro h'
      rw [(inC_frY hβF hK hx hβF hαF hβC (Or.inr hxK) (Or.inr hba)).mpr h'] at h
      cases h
  · rintro (⟨hab, h⟩ | ⟨hba, h⟩)
    · exact Or.inl ⟨hab, (inC_frY hαF hK hy hαF hβF hαC (Or.inr hyK) (Or.inr hab)).mpr
        ((fr_inC_iff colly).mpr h)⟩
    · refine Or.inr ⟨hba, ?_⟩
      cases e : inC β α (Tm.Xi n α)
      · rfl
      · exact absurd ((inC_frY hβF hK hx hβF hαF hβC (Or.inr hxK) (Or.inr hba)).mp e)
          ((fr_inC_false_iff collx).mpr h)

/-! ### 前線の証人 -/

/-- `(2)`：`a ≤ d` で `a`・`ξ`・`π` のどれかが `C(d, x)` に入らない（`x < π`）なら、`Ψ^ξ_π(a)` の引数・目標・
    Mahlo 添字の前線（`π` について）に `x` 未満でない元がある -/
theorem wit_c2 {ξ π a x d : Tm} (hy : FZNF (.Psi ξ π a)) (hx : FZNF x) (hd : FZNF d)
    (had : Le a d) (hxπ : Lt x π)
    (hn : ¬ (inC a d x = true ∧ inC ξ d x = true ∧ inC π d x = true)) :
    ∃ w, (w ∈ fr π a ∨ w ∈ fr π π ∨ w ∈ fr π ξ) ∧ ¬ Lt w x := by
  have hP := hy.psi
  by_cases ha : ∀ w, w ∈ fr π a → Lt w x
  · by_cases hπ : ∀ w, w ∈ fr π π → Lt w x
    · by_cases hξ : ∀ w, w ∈ fr π ξ → Lt w x
      · exfalso
        apply hn
        exact ⟨(inC_frY hP.aF hP.piF hx hP.aF hd hP.Ca (Or.inr hxπ) had).mpr
            (fun w hw => inC_of_lt_node (fr_node hw) (ha w hw)),
          (inC_frY hP.xiF hP.piF hx hP.aF hd hP.Cxi (Or.inr hxπ) had).mpr
            (fun w hw => inC_of_lt_node (fr_node hw) (hξ w hw)),
          (inC_frY hP.piF hP.piF hx hP.aF hd hP.Cpi (Or.inr hxπ) had).mpr
            (fun w hw => inC_of_lt_node (fr_node hw) (hπ w hw))⟩
      · obtain ⟨w, hw, hw'⟩ := exists_of_not_forall_mem _ hξ
        exact ⟨w, Or.inr (Or.inr hw), hw'⟩
    · obtain ⟨w, hw, hw'⟩ := exists_of_not_forall_mem _ hπ
      exact ⟨w, Or.inr (Or.inl hw), hw'⟩
  · obtain ⟨w, hw, hw'⟩ := exists_of_not_forall_mem _ ha
    exact ⟨w, Or.inl hw, hw'⟩

/-- `(4)`：`ξ < σ` で `ξ ∉ C(σ, x)`（`x < y = Ψ^ξ_π(a)`）なら、`ξ` の前線（`y` について）に `x` 未満でない
    元がある（`ξ ∈ C(ξ, y)` を使う） -/
theorem wit_c4 {ξ π a x σ : Tm} (hy : FZNF (.Psi ξ π a)) (hx : FZNF x) (hσ : FZNF σ)
    (hxy : Lt x (.Psi ξ π a)) (hξσ : Lt ξ σ) (hn : inC ξ σ x = false) :
    ∃ w, w ∈ fr (.Psi ξ π a) ξ ∧ ¬ Lt w x := by
  have hP := hy.psi
  by_cases h : ∀ w, w ∈ fr (.Psi ξ π a) ξ → Lt w x
  · exfalso
    rw [(inC_frY hP.xiF hy hx hP.xiF hσ (FZOrder.ms hy) (Or.inr hxy) (Or.inr hξσ)).mpr
      (fun w hw => inC_of_lt_node (fr_node hw) (h w hw))] at hn
    cases hn
  · exact exists_of_not_forall_mem _ h

/-- `x = Ψ^ξ_π(a) < Ξ_n(b) < π` なら `b < a` で、`b` の前線（`K_n` について）に `x` 未満でない元がある -/
theorem wit_psi_xi {ξ π a b : Tm} {n : Nat} (hx : FZNF (.Psi ξ π a)) (hy : FZNF (.Xi n b))
    (hl : lev π = n) (h : Lt (.Psi ξ π a) (.Xi n b)) (hyπ : Lt (.Xi n b) π) :
    Lt b a ∧ ∃ w, w ∈ fr (.K n) b ∧ ¬ Lt w (.Psi ξ π a) := by
  have hπF := hx.psi.piF
  have haF := hx.psi.aF
  obtain ⟨hn, hbF, -, -, hbC⟩ := hy.xi
  rcases (lt_psi_xiY hl).mp h with h1 | ⟨hba, hn'⟩
  · exact absurd hyπ (not_lt_of_leY hπF hy (le_of_ne_gtY hπF hy h1))
  · refine ⟨hba, ?_⟩
    have hxK : Lt (.Psi ξ π a) (.K n) := (lt_K_iffY hx hn).mpr (by simp only [lev]; omega)
    by_cases hb : ∀ w, w ∈ fr (.K n) b → Lt w (.Psi ξ π a)
    · exfalso
      rw [(inC_frY hbF (FZNF.K' hn) hx hbF haF hbC (Or.inr hxK) (Or.inr hba)).mpr
        (fun w hw => inC_of_lt_node (fr_node hw) (hb w hw))] at hn'
      cases hn'
    · exact exists_of_not_forall_mem _ hb

/-- 前線の取り替え：`R' ≤ R` で `R` についての前線の元が `R'` 未満なら、`R'` についての前線の元 -/
theorem fr_sub {R R' : Tm} (hR : FZNF R) (hR' : FZNF R') (hle : Le R' R) :
    ∀ {x w : Tm}, FZNF x → w ∈ fr R x → Lt w R' → w ∈ fr R' x
  | .zero, _, _, h, _ | .one, _, _, h, _ | .K _, _, _, h, _ => by simp [fr] at h
  | .plus a b, w, hx, h, hw => by
    obtain ⟨ha, hb, -, -⟩ := hx.plus
    rw [fr, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (fr_sub hR hR' hle ha h hw)
    · exact Or.inr (fr_sub hR hR' hle hb h hw)
  | .Om a, w, hx, h, hw => by
    rw [fr] at h ⊢
    exact fr_sub hR hR' hle hx.om.1 h hw
  | .Xi m a, w, hx, h, hw => by
    rw [fr] at h ⊢
    by_cases hl : Lt (.Xi m a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      subst h
      simp only [hw, ↓reduceIte, List.mem_singleton]
    · simp only [hl, ↓reduceIte] at h
      have hl' : ¬ Lt (.Xi m a) R' := fun h' => hl (lt_of_lt_of_leY hx hR' hR h' hle)
      simp only [hl', ↓reduceIte]
      exact fr_sub hR hR' hle hx.xi.2.1 h hw
  | .Psi s p a, w, hx, h, hw => by
    have hP := hx.psi
    rw [fr] at h ⊢
    by_cases hl : Lt (.Psi s p a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      subst h
      simp only [hw, ↓reduceIte, List.mem_singleton]
    · simp only [hl, ↓reduceIte, List.mem_append] at h
      have hl' : ¬ Lt (.Psi s p a) R' := fun h' => hl (lt_of_lt_of_leY hx hR' hR h' hle)
      simp only [hl', ↓reduceIte, List.mem_append]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (fr_sub hR hR' hle hP.xiF h hw))
      · exact Or.inl (Or.inr (fr_sub hR hR' hle hP.piF h hw))
      · exact Or.inr (fr_sub hR hR' hle hP.aF h hw)

end Order

end RTKA.Z
