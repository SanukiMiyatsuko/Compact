import Compact.WF.FY

/-! 断片 `FY` の比較の道具（順序の仮定 `FYOrder` の下で）。

* 和・階・`1`・`K_n`・`Ω` との比較（`FX` の同名の補題の `FY` 版）。
* `Ω` の不動点（`Ξ_n(a)` と `Ψ^0_{Ξ_n(p)}(a)`）と `Ω_e`・`Ψ^0_{Ω_c}(β)` の比較（`lt_om_OFG`・`lt_OF_omG`・
  `lt_OF_psiOm`）。
* `Ψ^0` どうしの比較の展開（`lt_psi_psiY`）と、`Ψ^0` と `Ξ` の比較の展開（`lt_psi_xiY`）。
* 崩壊の性質（`coll_psiY`・`coll_xiY`）と、比較の前線による言い換え（`ff_psiY`・`ff_xiY`）、目標の違う
  崩壊どうしの比較から前線の証人を取り出す補題（`wit_psi_psi`・`wit_psi_xi`）。 -/

namespace RTKA

open Tm

/-! ### 和 -/

theorem FYNF.plus_head {a b : Tm} (h : FYNF (.plus a b)) {h' : Tm} {rest : List Tm}
    (hs : summands b = h' :: rest) : cmp h' a ≠ .gt := by
  have hn := h.1
  simp only [isNF, Bool.and_eq_true] at hn
  have h2 := hn.2
  rw [hs] at h2
  simpa using h2

theorem lt_plus_leftY {a b : Tm} (h : FYNF (.plus a b)) : Lt a (.plus a b) := by
  obtain ⟨-, -, hap, hb0⟩ := h.plus
  unfold Lt
  rw [cmp_eq, summands_principal' hap, summands_plus, cmpList_cons_cons_eq _ _ (cmpP_self a)]
  cases hs : summands b with
  | nil => exact absurd hs (summands_ne_nil hb0)
  | cons _ _ => exact cmpList_nil_cons _ _

/-- 主要項 `y` について `a + b < y` ⟺ `a < y` -/
theorem lt_plus_prin_iffY {a b y : Tm} (h : FYNF (.plus a b)) (hyp : isPrincipal y = true) :
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
theorem not_lt_isBotY {x y : Tm} (hl : lev x = lev y) (hy : isBot y = true) (hx : FYNF x)
    (hyF : FYNF y) : cmpP x y ≠ .lt := by
  rw [cmpP.eq_def]
  simp only [hl, Nat.lt_irrefl, ↓reduceIte]
  cases x <;> cases y <;> simp_all [isBot]
  all_goals first
    | (split <;> simp)
    | (have := hyF.k; simp only [lev] at hl; omega)

theorem lev_posY : ∀ {t : Tm}, FYNF t → t ≠ .zero → 1 ≤ lev t
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
    obtain ⟨-, hT, hpF, -⟩ := ht.psi
    show 1 ≤ lev pi
    exact lev_posY hpF (by rcases hT with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ <;> intro e <;> cases e)

/-- `x < K_m` なら `x` の階は `m` 以下 -/
theorem lev_le_of_lt_KY {z : Tm} {n : Nat} (hn : 1 ≤ n) (hz : FYNF z) (h : Lt z (.K n)) :
    lev z ≤ n := by
  cases hs : summands z with
  | nil =>
    have : z = .zero := by cases z <;> simp_all [summands]
    subst this
    simp [lev]
  | cons x xs =>
    have hx := summands_FYNF z hz x (by rw [hs]; exact List.mem_cons_self)
    unfold Lt at h
    rw [cmp_eq, hs, show summands (Tm.K n) = [.K n] from rfl] at h
    have hl := lev_head hs
    rcases cmpList_lt_cases h with e | ⟨-, e'⟩
    · have := lev_le_of_cmpP_lt e
      simp only [lev] at this
      rcases Nat.lt_or_eq_of_le this with h1 | h1
      · rw [← hl]; omega
      · exact absurd e (not_lt_isBotY (by simp only [lev]; exact h1) rfl hx.1 (FYNF.K' hn))
    · cases xs with
      | nil => rw [cmpList_nil_nil] at e'; cases e'
      | cons _ _ => rw [cmpList_cons_nil] at e'; cases e'

/-- `x < K_m` ⟺ `x` の階が `m` 以下 -/
theorem lt_K_iffY {x : Tm} {m : Nat} (hx : FYNF x) (hm : 1 ≤ m) : Lt x (.K m) ↔ lev x ≤ m :=
  ⟨lev_le_of_lt_KY hm hx, fun h => lt_of_lev_lt' (by simp only [lev]; omega)⟩

theorem cmpP_one_ne_gtY {h : Tm} (hF : FYNF h) (hp : isPrincipal h = true) :
    cmpP .one h ≠ .gt := by
  have hl : 1 ≤ lev h := lev_posY hF (by intro e; subst e; simp [isPrincipal] at hp)
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · rw [cmpP_of_lev_lt (by simp only [lev]; exact hl)]; decide
  · rw [cmpP.eq_def]
    simp only [lev, ← hl, Nat.lt_irrefl, ↓reduceIte]
    cases h <;> simp

theorem lt_oneY {u : Tm} (hu : FYNF u) (h : Lt u .one) : u = .zero := by
  cases hs : summands u with
  | nil => cases u <;> simp_all [summands]
  | cons x xs =>
    exfalso
    unfold Lt at h
    rw [cmp_eq, hs, show summands Tm.one = [.one] from rfl] at h
    have hx := summands_FYNF u hu x (by rw [hs]; exact List.mem_cons_self)
    have hl : 1 ≤ lev x := lev_posY hx.1 (by intro e; subst e; simp [isPrincipal] at hx)
    rcases cmpList_lt_cases h with e | ⟨e, e'⟩
    · rcases Nat.lt_or_eq_of_le hl with hl | hl
      · rw [cmpP_of_lev_gt (by simp only [lev]; exact hl)] at e; cases e
      · exact not_lt_isBotY (by simp only [lev]; exact hl.symm) rfl hx.1 FYNF.one e
    · cases xs with
      | nil => rw [cmpList_nil_nil] at e'; cases e'
      | cons _ _ => rw [cmpList_cons_nil] at e'; cases e'

section Order

variable [FYOrder]

theorem lt_plus_rightY : ∀ {a b : Tm}, FYNF (.plus a b) → Lt b (.plus a b)
  | a, b, h => by
    obtain ⟨-, hb, hap, hb0⟩ := h.plus
    cases hs : summands b with
    | nil => exact absurd hs (summands_ne_nil hb0)
    | cons x xs =>
      have hxa := h.plus_head hs
      have hx := summands_FYNF b hb x (by rw [hs]; exact List.mem_cons_self)
      have hxa' : cmpP x a ≠ .gt := by rwa [← cmp_principal hx.2 hap]
      unfold Lt
      rw [cmp_eq, hs, summands_plus, hs]
      cases e : cmpP x a with
      | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]
      | gt => exact absurd e hxa'
      | eq =>
        rw [cmpList_cons_cons_eq _ _ e]
        have hxe : x = a :=
          eq_of_cmpP_eqY hx.1 (summands_FYNF _ h a (by simp [summands])).1 hx.2 hap e
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
theorem lt_prin_plus_iffY {x a b : Tm} (hx : FYNF x) (hxp : isPrincipal x = true)
    (h : FYNF (.plus a b)) : Lt x (.plus a b) ↔ Le x a := by
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

theorem lt_plus_plus_neY {a b a' b' : Tm} (h : FYNF (.plus a b)) (h' : FYNF (.plus a' b'))
    (hne : a ≠ a') : Lt (.plus a b) (.plus a' b') ↔ Lt a a' := by
  obtain ⟨ha, -, hap, -⟩ := h.plus
  obtain ⟨ha', -, hap', -⟩ := h'.plus
  have e : cmpP a a' ≠ .eq := fun e => hne (eq_of_cmpP_eqY ha ha' hap hap' e)
  rw [lt_principal_iff hap hap']
  unfold Lt
  rw [cmp_eq, summands_plus, summands_plus, cmpList_cons_cons_ne _ _ e]

theorem one_leY {c : Tm} (hc : FYNF c) (h0 : c ≠ .zero) : Le .one c := by
  rcases triY FYNF.one hc with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact absurd (lt_oneY hc h) h0

/-! ### `Ω` -/

theorem lt_om_iffY {a b : Tm} (ha : FYNF a) (hb : FYNF b) : Lt (.Om a) (.Om b) ↔ Lt a b := by
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

theorem le_om_of_leY {a b : Tm} (ha : FYNF a) (hb : FYNF b) (h : Le a b) :
    Le (.Om a) (.Om b) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr ((lt_om_iffY ha hb).mpr h)

omit [FYOrder] in
theorem FYNF.psiOm {c a : Tm} (h : FYNF (.Psi .zero (.Om c) a)) :
    FYNF c ∧ FYNF (.Om c) ∧ isSucc c = true ∧ FYNF a ∧ inC a a (.Om c) = true := by
  obtain ⟨-, hT, hcF, haF, hC, -⟩ := h.psi
  rcases hT with ⟨c', e, hs⟩ | ⟨n, p, e⟩
  · cases e
    exact ⟨hcF.om.1, hcF, hs, haF, hC⟩
  · cases e

theorem lt_psi_omY {c β e : Tm} (hψ : FYNF (.Psi .zero (.Om c) β)) (he : FYNF e) :
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

omit [FYOrder] in
theorem lt_om_psiY {e c β : Tm} (hψ : FYNF (.Psi .zero (.Om c) β)) :
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

theorem lt_K_omY {m : Nat} {e : Tm} (hm : 1 ≤ m) (he : FYNF e) :
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
        rcases triY (FYNF.K' hm) he with h | h | h
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


/-! ### `Ψ^0` と目標・`Ξ` の比較の展開（順序の仮定なし） -/

theorem lt_psi_targetY {π a : Tm} (h : FYNF (.Psi .zero π a)) : Lt (.Psi .zero π a) π := by
  obtain ⟨-, hT, -⟩ := h.psi
  rcases hT with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
  · exact lt_psi_om_self c a
  · rw [lt_principal_iff rfl rfl, cmpP_psi_xi (pi := .Xi n p) (m := n) rfl, psiLtXi_eq, cmp_self]
    simp

/-- 同じ階の `Ψ^0_π(a)` と `Ξ_n(b)` の比較（Prop. 4.21） -/
theorem lt_psi_xiY {π a b : Tm} {n : Nat} (hl : lev π = n) :
    Lt (.Psi .zero π a) (.Xi n b) ↔
      cmp π (.Xi n b) ≠ .gt ∨ (Lt b a ∧ inC b a (.Psi .zero π a) = false) := by
  rw [lt_principal_iff rfl rfl, cmpP_psi_xi hl, psiLtXi_eq, ite_lt_gt_eq_lt]
  unfold Lt
  cases cmp π (Tm.Xi n b) <;> cases cmp b a <;> cases inC b a (Tm.Psi .zero π a) <;> simp

theorem lt_xi_psiY {π a b : Tm} {n : Nat} (hl : lev π = n) :
    Lt (.Xi n b) (.Psi .zero π a) ↔ ¬ Lt (.Psi .zero π a) (.Xi n b) := by
  rw [lt_principal_iff rfl rfl, lt_principal_iff rfl rfl, cmpP_xi_psi hl, cmpP_psi_xi hl]
  cases psiLtXi (Tm.Psi .zero π a) (.Xi n b) <;> simp

/-- 同じ階の `Ψ^0` どうしの比較の展開（`cmpPsi` で `ξ = σ = 0` としたもの） -/
theorem lt_psi_psiY {π κ a b : Tm} (hl : lev π = lev κ)
    (hne : Tm.Psi .zero π a ≠ .Psi .zero κ b) :
    Lt (.Psi .zero π a) (.Psi .zero κ b) ↔
      ¬ Lt (.Psi .zero κ b) π ∨
        (Lt (.Psi .zero κ b) π ∧ Lt (.Psi .zero π a) κ ∧
          ((Lt a b ∧ inC a b (.Psi .zero κ b) = true ∧ inC π b (.Psi .zero κ b) = true) ∨
            (cmp b a ≠ .gt ∧ ¬ (inC b a (.Psi .zero π a) = true ∧
              inC κ a (.Psi .zero π a) = true)))) := by
  rw [lt_principal_iff rfl rfl, cmpP_psi_psi hl, cmpPsi.eq_def]
  simp only []
  rw [cmp_self .zero, inC_zero, inC_zero]
  unfold Lt
  by_cases h1 : cmp (Tm.Psi .zero κ b) π = .lt
  · by_cases h2 : cmp (Tm.Psi .zero π a) κ = .lt
    · simp only [hne, h1, h2, beq_iff_eq, bne_iff_ne, ne_eq, not_true_eq_false, false_or,
        true_and, ↓reduceIte, Bool.and_true]
      cases cmp a b <;> cases cmp b a <;> cases inC a b (Tm.Psi .zero κ b) <;>
        cases inC π b (Tm.Psi .zero κ b) <;> cases inC b a (Tm.Psi .zero π a) <;>
        cases inC κ a (Tm.Psi .zero π a) <;> simp
    · simp [hne, h1, h2]
  · simp [hne, h1]

section Order

variable [FYOrder]

/-! ### `Ω` の不動点 -/

/-- `Ω` の不動点になる主要項（`Ξ_n(a)` と `Ψ^0_{Ξ_n(p)}(a)`） -/
def IsOF (X : Tm) : Prop := (∃ n a, X = .Xi n a) ∨ ∃ n p a, X = .Psi .zero (.Xi n p) a

omit [FYOrder] in
theorem IsOF.principal {X : Tm} (h : IsOF X) : isPrincipal X = true := by
  rcases h with ⟨n, a, rfl⟩ | ⟨n, p, a, rfl⟩ <;> rfl

omit [FYOrder] in
theorem cmpP_om_OF {e X : Tm} (hX : IsOF X) (hl : lev e = lev X) :
    cmpP (.Om e) X = cmp e X := by
  rcases hX with ⟨n, a, rfl⟩ | ⟨n, p, a, rfl⟩
  · exact cmpP_om_xi hl
  · rw [cmpP.eq_def]
    have hl' : lev e = n := hl
    simp only [lev, hl', Nat.lt_irrefl, ↓reduceIte]
    rw [cmpOmX.eq_def]
    simp [omegaFixed, isInacc]

omit [FYOrder] in
theorem cmpP_OF_om {e X : Tm} (hX : IsOF X) (hl : lev e = lev X) :
    cmpP X (.Om e) = (cmp e X).swap := by
  rcases hX with ⟨n, a, rfl⟩ | ⟨n, p, a, rfl⟩
  · exact cmpP_xi_om hl
  · rw [cmpP.eq_def]
    have hl' : lev e = n := hl
    simp only [lev, hl', Nat.lt_irrefl, ↓reduceIte]
    rw [cmpOmX.eq_def]
    simp [omegaFixed, isInacc]

omit [FYOrder] in
theorem lt_om_OFG {e X : Tm} (hX : IsOF X) :
    Lt (.Om e) X ↔ Lt e X := by
  rcases Nat.lt_trichotomy (lev e) (lev X) with hl | hl | hl
  · exact ⟨fun _ => lt_of_lev_lt' hl, fun _ => lt_of_lev_lt' (by simp only [lev]; exact hl)⟩
  · rw [lt_principal_iff rfl hX.principal, cmpP_om_OF hX hl]; rfl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · intro h; have := lev_le_of_lt_gen h; exfalso; omega

theorem lt_OF_omG {e X : Tm} (hX : IsOF X) (hXF : FYNF X) (he : FYNF e) :
    Lt X (.Om e) ↔ Lt X e := by
  rcases Nat.lt_trichotomy (lev e) (lev X) with hl | hl | hl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · intro h; have := lev_le_of_lt_gen h; exfalso; omega
  · rw [lt_principal_iff hX.principal rfl, cmpP_OF_om hX hl]
    unfold Lt
    rw [FYOrder.swap hXF he]
    cases cmp X e <;> simp
  · exact ⟨fun _ => lt_of_lev_lt' hl, fun _ => lt_of_lev_lt' (by simp only [lev]; exact hl)⟩

/-- `Ω` の不動点 `X` と `Ψ^0_{Ω_c}(β)`：`X < Ψ_c(β)` ⟺ `X < c`（KL） -/
theorem lt_OF_psiOm {X c β : Tm} (hX : IsOF X) (hXF : FYNF X)
    (hψ : FYNF (.Psi .zero (.Om c) β)) :
    Lt X (.Psi .zero (.Om c) β) ↔ Lt X c := by
  obtain ⟨hc, hσ, -⟩ := hψ.psiOm
  constructor
  · intro h
    exact (lt_OF_omG hX hXF hc).mp (lt_transY hXF hψ hσ h (lt_psi_om_self c β))
  · intro h
    exact lt_transY hXF hc hψ h (FYOrder.cx hψ)

/-! ### `Ξ` どうし -/

/-- 同じ階の `Ξ` どうしの比較（Lemma 4.14） -/
theorem lt_xi_xi_sameY {n : Nat} {α β : Tm} (hα : FYNF α) (hβ : FYNF β) (hne : α ≠ β) :
    Lt (.Xi n α) (.Xi n β) ↔
      (Lt α β ∧ inC α β (.Xi n β) = true) ∨ (Lt β α ∧ inC β α (.Xi n α) = false) := by
  rw [lt_principal_iff rfl rfl, cmpP_xi_xi, xiLtXi_eq]
  simp only [hne, ↓reduceIte]
  rw [ite_lt_gt_eq_lt]
  rcases triY hα hβ with h | h | h
  · have h' : cmp β α = .gt := by unfold Lt at h; rw [FYOrder.swap hα hβ, h]; rfl
    unfold Lt at h
    simp [h, h', Lt]
  · exact absurd h hne
  · have h' : cmp α β = .gt := by unfold Lt at h; rw [FYOrder.swap hβ hα, h]; rfl
    unfold Lt at h
    cases inC β α (Tm.Xi n α) <;> simp [h, h', Lt]

end Order


section Order

variable [FYOrder]

/-! ### 崩壊の性質 -/

/-- `Ψ^0_π(γ)` の崩壊の性質：`z ∈ C(γ, Ψ_π(γ))` で `z < π` なら `z < Ψ_π(γ)` -/
theorem coll_psiY {π γ : Tm} (ht : FYNF (.Psi .zero π γ)) :
    ∀ z, FYNF z → inC z γ (.Psi .zero π γ) = true → Lt z π → Lt z (.Psi .zero π γ) := by
  have hπ := ht.psi.2.2.1
  have hT := ht.psi.2.1
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
    rcases hT with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
    · exact (lt_om_psiY ht).mpr ((lt_om_iffY heF hπ.om.1).mp hlt)
    · exact (lt_om_OFG (Or.inr ⟨n, p, γ, rfl⟩)).mpr
        (ihe heF hin (lt_transY heF hz hπ hz.om.2.2 hlt))
  | Xi m f _ =>
    intro hz hin hlt
    rcases inC_xi_iff.mp hin with h | ⟨hf, -⟩
    · exact h
    rcases hT with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
    · exact (lt_OF_psiOm (Or.inl ⟨m, f, rfl⟩) hz ht).mpr
        ((lt_OF_omG (Or.inl ⟨m, f, rfl⟩) hz hπ.om.1).mp hlt)
    · have hl := lev_le_of_lt_gen hlt
      simp only [lev] at hl
      rcases Nat.lt_or_eq_of_le hl with hl | hl
      · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
      · subst hl
        have hgt : cmp (.Xi m p) (.Xi m f) = .gt := by
          unfold Lt at hlt; rw [FYOrder.swap hz hπ, hlt]; rfl
        rw [lt_xi_psiY (π := .Xi m p) (n := m) rfl, lt_psi_xiY (π := .Xi m p) (n := m) rfl]
        rintro (h | ⟨-, h⟩)
        · exact h hgt
        · rw [hf] at h; cases h
  | Psi s κ β _ _ _ =>
    intro hz hin hlt
    obtain ⟨rfl, -, -, -, -, -⟩ := hz.psi
    rcases inC_psi_iff.mp hin with h | ⟨hκ, -, hβ, hβγ⟩
    · exact h
    have hl := lev_le_of_lt_gen hlt
    simp only [lev] at hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · have hne : Tm.Psi .zero κ β ≠ .Psi .zero π γ := by
        intro e; cases e; exact Lt.irrefl _ hβγ
      rw [lt_psi_psiY hl hne]
      by_cases h1 : Lt (.Psi .zero π γ) κ
      · exact Or.inr ⟨h1, hlt, Or.inl ⟨hβγ, hβ, hκ⟩⟩
      · exact Or.inl h1

/-- `Ξ_n(γ)` の崩壊の性質：`z ∈ C(γ, Ξ_n(γ))` で `z < K_n` なら `z < Ξ_n(γ)` -/
theorem coll_xiY {n : Nat} {γ : Tm} (ht : FYNF (.Xi n γ)) :
    ∀ z, FYNF z → inC z γ (.Xi n γ) = true → Lt z (.K n) → Lt z (.Xi n γ) := by
  obtain ⟨hn, hγF, -, -, -⟩ := ht.xi
  have hK := FYNF.K' hn
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
    obtain ⟨rfl, -, hκF, -, -, -⟩ := hz.psi
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

theorem inC_frY {R g0 g d x : Tm} (hx : FYNF x) (hR : FYNF R) (hd : FYNF d) (hg0 : FYNF g0)
    (hg : FYNF g) (h0 : inC x g0 R = true) (hdR : Le d R) (hgg : Le g0 g) :
    inC x g d = true ↔ ∀ w, w ∈ fr R x → inC w g d = true :=
  inC_fr x h0 (fun _ hw hn hwd => hn (lt_of_lt_of_leY (hx.of_mem_subs hw) hd hR hwd hdR))
    (fun _ hv hvg => lt_of_lt_of_leY (hx.of_mem_subs hv) hg0 hg hvg hgg)

/-- `a ∈ C(a, Ψ_π(a))` -/
theorem inC_arg_own {π a : Tm} (h : FYNF (.Psi .zero π a)) :
    inC a a (.Psi .zero π a) = true := by
  obtain ⟨-, -, hπ, ha, hC, -⟩ := h.psi
  exact (inC_frY ha hπ h ha ha hC (Or.inr (lt_psi_targetY h)) (Or.inl rfl)).mpr
    (fun w hw => inC_of_lt_node (fr_node hw) (FYOrder.k2 h w hw))

/-- `π ∈ C(a, Ψ_π(a))` -/
theorem inC_tgt_own {π a : Tm} (h : FYNF (.Psi .zero π a)) :
    inC π a (.Psi .zero π a) = true := by
  obtain ⟨-, -, hπ, ha, -, hC⟩ := h.psi
  exact (inC_frY hπ hπ h ha ha hC (Or.inr (lt_psi_targetY h)) (Or.inl rfl)).mpr
    (fun w hw => inC_of_lt_node (fr_node hw) (FYOrder.k2t h w hw))

/-- 同じ目標の `Ψ^0` どうしの比較の前線による言い換え -/
theorem ff_psiY {π α β : Tm} (hx : FYNF (.Psi .zero π α)) (hy : FYNF (.Psi .zero π β))
    (hne : α ≠ β) :
    Lt (.Psi .zero π α) (.Psi .zero π β) ↔
      (Lt α β ∧ ∀ w, w ∈ fr π α → Lt w (.Psi .zero π β)) ∨
        (Lt β α ∧ ∃ w, w ∈ fr π β ∧ ¬ Lt w (.Psi .zero π α)) := by
  obtain ⟨-, -, hπ, hαF, hαC, -⟩ := hx.psi
  obtain ⟨-, -, -, hβF, hβC, -⟩ := hy.psi
  have hne' : Tm.Psi .zero π α ≠ .Psi .zero π β := fun e => by cases e; exact hne rfl
  have hyπ := lt_psi_targetY hy
  have hxπ := lt_psi_targetY hx
  have collx : ∀ w, w ∈ fr π β → inC w α (.Psi .zero π α) = true →
      Lt w (.Psi .zero π α) := fun w hw h =>
    coll_psiY hx w (hβF.of_mem_subs (fr_spec hw).1) h (fr_spec hw).2
  have colly : ∀ w, w ∈ fr π α → inC w β (.Psi .zero π β) = true →
      Lt w (.Psi .zero π β) := fun w hw h =>
    coll_psiY hy w (hαF.of_mem_subs (fr_spec hw).1) h (fr_spec hw).2
  rw [lt_psi_psiY rfl hne']
  have e1 := inC_tgt_own hy
  have e2 := inC_tgt_own hx
  constructor
  · rintro (h | ⟨-, -, (⟨hab, h, -⟩ | ⟨hba, h⟩)⟩)
    · exact absurd hyπ h
    · exact Or.inl ⟨hab, (fr_inC_iff colly).mp
        ((inC_frY hαF hπ hy hαF hβF hαC (Or.inr hyπ) (Or.inr hab)).mp h)⟩
    · have hba' : Lt β α := by
        rcases le_of_ne_gtY hβF hαF hba with e | h'
        · exact absurd e.symm hne
        · exact h'
      refine Or.inr ⟨hba', (fr_inC_false_iff collx).mp ?_⟩
      intro h'
      exact h ⟨(inC_frY hβF hπ hx hβF hαF hβC (Or.inr hxπ) (Or.inr hba')).mpr h', e2⟩
  · rintro (⟨hab, h⟩ | ⟨hba, h⟩)
    · exact Or.inr ⟨hyπ, hxπ, Or.inl ⟨hab, (inC_frY hαF hπ hy hαF hβF hαC (Or.inr hyπ)
        (Or.inr hab)).mpr ((fr_inC_iff colly).mpr h), e1⟩⟩
    · refine Or.inr ⟨hyπ, hxπ, Or.inr ⟨ne_gt_of_le (Or.inr hba), ?_⟩⟩
      rintro ⟨h', -⟩
      exact (fr_inC_false_iff collx).mpr h
        ((inC_frY hβF hπ hx hβF hαF hβC (Or.inr hxπ) (Or.inr hba)).mp h')

/-- 同じ階の `Ξ_n` どうしの比較の前線による言い換え -/
theorem ff_xiY {n : Nat} {α β : Tm} (hx : FYNF (.Xi n α)) (hy : FYNF (.Xi n β)) (hne : α ≠ β) :
    Lt (.Xi n α) (.Xi n β) ↔
      (Lt α β ∧ ∀ w, w ∈ fr (.K n) α → Lt w (.Xi n β)) ∨
        (Lt β α ∧ ∃ w, w ∈ fr (.K n) β ∧ ¬ Lt w (.Xi n α)) := by
  obtain ⟨hn, hαF, -, -, hαC⟩ := hx.xi
  obtain ⟨-, hβF, -, -, hβC⟩ := hy.xi
  have hK := FYNF.K' hn
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

/-! ### 目標の違う崩壊どうしの比較の証人 -/

/-- 目標の違う崩壊 `x = Ψ_π(a) < y = Ψ_κ(b)`（`y < π < κ`）なら、`y` の引数か目標の前線（`κ` について）に
    `x` 未満でない元がある -/
theorem wit_psi_psi {π κ a b : Tm} (hx : FYNF (.Psi .zero π a)) (hy : FYNF (.Psi .zero κ b))
    (hl : lev π = lev κ) (h : Lt (.Psi .zero π a) (.Psi .zero κ b))
    (hyπ : Lt (.Psi .zero κ b) π) (hπκ : Lt π κ) :
    ∃ w, (w ∈ fr κ b ∨ w ∈ fr κ κ) ∧ ¬ Lt w (.Psi .zero π a) := by
  obtain ⟨-, -, hπF, haF, -, -⟩ := hx.psi
  obtain ⟨-, -, hκF, hbF, hbC, hκC⟩ := hy.psi
  rcases (lt_psi_psiY hl h.ne).mp h with h1 | ⟨-, hxκ, (⟨-, -, hπC⟩ | ⟨hba, hn⟩)⟩
  · exact absurd hyπ h1
  · exact absurd (coll_psiY hy π hπF hπC hπκ) (Lt.asymmY hy hπF hyπ)
  · have hba' : Le b a := le_of_ne_gtY hbF haF hba
    by_cases hb : ∀ w, w ∈ fr κ b → Lt w (.Psi .zero π a)
    · by_cases hk : ∀ w, w ∈ fr κ κ → Lt w (.Psi .zero π a)
      · exfalso
        apply hn
        exact ⟨(inC_frY hbF hκF hx hbF haF hbC (Or.inr hxκ) hba').mpr
            (fun w hw => inC_of_lt_node (fr_node hw) (hb w hw)),
          (inC_frY hκF hκF hx hbF haF hκC (Or.inr hxκ) hba').mpr
            (fun w hw => inC_of_lt_node (fr_node hw) (hk w hw))⟩
      · obtain ⟨w, hw, hw'⟩ := exists_of_not_forall_mem _ hk
        exact ⟨w, Or.inr hw, hw'⟩
    · obtain ⟨w, hw, hw'⟩ := exists_of_not_forall_mem _ hb
      exact ⟨w, Or.inl hw, hw'⟩

/-- `x = Ψ_π(a) < Ξ_n(b) < π` なら `b < a` で、`b` の前線（`K_n` について）に `x` 未満でない元がある -/
theorem wit_psi_xi {π a b : Tm} {n : Nat} (hx : FYNF (.Psi .zero π a)) (hy : FYNF (.Xi n b))
    (hl : lev π = n) (h : Lt (.Psi .zero π a) (.Xi n b)) (hyπ : Lt (.Xi n b) π) :
    Lt b a ∧ ∃ w, w ∈ fr (.K n) b ∧ ¬ Lt w (.Psi .zero π a) := by
  obtain ⟨-, -, hπF, haF, -, -⟩ := hx.psi
  obtain ⟨hn, hbF, -, -, hbC⟩ := hy.xi
  rcases (lt_psi_xiY hl).mp h with h1 | ⟨hba, hn'⟩
  · exact absurd hyπ (not_lt_of_leY hπF hy (le_of_ne_gtY hπF hy h1))
  · refine ⟨hba, ?_⟩
    have hxK : Lt (.Psi .zero π a) (.K n) := (lt_K_iffY hx hn).mpr (by simp only [lev]; omega)
    by_cases hb : ∀ w, w ∈ fr (.K n) b → Lt w (.Psi .zero π a)
    · exfalso
      rw [(inC_frY hbF (FYNF.K' hn) hx hbF haF hbC (Or.inr hxK) (Or.inr hba)).mpr
        (fun w hw => inC_of_lt_node (fr_node hw) (hb w hw))] at hn'
      cases hn'
    · exact exists_of_not_forall_mem _ hb

/-- 前線の取り替え：`R' ≤ R` で `R` についての前線の元が `R'` 未満なら、`R'` についての前線の元 -/
theorem fr_sub {R R' : Tm} (hR : FYNF R) (hR' : FYNF R') (hle : Le R' R) :
    ∀ {x w : Tm}, FYNF x → w ∈ fr R x → Lt w R' → w ∈ fr R' x
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
    obtain ⟨hs, -, hp, ha, -, -⟩ := hx.psi
    rw [fr] at h ⊢
    by_cases hl : Lt (.Psi s p a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      subst h
      simp only [hw, ↓reduceIte, List.mem_singleton]
    · simp only [hl, ↓reduceIte, List.mem_append] at h
      have hl' : ¬ Lt (.Psi s p a) R' := fun h' => hl (lt_of_lt_of_leY hx hR' hR h' hle)
      simp only [hl', ↓reduceIte, List.mem_append]
      rcases h with (h | h) | h
      · subst hs; simp [fr] at h
      · exact Or.inl (Or.inr (fr_sub hR hR' hle hp h hw))
      · exact Or.inr (fr_sub hR hR' hle ha h hw)

end Order

end RTKA
