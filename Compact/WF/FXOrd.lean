import Compact.WF.FXLin

/-! 断片 `FX` の整列性の証明の下準備（順序の道具と次の正則項）。

* `≤` の推移性など（`lt_trans_FX` から）。
* 和との比較（`lt_prin_plus_iff`・`lt_plus_prin_iff`・`lt_plus_plus_same`・`lt_plus_plus_ne`）。
* 推移性の証明の不変条件 `GoodX` を、任意の標準形について使える形にしたもの（`k2_FX`・`k2x_FX`・`cx_FX`・
  `xi_lt_psi_FX`・`ff_xi_FX`・`ff_psi_FX`）。
* 階の違う項も含めた主要項どうしの比較（`lt_K_iff`・`lt_xi_omG`・`lt_psi_omG`・`lt_K_omG`・`lt_psi_psiG`・
  `xi_lt_psiG`）。
* 次の正則項 `nr t`（`t` より大きい最小の `Ω_c`（`c` は後者）または `K_n`）と、その性質
  （`nr_spec`・`nr_least`）。`Ψ` の添字 `Ω_c` と `Ξ_n` の添字 `K_n` が正則項にあたる。
* 前線の元は項以下（`fr_le`）。 -/

namespace RTKA

open Tm

/-! ### `≤` -/

theorem lt_of_lt_of_leX {a b c : Tm} (ha : FXNF a) (hb : FXNF b) (hc : FXNF c)
    (h1 : Lt a b) (h2 : Le b c) : Lt a c := by
  rcases h2 with rfl | h2
  · exact h1
  · exact lt_trans_FX ha hb hc h1 h2

theorem lt_of_le_of_ltX {a b c : Tm} (ha : FXNF a) (hb : FXNF b) (hc : FXNF c)
    (h1 : Le a b) (h2 : Lt b c) : Lt a c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact lt_trans_FX ha hb hc h1 h2

theorem le_transX {a b c : Tm} (ha : FXNF a) (hb : FXNF b) (hc : FXNF c)
    (h1 : Le a b) (h2 : Le b c) : Le a c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact Or.inr (lt_of_lt_of_leX ha hb hc h1 h2)

theorem le_antisymmX {a b : Tm} (ha : FXNF a) (hb : FXNF b) (h1 : Le a b) (h2 : Le b a) :
    a = b := by
  rcases h1 with e | h1
  · exact e
  · exact absurd h1 (not_lt_of_leX hb ha h2)

/-! ### `0` と `1` -/

theorem FXNF.zero : FXNF .zero := ⟨rfl, rfl⟩

theorem FXNF.one : FXNF .one := ⟨rfl, rfl⟩

theorem lev_posX : ∀ {t : Tm}, FXNF t → t ≠ .zero → 1 ≤ lev t
  | .zero, _, h => absurd rfl h
  | .one, _, _ => Nat.le_refl _
  | .K _, _, _ => by simp only [lev]; omega
  | .plus a _, ht, _ => by
    obtain ⟨ha, -, hap, -⟩ := ht.plus
    have : a ≠ .zero := by intro e; subst e; simp [isPrincipal] at hap
    show 1 ≤ lev a
    exact lev_posX ha this
  | .Om a, ht, _ => by show 1 ≤ lev a; exact lev_posX ht.om.1 ht.om.2.1
  | .Xi _ _, ht, _ => ht.xi.1
  | .Psi _ pi _, ht, _ => by
    obtain ⟨-, c, hpi, hc, -⟩ := ht.psi
    subst hpi
    show 1 ≤ lev (.Om c)
    exact lev_posX hc (by intro e; cases e)

/-- 主要項は `1` 以上 -/
theorem cmpP_one_ne_gtX {h : Tm} (hF : FXNF h) (hp : isPrincipal h = true) :
    cmpP .one h ≠ .gt := by
  have hl : 1 ≤ lev h := lev_posX hF (by intro e; subst e; simp [isPrincipal] at hp)
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · rw [cmpP_of_lev_lt (by simp only [lev]; exact hl)]; decide
  · rw [cmpP.eq_def]
    simp only [lev, ← hl, Nat.lt_irrefl, ↓reduceIte]
    cases h <;> simp

theorem lt_oneX {u : Tm} (hu : FXNF u) (h : Lt u .one) : u = .zero := by
  cases hs : summands u with
  | nil => cases u <;> simp_all [summands]
  | cons x xs =>
    exfalso
    unfold Lt at h
    rw [cmp_eq, hs, show summands Tm.one = [.one] from rfl] at h
    have hx := summands_FXNF u hu x (by rw [hs]; exact List.mem_cons_self)
    have hl : 1 ≤ lev x := lev_posX hx.1 (by intro e; subst e; simp [isPrincipal] at hx)
    rcases cmpList_lt_cases h with e | ⟨e, e'⟩
    · rcases Nat.lt_or_eq_of_le hl with hl | hl
      · rw [cmpP_of_lev_gt (by simp only [lev]; exact hl)] at e; cases e
      · exact not_lt_isBotX (by simp only [lev]; exact hl.symm) rfl hx.1 FXNF.one e
    · cases xs with
      | nil => rw [cmpList_nil_nil] at e'; cases e'
      | cons _ _ => rw [cmpList_cons_nil] at e'; cases e'

theorem one_leX {c : Tm} (hc : FXNF c) (h0 : c ≠ .zero) : Le .one c := by
  rcases triX FXNF.one hc with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact absurd (lt_oneX hc h) h0

/-! ### 和との比較 -/

/-- 主要項 `x` について `x < a + b` ⟺ `x ≤ a` -/
theorem lt_prin_plus_iff {x a b : Tm} (hx : FXNF x) (hxp : isPrincipal x = true)
    (h : FXNF (.plus a b)) : Lt x (.plus a b) ↔ Le x a := by
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
    exact le_of_ne_gtX hx ha (by rwa [cmp_principal hxp hap])
  · intro h'
    rw [← cmp_principal hxp hap]
    exact ne_gt_of_le h'

/-- 主要項 `y` について `a + b < y` ⟺ `a < y` -/
theorem lt_plus_prin_iff {a b y : Tm} (h : FXNF (.plus a b)) (hyp : isPrincipal y = true) :
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

theorem lt_plus_plus_same {a b b' : Tm} : Lt (.plus a b) (.plus a b') ↔ Lt b b' := by
  unfold Lt
  rw [cmp_eq, cmp_eq, summands_plus, summands_plus, cmpList_cons_cons_eq _ _ (cmpP_self a)]

theorem lt_plus_plus_ne {a b a' b' : Tm} (h : FXNF (.plus a b)) (h' : FXNF (.plus a' b'))
    (hne : a ≠ a') : Lt (.plus a b) (.plus a' b') ↔ Lt a a' := by
  obtain ⟨ha, -, hap, -⟩ := h.plus
  obtain ⟨ha', -, hap', -⟩ := h'.plus
  have e : cmpP a a' ≠ .eq := fun e => hne (eq_of_cmpP_eqX ha ha' hap hap' e)
  rw [lt_principal_iff hap hap']
  unfold Lt
  rw [cmp_eq, summands_plus, summands_plus, cmpList_cons_cons_ne _ _ e]

/-! ### 推移性の証明の不変条件から -/

theorem goodX_pair {x y : Tm} (hx : FXNF x) (hy : FXNF y) : GoodX (subs x ++ subs y) := by
  have hcl : ∀ s, s ∈ subs x ++ subs y → ∀ r, r ∈ subs s → r ∈ subs x ++ subs y := by
    intro s hs r hr
    rcases List.mem_append.mp hs with hs | hs
    · exact List.mem_append.mpr (Or.inl (subs_trans hs hr))
    · exact List.mem_append.mpr (Or.inr (subs_trans hs hr))
  have hNF : ∀ s, s ∈ subs x ++ subs y → FXNF s := by
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hx.of_mem_subs hs
    · exact hy.of_mem_subs hs
  exact lin_closedX _ _ (Nat.le_refl _) hcl hNF

theorem mem_pair_l (x y : Tm) : x ∈ subs x ++ subs y :=
  List.mem_append.mpr (Or.inl (self_mem_subs x))

theorem mem_pair_r (x y : Tm) : y ∈ subs x ++ subs y :=
  List.mem_append.mpr (Or.inr (self_mem_subs y))

/-- K2：`Ψ_c(γ)` の前線（`Ω_c` について）は `Ψ_c(γ)` 未満 -/
theorem k2_FX {c γ : Tm} (ht : FXNF (.Psi .zero (.Om c) γ)) :
    ∀ w, w ∈ fr (.Om c) γ → Lt w (.Psi .zero (.Om c) γ) :=
  (goodX_pair ht ht).k2 c γ (mem_pair_l _ _)

/-- `Ξ_n(γ)` の前線（`K_n` について）は `Ξ_n(γ)` 未満 -/
theorem k2x_FX {n : Nat} {γ : Tm} (ht : FXNF (.Xi n γ)) :
    ∀ w, w ∈ fr (.K n) γ → Lt w (.Xi n γ) :=
  (goodX_pair ht ht).k2x n γ (mem_pair_l _ _)

/-- `c < Ψ_c(γ)` -/
theorem cx_FX {c γ : Tm} (ht : FXNF (.Psi .zero (.Om c) γ)) : Lt c (.Psi .zero (.Om c) γ) :=
  (goodX_pair ht ht).cx c γ (mem_pair_l _ _)

/-- 同じ階の `Ξ` と `Ψ`：`Ξ < Ψ_c(β)` ⟺ `Ξ < c` -/
theorem xi_lt_psi_FX {c β ξ : Tm} {n : Nat} (hψ : FXNF (.Psi .zero (.Om c) β))
    (hX : FXNF (.Xi n ξ)) (hl : lev c = n) :
    Lt (.Xi n ξ) (.Psi .zero (.Om c) β) ↔ Lt (.Xi n ξ) c :=
  (goodX_pair hψ hX).xi_lt_psi (mem_pair_l _ _) (mem_pair_r _ _) hl

theorem ff_xi_FX {n : Nat} {α β : Tm} (hx : FXNF (.Xi n α)) (hy : FXNF (.Xi n β)) (hne : α ≠ β) :
    Lt (.Xi n α) (.Xi n β) ↔
      (Lt α β ∧ ∀ w, w ∈ fr (.K n) α → Lt w (.Xi n β)) ∨
        (Lt β α ∧ ∃ w, w ∈ fr (.K n) β ∧ ¬ Lt w (.Xi n α)) :=
  (goodX_pair hx hy).ff_xi (mem_pair_l _ _) (mem_pair_r _ _) hne

theorem ff_psi_FX {c α β : Tm} (hx : FXNF (.Psi .zero (.Om c) α))
    (hy : FXNF (.Psi .zero (.Om c) β)) (hne : α ≠ β) :
    Lt (.Psi .zero (.Om c) α) (.Psi .zero (.Om c) β) ↔
      (Lt α β ∧ ∀ w, w ∈ fr (.Om c) α → Lt w (.Psi .zero (.Om c) β)) ∨
        (Lt β α ∧ ∃ w, w ∈ fr (.Om c) β ∧ ¬ Lt w (.Psi .zero (.Om c) α)) :=
  (goodX_pair hx hy).ff_psi (mem_pair_l _ _) (mem_pair_r _ _) hne

/-! ### 主要項どうしの比較（階が違ってもよい） -/

theorem FXNF.psi' {c a : Tm} (h : FXNF (.Psi .zero (.Om c) a)) :
    FXNF c ∧ FXNF (.Om c) ∧ isSucc c = true ∧ FXNF a ∧ inC a a (.Om c) = true := by
  obtain ⟨-, c', hc', hcF, hs, haF, hC, -⟩ := h.psi
  cases hc'
  exact ⟨hcF.om.1, hcF, hs, haF, hC⟩

/-- `x < K_m` ⟺ `x` の階が `m` 以下 -/
theorem lt_K_iff {x : Tm} {m : Nat} (hx : FXNF x) (hm : 1 ≤ m) : Lt x (.K m) ↔ lev x ≤ m :=
  ⟨lev_le_of_lt_K hm hx, fun h => lt_of_lev_lt' (by simp only [lev]; omega)⟩

theorem lt_xi_omG {n : Nat} {b e : Tm} (hX : FXNF (.Xi n b)) (he : FXNF e) :
    Lt (.Xi n b) (.Om e) ↔ Lt (.Xi n b) e := by
  rcases Nat.lt_trichotomy (lev e) n with hl | hl | hl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
  · exact lt_xi_om hl he hX
  · constructor
    · intro _; exact lt_of_lev_lt' (by simp only [lev]; omega)
    · intro _; exact lt_of_lev_lt' (by simp only [lev]; omega)

theorem lt_psi_omG {c β e : Tm} (hψ : FXNF (.Psi .zero (.Om c) β)) (he : FXNF e) :
    Lt (.Psi .zero (.Om c) β) (.Om e) ↔ Le c e := by
  have hc := hψ.psi'.1
  rcases Nat.lt_trichotomy (lev e) (lev c) with hl | hl | hl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · rintro (rfl | h)
      · exact absurd hl (Nat.lt_irrefl _)
      · exact absurd (lev_le_of_lt_gen h) (by omega)
  · rw [lt_psi_om e c β hl]
    constructor
    · intro h; exact le_of_not_ltX he hc h
    · intro h; exact not_lt_of_leX hc he h
  · constructor
    · intro _; exact Or.inr (lt_of_lev_lt' hl)
    · intro _; exact lt_of_lev_lt' (by simp only [lev]; exact hl)

theorem lt_K_omG {m : Nat} {e : Tm} (hm : 1 ≤ m) (he : FXNF e) :
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
        rcases triX (FXNF.K' hm) he with h | h | h
        · exact h
        · exact absurd h.symm hek
        · have := (lt_K_iff he hm).mp h; exfalso; omega
      · intro _
        rw [lt_principal_iff rfl rfl, cmpP.eq_def]
        simp only [lev, hl, Nat.lt_irrefl, ↓reduceIte]
        simp [hek]
  · constructor
    · intro _; exact lt_of_lev_lt' (by simp only [lev]; omega)
    · intro _; exact lt_of_lev_lt' (by simp only [lev]; omega)

theorem lt_psi_psiG {c d α β : Tm} (h : Lt c d) :
    Lt (.Psi .zero (.Om c) α) (.Psi .zero (.Om d) β) := by
  have hl := lev_le_of_lt_gen h
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
  · exact lt_psi_psi_of_lt c d α β hl h

theorem xi_lt_psiG {n : Nat} {ξ c β : Tm} (hX : FXNF (.Xi n ξ))
    (hψ : FXNF (.Psi .zero (.Om c) β)) :
    Lt (.Xi n ξ) (.Psi .zero (.Om c) β) ↔ Lt (.Xi n ξ) c := by
  rcases Nat.lt_trichotomy (lev c) n with hl | hl | hl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
  · exact xi_lt_psi_FX hψ hX hl
  · constructor
    · intro _; exact lt_of_lev_lt' (by simp only [lev]; omega)
    · intro _; exact lt_of_lev_lt' (by simp only [lev]; omega)

theorem le_om_of_leX {a b : Tm} (ha : FXNF a) (hb : FXNF b) (h : Le a b) :
    Le (.Om a) (.Om b) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr ((lt_om_iffX ha hb).mpr h)

/-! ### 後者 -/

theorem FXNF.mk_plus {a b : Tm} (ha : FXNF a) (hb : FXNF b) (hap : isPrincipal a = true)
    (hb0 : b ≠ .zero) (hh : ∀ h rest, summands b = h :: rest → cmp h a ≠ .gt) :
    FXNF (.plus a b) := by
  refine ⟨?_, ?_⟩
  · simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq]
    refine ⟨⟨⟨⟨hap, hb0⟩, ha.1⟩, hb.1⟩, ?_⟩
    cases hs : summands b with
    | nil => exact absurd hs (summands_ne_nil hb0)
    | cons h rest =>
      have := hh h rest hs
      simpa using this
  · simp only [isFX, Bool.and_eq_true]
    exact ⟨ha.2, hb.2⟩

theorem succT_FXNF : ∀ {z : Tm}, FXNF z → FXNF (succT z)
  | .zero, _ => FXNF.one
  | .plus a b, hz => by
    obtain ⟨ha, hb, hap, hb0⟩ := hz.plus
    refine FXNF.mk_plus ha (succT_FXNF hb) hap (succT_ne_zero b) ?_
    intro h rest hs
    rw [summands_succT] at hs
    cases hs' : summands b with
    | nil => exact absurd hs' (summands_ne_nil hb0)
    | cons h' rest' =>
      rw [hs', List.cons_append, List.cons.injEq] at hs
      rw [← hs.1]
      exact hz.plus_head hs'
  | .one, hz | .K _, hz | .Om _, hz | .Xi _ _, hz | .Psi _ _ _, hz => by
    refine FXNF.mk_plus hz FXNF.one rfl (by intro e; cases e) ?_
    intro h rest hs
    simp only [summands, List.cons.injEq] at hs
    rw [← hs.1, cmp_principal rfl rfl]
    exact cmpP_one_ne_gtX hz rfl

theorem cmpList_succ_ne_gtX : ∀ (l m : List Tm), (∀ y, y ∈ m → FXNF y ∧ isPrincipal y = true) →
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
    | gt => exact absurd e (cmpP_one_ne_gtX hy.1 hy.2)
  | _ :: _, [], _, h => by rw [cmpList_cons_nil] at h; cases h
  | x :: xs, y :: ys, hm, h => by
    rw [List.cons_append]
    rcases cmpList_lt_cases h with e | ⟨e, e'⟩
    · rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]; decide
    · rw [cmpList_cons_cons_eq _ _ e]
      exact cmpList_succ_ne_gtX xs ys (fun y hy => hm y (List.mem_cons_of_mem _ hy)) e'

/-- `z < c` なら `z + 1 ≤ c` -/
theorem succT_leX {z c : Tm} (hz : FXNF z) (hc : FXNF c) (h : Lt z c) : Le (succT z) c := by
  have hne : cmp (succT z) c ≠ .gt := by
    rw [cmp_eq, summands_succT]
    unfold Lt at h
    rw [cmp_eq] at h
    exact cmpList_succ_ne_gtX _ _ (summands_FXNF c hc) h
  exact le_of_ne_gtX (succT_FXNF hz) hc hne

theorem isSucc_succT (z : Tm) : isSucc (succT z) = true := by
  simp [isSucc, summands_succT]

/-! ### `Ω_z` の標準形 -/

/-- `0`・`K_m`・`Ξ_n(a)` でない標準形 `z` について `Ω_z` は標準形 -/
theorem FXNF.om_ofX {z : Tm} (hz : FXNF z) (h0 : z ≠ .zero) (hK : ∀ m, z ≠ .K m)
    (hX : ∀ n a, z ≠ .Xi n a) : FXNF (.Om z) := by
  have hlt : Lt z (.Om z) := by
    cases hs : summands z with
    | nil => exact absurd hs (summands_ne_nil h0)
    | cons h rest =>
      have hh := summands_FXNF z hz h (by rw [hs]; exact List.mem_cons_self)
      have hle := head_leX hz hs
      have : Lt h (.Om z) := by
        cases h with
        | zero => simp [isPrincipal] at hh
        | plus _ _ => simp [isPrincipal] at hh
        | K m =>
          rcases hle with e | e
          · exact absurd e.symm (hK m)
          · exact (lt_K_omG hh.1.k hz).mpr e
        | Xi n a =>
          rcases hle with e | e
          · exact absurd e.symm (hX n a)
          · exact (lt_xi_omG hh.1 hz).mpr e
        | one =>
          have hl : 1 ≤ lev z := lev_posX hz h0
          rcases Nat.lt_or_eq_of_le hl with hl | hl
          · rw [lt_principal_iff rfl rfl, cmpP_of_lev_lt (by simp only [lev]; exact hl)]
          · rw [lt_principal_iff rfl rfl, cmpP.eq_def]
            simp only [lev, ← hl, Nat.lt_irrefl, ↓reduceIte]
        | Om x =>
          have hx := hh.1.om
          rw [lt_om_iffX hx.1 hz]
          exact lt_of_lt_of_leX hx.1 hh.1 hz hx.2.2 hle
        | Psi s p β =>
          obtain ⟨rfl, c, rfl, -⟩ := hh.1.psi
          exact (lt_psi_omG hh.1 hz).mpr
            (Or.inr (lt_of_lt_of_leX hh.1.psi'.1 hh.1 hz (cx_FX hh.1) hle))
      exact lt_of_head_lt rfl hs ((lt_principal_iff hh.2 rfl).mp this)
  refine ⟨?_, hz.2⟩
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq]
  refine ⟨⟨hz.1, h0⟩, ?_⟩
  unfold lt
  unfold Lt at hlt
  simp [hlt]

theorem FXNF.om_succT {z : Tm} (hz : FXNF z) : FXNF (.Om (succT z)) :=
  FXNF.om_ofX (succT_FXNF hz) (succT_ne_zero z) (succT_ne_K z)
    (fun n a e => by cases z <;> simp [succT] at e)

theorem FXNF.om_one : FXNF (.Om .one) :=
  FXNF.om_ofX FXNF.one (by intro e; cases e) (fun _ e => by cases e) (fun _ _ e => by cases e)

/-! ### 次の正則項 -/

/-- 正則項：`Ψ` の添字 `Ω_c`（`c` は後者）と `Ξ_n` の添字 `K_n` -/
def IsReg (σ : Tm) : Prop := (∃ c, σ = .Om c ∧ isSucc c = true) ∨ ∃ n, σ = .K n

/-- 次の正則項：`t` より大きい最小の正則項 -/
def nr : Tm → Tm
  | .plus a _ => nr a
  | .Psi _ p _ => p
  | .K n => .Om (succT (.K n))
  | .Om a => .Om (succT a)
  | .Xi n a => .Om (succT (.Xi n a))
  | _ => .Om .one

theorem lev_nr : ∀ {t : Tm}, FXNF t → t ≠ .zero → lev (nr t) = lev t
  | .zero, _, h => absurd rfl h
  | .one, _, _ => rfl
  | .K _, _, _ => rfl
  | .plus a _, ht, _ => by
    obtain ⟨ha, -, hap, -⟩ := ht.plus
    have : a ≠ .zero := by intro e; subst e; simp [isPrincipal] at hap
    have h := lev_nr ha this
    exact h
  | .Om _, ht, _ => lev_succT ht.om.2.1
  | .Xi _ _, _, _ => rfl
  | .Psi _ _ _, ht, _ => by obtain ⟨-, c, rfl, -⟩ := ht.psi; rfl

theorem nr_spec : ∀ t : Tm, FXNF t → FXNF (nr t) ∧ IsReg (nr t) ∧ Lt t (nr t)
  | .zero, _ => ⟨FXNF.om_one, Or.inl ⟨.one, rfl, rfl⟩, zero_lt (by intro e; cases e)⟩
  | .one, _ => ⟨FXNF.om_one, Or.inl ⟨.one, rfl, rfl⟩, FXNF.om_one.om.2.2⟩
  | .K _, ht => ⟨FXNF.om_succT ht, Or.inl ⟨_, rfl, isSucc_succT _⟩,
      (lt_K_omG ht.k (succT_FXNF ht)).mpr (lt_succT _)⟩
  | .plus a _, ht => by
    obtain ⟨ha, -, -, -⟩ := ht.plus
    obtain ⟨h1, h2, h3⟩ := nr_spec a ha
    refine ⟨h1, h2, (lt_plus_prin_iff ht ?_).mpr h3⟩
    show isPrincipal (nr a) = true
    rcases h2 with ⟨c, e, -⟩ | ⟨n, e⟩ <;> rw [e] <;> rfl
  | .Om a, ht => ⟨FXNF.om_succT ht.om.1, Or.inl ⟨_, rfl, isSucc_succT _⟩,
      (lt_om_iffX ht.om.1 (succT_FXNF ht.om.1)).mpr (lt_succT _)⟩
  | .Xi _ _, ht => ⟨FXNF.om_succT ht, Or.inl ⟨_, rfl, isSucc_succT _⟩,
      (lt_xi_omG ht (succT_FXNF ht)).mpr (lt_succT _)⟩
  | .Psi _ _ a, ht => by
    obtain ⟨rfl, c, rfl, hcF, hs, -⟩ := ht.psi
    exact ⟨hcF, Or.inl ⟨c, rfl, hs⟩, lt_psi_om_self c a⟩

theorem nr_lt_K {t : Tm} {m : Nat} (ht : FXNF t) (hm : 1 ≤ m) (h : Lt t (.K m)) :
    Lt (nr t) (.K m) := by
  rw [lt_K_iff (nr_spec t ht).1 hm]
  by_cases h0 : t = .zero
  · subst h0
    show 1 ≤ m
    exact hm
  · rw [lev_nr ht h0]
    exact (lt_K_iff ht hm).mp h

theorem nr_le_om : ∀ t : Tm, FXNF t → ∀ c : Tm, FXNF (.Om c) → Lt t (.Om c) → Le (nr t) (.Om c)
  | .zero, _, _, hc, _ | .one, _, _, hc, _ =>
    le_om_of_leX FXNF.one hc.om.1 (one_leX hc.om.1 hc.om.2.1)
  | .K _, ht, _, hc, h =>
    le_om_of_leX (succT_FXNF ht) hc.om.1 (succT_leX ht hc.om.1 ((lt_K_omG ht.k hc.om.1).mp h))
  | .plus a _, ht, c, hc, h => by
    obtain ⟨ha, -, -, -⟩ := ht.plus
    exact nr_le_om a ha c hc (lt_trans_FX ha ht hc (lt_plus_leftX ht) h)
  | .Om _, ht, _, hc, h =>
    le_om_of_leX (succT_FXNF ht.om.1) hc.om.1
      (succT_leX ht.om.1 hc.om.1 ((lt_om_iffX ht.om.1 hc.om.1).mp h))
  | .Xi _ _, ht, _, hc, h =>
    le_om_of_leX (succT_FXNF ht) hc.om.1 (succT_leX ht hc.om.1 ((lt_xi_omG ht hc.om.1).mp h))
  | .Psi _ _ _, ht, _, hc, h => by
    obtain ⟨rfl, c', rfl, hc'F, -⟩ := ht.psi
    exact le_om_of_leX hc'F.om.1 hc.om.1 ((lt_psi_omG ht hc.om.1).mp h)

/-- 次の正則項は `t` より大きい正則項の中で最小 -/
theorem nr_least (t : Tm) (ht : FXNF t) (σ : Tm) (hσ : FXNF σ) (hR : IsReg σ) (h : Lt t σ) :
    Le (nr t) σ := by
  rcases hR with ⟨c, rfl, -⟩ | ⟨m, rfl⟩
  · exact nr_le_om t ht c hσ h
  · exact Or.inr (nr_lt_K ht hσ.k h)

theorem IsReg.FXNF_psi {c a : Tm} (h : FXNF (.Psi .zero (.Om c) a)) : IsReg (.Om c) :=
  Or.inl ⟨c, rfl, h.psi'.2.2.1⟩

theorem IsReg.K (n : Nat) : IsReg (.K n) := Or.inr ⟨n, rfl⟩

/-! ### 前線の元は項以下 -/

theorem fr_le {R : Tm} (hR : FXNF R) : ∀ {x w : Tm}, FXNF x → w ∈ fr R x → Le w x
  | .zero, _, _, h | .one, _, _, h | .K _, _, _, h => by simp [fr] at h
  | .plus a b, w, hx, h => by
    obtain ⟨ha, hb, -, -⟩ := hx.plus
    have hw : FXNF w := hx.of_mem_subs (fr_spec h).1
    rw [fr, List.mem_append] at h
    rcases h with h | h
    · exact Or.inr (lt_of_le_of_ltX hw ha hx (fr_le hR ha h) (lt_plus_leftX hx))
    · exact Or.inr (lt_of_le_of_ltX hw hb hx (fr_le hR hb h) (lt_plus_rightX hx))
  | .Om a, w, hx, h => by
    have hw : FXNF w := hx.of_mem_subs (fr_spec h).1
    rw [fr] at h
    exact Or.inr (lt_of_le_of_ltX hw hx.om.1 hx (fr_le hR hx.om.1 h) hx.om.2.2)
  | .Xi m a, w, hx, h => by
    have hw : FXNF w := hx.of_mem_subs (fr_spec h).1
    have hwR := (fr_spec h).2
    rw [fr] at h
    by_cases hl : Lt (.Xi m a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      exact Or.inl h
    · exact Or.inr (lt_of_lt_of_leX hw hR hx hwR (le_of_not_ltX hx hR hl))
  | .Psi s p a, w, hx, h => by
    have hw : FXNF w := hx.of_mem_subs (fr_spec h).1
    have hwR := (fr_spec h).2
    rw [fr] at h
    by_cases hl : Lt (.Psi s p a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      exact Or.inl h
    · exact Or.inr (lt_of_lt_of_leX hw hR hx hwR (le_of_not_ltX hx hR hl))

end RTKA
