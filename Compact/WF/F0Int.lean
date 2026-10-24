import Compact.WF.F0Lin

/-! 断片 `F0` の区間の構文論（整列性の証明の下準備）。

`F0` の標準形 `t` は区間 `[Ω_z, Ω_{z+1})` のどれか一つに入る（`Ω_0 = 0`、`Ω_{K_m} = K_m` とする）。
この `z` を `ix t`、区間の下端 `Ω_z` を `bot t` と書く。

* `ix_lt_ix`：区間の添字が小さければ項も小さい。
* `ix_le_ix`：項が小さければ区間の添字も大きくない。
* `isCard`：区間の下端（基数）。基数どうしの大小は添字の大小と一致する（`card_lt_iff`）。
* `k2_F0`・`ic_F0`：推移性の証明で得た K2 と IC を、全ての `F0` の標準形の `Ψ` に使える形にしたもの。 -/

namespace RTKA

open Tm

/-! ### `≤` -/

/-- `a ≤ b` -/
def Le (a b : Tm) : Prop := a = b ∨ Lt a b

theorem Le.refl (a : Tm) : Le a a := Or.inl rfl

theorem Le.of_lt {a b : Tm} (h : Lt a b) : Le a b := Or.inr h

theorem lt_of_lt_of_le {a b c : Tm} (ha : F0NF a) (hb : F0NF b) (hc : F0NF c)
    (h1 : Lt a b) (h2 : Le b c) : Lt a c := by
  rcases h2 with e | h2
  · subst e; exact h1
  · exact lt_trans_F0 ha hb hc h1 h2

theorem lt_of_le_of_lt {a b c : Tm} (ha : F0NF a) (hb : F0NF b) (hc : F0NF c)
    (h1 : Le a b) (h2 : Lt b c) : Lt a c := by
  rcases h1 with e | h1
  · subst e; exact h2
  · exact lt_trans_F0 ha hb hc h1 h2

theorem Le.trans {a b c : Tm} (ha : F0NF a) (hb : F0NF b) (hc : F0NF c)
    (h1 : Le a b) (h2 : Le b c) : Le a c := by
  rcases h1 with e | h1
  · subst e; exact h2
  · exact Or.inr (lt_of_lt_of_le ha hb hc h1 h2)

theorem not_lt_of_le {a b : Tm} (ha : F0NF a) (hb : F0NF b) (h : Le a b) : ¬ Lt b a := by
  rcases h with e | h
  · subst e; exact Lt.irrefl _
  · exact Lt.asymm ha hb h

theorem le_of_not_lt {a b : Tm} (ha : F0NF a) (hb : F0NF b) (h : ¬ Lt b a) : Le a b := by
  rcases tri ha hb with h' | h' | h'
  · exact Or.inr h'
  · exact Or.inl h'
  · exact absurd h' h

theorem le_or_lt {a b : Tm} (ha : F0NF a) (hb : F0NF b) : Le a b ∨ Lt b a := by
  rcases tri ha hb with h' | h' | h'
  · exact Or.inl (Or.inr h')
  · exact Or.inl (Or.inl h')
  · exact Or.inr h'

theorem Le.antisymm {a b : Tm} (ha : F0NF a) (hb : F0NF b) (h1 : Le a b) (h2 : Le b a) : a = b := by
  rcases h1 with e | h1
  · exact e
  · exact absurd h1 (not_lt_of_le hb ha h2)

/-! ### `0` と `1` -/

theorem F0NF.zero : F0NF .zero := ⟨rfl, rfl⟩

theorem F0NF.one : F0NF .one := ⟨rfl, rfl⟩

theorem F0NF.K' {m : Nat} (h : 1 ≤ m) : F0NF (.K m) := by
  refine ⟨?_, rfl⟩
  simp only [isNF, decide_eq_true_eq]
  exact h

theorem not_lt_zero (t : Tm) : ¬ Lt t .zero := by
  unfold Lt
  rw [cmp_eq]
  show ¬ cmpList (summands t) [] = .lt
  cases summands t with
  | nil => rw [cmpList_nil_nil]; decide
  | cons _ _ => rw [cmpList_cons_nil]; decide

theorem zero_lt {t : Tm} (ht : t ≠ .zero) : Lt .zero t := by
  unfold Lt
  rw [cmp_eq]
  show cmpList [] (summands t) = .lt
  cases hs : summands t with
  | nil => exact absurd hs (summands_ne_nil ht)
  | cons _ _ => exact cmpList_nil_cons _ _

theorem zero_le (t : Tm) : Le .zero t := by
  by_cases h : t = .zero
  · exact Or.inl h.symm
  · exact Or.inr (zero_lt h)

theorem F0NF.ne_zero_of_om {a : Tm} (h : F0NF (.Om a)) : a ≠ .zero := h.om.2.1

theorem lev_pos : ∀ {t : Tm}, F0NF t → t ≠ .zero → 1 ≤ lev t
  | .zero, _, h => absurd rfl h
  | .one, _, _ => Nat.le_refl _
  | .K _, _, _ => by simp only [lev]; omega
  | .plus a _, ht, _ => by
    obtain ⟨ha, -, hap, -⟩ := ht.plus
    have : a ≠ .zero := by intro e; subst e; simp [isPrincipal] at hap
    show 1 ≤ lev a
    exact lev_pos ha this
  | .Om a, ht, _ => by show 1 ≤ lev a; exact lev_pos ht.om.1 ht.om.2.1
  | .Xi _ _, ht, _ => (ht.not_xi).elim
  | .Psi _ pi _, ht, _ => by
    obtain ⟨-, c, hpi, hc, -⟩ := ht.psi
    subst hpi
    show 1 ≤ lev (.Om c)
    exact lev_pos hc (by intro e; cases e)

/-- 主要項は `1` 以上 -/
theorem cmpP_one_ne_gt {h : Tm} (hF : F0NF h) (hp : isPrincipal h = true) : cmpP .one h ≠ .gt := by
  have hl : 1 ≤ lev h := lev_pos hF (by intro e; subst e; simp [isPrincipal] at hp)
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · rw [cmpP_of_lev_lt (by simp only [lev]; exact hl)]; decide
  · rw [cmpP.eq_def]
    simp only [lev, ← hl, Nat.lt_irrefl, ↓reduceIte]
    cases h <;> simp

theorem lt_one {u : Tm} (hu : F0NF u) (h : Lt u .one) : u = .zero := by
  cases hs : summands u with
  | nil => cases u <;> simp_all [summands]
  | cons x xs =>
    exfalso
    unfold Lt at h
    rw [cmp_eq, hs, show summands Tm.one = [.one] from rfl] at h
    have hx := summands_F0NF u hu x (by rw [hs]; exact List.mem_cons_self)
    have hl : 1 ≤ lev x := lev_pos hx.1 (by intro e; subst e; simp [isPrincipal] at hx)
    rcases cmpList_lt_cases h with e | ⟨e, e'⟩
    · rcases Nat.lt_or_eq_of_le hl with hl | hl
      · rw [cmpP_of_lev_gt (by simp only [lev]; exact hl)] at e; cases e
      · exact not_lt_isBot (by simp only [lev]; exact hl.symm) rfl hx.1 F0NF.one e
    · cases xs with
      | nil => rw [cmpList_nil_nil] at e'; cases e'
      | cons _ _ => rw [cmpList_cons_nil] at e'; cases e'

/-! ### 和 -/

theorem summands_plus (a b : Tm) : summands (.plus a b) = a :: summands b := rfl

/-- 先頭が `a` の和は `a` より大きい -/
theorem lt_plus_left {a b : Tm} (h : F0NF (.plus a b)) : Lt a (.plus a b) := by
  obtain ⟨-, -, hap, hb0⟩ := h.plus
  unfold Lt
  rw [cmp_eq, summands_principal' hap, summands_plus,
    cmpList_cons_cons_eq _ _ (cmpP_self a)]
  cases hs : summands b with
  | nil => exact absurd hs (summands_ne_nil hb0)
  | cons _ _ => exact cmpList_nil_cons _ _

theorem lt_plus_right : ∀ {a b : Tm}, F0NF (.plus a b) → Lt b (.plus a b)
  | a, b, h => by
    obtain ⟨-, hb, hap, hb0⟩ := h.plus
    cases hs : summands b with
    | nil => exact absurd hs (summands_ne_nil hb0)
    | cons x xs =>
      have hxa := h.plus_head hs
      have hx := summands_F0NF b hb x (by rw [hs]; exact List.mem_cons_self)
      have hxa' : cmpP x a ≠ .gt := by rwa [← cmp_principal hx.2 hap]
      unfold Lt
      rw [cmp_eq, hs, summands_plus, hs]
      cases e : cmpP x a with
      | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]
      | gt => exact absurd e hxa'
      | eq =>
        rw [cmpList_cons_cons_eq _ _ e]
        have hxe : x = a := eq_of_cmpP_eq hx.1 (summands_F0NF _ h a (by simp [summands])).1 hx.2 hap e
        subst hxe
        cases b with
        | zero => exact absurd rfl hb0
        | plus p q =>
          rw [summands_plus, List.cons.injEq] at hs
          obtain ⟨rfl, hq⟩ := hs
          have := lt_plus_right hb
          unfold Lt at this
          rw [cmp_eq, summands_plus] at this
          rwa [← hq]
        | _ =>
          simp only [summands, List.cons.injEq] at hs
          rw [← hs.2]
          exact cmpList_nil_cons _ _

/-- 和 `p + s` より小さい項は `p` より小さいか、`p` か、`p + s'`（`s' < s`） -/
theorem lt_plus_cases {p s u : Tm} (h : F0NF (.plus p s)) (hu : F0NF u) (hlt : Lt u (.plus p s)) :
    Lt u p ∨ u = p ∨ ∃ u', u = .plus p u' ∧ F0NF u' ∧ Lt u' s := by
  obtain ⟨hp, hs, hpp, -⟩ := h.plus
  cases hus : summands u with
  | nil =>
    have : u = .zero := by cases u <;> simp_all [summands]
    subst this
    exact Or.inl (zero_lt (by intro e; subst e; simp [isPrincipal] at hpp))
  | cons x xs =>
    have hx := summands_F0NF u hu x (by rw [hus]; exact List.mem_cons_self)
    unfold Lt at hlt
    rw [cmp_eq, hus, summands_plus] at hlt
    rcases cmpList_lt_cases hlt with e | ⟨e, e'⟩
    · exact Or.inl (lt_of_head_lt hpp hus e)
    · have hxp := eq_of_cmpP_eq hx.1 hp hx.2 hpp e
      subst hxp
      cases u with
      | zero => simp [summands] at hus
      | plus a b =>
        rw [summands_plus, List.cons.injEq] at hus
        obtain ⟨rfl, hb⟩ := hus
        refine Or.inr (Or.inr ⟨b, rfl, hu.plus.2.1, ?_⟩)
        unfold Lt
        rw [cmp_eq, hb]
        exact e'
      | _ =>
        simp only [summands, List.cons.injEq] at hus
        exact Or.inr (Or.inl hus.1)

/-- 先頭の項は和以下 -/
theorem head_le {t h : Tm} {rest : List Tm} (ht : F0NF t) (hs : summands t = h :: rest) : Le h t := by
  cases t with
  | zero => simp [summands] at hs
  | plus a b =>
    rw [summands_plus, List.cons.injEq] at hs
    rw [← hs.1]
    exact Or.inr (lt_plus_left ht)
  | _ =>
    simp only [summands, List.cons.injEq] at hs
    rw [hs.1]
    exact Le.refl _

/-! ### 階 -/

theorem lt_of_lev_lt {a b : Tm} (ha : F0NF a) (hb : F0NF b) (h : lev a < lev b) : Lt a b := by
  by_cases ha0 : a = .zero
  · subst ha0
    exact zero_lt (by intro e; subst e; simp [lev] at h)
  · have hb0 : b ≠ .zero := by intro e; subst e; simp [lev] at h
    cases hsa : summands a with
    | nil => exact absurd hsa (summands_ne_nil ha0)
    | cons x xs =>
      cases hsb : summands b with
      | nil => exact absurd hsb (summands_ne_nil hb0)
      | cons y ys =>
        unfold Lt
        rw [cmp_eq, hsa, hsb]
        have e : cmpP x y = .lt := cmpP_of_lev_lt (by rw [lev_head hsa, lev_head hsb]; exact h)
        rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]

theorem lev_le_of_lt {a b : Tm} (ha : F0NF a) (hb : F0NF b) (h : Lt a b) : lev a ≤ lev b :=
  Nat.le_of_not_lt (fun h' => Lt.asymm ha hb h (lt_of_lev_lt hb ha h'))

/-! ### `Ω` の単調性 -/

theorem lt_om_iff {a b : Tm} (ha : F0NF a) (hb : F0NF b) : Lt (.Om a) (.Om b) ↔ Lt a b := by
  rcases Nat.lt_trichotomy (lev a) (lev b) with h | h | h
  · constructor
    · intro _; exact lt_of_lev_lt ha hb h
    · intro _
      rw [lt_principal_iff rfl rfl, cmpP_of_lev_lt (by simp only [lev]; exact h)]
  · exact lt_om_om a b h
  · constructor
    · intro h'
      rw [lt_principal_iff rfl rfl, cmpP_of_lev_gt (by simp only [lev]; exact h)] at h'
      cases h'
    · intro h'; exact absurd (lt_of_lev_lt hb ha h) (Lt.asymm ha hb h')

theorem le_om_of_le {a b : Tm} (ha : F0NF a) (hb : F0NF b) (h : Le a b) : Le (.Om a) (.Om b) := by
  rcases h with e | h
  · subst e; exact Le.refl _
  · exact Or.inr ((lt_om_iff ha hb).mpr h)

/-! ### 後者と前者 -/

/-- `z + 1` -/
def succT : Tm → Tm
  | .zero => .one
  | .plus a b => .plus a (succT b)
  | t => .plus t .one

/-- 後者 `c = z + 1` の `z` -/
def pred : Tm → Tm
  | .plus a .one => a
  | .plus a b => .plus a (pred b)
  | _ => .zero

theorem summands_succT : ∀ z : Tm, summands (succT z) = summands z ++ [.one]
  | .zero => rfl
  | .plus a b => by rw [succT, summands_plus, summands_plus, summands_succT b]; rfl
  | .one | .K _ | .Om _ | .Xi _ _ | .Psi _ _ _ => rfl

theorem succT_ne_zero (z : Tm) : succT z ≠ .zero := by
  cases z <;> simp [succT]

theorem succT_ne_K (z : Tm) (m : Nat) : succT z ≠ .K m := by
  cases z <;> simp [succT]

/-- `F0NF` な和を作る -/
theorem F0NF.mk_plus {a b : Tm} (ha : F0NF a) (hb : F0NF b) (hap : isPrincipal a = true)
    (hb0 : b ≠ .zero) (hh : ∀ h rest, summands b = h :: rest → cmp h a ≠ .gt) :
    F0NF (.plus a b) := by
  refine ⟨?_, ?_⟩
  · simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq]
    refine ⟨⟨⟨⟨hap, hb0⟩, ha.1⟩, hb.1⟩, ?_⟩
    cases hs : summands b with
    | nil => exact absurd hs (summands_ne_nil hb0)
    | cons h rest =>
      have := hh h rest hs
      simpa using this
  · simp only [isF0, Bool.and_eq_true]
    exact ⟨ha.2, hb.2⟩

theorem succT_F0NF : ∀ {z : Tm}, F0NF z → F0NF (succT z)
  | .zero, _ => F0NF.one
  | .plus a b, hz => by
    obtain ⟨ha, hb, hap, hb0⟩ := hz.plus
    refine F0NF.mk_plus ha (succT_F0NF hb) hap (succT_ne_zero b) ?_
    intro h rest hs
    rw [summands_succT] at hs
    cases hs' : summands b with
    | nil => exact absurd hs' (summands_ne_nil hb0)
    | cons h' rest' =>
      rw [hs', List.cons_append, List.cons.injEq] at hs
      rw [← hs.1]
      exact hz.plus_head hs'
  | .Xi _ _, hz => (hz.not_xi).elim
  | .one, hz | .K _, hz | .Om _, hz | .Psi _ _ _, hz => by
    refine F0NF.mk_plus hz F0NF.one rfl (by intro e; cases e) ?_
    intro h rest hs
    simp only [summands, List.cons.injEq] at hs
    rw [← hs.1, cmp_principal rfl rfl]
    exact cmpP_one_ne_gt hz rfl

theorem cmpList_append_lt (l m : List Tm) (hm : m ≠ []) : cmpList l (l ++ m) = .lt := by
  induction l with
  | nil =>
    cases m with
    | nil => exact absurd rfl hm
    | cons _ _ => exact cmpList_nil_cons _ _
  | cons x xs ih => rw [List.cons_append, cmpList_cons_cons_eq _ _ (cmpP_self x)]; exact ih

theorem lt_succT (z : Tm) : Lt z (succT z) := by
  unfold Lt
  rw [cmp_eq, summands_succT]
  exact cmpList_append_lt _ _ (by simp)

/-- `z < c` なら `z + 1 ≤ c`（`cmp` が `.gt` でない） -/
theorem cmpList_succ_ne_gt : ∀ (l m : List Tm), (∀ y, y ∈ m → F0NF y ∧ isPrincipal y = true) →
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
    | gt => exact absurd e (cmpP_one_ne_gt hy.1 hy.2)
  | _ :: _, [], _, h => by rw [cmpList_cons_nil] at h; cases h
  | x :: xs, y :: ys, hm, h => by
    rw [List.cons_append]
    rcases cmpList_lt_cases h with e | ⟨e, e'⟩
    · rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]; decide
    · rw [cmpList_cons_cons_eq _ _ e]
      exact cmpList_succ_ne_gt xs ys (fun y hy => hm y (List.mem_cons_of_mem _ hy)) e'

theorem succT_le {z c : Tm} (hz : F0NF z) (hc : F0NF c) (h : Lt z c) : Le (succT z) c := by
  have hne : cmp (succT z) c ≠ .gt := by
    rw [cmp_eq, summands_succT]
    unfold Lt at h
    rw [cmp_eq] at h
    exact cmpList_succ_ne_gt _ _ (summands_F0NF c hc) h
  rcases tri (succT_F0NF hz) hc with h' | h' | h'
  · exact Or.inr h'
  · exact Or.inl h'
  · exfalso
    apply hne
    unfold Lt at h'
    rw [cmp_swap_F0 hc (succT_F0NF hz), h']
    rfl

theorem pred_succT : ∀ {z : Tm}, F0NF z → pred (succT z) = z
  | .zero, _ => rfl
  | .plus a b, hz => by
    obtain ⟨-, hb, -, hb0⟩ := hz.plus
    have ih := pred_succT hb
    cases b with
    | zero => exact absurd rfl hb0
    | plus p q => simp only [succT, pred] at ih ⊢; rw [ih]
    | _ => simp only [succT, pred] at ih ⊢
  | .Xi _ _, hz => (hz.not_xi).elim
  | .one, _ | .K _, _ | .Om _, _ | .Psi _ _ _, _ => rfl

theorem getLast_summands_one : ∀ {c : Tm}, F0NF c → isSucc c = true →
    c = .one ∨ ∃ a b, c = .plus a b
  | .zero, _, h => by simp [isSucc, summands] at h
  | .one, _, _ => Or.inl rfl
  | .plus a b, _, _ => Or.inr ⟨a, b, rfl⟩
  | .K _, _, h | .Om _, _, h | .Xi _ _, _, h | .Psi _ _ _, _, h => by simp [isSucc, summands] at h

/-- 後者 `c` は `pred c + 1` で、`pred c` は標準形 -/
theorem succT_pred : ∀ {c : Tm}, F0NF c → isSucc c = true → succT (pred c) = c ∧ F0NF (pred c)
  | .zero, _, h => by simp [isSucc, summands] at h
  | .one, _, _ => ⟨rfl, F0NF.zero⟩
  | .plus a b, hc, hs => by
    obtain ⟨ha, hb, hap, hb0⟩ := hc.plus
    have hsb : isSucc b = true := by
      simp only [isSucc, summands_plus] at hs ⊢
      cases hsb : summands b with
      | nil => exact absurd hsb (summands_ne_nil hb0)
      | cons x xs => rw [hsb, List.getLast?_cons_cons] at hs; rw [← hsb] at hs ⊢; exact hs
    rcases getLast_summands_one hb hsb with e | ⟨p, q, e⟩
    · subst e
      refine ⟨?_, ha⟩
      cases a <;> simp_all [isPrincipal, succT, pred]
    · subst e
      obtain ⟨ih1, ih2⟩ := succT_pred hb hsb
      refine ⟨?_, ?_⟩
      · show Tm.plus a (succT (pred (.plus p q))) = _
        rw [ih1]
      · refine F0NF.mk_plus ha ih2 hap ?_ ?_
        · intro e; rw [e] at ih1; simp [succT] at ih1
        · intro h rest hs'
          have : summands (succT (pred (.plus p q))) = h :: (rest ++ [.one]) := by
            rw [summands_succT, hs']; rfl
          rw [ih1, summands_plus] at this
          rw [List.cons.injEq] at this
          rw [← this.1]
          exact hc.plus_head rfl
  | .K _, _, h | .Om _, _, h | .Xi _ _, _, h | .Psi _ _ _, _, h => by simp [isSucc, summands] at h

/-- `z < c`、`c` は後者なら `z ≤ pred c` -/
theorem le_pred {z c : Tm} (hz : F0NF z) (hc : F0NF c) (hs : isSucc c = true) (h : Lt z c) :
    Le z (pred c) := by
  obtain ⟨e, hp⟩ := succT_pred hc hs
  apply le_of_not_lt hz hp
  intro h'
  have := succT_le hp hz h'
  rw [e] at this
  exact not_lt_of_le hc hz this h

end RTKA

namespace RTKA

open Tm

/-! ### `Ω_z` の標準形 -/

/-- `K_m < y` なら `K_m < Ω_y` -/
theorem K_lt_om {m : Nat} {y : Tm} (hm : F0NF (.K m)) (hy : F0NF y) (h : Lt (.K m) y) :
    Lt (.K m) (.Om y) := by
  have hl := lev_le_of_lt hm hy h
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · rw [lt_principal_iff rfl rfl, cmpP_of_lev_lt (by simp only [lev] at hl ⊢; exact hl)]
  · rw [lt_principal_iff rfl rfl, cmpP.eq_def]
    simp only [lev] at hl
    simp only [lev, ← hl, Nat.lt_irrefl, ↓reduceIte]
    have hne : y ≠ .K m := fun e => by subst e; exact Lt.irrefl _ h
    simp [hne]

/-- 主要項 `h ≠ K_m` で `h ≤ y` なら `h < Ω_y` -/
theorem principal_lt_om {h y : Tm} (hF : F0NF h) (hp : isPrincipal h = true)
    (hK : ∀ m, h ≠ .K m) (hy : F0NF y) (hle : Le h y) : Lt h (.Om y) := by
  cases h with
  | zero => simp [isPrincipal] at hp
  | plus _ _ => simp [isPrincipal] at hp
  | K m => exact absurd rfl (hK m)
  | Xi _ _ => exact (hF.not_xi).elim
  | one =>
    have hy0 : y ≠ .zero := by
      intro e; subst e
      rcases hle with e | e
      · cases e
      · exact not_lt_zero _ e
    have hl : 1 ≤ lev y := lev_pos hy hy0
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · rw [lt_principal_iff rfl rfl, cmpP_of_lev_lt (by simp only [lev]; exact hl)]
    · rw [lt_principal_iff rfl rfl, cmpP.eq_def]
      simp only [lev, ← hl, Nat.lt_irrefl, ↓reduceIte]
  | Om x =>
    have hx := hF.om
    rw [lt_om_iff hx.1 hy]
    exact lt_of_lt_of_le hx.1 hF hy hx.2.2 hle
  | Psi s p β =>
    obtain ⟨rfl, c, rfl, hc, -⟩ := hF.psi
    have hcx : Lt c (.Psi .zero (.Om c) β) := cx _ c β (Nat.le_refl _) hF
    have hcF : F0NF c := hc.om.1
    have hcy : Lt c y := lt_of_lt_of_le hcF hF hy hcx hle
    have hl := lev_le_of_lt hcF hy hcy
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · rw [lt_principal_iff rfl rfl, cmpP_of_lev_lt (by simp only [lev]; exact hl)]
    · rw [lt_psi_om y c β hl.symm]
      exact Lt.asymm hcF hy hcy

/-- `0` でも `K_m` でもない標準形 `z` について `Ω_z` は標準形 -/
theorem F0NF.om_of {z : Tm} (hz : F0NF z) (h0 : z ≠ .zero) (hK : ∀ m, z ≠ .K m) : F0NF (.Om z) := by
  have hlt : Lt z (.Om z) := by
    cases hs : summands z with
    | nil => exact absurd hs (summands_ne_nil h0)
    | cons h rest =>
      have hh := summands_F0NF z hz h (by rw [hs]; exact List.mem_cons_self)
      have hle := head_le hz hs
      have : Lt h (.Om z) := by
        cases h with
        | K m =>
          rcases hle with e | e
          · exact absurd e.symm (hK m)
          · exact K_lt_om hh.1 hz e
        | _ => exact principal_lt_om hh.1 hh.2 (fun m e => by cases e) hz hle
      exact lt_of_head_lt rfl hs ((lt_principal_iff hh.2 rfl).mp this)
  refine ⟨?_, hz.2⟩
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq]
  refine ⟨⟨hz.1, h0⟩, ?_⟩
  unfold lt
  unfold Lt at hlt
  simp [hlt]

theorem F0NF.om_succT {z : Tm} (hz : F0NF z) : F0NF (.Om (succT z)) :=
  F0NF.om_of (succT_F0NF hz) (succT_ne_zero z) (succT_ne_K z)

/-! ### 区間 -/

/-- 区間の添字：`t` は `[Ω_{ix t}, Ω_{ix t + 1})` に入る（`Ω_0 = 0`、`Ω_{K_m} = K_m`） -/
def ix : Tm → Tm
  | .K m => .K m
  | .plus a _ => ix a
  | .Om a => a
  | .Psi _ (.Om c) _ => pred c
  | _ => .zero

/-- 添字 `z` の基数 `Ω_z`（`Ω_0 = 0`、`Ω_{K_m} = K_m`） -/
def cardOf : Tm → Tm
  | .zero => .zero
  | .K m => .K m
  | z => .Om z

/-- 区間の下端 -/
def bot (t : Tm) : Tm := cardOf (ix t)

/-- 区間の下端になる項（基数） -/
def isCard (κ : Tm) : Prop := F0NF κ ∧ bot κ = κ

/-- 区間の添字になる項 -/
def isIdx (z : Tm) : Prop := z = .zero ∨ (∃ m, z = .K m ∧ 1 ≤ m) ∨ F0NF (.Om z)

theorem isIdx.F0NF {z : Tm} (h : isIdx z) : F0NF z := by
  rcases h with rfl | ⟨m, rfl, hm⟩ | h
  · exact F0NF.zero
  · exact F0NF.K' hm
  · exact h.om.1

theorem cardOf_om {z : Tm} (h : F0NF (.Om z)) : cardOf z = .Om z := by
  have h0 := h.ne_zero_of_om
  have hK : ∀ m, z ≠ .K m := fun m => h.om_ne_k
  cases z with
  | zero => exact absurd rfl h0
  | K m => exact absurd rfl (hK m)
  | _ => rfl

theorem isIdx.card {z : Tm} (h : isIdx z) : isCard (cardOf z) ∧ ix (cardOf z) = z := by
  rcases h with rfl | ⟨m, rfl, hm⟩ | h
  · exact ⟨⟨F0NF.zero, rfl⟩, rfl⟩
  · exact ⟨⟨F0NF.K' hm, rfl⟩, rfl⟩
  · rw [cardOf_om h]
    exact ⟨⟨h, by rw [bot, ix, cardOf_om h]⟩, rfl⟩

/-- `Ψ` の区間の添字は後者の前者 -/
theorem ix_psi (c β : Tm) : ix (.Psi .zero (.Om c) β) = pred c := rfl

theorem isIdx_pred {c : Tm} (hc : F0NF c) (hs : isSucc c = true) : isIdx (pred c) := by
  have hp := (succT_pred hc hs).2
  cases e : pred c with
  | zero => exact Or.inl rfl
  | K m => rw [e] at hp; exact Or.inr (Or.inl ⟨m, rfl, hp.k⟩)
  | _ =>
    rw [e] at hp
    exact Or.inr (Or.inr (F0NF.om_of hp (by intro e; cases e) (fun m e => by cases e)))

theorem ix_idx : ∀ {t : Tm}, F0NF t → isIdx (ix t)
  | .zero, _ | .one, _ => Or.inl rfl
  | .K m, h => Or.inr (Or.inl ⟨m, rfl, h.k⟩)
  | .plus a _, h => by show isIdx (ix a); exact ix_idx h.plus.1
  | .Om _, h => Or.inr (Or.inr h)
  | .Xi _ _, h => (h.not_xi).elim
  | .Psi _ _ _, h => by
    obtain ⟨rfl, c, rfl, hc, hs, -⟩ := h.psi
    exact isIdx_pred hc.om.1 hs

theorem ix_F0NF {t : Tm} (h : F0NF t) : F0NF (ix t) := (ix_idx h).F0NF

theorem bot_card {t : Tm} (h : F0NF t) : isCard (bot t) ∧ ix (bot t) = ix t :=
  (ix_idx h).card

theorem bot_F0NF {t : Tm} (h : F0NF t) : F0NF (bot t) := (bot_card h).1.1

theorem lev_succT {z : Tm} (h : z ≠ .zero) : lev (succT z) = lev z := by
  cases z with
  | zero => exact absurd rfl h
  | _ => rfl

/-- 後者 `c` の前者の区間の下端は `Ψ_c(β)` 以下 -/
theorem cardOf_pred_le_psi {c β : Tm} (h : F0NF (.Psi .zero (.Om c) β)) :
    Le (cardOf (pred c)) (.Psi .zero (.Om c) β) := by
  obtain ⟨-, c', hc', hcF, hs, -⟩ := h.psi
  cases hc'
  obtain ⟨e, hp⟩ := succT_pred hcF.om.1 hs
  rcases isIdx_pred hcF.om.1 hs with h0 | ⟨m, hm, hm1⟩ | hO
  · rw [h0]; exact zero_le _
  · rw [hm]
    refine Or.inr ?_
    rw [hm] at e
    show Lt (.K m) _
    rw [← e, lt_principal_iff rfl rfl, cmpP.eq_def]
    simp only [lev, succT, Nat.lt_irrefl, ↓reduceIte]
  · rw [cardOf_om hO]
    refine Or.inr ?_
    have hl : lev (pred c) = lev c := by
      have := lev_succT (hO.ne_zero_of_om)
      rw [e] at this
      exact this.symm
    rw [lt_om_psi (pred c) c β hl]
    have := lt_succT (pred c)
    rwa [e] at this

theorem bot_le : ∀ {t : Tm}, F0NF t → Le (bot t) t
  | .zero, _ => Le.refl _
  | .one, _ => zero_le _
  | .K _, _ => Le.refl _
  | .plus a b, h => by
    show Le (bot a) (.plus a b)
    exact Le.trans (bot_F0NF h.plus.1) h.plus.1 h (bot_le h.plus.1) (Or.inr (lt_plus_left h))
  | .Om a, h => by
    show Le (cardOf a) (.Om a)
    rw [cardOf_om h]
    exact Le.refl _
  | .Xi _ _, h => (h.not_xi).elim
  | .Psi _ _ _, h => by
    obtain ⟨rfl, c, rfl, -⟩ := h.psi
    exact cardOf_pred_le_psi h

/-- `t < Ω_{ix t + 1}` -/
theorem lt_om_succ_ix : ∀ {t : Tm}, F0NF t → Lt t (.Om (succT (ix t)))
  | .zero, _ => zero_lt (by intro e; cases e)
  | .one, _ => by
    show Lt .one (.Om .one)
    rw [lt_principal_iff rfl rfl, cmpP.eq_def]
    simp only [lev, Nat.lt_irrefl, ↓reduceIte]
  | .K m, h => K_lt_om h (succT_F0NF h) (lt_succT _)
  | .plus a b, h => by
    show Lt (.plus a b) (.Om (succT (ix a)))
    have := lt_om_succ_ix h.plus.1
    exact lt_of_head_lt rfl (summands_plus a b) ((lt_principal_iff h.plus.2.2.1 rfl).mp this)
  | .Om a, h => by
    show Lt (.Om a) (.Om (succT a))
    exact (lt_om_iff h.om.1 (succT_F0NF h.om.1)).mpr (lt_succT a)
  | .Xi _ _, h => (h.not_xi).elim
  | .Psi _ _ _, h => by
    obtain ⟨rfl, c, rfl, hc, hs, -⟩ := h.psi
    show Lt _ (.Om (succT (pred c)))
    rw [(succT_pred hc.om.1 hs).1]
    exact lt_psi_om_self c _

theorem lev_lt_of_lt_K {z : Tm} {m : Nat} (hz : F0NF z) (hm : F0NF (.K m)) (h : Lt z (.K m)) :
    lev z < m + 1 := by
  cases hs : summands z with
  | nil =>
    have : z = .zero := by cases z <;> simp_all [summands]
    subst this
    simp [lev]
  | cons x xs =>
    have hx := summands_F0NF z hz x (by rw [hs]; exact List.mem_cons_self)
    unfold Lt at h
    rw [cmp_eq, hs, show summands (Tm.K m) = [.K m] from rfl] at h
    have hl := lev_head hs
    rcases cmpList_lt_cases h with e | ⟨-, e'⟩
    · have := lev_le_of_cmpP_lt e
      simp only [lev] at this
      rcases Nat.lt_or_eq_of_le this with h1 | h1
      · rw [← hl]; exact h1
      · exact absurd e (not_lt_isBot (by simp only [lev]; exact h1) rfl hx.1 hm)
    · cases xs with
      | nil => rw [cmpList_nil_nil] at e'; cases e'
      | cons _ _ => rw [cmpList_cons_nil] at e'; cases e'

/-- 添字 `z < z'` なら `Ω_{z+1} ≤ Ω_{z'}` -/
theorem om_succT_le_card {z z' : Tm} (hz : isIdx z) (hz' : isIdx z') (h : Lt z z') :
    Le (.Om (succT z)) (cardOf z') := by
  rcases hz' with rfl | ⟨m, rfl, hm⟩ | hO
  · exact absurd h (not_lt_zero _)
  · refine Or.inr ?_
    show Lt _ (.K m)
    apply lt_of_lev_lt (F0NF.om_succT hz.F0NF) (F0NF.K' hm)
    show lev (succT z) < m + 1
    by_cases h0 : z = .zero
    · subst h0
      show 1 < m + 1
      omega
    · rw [lev_succT h0]
      exact lev_lt_of_lt_K hz.F0NF (F0NF.K' hm) h
  · rw [cardOf_om hO]
    exact le_om_of_le (succT_F0NF hz.F0NF) hO.om.1 (succT_le hz.F0NF hO.om.1 h)

/-- 区間の添字が小さければ項も小さい -/
theorem ix_lt_ix {s t : Tm} (hs : F0NF s) (ht : F0NF t) (h : Lt (ix s) (ix t)) : Lt s t :=
  lt_of_lt_of_le hs (F0NF.om_succT (ix_F0NF hs)) ht (lt_om_succ_ix hs)
    (Le.trans (F0NF.om_succT (ix_F0NF hs)) (bot_F0NF ht) ht
      (om_succT_le_card (ix_idx hs) (ix_idx ht) h) (bot_le ht))

/-- 項が小さければ区間の添字も大きくない -/
theorem ix_le_ix {s t : Tm} (hs : F0NF s) (ht : F0NF t) (h : Lt s t) : Le (ix s) (ix t) := by
  rcases le_or_lt (ix_F0NF hs) (ix_F0NF ht) with h' | h'
  · exact h'
  · exact absurd (ix_lt_ix ht hs h') (Lt.asymm hs ht h)

theorem ix_le_ix' {s t : Tm} (hs : F0NF s) (ht : F0NF t) (h : Le s t) : Le (ix s) (ix t) := by
  rcases h with e | h
  · subst e; exact Le.refl _
  · exact ix_le_ix hs ht h

/-! ### 基数 -/

theorem card_eq {κ μ : Tm} (hκ : isCard κ) (hμ : isCard μ) (h : ix κ = ix μ) : κ = μ := by
  rw [← hκ.2, ← hμ.2]
  unfold bot
  rw [h]

theorem card_lt_iff {κ μ : Tm} (hκ : isCard κ) (hμ : isCard μ) : Lt κ μ ↔ Lt (ix κ) (ix μ) := by
  constructor
  · intro h
    rcases ix_le_ix hκ.1 hμ.1 h with e | e
    · exact absurd (card_eq hκ hμ e) h.ne
    · exact e
  · exact ix_lt_ix hκ.1 hμ.1

theorem card_le_iff {κ μ : Tm} (hκ : isCard κ) (hμ : isCard μ) : Le κ μ ↔ Le (ix κ) (ix μ) := by
  constructor
  · exact ix_le_ix' hκ.1 hμ.1
  · intro h
    rcases h with e | e
    · exact Or.inl (card_eq hκ hμ e)
    · exact Or.inr (ix_lt_ix hκ.1 hμ.1 e)

/-- 基数 `κ ≤ t` なら `κ ≤ bot t` -/
theorem card_le_bot {κ t : Tm} (hκ : isCard κ) (ht : F0NF t) (h : Le κ t) : Le κ (bot t) := by
  obtain ⟨hb, hix⟩ := bot_card ht
  rw [card_le_iff hκ hb, hix]
  exact ix_le_ix' hκ.1 ht h

/-- 区間の添字が等しい基数は `bot` -/
theorem bot_eq_of_ix {κ t : Tm} (hκ : isCard κ) (ht : F0NF t) (h : ix t = ix κ) : bot t = κ := by
  obtain ⟨hb, hix⟩ := bot_card ht
  exact card_eq hb hκ (by rw [hix, h])

/-! ### K2・IC（全ての `F0` の標準形の `Ψ` について） -/

theorem k2_ic_F0 {c γ : Tm} (ht : F0NF (.Psi .zero (.Om c) γ)) :
    inC γ γ (.Psi .zero (.Om c) γ) = true ∧ ∀ g, inC (.Om c) g (.Psi .zero (.Om c) γ) = true := by
  have hcl : ∀ s, s ∈ subs (Tm.Psi .zero (.Om c) γ) → ∀ r, r ∈ subs s →
      r ∈ subs (Tm.Psi .zero (.Om c) γ) := fun _ hs _ hr => subs_trans hs hr
  have hNF : ∀ s, s ∈ subs (Tm.Psi .zero (.Om c) γ) → F0NF s := fun _ hs => ht.of_mem_subs hs
  obtain ⟨-, hK2, hIC⟩ := lin_closed _ _ (Nat.le_refl _) hcl hNF
  exact ⟨hK2 c γ (self_mem_subs _), fun g => hIC c γ g (self_mem_subs _)⟩

/-- 同じ区間の `Ψ` どうしの比較 -/
theorem lt_psi_same_F0 {c α β : Tm} (hx : F0NF (.Psi .zero (.Om c) α))
    (hy : F0NF (.Psi .zero (.Om c) β)) (hne : α ≠ β) :
    Lt (.Psi .zero (.Om c) α) (.Psi .zero (.Om c) β) ↔
      (Lt α β ∧ inC α β (.Psi .zero (.Om c) β) = true) ∨
        (Lt β α ∧ inC β α (.Psi .zero (.Om c) α) = false) :=
  lt_psi_same_iff hx hy hne (k2_ic_F0 hx).2 (k2_ic_F0 hy).2

end RTKA
