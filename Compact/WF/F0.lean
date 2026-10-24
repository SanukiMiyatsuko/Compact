import Compact.WF.Basic

/-! 断片 `F0`（`0`、`1`、`K_n`、`+`、`Ω`、`Ψ^0`。`Ξ` も `ξ > 0` の `Ψ^ξ` も含まない）の構文的な順序論。

* `F0NF t`：`t` は標準形で `F0` に入る。
* `ofSummands_summands`：標準形は加法的主数の列から復元できる。
* `cmp_swap_F0`・`eq_of_cmp_eq_F0`：`F0` の標準形の上で `cmp` は反対称で、`.eq` なら構文的に等しい。 -/

namespace RTKA

open Tm

/-- 断片 `F0` の項 -/
def isF0 : Tm → Bool
  | zero | one | K _ => true
  | plus a b => isF0 a && isF0 b
  | Om a => isF0 a
  | Xi _ _ => false
  | Psi xi pi a => xi == zero && isF0 pi && isF0 a

/-- `F0` の標準形 -/
def F0NF (t : Tm) : Prop := isNF t = true ∧ isF0 t = true

/-! ### 標準形の分解 -/

theorem F0NF.plus {a b : Tm} (h : F0NF (.plus a b)) :
    F0NF a ∧ F0NF b ∧ isPrincipal a = true ∧ b ≠ .zero := by
  obtain ⟨hn, hf⟩ := h
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
  simp only [isF0, Bool.and_eq_true] at hf
  exact ⟨⟨hn.1.1.2, hf.1⟩, ⟨hn.1.2, hf.2⟩, hn.1.1.1.1, hn.1.1.1.2⟩

theorem F0NF.om {a : Tm} (h : F0NF (.Om a)) : F0NF a ∧ a ≠ .zero ∧ cmp a (.Om a) = .lt := by
  obtain ⟨hn, hf⟩ := h
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
  simp only [isF0] at hf
  refine ⟨⟨hn.1.1, hf⟩, hn.1.2, ?_⟩
  have h2 := hn.2
  unfold lt at h2
  simpa using h2

theorem F0NF.not_xi {n : Nat} {a : Tm} (h : F0NF (.Xi n a)) : False := by
  have := h.2
  simp [isF0] at this

/-- `F0` の `Ψ` は `Ψ^0_{Ω_c}(α)`（`c` は後者） -/
theorem F0NF.psi {xi pi a : Tm} (h : F0NF (.Psi xi pi a)) :
    xi = .zero ∧ ∃ c, pi = .Om c ∧ F0NF (.Om c) ∧ isSucc c = true ∧ F0NF a ∧
      inC a a pi = true ∧ inC pi a pi = true := by
  obtain ⟨hn, hf⟩ := h
  simp only [isF0, Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨hxi, hpif⟩, haf⟩ := hf
  subst hxi
  simp only [isNF, Bool.and_eq_true] at hn
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, hpin⟩, han⟩, hreg⟩, _⟩, hCa⟩, _⟩, hCpi⟩, _⟩ := hn
  refine ⟨rfl, ?_⟩
  cases pi with
  | Om c => exact ⟨c, rfl, ⟨hpin, hpif⟩, hreg, ⟨han, haf⟩, hCa, hCpi⟩
  | _ => simp_all [isRegTerm, isF0]

/-! ### 和の分解 -/

theorem isNF_plus {a b : Tm} (h : isNF (.plus a b) = true) : isNF a = true ∧ isNF b = true := by
  simp only [isNF, Bool.and_eq_true] at h
  exact ⟨h.1.1.2, h.1.2⟩

theorem ofSummands_summands : ∀ t : Tm, isNF t = true → ofSummands (summands t) = t
  | .zero, _ => rfl
  | .one, _ | .K _, _ | .Om _, _ | .Xi _ _, _ | .Psi _ _ _, _ => rfl
  | .plus a b, h => by
    have hb0 : b ≠ .zero := by
      simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact h.1.1.1.2
    have ih := ofSummands_summands b (isNF_plus h).2
    rw [summands]
    cases hs : summands b with
    | nil =>
      exfalso
      cases b <;> simp_all [summands]
    | cons s ss =>
      rw [hs] at ih
      show plus a (ofSummands (s :: ss)) = plus a b
      rw [ih]

theorem eq_of_summands_eq {a b : Tm} (ha : isNF a = true) (hb : isNF b = true)
    (h : summands a = summands b) : a = b := by
  rw [← ofSummands_summands a ha, ← ofSummands_summands b hb, h]

theorem summands_F0NF : ∀ t : Tm, F0NF t → ∀ s, s ∈ summands t → F0NF s ∧ isPrincipal s = true
  | .zero, _, s, hs => by simp [summands] at hs
  | .plus a b, h, s, hs => by
    obtain ⟨ha, hb, hap, _⟩ := h.plus
    rw [summands, List.mem_cons] at hs
    cases hs with
    | inl e => rw [e]; exact ⟨ha, hap⟩
    | inr hs => exact summands_F0NF b hb s hs
  | .one, h, s, hs | .K _, h, s, hs | .Om _, h, s, hs | .Xi _ _, h, s, hs
  | .Psi _ _ _, h, s, hs => by
    simp only [summands, List.mem_singleton] at hs
    rw [hs]
    exact ⟨h, rfl⟩

/-! ### 列の比較 -/

theorem cmpList_swap : ∀ l1 l2 : List Tm,
    (∀ x, x ∈ l1 → ∀ y, y ∈ l2 → cmpP y x = (cmpP x y).swap) →
    cmpList l2 l1 = (cmpList l1 l2).swap
  | [], [], _ => by rw [cmpList_nil_nil]; rfl
  | [], _ :: _, _ => by rw [cmpList_cons_nil, cmpList_nil_cons]; rfl
  | _ :: _, [], _ => by rw [cmpList_cons_nil, cmpList_nil_cons]; rfl
  | x :: xs, y :: ys, h => by
    have hxy := h x List.mem_cons_self y List.mem_cons_self
    have ht : ∀ a, a ∈ xs → ∀ b, b ∈ ys → cmpP b a = (cmpP a b).swap :=
      fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
    cases e : cmpP x y with
    | eq =>
      have e' : cmpP y x = .eq := by rw [hxy, e]; rfl
      rw [cmpList_cons_cons_eq _ _ e, cmpList_cons_cons_eq _ _ e']
      exact cmpList_swap xs ys ht
    | lt =>
      have e' : cmpP y x = .gt := by rw [hxy, e]; rfl
      rw [cmpList_cons_cons_ne _ _ (by rw [e']; decide), cmpList_cons_cons_ne _ _ (by rw [e]; decide),
        e, e']
      rfl
    | gt =>
      have e' : cmpP y x = .lt := by rw [hxy, e]; rfl
      rw [cmpList_cons_cons_ne _ _ (by rw [e']; decide), cmpList_cons_cons_ne _ _ (by rw [e]; decide),
        e, e']
      rfl

theorem eq_of_cmpList_eq : ∀ l1 l2 : List Tm,
    (∀ x, x ∈ l1 → ∀ y, y ∈ l2 → cmpP x y = .eq → x = y) →
    cmpList l1 l2 = .eq → l1 = l2
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by rw [cmpList_nil_cons] at h; cases h
  | _ :: _, [], _, h => by rw [cmpList_cons_nil] at h; cases h
  | x :: xs, y :: ys, hxy, h => by
    cases e : cmpP x y with
    | eq =>
      rw [cmpList_cons_cons_eq _ _ e] at h
      rw [hxy x List.mem_cons_self y List.mem_cons_self e,
        eq_of_cmpList_eq xs ys (fun a ha b hb => hxy a (List.mem_cons_of_mem _ ha) b
          (List.mem_cons_of_mem _ hb)) h]
    | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e] at h; cases h
    | gt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e] at h; cases h

/-! ### `cmpP` の計算 -/

theorem summands_principal' {t : Tm} (h : isPrincipal t = true) : summands t = [t] := by
  cases t <;> simp_all [isPrincipal, summands]

theorem cmp_principal {x y : Tm} (hx : isPrincipal x = true) (hy : isPrincipal y = true) :
    cmp x y = cmpP x y := by
  rw [cmp_eq, summands_principal' hx, summands_principal' hy]
  cases e : cmpP x y with
  | eq => rw [cmpList_cons_cons_eq _ _ e, cmpList_nil_nil]
  | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]
  | gt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]

theorem cmpP_of_lev_lt {x y : Tm} (h : lev x < lev y) : cmpP x y = .lt := by
  rw [cmpP.eq_def, ite_eq_left h]

theorem cmpP_of_lev_gt {x y : Tm} (h : lev y < lev x) : cmpP x y = .gt := by
  rw [cmpP.eq_def, ite_eq_right (Nat.lt_asymm h), ite_eq_left h]

theorem cmpOmX_psi0 (a c β : Tm) :
    cmpOmX a (.Psi .zero (.Om c) β) = if cmp a c = .lt then .lt else .gt := by
  rw [cmpOmX.eq_def]
  simp only [omegaFixed, isInacc, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    beq_iff_eq]

theorem cmpP_om_psi0 {a c β : Tm} (h : lev a = lev c) :
    cmpP (.Om a) (.Psi .zero (.Om c) β) = if cmp a c = .lt then .lt else .gt := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]
  exact cmpOmX_psi0 a c β

theorem cmpP_psi0_om {a c β : Tm} (h : lev a = lev c) :
    cmpP (.Psi .zero (.Om c) β) (.Om a) = (if cmp a c = .lt then Ordering.lt else .gt).swap := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]
  rw [cmpOmX_psi0]

theorem cmpP_om_om {a b : Tm} (h : lev a = lev b) : cmpP (.Om a) (.Om b) = cmp a b := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]

theorem cmpP_psi_psi {xi pi a sg ka b : Tm} (h : lev pi = lev ka) :
    cmpP (.Psi xi pi a) (.Psi sg ka b) = cmpPsi (.Psi xi pi a) (.Psi sg ka b) := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]

theorem inC_zero (g d : Tm) : inC .zero g d = true := by
  rw [inC.eq_def]

/-- `Ψ^0_{Ω_d}(β)` と `Ω_c` の比較（同じ階） -/
theorem cmp_psi0_om {c d β : Tm} (h : lev c = lev d) :
    cmp (.Psi .zero (.Om d) β) (.Om c) = (if cmp c d = .lt then Ordering.lt else .gt).swap := by
  rw [cmp_principal rfl rfl, cmpP_psi0_om h]

/-- `cmpPsi` の `F0` での形：区間 `c`・`d` を比べ、同じ区間なら引数と `C` で比べる -/
theorem cmpPsi_psi0 {c d α β : Tm} (h : lev c = lev d) :
    cmpPsi (.Psi .zero (.Om c) α) (.Psi .zero (.Om d) β) =
      if Tm.Psi .zero (.Om c) α = .Psi .zero (.Om d) β then .eq
      else if cmp c d = .lt then .lt
      else if cmp d c = .lt then .gt
      else if (cmp α β = .lt ∧ inC α β (.Psi .zero (.Om d) β) = true ∧
          inC (.Om c) β (.Psi .zero (.Om d) β) = true) ∨
        (cmp β α ≠ .gt ∧ ¬ (inC β α (.Psi .zero (.Om c) α) = true ∧
          inC (.Om d) α (.Psi .zero (.Om c) α) = true)) then .lt
      else .gt := by
  rw [cmpPsi.eq_def]
  simp only []
  rw [cmp_psi0_om h, cmp_psi0_om h.symm, cmp_self .zero, inC_zero, inC_zero]
  by_cases hcd : cmp c d = .lt
  · simp [hcd]
  · by_cases hdc : cmp d c = .lt
    · simp [hcd, hdc]
    · simp only [hcd, hdc, ↓reduceIte]
      cases inC β α (Tm.Psi .zero (.Om c) α) <;> cases inC (Tm.Om d) α (Tm.Psi .zero (.Om c) α) <;>
        cases inC α β (Tm.Psi .zero (.Om d) β) <;> cases inC (Tm.Om c) β (Tm.Psi .zero (.Om d) β) <;>
        simp

/-! ### 反対称性と相等 -/

/-- 大きさの和が `N` 以下の `F0` の標準形の組で、`cmp` は反対称で、`.eq` なら等しい -/
def SE (N : Nat) : Prop :=
  ∀ a b : Tm, F0NF a → F0NF b → a.size + b.size ≤ N →
    cmp b a = (cmp a b).swap ∧ (cmp a b = .eq → a = b)

theorem F0NF.k {n : Nat} (h : F0NF (.K n)) : 1 ≤ n := by
  have := h.1
  simp only [isNF, decide_eq_true_eq] at this
  exact this

/-- `Ω_{K_m}` は標準形でない -/
theorem F0NF.om_ne_k {a : Tm} {m : Nat} (h : F0NF (.Om a)) : a ≠ .K m := by
  intro e
  subst e
  have h2 := h.om.2.2
  rw [cmp_principal rfl rfl, cmpP.eq_def] at h2
  simp [lev] at h2

/-- `Ψ^0_{Ω_c}(α)` どうし（同じ階）の反対称性と相等 -/
theorem psi0_SE {c d α β : Tm} (hl : lev c = lev d)
    (hcd : cmp d c = (cmp c d).swap ∧ (cmp c d = .eq → c = d))
    (hab : cmp β α = (cmp α β).swap ∧ (cmp α β = .eq → α = β)) :
    cmpPsi (.Psi .zero (.Om d) β) (.Psi .zero (.Om c) α) =
        (cmpPsi (.Psi .zero (.Om c) α) (.Psi .zero (.Om d) β)).swap ∧
      (cmpPsi (.Psi .zero (.Om c) α) (.Psi .zero (.Om d) β) = .eq →
        Tm.Psi .zero (.Om c) α = .Psi .zero (.Om d) β) := by
  rw [cmpPsi_psi0 hl, cmpPsi_psi0 hl.symm]
  by_cases h1 : cmp c d = .lt
  · have h2 : cmp d c = .gt := by rw [hcd.1, h1]; rfl
    have hne : Tm.Psi .zero (.Om c) α ≠ .Psi .zero (.Om d) β := by
      intro e
      cases e
      rw [cmp_self] at h1
      cases h1
    have hne' : Tm.Psi .zero (.Om d) β ≠ .Psi .zero (.Om c) α := fun e => hne e.symm
    simp [hne, hne', h1, h2]
  · by_cases h2 : cmp d c = .lt
    · have h1' : cmp c d = .gt := by
        cases e : cmp c d with
        | lt => exact absurd e h1
        | eq => rw [hcd.1, e] at h2; cases h2
        | gt => rfl
      have hne : Tm.Psi .zero (.Om c) α ≠ .Psi .zero (.Om d) β := by
        intro e
        cases e
        rw [cmp_self] at h2
        cases h2
      have hne' : Tm.Psi .zero (.Om d) β ≠ .Psi .zero (.Om c) α := fun e => hne e.symm
      simp [hne, hne', h1, h2]
    · have he : cmp c d = .eq := by
        cases e : cmp c d with
        | lt => exact absurd e h1
        | eq => rfl
        | gt => rw [hcd.1, e] at h2; exact absurd rfl h2
      have hcd' := hcd.2 he
      subst hcd'
      cases eab : cmp α β with
      | eq =>
        have := hab.2 eab
        subst this
        simp
      | lt =>
        have eba : cmp β α = .gt := by rw [hab.1, eab]; rfl
        have hne : α ≠ β := by intro e; subst e; rw [cmp_self] at eab; cases eab
        have hne' : β ≠ α := fun e => hne e.symm
        simp only [Tm.Psi.injEq, true_and, hne, hne', h1, eba, ↓reduceIte]
        cases inC α β (Tm.Psi .zero (.Om c) β) <;> cases inC (Tm.Om c) β (Tm.Psi .zero (.Om c) β) <;>
          simp
      | gt =>
        have eba : cmp β α = .lt := by rw [hab.1, eab]; rfl
        have hne : α ≠ β := by intro e; subst e; rw [cmp_self] at eab; cases eab
        have hne' : β ≠ α := fun e => hne e.symm
        simp only [Tm.Psi.injEq, true_and, hne, hne', h1, eba, ↓reduceIte]
        cases inC β α (Tm.Psi .zero (.Om c) α) <;> cases inC (Tm.Om c) α (Tm.Psi .zero (.Om c) α) <;>
          simp

/-- 同じ階の主要項どうしの反対称性と相等 -/
theorem cmpP_SE_same {N : Nat} (ih : SE N) {x y : Tm} (hx : F0NF x) (hy : F0NF y)
    (hpx : isPrincipal x = true) (hpy : isPrincipal y = true) (hs : x.size + y.size ≤ N + 1)
    (hl : lev x = lev y) : cmpP y x = (cmpP x y).swap ∧ (cmpP x y = .eq → x = y) := by
  cases x <;> cases y
  all_goals first
    | (exfalso; simp_all [isPrincipal, isF0, F0NF]; done)
    | skip
  case Om.Om a b =>
    have h := ih a b hx.om.1 hy.om.1 (by simp only [Tm.size] at hs; omega)
    rw [cmpP_om_om (a := a) (b := b) hl, cmpP_om_om (a := b) (b := a) hl.symm]
    exact ⟨h.1, fun e => by rw [h.2 e]⟩
  case K.Om m b =>
    have hne := hy.om_ne_k (m := m)
    rw [cmpP.eq_def, cmpP.eq_def]
    simp [hl, hne]
  case Om.K a m =>
    have hne := hx.om_ne_k (m := m)
    rw [cmpP.eq_def, cmpP.eq_def]
    simp [hl, hne]
  case K.K m n =>
    have : m = n := by simp only [lev] at hl; omega
    subst this
    rw [cmpP_self]
    exact ⟨rfl, fun _ => rfl⟩
  case Psi.Psi xi pi α sg ka β =>
    obtain ⟨hxi, c, hpi, hc, -, hα, -, -⟩ := hx.psi
    obtain ⟨hsg, d, hka, hd, -, hβ, -, -⟩ := hy.psi
    subst hxi hpi hsg hka
    have hl' : lev c = lev d := hl
    have hcd := ih c d hc.om.1 hd.om.1 (by simp only [Tm.size] at hs; omega)
    have hab := ih α β hα hβ (by simp only [Tm.size] at hs; omega)
    rw [cmpP_psi_psi (xi := .zero) (pi := .Om c) (a := α) (sg := .zero) (ka := .Om d) (b := β) hl,
      cmpP_psi_psi (xi := .zero) (pi := .Om d) (a := β) (sg := .zero) (ka := .Om c) (b := α) hl.symm]
    exact psi0_SE hl' hcd hab
  case Om.Psi a xi pi β =>
    obtain ⟨hxi, c, hpi, -, -, -, -, -⟩ := hy.psi
    subst hxi hpi
    have h' : lev a = lev c := hl
    rw [cmpP_om_psi0 h', cmpP_psi0_om h']
    by_cases h : cmp a c = .lt <;> simp [h]
  case Psi.Om xi pi β a =>
    obtain ⟨hxi, c, hpi, -, -, -, -, -⟩ := hx.psi
    subst hxi hpi
    have h' : lev a = lev c := hl.symm
    rw [cmpP_om_psi0 h', cmpP_psi0_om h']
    by_cases h : cmp a c = .lt <;> simp [h]
  case one.K n =>
    exfalso
    have := hy.k
    simp only [lev] at hl
    omega
  case K.one n =>
    exfalso
    have := hx.k
    simp only [lev] at hl
    omega
  all_goals
    simp only [cmpP.eq_def]
    simp_all [lev, F0NF, isF0]

theorem cmpP_SE {N : Nat} (ih : SE N) {x y : Tm} (hx : F0NF x) (hy : F0NF y)
    (hpx : isPrincipal x = true) (hpy : isPrincipal y = true) (hs : x.size + y.size ≤ N + 1) :
    cmpP y x = (cmpP x y).swap ∧ (cmpP x y = .eq → x = y) := by
  by_cases h1 : lev x < lev y
  · rw [cmpP_of_lev_lt h1, cmpP_of_lev_gt h1]
    exact ⟨rfl, fun h => by cases h⟩
  by_cases h2 : lev y < lev x
  · rw [cmpP_of_lev_gt h2, cmpP_of_lev_lt h2]
    exact ⟨rfl, fun h => by cases h⟩
  exact cmpP_SE_same ih hx hy hpx hpy hs (by omega)

theorem SE_succ {N : Nat} (ih : SE N) : SE (N + 1) := by
  intro a b ha hb hs
  have hP : ∀ x, x ∈ summands a → ∀ y, y ∈ summands b →
      cmpP y x = (cmpP x y).swap ∧ (cmpP x y = .eq → x = y) := by
    intro x hx y hy
    have sx := summands_F0NF a ha x hx
    have sy := summands_F0NF b hb y hy
    have := size_le_of_mem_summands a x hx
    have := size_le_of_mem_summands b y hy
    exact cmpP_SE ih sx.1 sy.1 sx.2 sy.2 (by omega)
  rw [cmp_eq a b, cmp_eq b a]
  exact ⟨cmpList_swap _ _ (fun x hx y hy => (hP x hx y hy).1),
    fun h => eq_of_summands_eq ha.1 hb.1
      (eq_of_cmpList_eq _ _ (fun x hx y hy => (hP x hx y hy).2) h)⟩

theorem SE_all : ∀ N, SE N
  | 0 => fun a _ _ _ h => absurd h (by have := Tm.size_pos a; omega)
  | N + 1 => SE_succ (SE_all N)

/-- `F0` の標準形の上で `cmp` は反対称 -/
theorem cmp_swap_F0 {a b : Tm} (ha : F0NF a) (hb : F0NF b) : cmp b a = (cmp a b).swap :=
  (SE_all _ a b ha hb (Nat.le_refl _)).1

/-- `F0` の標準形の上で `cmp a b = .eq` なら `a = b` -/
theorem eq_of_cmp_eq_F0 {a b : Tm} (ha : F0NF a) (hb : F0NF b) (h : cmp a b = .eq) : a = b :=
  (SE_all _ a b ha hb (Nat.le_refl _)).2 h

end RTKA
