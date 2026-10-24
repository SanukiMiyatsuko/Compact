import Compact.Additive

/-! 構成的な整列性証明（`Compact/WF`）の土台：`cmp`・`inC`・前線 `fr` の構文的な性質。

順序数・`Classical.choice`・大基数の仮定を使わず、項の大きさについての帰納法だけで示す。

* `cmp` の展開（和は先頭の主要項から辞書式、主要項は階・形ごと）と `cmp_self`。
* `Lt`・`Le`、部分項の一覧 `subs`、後者 `succT`。
* `inC`（`α ∈ C(γ, δ)`）の展開と単調性。
* 前線 `fr R x`（`x` の `R` 未満の極大の崩壊の節点）と、`inC` の前線による言い換え。
* 体系全体の標準形 `WNF`、順序の性質を仮定せずに成り立つ比較の展開、次の正則項 `nrY`（`RTKA.W`）。 -/

namespace RTKA

open Tm

theorem cmpList_nil_nil : cmpList [] [] = .eq := by rw [cmpList]

theorem cmpList_nil_cons (y : Tm) (ys : List Tm) : cmpList [] (y :: ys) = .lt := by rw [cmpList]

theorem cmpList_cons_nil (x : Tm) (xs : List Tm) : cmpList (x :: xs) [] = .gt := by rw [cmpList]

theorem cmpList_cons_cons_eq {x y : Tm} (xs ys : List Tm) (h : cmpP x y = .eq) :
    cmpList (x :: xs) (y :: ys) = cmpList xs ys := by
  rw [cmpList, h]

theorem cmpList_cons_cons_ne {x y : Tm} (xs ys : List Tm) (h : cmpP x y ≠ .eq) :
    cmpList (x :: xs) (y :: ys) = cmpP x y := by
  rw [cmpList]
  cases e : cmpP x y with
  | eq => exact absurd e h
  | lt => rfl
  | gt => rfl

theorem cmp_eq (a b : Tm) : cmp a b = cmpList (summands a) (summands b) := by rw [cmp]

theorem cmpList_self : ∀ l : List Tm, (∀ x, x ∈ l → cmpP x x = .eq) → cmpList l l = .eq
  | [], _ => cmpList_nil_nil
  | x :: xs, h => by
    rw [cmpList_cons_cons_eq xs xs (h x List.mem_cons_self)]
    exact cmpList_self xs (fun y hy => h y (List.mem_cons_of_mem x hy))

theorem size_le_of_mem_summands : ∀ (t s : Tm), s ∈ summands t → s.size ≤ t.size
  | .zero, s, h => by simp [summands] at h
  | .plus a b, s, h => by
    rw [summands, List.mem_cons] at h
    cases h with
    | inl e => rw [e]; simp only [Tm.size]; omega
    | inr h => have := size_le_of_mem_summands b s h; simp only [Tm.size]; omega
  | .one, s, h | .K _, s, h | .Om _, s, h | .Xi _ _, s, h | .Psi _ _ _, s, h => by
    simp only [summands, List.mem_singleton] at h
    rw [h]
    exact Nat.le_refl _

theorem cmp_self_aux : ∀ n, ∀ t : Tm, t.size ≤ n → cmp t t = .eq ∧ cmpP t t = .eq := by
  intro n
  induction n with
  | zero => intro t h; exact absurd h (Nat.not_le.mpr (Tm.size_pos t))
  | succ n ih =>
    intro t ht
    have hP : ∀ x : Tm, x.size ≤ n + 1 → cmpP x x = .eq := by
      intro x hx
      rw [cmpP.eq_def]
      simp only [Nat.lt_irrefl, ↓reduceIte]
      cases x with
      | Om a =>
        have := (ih a (by simp only [Tm.size] at hx; omega)).1
        simpa using this
      | Xi m a => simp
      | Psi xi pi a => simp [cmpPsi.eq_def]
      | _ => rfl
    refine ⟨?_, hP t ht⟩
    rw [cmp_eq]
    exact cmpList_self _ (fun x hx => hP x (Nat.le_trans (size_le_of_mem_summands t x hx) ht))

/-- `cmp t t = .eq` -/
theorem cmp_self (t : Tm) : cmp t t = .eq := (cmp_self_aux t.size t (Nat.le_refl _)).1

theorem cmpP_self (t : Tm) : cmpP t t = .eq := (cmp_self_aux t.size t (Nat.le_refl _)).2

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

theorem cmp_principal {x y : Tm} (hx : isPrincipal x = true) (hy : isPrincipal y = true) :
    cmp x y = cmpP x y := by
  rw [cmp_eq, summands_principal hx, summands_principal hy]
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

/-- `Ψ^0_{Ω_c}(α)` どうしの `cmpPsi`：区間 `c`・`d` を比べ、同じ区間なら引数と `C` で比べる -/
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

/-- `a < b` -/
def Lt (a b : Tm) : Prop := cmp a b = .lt

instance (a b : Tm) : Decidable (Lt a b) := inferInstanceAs (Decidable (cmp a b = .lt))

theorem Lt.ne {a b : Tm} (h : Lt a b) : a ≠ b := by
  intro e
  subst e
  unfold Lt at h
  rw [cmp_self] at h
  cases h

theorem Lt.irrefl (a : Tm) : ¬ Lt a a := fun h => h.ne rfl

theorem inC_one (g d : Tm) : inC .one g d = true := by rw [inC.eq_def]

theorem inC_K (n : Nat) (g d : Tm) : inC (.K n) g d = true := by rw [inC.eq_def]

theorem inC_plus (a b g d : Tm) : inC (.plus a b) g d = (inC a g d && inC b g d) := by
  rw [inC.eq_def]

theorem inC_om (e g d : Tm) : inC (.Om e) g d = inC e g d := by rw [inC.eq_def]

theorem inC_psi (s k δ g d : Tm) :
    inC (.Psi s k δ) g d = (cmp (.Psi s k δ) d == .lt ||
      (inC k g d && inC s g d && inC δ g d && cmp δ g == .lt)) := by
  rw [inC.eq_def]

/-- `Ψ` の項の `C` への所属：`d` より小さいか、引数が `g` より小さくパラメタが `C` に入る -/
theorem inC_psi_iff {s k δ g d : Tm} :
    inC (.Psi s k δ) g d = true ↔
      Lt (.Psi s k δ) d ∨ (inC k g d = true ∧ inC s g d = true ∧ inC δ g d = true ∧ Lt δ g) := by
  rw [inC_psi]
  unfold Lt
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, and_assoc]

/-- 部分項の一覧（自分自身を含む） -/
def subs : Tm → List Tm
  | .zero => [.zero]
  | .one => [.one]
  | .K n => [.K n]
  | .plus a b => .plus a b :: (subs a ++ subs b)
  | .Om a => .Om a :: subs a
  | .Xi n a => .Xi n a :: subs a
  | .Psi s k a => .Psi s k a :: (subs s ++ subs k ++ subs a)

theorem self_mem_subs (t : Tm) : t ∈ subs t := by
  cases t <;> simp [subs]

theorem size_le_of_mem_subs : ∀ {t s : Tm}, s ∈ subs t → s.size ≤ t.size
  | .zero, s, h | .one, s, h | .K _, s, h => by
    simp only [subs, List.mem_singleton] at h
    rw [h]
    exact Nat.le_refl _
  | .plus a b, s, h => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    rcases h with h | h | h
    · rw [h]; exact Nat.le_refl _
    · have := size_le_of_mem_subs h; simp only [Tm.size]; omega
    · have := size_le_of_mem_subs h; simp only [Tm.size]; omega
  | .Om a, s, h | .Xi _ a, s, h => by
    simp only [subs, List.mem_cons] at h
    rcases h with h | h
    · rw [h]; exact Nat.le_refl _
    · have := size_le_of_mem_subs h; simp only [Tm.size]; omega
  | .Psi x p a, s, h => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    rcases h with h | (h | h) | h
    · rw [h]; exact Nat.le_refl _
    · have := size_le_of_mem_subs h; simp only [Tm.size]; omega
    · have := size_le_of_mem_subs h; simp only [Tm.size]; omega
    · have := size_le_of_mem_subs h; simp only [Tm.size]; omega

/-- 大きさが同じ部分項は自分自身 -/
theorem eq_of_mem_subs_size : ∀ {t s : Tm}, s ∈ subs t → t.size ≤ s.size → s = t
  | .zero, s, h, _ | .one, s, h, _ | .K _, s, h, _ => by
    simp only [subs, List.mem_singleton] at h
    exact h
  | .plus a b, s, h, hs => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    rcases h with h | h | h
    · exact h
    · have := size_le_of_mem_subs h; simp only [Tm.size] at hs; omega
    · have := size_le_of_mem_subs h; simp only [Tm.size] at hs; omega
  | .Om a, s, h, hs | .Xi _ a, s, h, hs => by
    simp only [subs, List.mem_cons] at h
    rcases h with h | h
    · exact h
    · have := size_le_of_mem_subs h; simp only [Tm.size] at hs; omega
  | .Psi x p a, s, h, hs => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    rcases h with h | (h | h) | h
    · exact h
    · have := size_le_of_mem_subs h; simp only [Tm.size] at hs; omega
    · have := size_le_of_mem_subs h; simp only [Tm.size] at hs; omega
    · have := size_le_of_mem_subs h; simp only [Tm.size] at hs; omega

theorem subs_trans : ∀ {t s r : Tm}, s ∈ subs t → r ∈ subs s → r ∈ subs t
  | .zero, s, r, h, hr | .one, s, r, h, hr | .K _, s, r, h, hr => by
    simp only [subs, List.mem_singleton] at h
    subst h
    exact hr
  | .plus a b, s, r, h, hr => by
    simp only [subs, List.mem_cons, List.mem_append] at h ⊢
    rcases h with h | h | h
    · subst h
      simp only [subs, List.mem_cons, List.mem_append] at hr
      exact hr
    · exact Or.inr (Or.inl (subs_trans h hr))
    · exact Or.inr (Or.inr (subs_trans h hr))
  | .Om a, s, r, h, hr | .Xi _ a, s, r, h, hr => by
    simp only [subs, List.mem_cons] at h ⊢
    rcases h with h | h
    · subst h
      simp only [subs, List.mem_cons] at hr
      exact hr
    · exact Or.inr (subs_trans h hr)
  | .Psi x p a, s, r, h, hr => by
    simp only [subs, List.mem_cons, List.mem_append] at h ⊢
    rcases h with h | (h | h) | h
    · subst h
      simp only [subs, List.mem_cons, List.mem_append] at hr
      exact hr
    · exact Or.inr (Or.inl (Or.inl (subs_trans h hr)))
    · exact Or.inr (Or.inl (Or.inr (subs_trans h hr)))
    · exact Or.inr (Or.inr (subs_trans h hr))

theorem lev_le_of_cmpP_lt {x y : Tm} (h : cmpP x y = .lt) : lev x ≤ lev y := by
  apply Nat.le_of_not_lt
  intro h'
  rw [cmpP_of_lev_gt h'] at h
  cases h

theorem lt_principal_iff {x y : Tm} (hx : isPrincipal x = true) (hy : isPrincipal y = true) :
    Lt x y ↔ cmpP x y = .lt := by
  unfold Lt
  rw [cmp_principal hx hy]

/-- 底（同じ階の最小元）：`1` と `K_n` -/
def isBot : Tm → Bool
  | .one | .K _ => true
  | _ => false

theorem lt_om_om (a b : Tm) (hl : lev a = lev b) : Lt (.Om a) (.Om b) ↔ Lt a b := by
  rw [lt_principal_iff rfl rfl, cmpP_om_om hl]
  rfl

theorem lt_om_psi (a c β : Tm) (hl : lev a = lev c) :
    Lt (.Om a) (.Psi .zero (.Om c) β) ↔ Lt a c := by
  rw [lt_principal_iff rfl rfl, cmpP_om_psi0 hl]
  unfold Lt
  by_cases h : cmp a c = .lt <;> simp [h]

theorem lt_psi_om (a c β : Tm) (hl : lev a = lev c) :
    Lt (.Psi .zero (.Om c) β) (.Om a) ↔ ¬ Lt a c := by
  rw [lt_principal_iff rfl rfl, cmpP_psi0_om hl]
  unfold Lt
  by_cases h : cmp a c = .lt <;> simp [h]

theorem lt_psi_psi_of_lt (c d α β : Tm) (hl : lev c = lev d) (h : Lt c d) :
    Lt (.Psi .zero (.Om c) α) (.Psi .zero (.Om d) β) := by
  rw [lt_principal_iff rfl rfl, cmpP_psi_psi (pi := .Om c) (ka := .Om d) hl, cmpPsi_psi0 hl]
  have hne : Tm.Psi .zero (.Om c) α ≠ .Psi .zero (.Om d) β := by
    intro e
    cases e
    exact Lt.irrefl _ h
  unfold Lt at h
  simp [hne, h]

theorem ite_lt_gt_eq_lt {P : Prop} [Decidable P] :
    ((if P then Ordering.lt else Ordering.gt) = .lt) ↔ P := by
  by_cases h : P
  · simp [h]
  · simp [h]

theorem mem_subs_om (a : Tm) : a ∈ subs (.Om a) := by
  simp [subs, self_mem_subs]

theorem mem_subs_psi_c (s c α : Tm) : c ∈ subs (.Psi s (.Om c) α) := by
  simp [subs, self_mem_subs]

theorem mem_subs_psi_a (s k α : Tm) : α ∈ subs (.Psi s k α) := by
  simp [subs, self_mem_subs]

theorem ne_of_mem_subs_lt {t s : Tm} (h : s.size < t.size) : s ≠ t := by
  intro e
  subst e
  exact Nat.lt_irrefl _ h

/-- `S` の上で `<` が推移的 -/
def LinOn (S : List Tm) : Prop :=
  ∀ a, a ∈ S → ∀ b, b ∈ S → ∀ c, c ∈ S → Lt a b → Lt b c → Lt a c

theorem cmpList_lt_cases {x y : Tm} {xs ys : List Tm} (h : cmpList (x :: xs) (y :: ys) = .lt) :
    cmpP x y = .lt ∨ (cmpP x y = .eq ∧ cmpList xs ys = .lt) := by
  cases e : cmpP x y with
  | lt => exact Or.inl rfl
  | eq => rw [cmpList_cons_cons_eq _ _ e] at h; exact Or.inr ⟨rfl, h⟩
  | gt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e] at h; cases h

theorem mem_subs_of_mem_summands : ∀ {t s : Tm}, s ∈ summands t → s ∈ subs t
  | .zero, s, h => by simp [summands] at h
  | .plus a b, s, h => by
    rw [summands, List.mem_cons] at h
    simp only [subs, List.mem_cons, List.mem_append]
    rcases h with h | h
    · exact Or.inr (Or.inl (by rw [h]; exact self_mem_subs a))
    · exact Or.inr (Or.inr (mem_subs_of_mem_summands h))
  | .one, s, h | .K _, s, h | .Om _, s, h | .Xi _ _, s, h | .Psi _ _ _, s, h => by
    simp only [summands, List.mem_singleton] at h
    rw [h]
    exact self_mem_subs _

theorem summands_ne_nil {c : Tm} (hc : c ≠ .zero) : summands c ≠ [] := by
  intro h
  cases c <;> simp_all [summands]

theorem lev_head {c h : Tm} {rest : List Tm} (hc : summands c = h :: rest) : lev h = lev c := by
  cases c with
  | zero => simp [summands] at hc
  | plus a b => rw [summands, List.cons.injEq] at hc; rw [← hc.1]; rfl
  | _ => simp only [summands, List.cons.injEq] at hc; rw [hc.1]

theorem lt_of_head_lt {b t h : Tm} {rest : List Tm} (htp : isPrincipal t = true)
    (hs : summands b = h :: rest) (h1 : cmpP h t = .lt) : Lt b t := by
  unfold Lt
  rw [cmp_eq, hs, summands_principal htp, cmpList_cons_cons_ne _ _ (by rw [h1]; decide), h1]

theorem lt_psi_om_self (c δ : Tm) : Lt (.Psi .zero (.Om c) δ) (.Om c) :=
  (lt_psi_om c c δ rfl).mpr (Lt.irrefl c)

theorem inC_xi (n : Nat) (a g d : Tm) :
    inC (.Xi n a) g d = (cmp (.Xi n a) d == .lt || (inC a g d && cmp a g == .lt)) := by
  rw [inC.eq_def]

/-- `w ∈ C(g, d)` で、`w` の部分項 `v` について `v < d → v < d'` と `v < g → v < g'` なら
    `w ∈ C(g', d')` -/
theorem inC_mono : ∀ w g d g' d' : Tm, inC w g d = true →
    (∀ v, v ∈ subs w → Lt v d → Lt v d') → (∀ v, v ∈ subs w → Lt v g → Lt v g') →
    inC w g' d' = true := by
  intro w
  induction w with
  | zero => intros; exact inC_zero _ _
  | one => intros; exact inC_one _ _
  | K n => intros; exact inC_K n _ _
  | plus a b iha ihb =>
    intro g d g' d' h hd hg
    rw [inC_plus, Bool.and_eq_true] at h ⊢
    exact ⟨iha g d g' d' h.1 (fun v hv => hd v (by simp [subs, hv]))
        (fun v hv => hg v (by simp [subs, hv])),
      ihb g d g' d' h.2 (fun v hv => hd v (by simp [subs, hv]))
        (fun v hv => hg v (by simp [subs, hv]))⟩
  | Om e ihe =>
    intro g d g' d' h hd hg
    rw [inC_om] at h ⊢
    exact ihe g d g' d' h (fun v hv => hd v (by simp [subs, hv]))
      (fun v hv => hg v (by simp [subs, hv]))
  | Xi n a iha =>
    intro g d g' d' h hd hg
    rw [inC_xi] at h ⊢
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h ⊢
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl (hd _ (self_mem_subs _) h)
    · exact Or.inr ⟨iha g d g' d' h1 (fun v hv => hd v (by simp [subs, hv]))
        (fun v hv => hg v (by simp [subs, hv])), hg a (by simp [subs, self_mem_subs]) h2⟩
  | Psi s k δ ihs ihk ihδ =>
    intro g d g' d' h hd hg
    rcases inC_psi_iff.mp h with h | ⟨hk, hs, hδ, hlt⟩
    · exact inC_psi_iff.mpr (Or.inl (hd _ (self_mem_subs _) h))
    · refine inC_psi_iff.mpr (Or.inr ⟨?_, ?_, ?_, hg δ (by simp [subs, self_mem_subs]) hlt⟩)
      · exact ihk g d g' d' hk (fun v hv => hd v (by simp [subs, hv]))
          (fun v hv => hg v (by simp [subs, hv]))
      · exact ihs g d g' d' hs (fun v hv => hd v (by simp [subs, hv]))
          (fun v hv => hg v (by simp [subs, hv]))
      · exact ihδ g d g' d' hδ (fun v hv => hd v (by simp [subs, hv]))
          (fun v hv => hg v (by simp [subs, hv]))

theorem exists_max_size : ∀ S : List Tm, S ≠ [] → ∃ t, t ∈ S ∧ ∀ s, s ∈ S → s.size ≤ t.size
  | [], h => absurd rfl h
  | x :: rest, _ => by
    cases rest with
    | nil =>
      exact ⟨x, List.mem_cons_self, fun s hs => by
        rw [List.mem_singleton.mp hs]; exact Nat.le_refl _⟩
    | cons y rest' =>
      obtain ⟨t, ht, hmax⟩ := exists_max_size (y :: rest') (by simp)
      by_cases hxt : t.size ≤ x.size
      · refine ⟨x, List.mem_cons_self, fun s hs => ?_⟩
        rcases List.mem_cons.mp hs with e | e
        · rw [e]; exact Nat.le_refl _
        · exact Nat.le_trans (hmax s e) hxt
      · refine ⟨t, List.mem_cons_of_mem _ ht, fun s hs => ?_⟩
        rcases List.mem_cons.mp hs with e | e
        · rw [e]; omega
        · exact hmax s e

theorem length_filter_ne_lt : ∀ {S : List Tm} {t : Tm}, t ∈ S →
    (S.filter (fun s => s != t)).length < S.length
  | [], _, h => absurd h List.not_mem_nil
  | x :: xs, t, h => by
    rw [List.filter_cons]
    by_cases e : x = t
    · subst e
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      exact Nat.lt_succ_of_le (List.length_filter_le _ _)
    · have hx : (x != t) = true := bne_iff_ne.mpr e
      simp only [hx, ↓reduceIte, List.length_cons]
      rcases List.mem_cons.mp h with h' | h'
      · exact absurd h'.symm e
      · exact Nat.succ_lt_succ (length_filter_ne_lt h')

/-- `a ≤ b` -/
def Le (a b : Tm) : Prop := a = b ∨ Lt a b

theorem Le.refl (a : Tm) : Le a a := Or.inl rfl

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

/-- `z + 1` -/
def succT : Tm → Tm
  | .zero => .one
  | .plus a b => .plus a (succT b)
  | t => .plus t .one

theorem summands_succT : ∀ z : Tm, summands (succT z) = summands z ++ [.one]
  | .zero => rfl
  | .plus a b => by rw [succT, summands_plus, summands_plus, summands_succT b]; rfl
  | .one | .K _ | .Om _ | .Xi _ _ | .Psi _ _ _ => rfl

theorem succT_ne_zero (z : Tm) : succT z ≠ .zero := by
  cases z <;> simp [succT]

theorem succT_ne_K (z : Tm) (m : Nat) : succT z ≠ .K m := by
  cases z <;> simp [succT]

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

theorem lev_succT {z : Tm} (h : z ≠ .zero) : lev (succT z) = lev z := by
  cases z with
  | zero => exact absurd rfl h
  | _ => rfl

theorem cmpOmX_xi (a b : Tm) (n : Nat) : cmpOmX a (.Xi n b) = cmp a (.Xi n b) := by
  rw [cmpOmX.eq_def]
  simp [omegaFixed]

theorem cmpP_om_xi {a b : Tm} {n : Nat} (h : lev a = n) :
    cmpP (.Om a) (.Xi n b) = cmp a (.Xi n b) := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]
  exact cmpOmX_xi a b n

theorem cmpP_xi_om {a b : Tm} {n : Nat} (h : lev a = n) :
    cmpP (.Xi n b) (.Om a) = (cmp a (.Xi n b)).swap := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]
  rw [cmpOmX_xi]

theorem cmpP_xi_xi (n : Nat) (a b : Tm) :
    cmpP (.Xi n a) (.Xi n b) =
      if a = b then .eq else if xiLtXi (.Xi n a) (.Xi n b) = true then .lt else .gt := by
  rw [cmpP.eq_def]
  simp only [lev, Nat.lt_irrefl, ↓reduceIte, beq_iff_eq]

theorem xiLtXi_eq (n m : Nat) (a b : Tm) :
    xiLtXi (.Xi n a) (.Xi m b) =
      ((cmp a b == .lt && inC a b (.Xi m b)) || (cmp b a == .lt && !inC b a (.Xi n a))) := by
  rw [xiLtXi]

theorem cmpP_psi_xi {xi pi a b : Tm} {m : Nat} (h : lev pi = m) :
    cmpP (.Psi xi pi a) (.Xi m b) =
      if psiLtXi (.Psi xi pi a) (.Xi m b) = true then .lt else .gt := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]

theorem cmpP_xi_psi {xi pi a b : Tm} {m : Nat} (h : lev pi = m) :
    cmpP (.Xi m b) (.Psi xi pi a) =
      if psiLtXi (.Psi xi pi a) (.Xi m b) = true then .gt else .lt := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]

theorem psiLtXi_eq (xi pi a b : Tm) (m : Nat) :
    psiLtXi (.Psi xi pi a) (.Xi m b) =
      (cmp pi (.Xi m b) != .gt || (cmp b a == .lt && !inC b a (.Psi xi pi a))) := by
  rw [psiLtXi]

/-- `Ξ_n` どうしの反対称性と相等 -/
theorem xi_SE {n : Nat} {a b : Tm}
    (hab : cmp b a = (cmp a b).swap ∧ (cmp a b = .eq → a = b)) :
    cmpP (.Xi n b) (.Xi n a) = (cmpP (.Xi n a) (.Xi n b)).swap ∧
      (cmpP (.Xi n a) (.Xi n b) = .eq → Tm.Xi n a = .Xi n b) := by
  rw [cmpP_xi_xi, cmpP_xi_xi, xiLtXi_eq, xiLtXi_eq]
  cases eab : cmp a b with
  | eq =>
    have := hab.2 eab
    subst this
    simp
  | lt =>
    have eba : cmp b a = .gt := by rw [hab.1, eab]; rfl
    have hne : a ≠ b := by intro e; subst e; rw [cmp_self] at eab; cases eab
    have hne' : b ≠ a := fun e => hne e.symm
    simp only [hne, hne', eba, ↓reduceIte]
    cases inC a b (Tm.Xi n b) <;> simp
  | gt =>
    have eba : cmp b a = .lt := by rw [hab.1, eab]; rfl
    have hne : a ≠ b := by intro e; subst e; rw [cmp_self] at eab; cases eab
    have hne' : b ≠ a := fun e => hne e.symm
    simp only [hne, hne', eba, ↓reduceIte]
    cases inC b a (Tm.Xi n a) <;> simp

theorem ne_gt_of_le {a b : Tm} (h : a = b ∨ Lt a b) : cmp a b ≠ .gt := by
  rcases h with rfl | h
  · rw [cmp_self]; decide
  · unfold Lt at h; rw [h]; decide

theorem mem_subs_xi (n : Nat) (a : Tm) : a ∈ subs (.Xi n a) := by
  simp [subs, self_mem_subs]

theorem lt_of_lev_lt' {a b : Tm} (h : lev a < lev b) : Lt a b := by
  have hb0 : b ≠ .zero := by intro e; subst e; simp [lev] at h
  by_cases ha0 : a = .zero
  · subst ha0
    exact zero_lt hb0
  · cases hsa : summands a with
    | nil => exact absurd hsa (summands_ne_nil ha0)
    | cons x xs =>
      cases hsb : summands b with
      | nil => exact absurd hsb (summands_ne_nil hb0)
      | cons y ys =>
        unfold Lt
        rw [cmp_eq, hsa, hsb]
        have e : cmpP x y = .lt := cmpP_of_lev_lt (by rw [lev_head hsa, lev_head hsb]; exact h)
        rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]

theorem inC_xi_iff {n : Nat} {a g d : Tm} :
    inC (.Xi n a) g d = true ↔ Lt (.Xi n a) d ∨ (inC a g d = true ∧ Lt a g) := by
  rw [inC_xi]
  unfold Lt
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]

/-- 有限の一覧の上の「全ては成り立たない」から反例を取り出す -/
theorem exists_of_not_forall_mem {P : Tm → Prop} [DecidablePred P] :
    ∀ l : List Tm, ¬ (∀ w, w ∈ l → P w) → ∃ w, w ∈ l ∧ ¬ P w
  | [], h => absurd (fun _ hw => absurd hw List.not_mem_nil) h
  | x :: xs, h => by
    by_cases hx : P x
    · obtain ⟨w, hw, hP⟩ := exists_of_not_forall_mem xs (fun h' => h (fun w hw => by
        rcases List.mem_cons.mp hw with e | e
        · subst e; exact hx
        · exact h' w e))
      exact ⟨w, List.mem_cons_of_mem _ hw, hP⟩
    · exact ⟨x, List.mem_cons_self, hx⟩

/-- 正則項 `R` についての前線 -/
def fr (R : Tm) : Tm → List Tm
  | .plus a b => fr R a ++ fr R b
  | .Om a => fr R a
  | .Xi m a => if Lt (.Xi m a) R then [.Xi m a] else fr R a
  | .Psi s p a => if Lt (.Psi s p a) R then [.Psi s p a] else fr R s ++ fr R p ++ fr R a
  | _ => []

theorem subs_plus_l {a b w : Tm} (h : w ∈ subs a) : w ∈ subs (.plus a b) :=
  subs_trans (by simp [subs, self_mem_subs]) h

theorem subs_plus_r {a b w : Tm} (h : w ∈ subs b) : w ∈ subs (.plus a b) :=
  subs_trans (by simp [subs, self_mem_subs]) h

theorem subs_om {a w : Tm} (h : w ∈ subs a) : w ∈ subs (.Om a) :=
  subs_trans (mem_subs_om a) h

theorem subs_xi {n : Nat} {a w : Tm} (h : w ∈ subs a) : w ∈ subs (.Xi n a) :=
  subs_trans (mem_subs_xi n a) h

theorem subs_psi_s {s p a w : Tm} (h : w ∈ subs s) : w ∈ subs (.Psi s p a) :=
  subs_trans (by simp [subs, self_mem_subs]) h

theorem subs_psi_p {s p a w : Tm} (h : w ∈ subs p) : w ∈ subs (.Psi s p a) :=
  subs_trans (by simp [subs, self_mem_subs]) h

theorem subs_psi_a {s p a w : Tm} (h : w ∈ subs a) : w ∈ subs (.Psi s p a) :=
  subs_trans (mem_subs_psi_a s p a) h

/-- 前線の元は部分項で `R` 未満 -/
theorem fr_spec {R : Tm} : ∀ {x w : Tm}, w ∈ fr R x → w ∈ subs x ∧ Lt w R
  | .zero, _, h | .one, _, h | .K _, _, h => by simp [fr] at h
  | .plus a b, w, h => by
    rw [fr, List.mem_append] at h
    rcases h with h | h
    · exact ⟨subs_plus_l (fr_spec h).1, (fr_spec h).2⟩
    · exact ⟨subs_plus_r (fr_spec h).1, (fr_spec h).2⟩
  | .Om a, w, h => by
    rw [fr] at h
    exact ⟨subs_om (fr_spec h).1, (fr_spec h).2⟩
  | .Xi m a, w, h => by
    rw [fr] at h
    by_cases hR : Lt (.Xi m a) R
    · simp only [hR, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact ⟨self_mem_subs _, hR⟩
    · simp only [hR, ↓reduceIte] at h
      exact ⟨subs_xi (fr_spec h).1, (fr_spec h).2⟩
  | .Psi s p a, w, h => by
    rw [fr] at h
    by_cases hR : Lt (.Psi s p a) R
    · simp only [hR, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact ⟨self_mem_subs _, hR⟩
    · simp only [hR, ↓reduceIte, List.mem_append] at h
      rcases h with (h | h) | h
      · exact ⟨subs_psi_s (fr_spec h).1, (fr_spec h).2⟩
      · exact ⟨subs_psi_p (fr_spec h).1, (fr_spec h).2⟩
      · exact ⟨subs_psi_a (fr_spec h).1, (fr_spec h).2⟩

/-- 前線による `C` への所属の言い換え：`R` 以上の節点が `d` 未満でなく、その引数が `g0` 未満
    （したがって `g` 未満）なら、`x ∈ C(g, d)` は前線の各節点が `C(g, d)` に入ることと同値 -/
theorem inC_fr {R g0 g d : Tm} : ∀ x : Tm, inC x g0 R = true →
    (∀ w, w ∈ subs x → ¬ Lt w R → ¬ Lt w d) →
    (∀ v, v ∈ subs x → Lt v g0 → Lt v g) →
    (inC x g d = true ↔ ∀ w, w ∈ fr R x → inC w g d = true)
  | .zero, _, _, _ => by simp [fr, inC_zero]
  | .one, _, _, _ => by simp [fr, inC_one]
  | .K n, _, _, _ => by simp [fr, inC_K]
  | .plus a b, h0, hd, hg => by
    rw [inC_plus, Bool.and_eq_true] at h0
    rw [inC_plus, Bool.and_eq_true, fr]
    rw [inC_fr a h0.1 (fun w hw => hd w (subs_plus_l hw)) (fun v hv => hg v (subs_plus_l hv)),
      inC_fr b h0.2 (fun w hw => hd w (subs_plus_r hw)) (fun v hv => hg v (subs_plus_r hv))]
    simp only [List.mem_append]
    constructor
    · rintro ⟨h1, h2⟩ w (hw | hw)
      · exact h1 w hw
      · exact h2 w hw
    · intro h
      exact ⟨fun w hw => h w (Or.inl hw), fun w hw => h w (Or.inr hw)⟩
  | .Om a, h0, hd, hg => by
    rw [inC_om] at h0
    rw [inC_om, fr]
    exact inC_fr a h0 (fun w hw => hd w (subs_om hw)) (fun v hv => hg v (subs_om hv))
  | .Xi m a, h0, hd, hg => by
    rw [fr]
    by_cases hR : Lt (.Xi m a) R
    · simp only [hR, ↓reduceIte]
      simp
    · simp only [hR, ↓reduceIte]
      rcases inC_xi_iff.mp h0 with h | ⟨ha, hlt⟩
      · exact absurd h hR
      have hnd := hd _ (self_mem_subs _) hR
      have hag : Lt a g := hg a (mem_subs_xi m a) hlt
      rw [inC_xi_iff, ← inC_fr a ha (fun w hw => hd w (subs_xi hw)) (fun v hv => hg v (subs_xi hv))]
      constructor
      · rintro (h | ⟨h, _⟩)
        · exact absurd h hnd
        · exact h
      · intro h
        exact Or.inr ⟨h, hag⟩
  | .Psi s p a, h0, hd, hg => by
    rw [fr]
    by_cases hR : Lt (.Psi s p a) R
    · simp only [hR, ↓reduceIte]
      simp
    · simp only [hR, ↓reduceIte]
      rcases inC_psi_iff.mp h0 with h | ⟨hp, hs, ha, hlt⟩
      · exact absurd h hR
      have hnd := hd _ (self_mem_subs _) hR
      have hag : Lt a g := hg a (mem_subs_psi_a s p a) hlt
      rw [inC_psi_iff,
        inC_fr p hp (fun w hw => hd w (subs_psi_p hw)) (fun v hv => hg v (subs_psi_p hv)),
        inC_fr s hs (fun w hw => hd w (subs_psi_s hw)) (fun v hv => hg v (subs_psi_s hv)),
        inC_fr a ha (fun w hw => hd w (subs_psi_a hw)) (fun v hv => hg v (subs_psi_a hv))]
      simp only [List.mem_append]
      constructor
      · rintro (h | ⟨h1, h2, h3, _⟩)
        · exact absurd h hnd
        · rintro w ((hw | hw) | hw)
          · exact h2 w hw
          · exact h1 w hw
          · exact h3 w hw
      · intro h
        exact Or.inr ⟨fun w hw => h w (Or.inl (Or.inr hw)), fun w hw => h w (Or.inl (Or.inl hw)),
          fun w hw => h w (Or.inr hw), hag⟩

/-- 前線の元は `Ξ` か `Ψ` の節点 -/
theorem fr_node {R : Tm} : ∀ {x w : Tm}, w ∈ fr R x →
    (∃ m a, w = .Xi m a) ∨ (∃ s p a, w = .Psi s p a)
  | .zero, _, h | .one, _, h | .K _, _, h => by simp [fr] at h
  | .plus a b, w, h => by
    rw [fr, List.mem_append] at h
    rcases h with h | h
    · exact fr_node h
    · exact fr_node h
  | .Om a, w, h => by rw [fr] at h; exact fr_node h
  | .Xi m a, w, h => by
    rw [fr] at h
    by_cases hR : Lt (.Xi m a) R
    · simp only [hR, ↓reduceIte, List.mem_singleton] at h
      exact Or.inl ⟨m, a, h⟩
    · simp only [hR, ↓reduceIte] at h
      exact fr_node h
  | .Psi s p a, w, h => by
    rw [fr] at h
    by_cases hR : Lt (.Psi s p a) R
    · simp only [hR, ↓reduceIte, List.mem_singleton] at h
      exact Or.inr ⟨s, p, a, h⟩
    · simp only [hR, ↓reduceIte, List.mem_append] at h
      rcases h with (h | h) | h
      · exact fr_node h
      · exact fr_node h
      · exact fr_node h

theorem inC_of_lt_node {w g d : Tm} (hw : (∃ m a, w = .Xi m a) ∨ (∃ s p a, w = .Psi s p a))
    (h : Lt w d) : inC w g d = true := by
  rcases hw with ⟨m, a, rfl⟩ | ⟨s, p, a, rfl⟩
  · exact inC_xi_iff.mpr (Or.inl h)
  · exact inC_psi_iff.mpr (Or.inl h)

/-- 前線の各節点が `C(g, d)` に入ることは、崩壊の性質があれば `d` 未満と同値 -/
theorem fr_inC_iff {R x g d : Tm} (hcoll : ∀ w, w ∈ fr R x → inC w g d = true → Lt w d) :
    (∀ w, w ∈ fr R x → inC w g d = true) ↔ (∀ w, w ∈ fr R x → Lt w d) :=
  ⟨fun h w hw => hcoll w hw (h w hw), fun h w hw => inC_of_lt_node (fr_node hw) (h w hw)⟩

/-- 前線のどれかが `C(g, d)` に入らないことは、崩壊の性質があれば、どれかが `d` 未満でないことと同値 -/
theorem fr_inC_false_iff {R x g d : Tm} (hcoll : ∀ w, w ∈ fr R x → inC w g d = true → Lt w d) :
    (¬ ∀ w, w ∈ fr R x → inC w g d = true) ↔ (∃ w, w ∈ fr R x ∧ ¬ Lt w d) := by
  rw [fr_inC_iff hcoll]
  constructor
  · exact exists_of_not_forall_mem _
  · rintro ⟨w, hw, hn⟩ h
    exact hn (h w hw)

theorem lev_le_of_lt_gen {w y : Tm} (h : Lt w y) : lev w ≤ lev y := by
  apply Nat.le_of_not_lt
  intro hl
  have hw0 : w ≠ .zero := by intro e; subst e; simp [lev] at hl
  by_cases hy0 : y = .zero
  · subst hy0; exact not_lt_zero w h
  · cases hsw : summands w with
    | nil => exact absurd hsw (summands_ne_nil hw0)
    | cons x xs =>
      cases hsy : summands y with
      | nil => exact absurd hsy (summands_ne_nil hy0)
      | cons z zs =>
        unfold Lt at h
        rw [cmp_eq, hsw, hsy] at h
        have e : cmpP x z = .gt := cmpP_of_lev_gt (by rw [lev_head hsw, lev_head hsy]; exact hl)
        rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e] at h
        cases h

/-- `K_n` 以上の項は階 `n` の項より小さくない -/
theorem not_lt_of_not_lt_K {n : Nat} {w y : Tm} (hy : lev y = n)
    (h : ¬ Lt w (.K n)) : ¬ Lt w y := by
  intro h'
  have hl := lev_le_of_lt_gen h'
  exact h (lt_of_lev_lt' (by simp only [lev]; omega))

/-- 主要項 `t` より小さい和は、先頭の項も `t` より小さい -/
theorem cmpP_head_of_lt {w h t : Tm} {rest : List Tm} (hs : summands w = h :: rest)
    (htp : isPrincipal t = true) (hlt : Lt w t) : cmpP h t = .lt := by
  unfold Lt at hlt
  rw [cmp_eq, hs, summands_principal htp] at hlt
  rcases cmpList_lt_cases hlt with e | ⟨_, e⟩
  · exact e
  · cases rest with
    | nil => rw [cmpList_nil_nil] at e; cases e
    | cons _ _ => rw [cmpList_cons_nil] at e; cases e

/-- `t` は `S` を切断する -/
def CutT (S : List Tm) (t : Tm) : Prop :=
  ∀ a b, a ∈ S → b ∈ S → Lt b a → Lt a t → Lt b t

theorem lt_plus_plus_same {a b b' : Tm} : Lt (.plus a b) (.plus a b') ↔ Lt b b' := by
  unfold Lt
  rw [cmp_eq, cmp_eq, summands_plus, summands_plus, cmpList_cons_cons_eq _ _ (cmpP_self a)]

theorem lt_psi_psiG {c d α β : Tm} (h : Lt c d) :
    Lt (.Psi .zero (.Om c) α) (.Psi .zero (.Om d) β) := by
  have hl := lev_le_of_lt_gen h
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
  · exact lt_psi_psi_of_lt c d α β hl h

theorem isSucc_succT (z : Tm) : isSucc (succT z) = true := by
  simp [isSucc, summands_succT]

theorem size_induction {P : Tm → Prop} (h : ∀ t, (∀ s, s.size < t.size → P s) → P t)
    (t : Tm) : P t := by
  have key : ∀ n, ∀ t : Tm, t.size < n → P t := by
    intro n
    induction n with
    | zero => intro t ht; exact absurd ht (Nat.not_lt_zero _)
    | succ n ih => intro t ht; exact h t (fun s hs => ih s (by omega))
  exact key _ t (Nat.lt_succ_self _)

/-- 部分項の大きさの比較 -/
macro "size_omega" : tactic =>
  `(tactic| first | (simp only [Tm.size]; omega) | (simp only [Tm.size] at *; omega))

theorem fr_mem_plus_l {R a b w : Tm} (h : w ∈ fr R a) : w ∈ fr R (.plus a b) := by
  rw [fr, List.mem_append]; exact Or.inl h

theorem fr_mem_plus_r {R a b w : Tm} (h : w ∈ fr R b) : w ∈ fr R (.plus a b) := by
  rw [fr, List.mem_append]; exact Or.inr h

theorem fr_mem_om {R a w : Tm} (h : w ∈ fr R a) : w ∈ fr R (.Om a) := by
  rw [fr]; exact h

theorem fr_mem_xi {R a w : Tm} {n : Nat} (hn : ¬ Lt (.Xi n a) R) (h : w ∈ fr R a) :
    w ∈ fr R (.Xi n a) := by
  rw [fr]; simp only [hn, ↓reduceIte]; exact h

theorem fr_mem_xi_self {R a : Tm} {n : Nat} (hl : Lt (.Xi n a) R) :
    Tm.Xi n a ∈ fr R (.Xi n a) := by
  rw [fr]; simp only [hl, ↓reduceIte, List.mem_singleton]

theorem fr_mem_psi_p {R s p a w : Tm} (hn : ¬ Lt (.Psi s p a) R) (h : w ∈ fr R p) :
    w ∈ fr R (.Psi s p a) := by
  rw [fr]; simp only [hn, ↓reduceIte, List.mem_append]; exact Or.inl (Or.inr h)

theorem fr_mem_psi_a {R s p a w : Tm} (hn : ¬ Lt (.Psi s p a) R) (h : w ∈ fr R a) :
    w ∈ fr R (.Psi s p a) := by
  rw [fr]; simp only [hn, ↓reduceIte, List.mem_append]; exact Or.inr h

theorem fr_mem_psi_self {R s p a : Tm} (hl : Lt (.Psi s p a) R) :
    Tm.Psi s p a ∈ fr R (.Psi s p a) := by
  rw [fr]; simp only [hl, ↓reduceIte, List.mem_singleton]

end RTKA

/-! ## 体系全体（`isNF` の標準形全て）の定義と、順序の性質を仮定せずに成り立つ比較の展開

`Ψ^ξ_π(a)` の目標 `π` は `Ω_c`・`Ξ_n(p)`・Mahlo 添字が `0` でない崩壊 `Ψ^ζ_κ(b)` のいずれか。目標をたどる列
（`Ψ^ξ_π(a)`、`π`、`π` の目標、…）の上で Mahlo 添字は真に減る。整列性の証明（`Wmax.lean`）が使う順序の性質は
`FWOrder` にまとめ、`Order.lean` で示す（`instFWOrder`）。 -/

namespace RTKA.W

open Tm

/-- 体系全体の標準形 -/
def WNF (t : Tm) : Prop := isNF t = true

/-- `Ψ` の目標：`Ω_c`（`c` は後者）、`Ξ_n(p)`、Mahlo 添字が `0` でない `Ψ^ζ_κ(b)` -/
def IsTgt (π : Tm) : Prop :=
  (∃ c, π = .Om c ∧ isSucc c = true) ∨ (∃ n p, π = .Xi n p) ∨
    ∃ ζ κ b, π = .Psi ζ κ b ∧ ζ ≠ .zero

/-- 目標の Mahlo 添字 `m(π)`（`Ω_c` は `1`、`Ξ_n(p)` は `p`、`Ψ^ζ_κ(b)` は `ζ`） -/
def mi : Tm → Tm
  | .Om _ => .one
  | .Xi _ p => p
  | .Psi ζ _ _ => ζ
  | _ => .zero

/-! ### 標準形の分解 -/

theorem WNF.plus {a b : Tm} (h : WNF (.plus a b)) :
    WNF a ∧ WNF b ∧ isPrincipal a = true ∧ b ≠ .zero := by
  have hn : isNF (.plus a b) = true := h
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
  exact ⟨hn.1.1.2, hn.1.2, hn.1.1.1.1, hn.1.1.1.2⟩

theorem WNF.om {a : Tm} (h : WNF (.Om a)) : WNF a ∧ a ≠ .zero ∧ cmp a (.Om a) = .lt := by
  have hn : isNF (.Om a) = true := h
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
  refine ⟨hn.1.1, hn.1.2, ?_⟩
  have h2 := hn.2
  unfold lt at h2
  simpa using h2

theorem WNF.xi {n : Nat} {a : Tm} (h : WNF (.Xi n a)) :
    1 ≤ n ∧ WNF a ∧ a ≠ .zero ∧ cmp a (succK n) ≠ .gt ∧ inC a a (.K n) = true := by
  have hn : isNF (.Xi n a) = true := h
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hn
  exact ⟨hn.1.1.1.1, hn.1.1.1.2, hn.1.1.2, hn.1.2, hn.2⟩

/-- `Ψ^ξ_π(a)` の標準形の条件 -/
structure PsiNF (xi pi a : Tm) : Prop where
  tgt : IsTgt pi
  xiF : WNF xi
  piF : WNF pi
  aF : WNF a
  le : cmp xi a ≠ .gt
  Ca : inC a a pi = true
  Cxi : inC xi a pi = true
  Cpi : inC pi a pi = true
  /-- Mahlo 添字は目標の Mahlo 添字未満で、`ξ ∈ C(m(π), π)` -/
  mlt : Lt xi (mi pi)
  mC : inC xi (mi pi) pi = true

theorem WNF.psi {xi pi a : Tm} (h : WNF (.Psi xi pi a)) : PsiNF xi pi a := by
  have hn : isNF (.Psi xi pi a) = true := h
  simp only [isNF, Bool.and_eq_true] at hn
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hxin, hpin⟩, han⟩, hreg⟩, hle⟩, hCa⟩, hCxi⟩, hCpi⟩, hm⟩ := hn
  have hle' : cmp xi a ≠ .gt := by simpa using hle
  have key : ∀ m, mOf pi = some m → mi pi = m ∧ IsTgt pi := by
    intro m hm'
    cases pi with
    | Om c =>
      simp only [mOf, Option.some.injEq] at hm'; subst hm'; exact ⟨rfl, Or.inl ⟨c, rfl, hreg⟩⟩
    | Xi n p =>
      simp only [mOf, Option.some.injEq] at hm'; subst hm'; exact ⟨rfl, Or.inr (Or.inl ⟨n, p, rfl⟩)⟩
    | Psi ζ κ b =>
      simp only [mOf, Option.some.injEq] at hm'; subst hm'
      refine ⟨rfl, Or.inr (Or.inr ⟨ζ, κ, b, rfl, ?_⟩)⟩
      simpa [isRegTerm] using hreg
    | _ => simp [mOf] at hm'
  cases e : mOf pi with
  | none => rw [e] at hm; simp at hm
  | some m =>
    rw [e] at hm
    simp only [Bool.and_eq_true] at hm
    obtain ⟨hmi, ht⟩ := key m e
    refine ⟨ht, hxin, hpin, han, hle', hCa, hCxi, hCpi, ?_, ?_⟩
    · rw [hmi]
      have := hm.1
      unfold lt at this
      show cmp xi m = .lt
      simpa using this
    · rw [hmi]; exact hm.2

theorem WNF.k {n : Nat} (h : WNF (.K n)) : 1 ≤ n := by
  have hn : isNF (.K n) = true := h
  simp only [isNF, decide_eq_true_eq] at hn
  exact hn

theorem WNF.zero : WNF .zero := rfl

theorem WNF.one : WNF .one := rfl

theorem WNF.K' {n : Nat} (h : 1 ≤ n) : WNF (.K n) := by
  show isNF (.K n) = true
  simp only [isNF, decide_eq_true_eq]
  exact h

/-- `Ω_{K_m}` は標準形でない -/
theorem WNF.om_ne_k {a : Tm} {m : Nat} (h : WNF (.Om a)) : a ≠ .K m := by
  intro e
  subst e
  have h2 := h.om.2.2
  rw [cmp_principal rfl rfl, cmpP.eq_def] at h2
  simp [lev] at h2

theorem summands_WNF : ∀ t : Tm, WNF t → ∀ s, s ∈ summands t → WNF s ∧ isPrincipal s = true
  | .zero, _, s, hs => by simp [summands] at hs
  | .plus a b, h, s, hs => by
    obtain ⟨ha, hb, hap, _⟩ := h.plus
    rw [summands, List.mem_cons] at hs
    cases hs with
    | inl e => rw [e]; exact ⟨ha, hap⟩
    | inr hs => exact summands_WNF b hb s hs
  | .one, h, s, hs | .K _, h, s, hs | .Om _, h, s, hs | .Xi _ _, h, s, hs
  | .Psi _ _ _, h, s, hs => by
    simp only [summands, List.mem_singleton] at hs
    rw [hs]
    exact ⟨h, rfl⟩

theorem WNF.of_mem_subs : ∀ {t s : Tm}, WNF t → s ∈ subs t → WNF s
  | .zero, s, ht, h | .one, s, ht, h | .K _, s, ht, h => by
    simp only [subs, List.mem_singleton] at h
    rw [h]
    exact ht
  | .plus a b, s, ht, h => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    obtain ⟨ha, hb, -, -⟩ := ht.plus
    rcases h with h | h | h
    · rw [h]; exact ht
    · exact WNF.of_mem_subs ha h
    · exact WNF.of_mem_subs hb h
  | .Om a, s, ht, h => by
    simp only [subs, List.mem_cons] at h
    rcases h with h | h
    · rw [h]; exact ht
    · exact WNF.of_mem_subs ht.om.1 h
  | .Xi _ a, s, ht, h => by
    simp only [subs, List.mem_cons] at h
    rcases h with h | h
    · rw [h]; exact ht
    · exact WNF.of_mem_subs ht.xi.2.1 h
  | .Psi x p a, s, ht, h => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    have hP := ht.psi
    rcases h with h | (h | h) | h
    · rw [h]; exact ht
    · exact WNF.of_mem_subs hP.xiF h
    · exact WNF.of_mem_subs hP.piF h
    · exact WNF.of_mem_subs hP.aF h

/-! ### 順序についての仮定 -/

/-- 整列性の証明が使う順序の性質：標準形の上で `cmp` は反対称で `.eq` なら等しく、`<` は推移的。
    さらに `Ψ^ξ_π(a)` の引数 `a`・目標 `π`・Mahlo 添字 `ξ` の前線（`π` について）は `Ψ^ξ_π(a)` 未満（K2）、
    `ξ ∈ C(ξ, Ψ^ξ_π(a))`、`Ξ_n(a)` の引数の前線（`K_n` について）は `Ξ_n(a)` 未満、`c < Ψ^0_{Ω_c}(a)`。 -/
class FWOrder : Prop where
  swap : ∀ {a b : Tm}, WNF a → WNF b → cmp b a = (cmp a b).swap
  eq : ∀ {a b : Tm}, WNF a → WNF b → cmp a b = .eq → a = b
  trans : ∀ {a b c : Tm}, WNF a → WNF b → WNF c → Lt a b → Lt b c → Lt a c
  k2 : ∀ {ξ π a : Tm}, WNF (.Psi ξ π a) → ∀ w, w ∈ fr π a → Lt w (.Psi ξ π a)
  k2t : ∀ {ξ π a : Tm}, WNF (.Psi ξ π a) → ∀ w, w ∈ fr π π → Lt w (.Psi ξ π a)
  k2s : ∀ {ξ π a : Tm}, WNF (.Psi ξ π a) → ∀ w, w ∈ fr π ξ → Lt w (.Psi ξ π a)
  ms : ∀ {ξ π a : Tm}, WNF (.Psi ξ π a) → inC ξ ξ (.Psi ξ π a) = true
  k2x : ∀ {n : Nat} {a : Tm}, WNF (.Xi n a) → ∀ w, w ∈ fr (.K n) a → Lt w (.Xi n a)
  cx : ∀ {c a : Tm}, WNF (.Psi .zero (.Om c) a) → Lt c (.Psi .zero (.Om c) a)

/-! ## 比較の展開

* 和・階・`1`・`K_n`・`Ω` との比較。
* `Ψ^ξ` どうしの比較の展開（`lt_psi_psiY`、Prop. 4.20 の (1)〜(4)）と、`Ψ^ξ` と `Ξ` の比較の展開。
* 目標の形（`WNF.shape`：`Ω_c`・`Ξ_n(p)`・`Ψ^ζ_κ(b)`）と、`Ω` の不動点 `IsOF`（`Ξ_n(a)` と目標が `Ω_c` でない
  `Ψ^ξ_π(a)`）と `Ω_e` の比較。 -/

/-! ### 和 -/

theorem WNF.plus_head {a b : Tm} (h : WNF (.plus a b)) {h' : Tm} {rest : List Tm}
    (hs : summands b = h' :: rest) : cmp h' a ≠ .gt := by
  have hn : isNF (.plus a b) = true := h
  simp only [isNF, Bool.and_eq_true] at hn
  have h2 := hn.2
  rw [hs] at h2
  simpa using h2

theorem lt_plus_leftY {a b : Tm} (h : WNF (.plus a b)) : Lt a (.plus a b) := by
  obtain ⟨-, -, hap, hb0⟩ := h.plus
  unfold Lt
  rw [cmp_eq, summands_principal hap, summands_plus, cmpList_cons_cons_eq _ _ (cmpP_self a)]
  cases hs : summands b with
  | nil => exact absurd hs (summands_ne_nil hb0)
  | cons _ _ => exact cmpList_nil_cons _ _

/-- 主要項 `y` について `a + b < y` ⟺ `a < y` -/
theorem lt_plus_prin_iffY {a b y : Tm} (h : WNF (.plus a b)) (hyp : isPrincipal y = true) :
    Lt (.plus a b) y ↔ Lt a y := by
  obtain ⟨-, -, hap, hb0⟩ := h.plus
  rw [lt_principal_iff hap hyp]
  unfold Lt
  rw [cmp_eq, summands_principal hyp, summands_plus]
  cases e : cmpP a y with
  | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]
  | eq =>
    rw [cmpList_cons_cons_eq _ _ e]
    cases hs : summands b with
    | nil => exact absurd hs (summands_ne_nil hb0)
    | cons _ _ => rw [cmpList_cons_nil]; simp
  | gt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]

/-- 底（同じ階の最小元）より小さい同じ階の項はない -/
theorem not_lt_isBotY {x y : Tm} (hl : lev x = lev y) (hy : isBot y = true) (hx : WNF x)
    (hyF : WNF y) : cmpP x y ≠ .lt := by
  rw [cmpP.eq_def]
  simp only [hl, Nat.lt_irrefl, ↓reduceIte]
  cases x <;> cases y <;> simp_all [isBot]
  all_goals first
    | (split <;> simp)
    | (have := hyF.k; simp only [lev] at hl; omega)

theorem lev_posY : ∀ {t : Tm}, WNF t → t ≠ .zero → 1 ≤ lev t
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
    exact lev_posY hP.piF (by rcases hP.tgt with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩ <;> intro e <;> cases e)

/-- `x < K_m` なら `x` の階は `m` 以下 -/
theorem lev_le_of_lt_KY {z : Tm} {n : Nat} (hn : 1 ≤ n) (hz : WNF z) (h : Lt z (.K n)) :
    lev z ≤ n := by
  cases hs : summands z with
  | nil =>
    have : z = .zero := by cases z <;> simp_all [summands]
    subst this
    simp [lev]
  | cons x xs =>
    have hx := summands_WNF z hz x (by rw [hs]; exact List.mem_cons_self)
    unfold Lt at h
    rw [cmp_eq, hs, show summands (Tm.K n) = [.K n] from rfl] at h
    have hl := lev_head hs
    rcases cmpList_lt_cases h with e | ⟨-, e'⟩
    · have := lev_le_of_cmpP_lt e
      simp only [lev] at this
      rcases Nat.lt_or_eq_of_le this with h1 | h1
      · rw [← hl]; omega
      · exact absurd e (not_lt_isBotY (by simp only [lev]; exact h1) rfl hx.1 (WNF.K' hn))
    · cases xs with
      | nil => rw [cmpList_nil_nil] at e'; cases e'
      | cons _ _ => rw [cmpList_cons_nil] at e'; cases e'

/-- `x < K_m` ⟺ `x` の階が `m` 以下 -/
theorem lt_K_iffY {x : Tm} {m : Nat} (hx : WNF x) (hm : 1 ≤ m) : Lt x (.K m) ↔ lev x ≤ m :=
  ⟨lev_le_of_lt_KY hm hx, fun h => lt_of_lev_lt' (by simp only [lev]; omega)⟩

theorem cmpP_one_ne_gtY {h : Tm} (hF : WNF h) (hp : isPrincipal h = true) :
    cmpP .one h ≠ .gt := by
  have hl : 1 ≤ lev h := lev_posY hF (by intro e; subst e; simp [isPrincipal] at hp)
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · rw [cmpP_of_lev_lt (by simp only [lev]; exact hl)]; decide
  · rw [cmpP.eq_def]
    simp only [lev, ← hl, Nat.lt_irrefl, ↓reduceIte]
    cases h <;> simp

theorem lt_oneY {u : Tm} (hu : WNF u) (h : Lt u .one) : u = .zero := by
  cases hs : summands u with
  | nil => cases u <;> simp_all [summands]
  | cons x xs =>
    exfalso
    unfold Lt at h
    rw [cmp_eq, hs, show summands Tm.one = [.one] from rfl] at h
    have hx := summands_WNF u hu x (by rw [hs]; exact List.mem_cons_self)
    have hl : 1 ≤ lev x := lev_posY hx.1 (by intro e; subst e; simp [isPrincipal] at hx)
    rcases cmpList_lt_cases h with e | ⟨e, e'⟩
    · rcases Nat.lt_or_eq_of_le hl with hl | hl
      · rw [cmpP_of_lev_gt (by simp only [lev]; exact hl)] at e; cases e
      · exact not_lt_isBotY (by simp only [lev]; exact hl.symm) rfl hx.1 WNF.one e
    · cases xs with
      | nil => rw [cmpList_nil_nil] at e'; cases e'
      | cons _ _ => rw [cmpList_cons_nil] at e'; cases e'

theorem WNF.psiOm {ξ c a : Tm} (h : WNF (.Psi ξ (.Om c) a)) :
    WNF c ∧ WNF (.Om c) ∧ isSucc c = true ∧ WNF a ∧ inC a a (.Om c) = true ∧ ξ = .zero := by
  have hP := h.psi
  refine ⟨hP.piF.om.1, hP.piF, ?_, hP.aF, hP.Ca, lt_oneY hP.xiF hP.mlt⟩
  rcases hP.tgt with ⟨c'', e', hs⟩ | ⟨n, p, e'⟩ | ⟨ζ, κ, b, e', -⟩ <;> cases e'
  exact hs

/-- 目標の形：`Ω_c`（このとき `ξ = 0`）、`Ξ_n(p)`、`Ψ^ζ_κ(b)`（`ζ ≠ 0`） -/
theorem WNF.shape {ξ π a : Tm} (h : WNF (.Psi ξ π a)) :
    (∃ c, π = .Om c ∧ ξ = .zero) ∨ (∃ n p, π = .Xi n p) ∨
      ∃ ζ κ b, π = .Psi ζ κ b ∧ ζ ≠ .zero := by
  rcases h.psi.tgt with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ | ⟨ζ, κ, b, rfl, hζ⟩
  · exact Or.inl ⟨c, rfl, (WNF.psiOm h).2.2.2.2.2⟩
  · exact Or.inr (Or.inl ⟨n, p, rfl⟩)
  · exact Or.inr (Or.inr ⟨ζ, κ, b, rfl, hζ⟩)

theorem lt_om_psiY {e c β : Tm} (hψ : WNF (.Psi .zero (.Om c) β)) :
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

/-! ### `Ψ^ξ` と目標・`Ξ` の比較の展開（順序の仮定なし） -/

theorem lt_psi_targetY {ξ π a : Tm} (h : WNF (.Psi ξ π a)) : Lt (.Psi ξ π a) π := by
  rcases h.shape with ⟨c, rfl, rfl⟩ | ⟨n, p, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩
  · exact lt_psi_om_self c a
  · rw [lt_principal_iff rfl rfl, cmpP_psi_xi (pi := .Xi n p) (m := n) rfl, psiLtXi_eq, cmp_self]
    simp
  · have hne : Tm.Psi ξ (.Psi ζ κ b) a ≠ .Psi ζ κ b := by
      intro e
      have := congrArg Tm.size e
      simp only [Tm.size] at this
      omega
    rw [lt_principal_iff rfl rfl, cmpP_psi_psi (pi := .Psi ζ κ b) (ka := κ) rfl, cmpPsi.eq_def]
    simp [cmp_self, hne]

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

/-- `Ω` の不動点になる主要項（`Ξ_n(a)` と、目標が `Ω_c` でない `Ψ^ξ_π(a)`） -/
def IsOF (X : Tm) : Prop :=
  (∃ n a, X = .Xi n a) ∨ ∃ ξ π a, X = .Psi ξ π a ∧ WNF (.Psi ξ π a) ∧ ∀ c, π ≠ .Om c

theorem IsOF.principal {X : Tm} (h : IsOF X) : isPrincipal X = true := by
  rcases h with ⟨n, a, rfl⟩ | ⟨ξ, π, a, rfl, -, -⟩ <;> rfl

theorem notOm_of_shape {π : Tm}
    (h : (∃ n p, π = .Xi n p) ∨ ∃ ζ κ b, π = .Psi ζ κ b ∧ ζ ≠ .zero) : ∀ c, π ≠ .Om c := by
  rcases h with ⟨n, p, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩ <;> intro c e <;> cases e

theorem IsOF.psi {ξ π a : Tm} (hw : WNF (.Psi ξ π a)) (hπ : ∀ c, π ≠ .Om c) :
    IsOF (.Psi ξ π a) :=
  Or.inr ⟨ξ, π, a, rfl, hw, hπ⟩

theorem IsOF.fixed {X : Tm} (h : IsOF X) : omegaFixed X = true := by
  rcases h with ⟨n, a, rfl⟩ | ⟨ξ, π, a, rfl, hw, hπ⟩
  · rfl
  · rcases hw.shape with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ | ⟨ζ, κ, b, rfl, hζ⟩
    · exact absurd rfl (hπ c)
    · simp [omegaFixed, isInacc]
    · simp [omegaFixed, isInacc, hζ]

theorem cmpP_om_OF {e X : Tm} (hX : IsOF X) (hl : lev e = lev X) :
    cmpP (.Om e) X = cmp e X := by
  have hof := hX.fixed
  rcases hX with ⟨n, a, rfl⟩ | ⟨ξ, π, a, rfl, -, -⟩
  · exact cmpP_om_xi hl
  · rw [cmpP.eq_def]
    have hl' : lev e = lev π := hl
    simp only [lev, hl', Nat.lt_irrefl, ↓reduceIte]
    rw [cmpOmX.eq_def]
    simp [hof]

theorem cmpP_OF_om {e X : Tm} (hX : IsOF X) (hl : lev e = lev X) :
    cmpP X (.Om e) = (cmp e X).swap := by
  have hof := hX.fixed
  rcases hX with ⟨n, a, rfl⟩ | ⟨ξ, π, a, rfl, -, -⟩
  · exact cmpP_xi_om hl
  · rw [cmpP.eq_def]
    have hl' : lev e = lev π := hl
    simp only [lev, hl', Nat.lt_irrefl, ↓reduceIte]
    rw [cmpOmX.eq_def]
    simp [hof]
theorem lt_om_OFG {e X : Tm} (hX : IsOF X) :
    Lt (.Om e) X ↔ Lt e X := by
  rcases Nat.lt_trichotomy (lev e) (lev X) with hl | hl | hl
  · exact ⟨fun _ => lt_of_lev_lt' hl, fun _ => lt_of_lev_lt' (by simp only [lev]; exact hl)⟩
  · rw [lt_principal_iff rfl hX.principal, cmpP_om_OF hX hl]; rfl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · intro h; have := lev_le_of_lt_gen h; exfalso; omega

/-! ## 次の正則項 `nrY`

正則項（崩壊の添字）は `Ω_c`（`c` は後者）、`K_n`、`Ξ_n(p)`、Mahlo 添字が `0` でない `Ψ^ζ_κ(b)`。
`Ψ^0_π(a)`（`π` は `Ω_c` 以外）は `Ω` の不動点で正則でないので、次の正則項は `Ω_{Ψ+1}`。 -/

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

theorem succT_ne_principal (z : Tm) {X : Tm} (hX : isPrincipal X = true) (hX1 : X ≠ .one) :
    succT z ≠ X := by
  intro e
  subst e
  cases z <;> simp_all [succT, isPrincipal]

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

end RTKA.W
