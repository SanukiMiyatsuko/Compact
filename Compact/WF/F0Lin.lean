import Compact.WF.F0

/-! 断片 `F0` の上で `cmp` が推移的であることの証明（の道具）。

部分項で閉じた有限集合 `S` の要素数についての帰納法で示す。`S` から大きさ最大の項 `t` を除いた `S'` が
全順序なら、`t` は `S'` を切断する（`t` より小さい元の集合は下に閉じる）。 -/

namespace RTKA

open Tm

/-- `a < b` -/
def Lt (a b : Tm) : Prop := cmp a b = .lt

instance (a b : Tm) : Decidable (Lt a b) := inferInstanceAs (Decidable (cmp a b = .lt))

/-! ### 三分律 -/

theorem Lt.ne {a b : Tm} (h : Lt a b) : a ≠ b := by
  intro e
  subst e
  unfold Lt at h
  rw [cmp_self] at h
  cases h

theorem Lt.irrefl (a : Tm) : ¬ Lt a a := fun h => h.ne rfl

theorem Lt.asymm {a b : Tm} (ha : F0NF a) (hb : F0NF b) (h : Lt a b) : ¬ Lt b a := by
  unfold Lt at *
  rw [cmp_swap_F0 ha hb, h]
  decide

theorem lt_of_gt {a b : Tm} (ha : F0NF a) (hb : F0NF b) (h : cmp a b = .gt) : Lt b a := by
  unfold Lt
  rw [cmp_swap_F0 ha hb, h]
  rfl

theorem tri {a b : Tm} (ha : F0NF a) (hb : F0NF b) : Lt a b ∨ a = b ∨ Lt b a := by
  cases e : cmp a b with
  | lt => exact Or.inl e
  | eq => exact Or.inr (Or.inl (eq_of_cmp_eq_F0 ha hb e))
  | gt => exact Or.inr (Or.inr (lt_of_gt ha hb e))

/-- `¬ a < b` なら `b ≤ a` -/
theorem le_of_not_lt' {a b : Tm} (ha : F0NF a) (hb : F0NF b) (h : ¬ Lt a b) : b = a ∨ Lt b a := by
  rcases tri ha hb with h' | h' | h'
  · exact absurd h' h
  · exact Or.inl h'.symm
  · exact Or.inr h'

/-! ### `inC` の展開 -/

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

/-! ### 部分項 -/

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

/-- `F0` の標準形の部分項は `F0` の標準形 -/
theorem F0NF.of_mem_subs : ∀ {t s : Tm}, F0NF t → s ∈ subs t → F0NF s
  | .zero, s, ht, h | .one, s, ht, h | .K _, s, ht, h => by
    simp only [subs, List.mem_singleton] at h
    rw [h]
    exact ht
  | .plus a b, s, ht, h => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    obtain ⟨ha, hb, -, -⟩ := ht.plus
    rcases h with h | h | h
    · rw [h]; exact ht
    · exact F0NF.of_mem_subs ha h
    · exact F0NF.of_mem_subs hb h
  | .Om a, s, ht, h => by
    simp only [subs, List.mem_cons] at h
    rcases h with h | h
    · rw [h]; exact ht
    · exact F0NF.of_mem_subs ht.om.1 h
  | .Xi _ _, _, ht, _ => (ht.not_xi).elim
  | .Psi x p a, s, ht, h => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    obtain ⟨hx, c, hp, hc, -, ha, -, -⟩ := ht.psi
    subst hx hp
    rcases h with h | (h | h) | h
    · rw [h]; exact ht
    · simp only [subs, List.mem_singleton] at h
      rw [h]
      exact ⟨rfl, rfl⟩
    · exact F0NF.of_mem_subs hc h
    · exact F0NF.of_mem_subs ha h

/-! ### 階と同じ階での比較 -/

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

theorem lt_of_isBot {x y : Tm} (hl : lev x = lev y) (hx : isBot x = true) (hy : isBot y = false)
    (hpy : isPrincipal y = true) (hyF : F0NF y) : cmpP x y = .lt := by
  rw [cmpP.eq_def]
  simp only [hl, Nat.lt_irrefl, ↓reduceIte]
  cases x <;> cases y <;> simp_all [isBot, isPrincipal]
  exact hyF.om_ne_k

theorem not_lt_isBot {x y : Tm} (hl : lev x = lev y) (hy : isBot y = true) (hx : F0NF x)
    (hyF : F0NF y) :
    cmpP x y ≠ .lt := by
  rw [cmpP.eq_def]
  simp only [hl, Nat.lt_irrefl, ↓reduceIte]
  cases x <;> cases y <;> simp_all [isBot]
  all_goals first
    | (split <;> simp)
    | (have := hyF.k; simp only [lev] at hl; omega)

theorem isBot_eq {x y : Tm} (hl : lev x = lev y) (hx : isBot x = true) (hy : isBot y = true)
    (hxF : F0NF x) (hyF : F0NF y) : x = y := by
  cases x <;> cases y <;> simp_all [isBot, lev]
  · have := hyF.k; omega
  · have := hxF.k; omega

/-! ### `Ω` と `Ψ` の比較（同じ階） -/

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

/-- 同じ区間の `Ψ` どうしの比較 -/
theorem lt_psi_psi_same {c α β : Tm} (hne : α ≠ β) :
    Lt (.Psi .zero (.Om c) α) (.Psi .zero (.Om c) β) ↔
      (Lt α β ∧ inC α β (.Psi .zero (.Om c) β) = true ∧
          inC (.Om c) β (.Psi .zero (.Om c) β) = true) ∨
        (cmp β α ≠ .gt ∧ ¬ (inC β α (.Psi .zero (.Om c) α) = true ∧
          inC (.Om c) α (.Psi .zero (.Om c) α) = true)) := by
  rw [lt_principal_iff rfl rfl, cmpP_psi_psi (pi := .Om c) (ka := .Om c) rfl, cmpPsi_psi0 rfl]
  have hne' : Tm.Psi .zero (.Om c) α ≠ .Psi .zero (.Om c) β := by
    intro e
    cases e
    exact hne rfl
  have hcc : ¬ cmp c c = .lt := by rw [cmp_self]; decide
  unfold Lt
  simp only [hne', hcc, ↓reduceIte]
  exact ite_lt_gt_eq_lt

/-- `Ψ_d(α) < Ψ_e(β)` なら `d ≤ e` -/
theorem le_of_lt_psi_psi {d e α β : Tm} (hd : F0NF d) (he : F0NF e) (hl : lev d = lev e)
    (hpsi : F0NF (.Psi .zero (.Om d) α)) (hpsi' : F0NF (.Psi .zero (.Om e) β))
    (h : Lt (.Psi .zero (.Om d) α) (.Psi .zero (.Om e) β)) : d = e ∨ Lt d e := by
  rcases tri hd he with h' | h' | h'
  · exact Or.inr h'
  · exact Or.inl h'
  · exact absurd (lt_psi_psi_of_lt _ _ _ _ hl.symm h') (Lt.asymm hpsi hpsi' h)

/-! ### 主要項の形 -/

theorem shape_F0 {x : Tm} (hx : F0NF x) (hp : isPrincipal x = true) (hb : isBot x = false) :
    (∃ a, x = .Om a) ∨ (∃ c α, x = .Psi .zero (.Om c) α) := by
  cases x with
  | Om a => exact Or.inl ⟨a, rfl⟩
  | Psi xi pi α =>
    obtain ⟨hxi, c, hpi, -⟩ := hx.psi
    subst hxi hpi
    exact Or.inr ⟨c, α, rfl⟩
  | Xi _ _ => exact (hx.not_xi).elim
  | _ => simp_all [isPrincipal, isBot]

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

/-- 組 `(q, p)` が `t = Ψ_c(γ)` と同じ区間の `Ψ` どうしのときの切断性 -/
def IntCutPair (q p t : Tm) : Prop :=
  ∀ c α β γ, t = .Psi .zero (.Om c) γ → q = .Psi .zero (.Om c) α → p = .Psi .zero (.Om c) β →
    Lt q p → Lt p t → Lt q t

/-- 主要項 `t` の切断性（同じ区間の `Ψ` どうしは `IntCut` に任せる） -/
theorem cutP {S : List Tm} (hS : LinOn S) (hNF : ∀ s, s ∈ S → F0NF s)
    (hcl : ∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S)
    {t : Tm} (ht : F0NF t) (htp : isPrincipal t = true)
    (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S)
    {p q : Tm} (hint : IntCutPair q p t) (hp : p ∈ S) (hq : q ∈ S) (hpp : isPrincipal p = true) (hqp : isPrincipal q = true)
    (h1 : Lt q p) (h2 : Lt p t) : Lt q t := by
  have hpF := hNF p hp
  have hqF := hNF q hq
  have c1 := h1
  have c2 := h2
  rw [lt_principal_iff hqp hpp] at c1
  rw [lt_principal_iff hpp htp] at c2
  have l1 := lev_le_of_cmpP_lt c1
  have l2 := lev_le_of_cmpP_lt c2
  rw [lt_principal_iff hqp htp]
  by_cases hlt : lev q < lev t
  · exact cmpP_of_lev_lt hlt
  have hqp' : lev q = lev p := by omega
  have hpt : lev p = lev t := by omega
  cases hbt : isBot t
  case true => exact absurd c2 (not_lt_isBot hpt hbt hpF ht)
  cases hbp : isBot p
  case true => exact absurd c1 (not_lt_isBot hqp' hbp hqF hpF)
  cases hbq : isBot q
  case true => exact lt_of_isBot (by omega) hbq hbt htp ht
  rw [← lt_principal_iff hqp htp]
  rcases shape_F0 ht htp hbt with ⟨e, rfl⟩ | ⟨c, γ, rfl⟩ <;>
    rcases shape_F0 hpF hpp hbp with ⟨a, rfl⟩ | ⟨c', β, rfl⟩ <;>
    rcases shape_F0 hqF hqp hbq with ⟨b, rfl⟩ | ⟨d, α, rfl⟩
  -- `t = Ω_e`
  · have he := hsub e (mem_subs_om e) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))
    have ha := hcl _ hp a (mem_subs_om a)
    have hb := hcl _ hq b (mem_subs_om b)
    rw [lt_om_om a e hpt] at h2
    rw [lt_om_om b a hqp'] at h1
    rw [lt_om_om b e (hqp'.trans hpt)]
    exact hS b hb a ha e he h1 h2
  · have he := hsub e (mem_subs_om e) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))
    have ha := hcl _ hp a (mem_subs_om a)
    have hd := hcl _ hq d (mem_subs_psi_c _ d α)
    rw [lt_om_om a e hpt] at h2
    rw [lt_psi_om a d α hqp'.symm] at h1
    rw [lt_psi_om e d α (hqp'.trans hpt).symm]
    intro hed
    rcases tri (hNF a ha) (hNF d hd) with h' | h' | h'
    · exact h1 h'
    · subst h'
      exact Lt.asymm (hNF e he) (hNF a ha) hed h2
    · exact Lt.asymm (hNF e he) (hNF d hd) hed (hS d hd a ha e he h' h2)
  · have he := hsub e (mem_subs_om e) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))
    have hc := hcl _ hp c' (mem_subs_psi_c _ c' β)
    have hb := hcl _ hq b (mem_subs_om b)
    rw [lt_psi_om e c' β hpt.symm] at h2
    rw [lt_om_psi b c' β hqp'] at h1
    rw [lt_om_om b e (hqp'.trans hpt)]
    rcases le_of_not_lt' (hNF e he) (hNF c' hc) h2 with h' | h'
    · subst h'; exact h1
    · exact hS b hb c' hc e he h1 h'
  · have he := hsub e (mem_subs_om e) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))
    have hc := hcl _ hp c' (mem_subs_psi_c _ c' β)
    have hd := hcl _ hq d (mem_subs_psi_c _ d α)
    rw [lt_psi_om e c' β hpt.symm] at h2
    rw [lt_psi_om e d α (hqp'.trans hpt).symm]
    intro hed
    rcases le_of_lt_psi_psi (hNF d hd) (hNF c' hc) hqp' hqF hpF h1 with h' | h'
    · subst h'; exact h2 hed
    · exact h2 (hS e he d hd c' hc hed h')
  -- `t = Ψ_c(γ)`
  · have hc := hsub c (mem_subs_psi_c _ c γ) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))
    have ha := hcl _ hp a (mem_subs_om a)
    have hb := hcl _ hq b (mem_subs_om b)
    rw [lt_om_psi a c γ hpt] at h2
    rw [lt_om_om b a hqp'] at h1
    rw [lt_om_psi b c γ (hqp'.trans hpt)]
    exact hS b hb a ha c hc h1 h2
  · have hc := hsub c (mem_subs_psi_c _ c γ) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))
    have ha := hcl _ hp a (mem_subs_om a)
    have hd := hcl _ hq d (mem_subs_psi_c _ d α)
    rw [lt_om_psi a c γ hpt] at h2
    rw [lt_psi_om a d α hqp'.symm] at h1
    apply lt_psi_psi_of_lt d c α γ (hqp'.trans hpt)
    rcases le_of_not_lt' (hNF a ha) (hNF d hd) h1 with h' | h'
    · subst h'; exact h2
    · exact hS d hd a ha c hc h' h2
  · have hc := hsub c (mem_subs_psi_c _ c γ) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))
    have hc' := hcl _ hp c' (mem_subs_psi_c _ c' β)
    have hb := hcl _ hq b (mem_subs_om b)
    rw [lt_om_psi b c' β hqp'] at h1
    rw [lt_om_psi b c γ (hqp'.trans hpt)]
    rcases le_of_lt_psi_psi (hNF c' hc') (hNF c hc) hpt hpF ht h2 with h' | h'
    · subst h'; exact h1
    · exact hS b hb c' hc' c hc h1 h'
  · have hc := hsub c (mem_subs_psi_c _ c γ) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))
    have hc' := hcl _ hp c' (mem_subs_psi_c _ c' β)
    have hd := hcl _ hq d (mem_subs_psi_c _ d α)
    rcases le_of_lt_psi_psi (hNF c' hc') (hNF c hc) hpt hpF ht h2 with h' | h'
    · subst h'
      rcases le_of_lt_psi_psi (hNF d hd) (hNF c' hc') hqp' hqF hpF h1 with h'' | h''
      · subst h''
        exact hint d α β γ rfl rfl rfl h1 h2
      · exact lt_psi_psi_of_lt d c' α γ (hqp'.trans hpt) h''
    · apply lt_psi_psi_of_lt d c α γ (hqp'.trans hpt)
      rcases le_of_lt_psi_psi (hNF d hd) (hNF c' hc') hqp' hqF hpF h1 with h'' | h''
      · subst h''; exact h'
      · exact hS d hd c' hc' c hc h'' h'

/-! ### 辞書式比較 -/

theorem cmpList_lt_cases {x y : Tm} {xs ys : List Tm} (h : cmpList (x :: xs) (y :: ys) = .lt) :
    cmpP x y = .lt ∨ (cmpP x y = .eq ∧ cmpList xs ys = .lt) := by
  cases e : cmpP x y with
  | lt => exact Or.inl rfl
  | eq => rw [cmpList_cons_cons_eq _ _ e] at h; exact Or.inr ⟨rfl, h⟩
  | gt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e] at h; cases h

theorem eq_of_cmpP_eq {x y : Tm} (hx : F0NF x) (hy : F0NF y) (hpx : isPrincipal x = true)
    (hpy : isPrincipal y = true) (h : cmpP x y = .eq) : x = y := by
  apply eq_of_cmp_eq_F0 hx hy
  rw [cmp_principal hpx hpy, h]

/-- 主要項の列の辞書式比較の推移性（元が全て `S` に入るとき） -/
theorem lexTrans {S : List Tm} (hS : LinOn S) (hNF : ∀ s, s ∈ S → F0NF s) :
    ∀ l1 l2 l3 : List Tm,
      (∀ x, x ∈ l1 → x ∈ S ∧ isPrincipal x = true) →
      (∀ x, x ∈ l2 → x ∈ S ∧ isPrincipal x = true) →
      (∀ x, x ∈ l3 → x ∈ S ∧ isPrincipal x = true) →
      cmpList l1 l2 = .lt → cmpList l2 l3 = .lt → cmpList l1 l3 = .lt
  | [], [], _, _, _, _, h, _ => by rw [cmpList_nil_nil] at h; cases h
  | [], _ :: _, [], _, _, _, _, h => by rw [cmpList_cons_nil] at h; cases h
  | [], _ :: _, _ :: _, _, _, _, _, _ => cmpList_nil_cons _ _
  | _ :: _, [], _, _, _, _, h, _ => by rw [cmpList_cons_nil] at h; cases h
  | _ :: _, _ :: _, [], _, _, _, _, h => by rw [cmpList_cons_nil] at h; cases h
  | x :: xs, y :: ys, z :: zs, h1, h2, h3, hxy, hyz => by
    have hx := h1 x List.mem_cons_self
    have hy := h2 y List.mem_cons_self
    have hz := h3 z List.mem_cons_self
    rcases cmpList_lt_cases hxy with e1 | ⟨e1, r1⟩ <;> rcases cmpList_lt_cases hyz with e2 | ⟨e2, r2⟩
    · have : Lt x z := hS x hx.1 y hy.1 z hz.1 ((lt_principal_iff hx.2 hy.2).mpr e1)
        ((lt_principal_iff hy.2 hz.2).mpr e2)
      rw [lt_principal_iff hx.2 hz.2] at this
      rw [cmpList_cons_cons_ne _ _ (by rw [this]; decide), this]
    · have := eq_of_cmpP_eq (hNF y hy.1) (hNF z hz.1) hy.2 hz.2 e2
      subst this
      rw [cmpList_cons_cons_ne _ _ (by rw [e1]; decide), e1]
    · have := eq_of_cmpP_eq (hNF x hx.1) (hNF y hy.1) hx.2 hy.2 e1
      subst this
      rw [cmpList_cons_cons_ne _ _ (by rw [e2]; decide), e2]
    · have := eq_of_cmpP_eq (hNF x hx.1) (hNF y hy.1) hx.2 hy.2 e1
      subst this
      have := eq_of_cmpP_eq (hNF x hx.1) (hNF z hz.1) hx.2 hz.2 e2
      subst this
      rw [cmpList_cons_cons_eq _ _ (cmpP_self x)]
      exact lexTrans hS hNF xs ys zs (fun w hw => h1 w (List.mem_cons_of_mem _ hw))
        (fun w hw => h2 w (List.mem_cons_of_mem _ hw)) (fun w hw => h3 w (List.mem_cons_of_mem _ hw))
        r1 r2

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

/-- 一般の項 `t` の切断性（主要項の切断性 `cutP` から） -/
theorem cutGen {S : List Tm} (hS : LinOn S) (hNF : ∀ s, s ∈ S → F0NF s)
    (hcl : ∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S)
    {t : Tm} (ht : F0NF t) (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S)
    {a b : Tm} (hint : ∀ q p, q ∈ summands b → p ∈ summands a → IntCutPair q p t)
    (ha : a ∈ S) (hb : b ∈ S) (h1 : Lt b a) (h2 : Lt a t) : Lt b t := by
  have hsa : ∀ x, x ∈ summands a → x ∈ S ∧ isPrincipal x = true := fun x hx =>
    ⟨hcl a ha x (mem_subs_of_mem_summands hx), (summands_F0NF a (hNF a ha) x hx).2⟩
  have hsb : ∀ x, x ∈ summands b → x ∈ S ∧ isPrincipal x = true := fun x hx =>
    ⟨hcl b hb x (mem_subs_of_mem_summands hx), (summands_F0NF b (hNF b hb) x hx).2⟩
  unfold Lt at h1 h2 ⊢
  rw [cmp_eq] at h1 h2 ⊢
  cases htp : isPrincipal t
  · -- `t` は `0` か和
    cases t with
    | zero =>
      exfalso
      cases hs : summands a with
      | nil => rw [hs, summands, cmpList_nil_nil] at h2; cases h2
      | cons _ _ => rw [hs, summands, cmpList_cons_nil] at h2; cases h2
    | plus h r =>
      have hst : ∀ x, x ∈ summands (.plus h r) → x ∈ S ∧ isPrincipal x = true := by
        intro x hx
        refine ⟨hsub x (mem_subs_of_mem_summands hx) ?_, (summands_F0NF _ ht x hx).2⟩
        intro e
        subst e
        rw [summands, List.mem_cons] at hx
        rcases hx with hx | hx
        · have := congrArg Tm.size hx
          simp only [Tm.size] at this
          omega
        · have := size_le_of_mem_subs (mem_subs_of_mem_summands hx)
          simp only [Tm.size] at this
          omega
      exact lexTrans hS hNF _ _ _ hsb hsa hst h1 h2
    | _ => simp [isPrincipal] at htp
  · -- `t` は主要項
    rw [summands_principal' htp] at h2 ⊢
    cases hsb' : summands b with
    | nil => exact cmpList_nil_cons _ _
    | cons q qs =>
      cases hsa' : summands a with
      | nil => rw [hsb', hsa', cmpList_cons_nil] at h1; cases h1
      | cons p ps =>
        rw [hsb', hsa'] at h1
        rw [hsa'] at h2
        have hp := hsa p (by rw [hsa']; exact List.mem_cons_self)
        have hq := hsb q (by rw [hsb']; exact List.mem_cons_self)
        have hpt : cmpP p t = .lt := by
          rcases cmpList_lt_cases h2 with e | ⟨_, e⟩
          · exact e
          · cases ps with
            | nil => rw [cmpList_nil_nil] at e; cases e
            | cons _ _ => rw [cmpList_cons_nil] at e; cases e
        have hqt : cmpP q t = .lt := by
          rcases cmpList_lt_cases h1 with e | ⟨e, _⟩
          · rw [← lt_principal_iff hq.2 htp]
            exact cutP hS hNF hcl ht htp hsub
              (hint q p (by rw [hsb']; exact List.mem_cons_self) (by rw [hsa']; exact List.mem_cons_self))
              hp.1 hq.1 hp.2 hq.2
              ((lt_principal_iff hq.2 hp.2).mpr e) ((lt_principal_iff hp.2 htp).mpr hpt)
          · have := eq_of_cmpP_eq (hNF q hq.1) (hNF p hp.1) hq.2 hp.2 e
            subst this
            exact hpt
        rw [cmpList_cons_cons_ne _ _ (by rw [hqt]; decide), hqt]

/-! ### CX：`c < Ψ_c(α)` -/

/-- `e < h` で `h` が `c` の先頭の項なら `e < c` -/
theorem lt_of_lt_head {e h c : Tm} {rest : List Tm} (hc : summands c = h :: rest) (h1 : Lt e h)
    (hh : isPrincipal h = true) : Lt e c := by
  unfold Lt at h1 ⊢
  rw [cmp_eq] at h1 ⊢
  rw [summands_principal' hh] at h1
  rw [hc]
  cases hs : summands e with
  | nil => exact cmpList_nil_cons _ _
  | cons p ps =>
    rw [hs] at h1
    rcases cmpList_lt_cases h1 with e1 | ⟨_, e1⟩
    · rw [cmpList_cons_cons_ne _ _ (by rw [e1]; decide), e1]
    · cases ps with
      | nil => rw [cmpList_nil_nil] at e1; cases e1
      | cons _ _ => rw [cmpList_cons_nil] at e1; cases e1

theorem summands_ne_nil {c : Tm} (hc : c ≠ .zero) : summands c ≠ [] := by
  intro h
  cases c <;> simp_all [summands]

theorem lev_head {c h : Tm} {rest : List Tm} (hc : summands c = h :: rest) : lev h = lev c := by
  cases c with
  | zero => simp [summands] at hc
  | plus a b => rw [summands, List.cons.injEq] at hc; rw [← hc.1]; rfl
  | _ => simp only [summands, List.cons.injEq] at hc; rw [hc.1]

/-- CX：`F0` の標準形 `Ψ_c(α)` について `c < Ψ_c(α)` -/
theorem cx : ∀ n, ∀ c α : Tm, (Tm.Psi .zero (.Om c) α).size ≤ n →
    F0NF (.Psi .zero (.Om c) α) → Lt c (.Psi .zero (.Om c) α)
  | 0, c, α, h, _ => absurd h (by have := Tm.size_pos (.Psi .zero (.Om c) α); omega)
  | n + 1, c, α, hn, hx => by
    obtain ⟨-, c', hc', hcF, -, -, -, -⟩ := hx.psi
    cases hc'
    obtain ⟨hcN, hc0, -⟩ := hcF.om
    cases hs : summands c with
    | nil => exact absurd hs (summands_ne_nil hc0)
    | cons h rest =>
      have hmem : h ∈ summands c := by rw [hs]; exact List.mem_cons_self
      obtain ⟨hF, hp⟩ := summands_F0NF c hcN h hmem
      have hl : lev h = lev c := lev_head hs
      have hlt : cmpP h (.Psi .zero (.Om c) α) = .lt := by
        cases hb : isBot h
        · rcases shape_F0 hF hp hb with ⟨a, rfl⟩ | ⟨e, δ, rfl⟩
          · rw [← lt_principal_iff hp rfl, lt_om_psi a c α hl]
            exact lt_of_lt_head hs hF.om.2.2 rfl
          · have hle : (Tm.Psi .zero (.Om e) δ).size ≤ n := by
              have := size_le_of_mem_subs (mem_subs_of_mem_summands hmem)
              simp only [Tm.size] at hn this ⊢
              omega
            rw [← lt_principal_iff hp rfl]
            exact lt_psi_psi_of_lt e c δ α hl (lt_of_lt_head hs (cx n e δ hle hF) rfl)
        · exact lt_of_isBot hl hb rfl rfl hx
      unfold Lt
      rw [cmp_eq, hs, summands_principal' (t := .Psi .zero (.Om c) α) rfl,
        cmpList_cons_cons_ne _ _ (by rw [hlt]; decide), hlt]

/-! ### 同じ区間の `Ψ` どうしの比較（`Ω_c ∈ C` を使って簡単にしたもの） -/

theorem lt_psi_same_iff {c α β : Tm} (hx : F0NF (.Psi .zero (.Om c) α))
    (hy : F0NF (.Psi .zero (.Om c) β)) (hne : α ≠ β)
    (icx : ∀ g, inC (.Om c) g (.Psi .zero (.Om c) α) = true)
    (icy : ∀ g, inC (.Om c) g (.Psi .zero (.Om c) β) = true) :
    Lt (.Psi .zero (.Om c) α) (.Psi .zero (.Om c) β) ↔
      (Lt α β ∧ inC α β (.Psi .zero (.Om c) β) = true) ∨
        (Lt β α ∧ inC β α (.Psi .zero (.Om c) α) = false) := by
  obtain ⟨-, c₁, hc₁, -, -, hαF, -, -⟩ := hx.psi
  obtain ⟨-, c₂, hc₂, -, -, hβF, -, -⟩ := hy.psi
  rw [lt_psi_psi_same hne, icx, icy]
  have hβα : cmp β α ≠ .gt ↔ Lt β α := by
    constructor
    · intro h
      cases e : cmp β α with
      | lt => exact e
      | eq => exact absurd (eq_of_cmp_eq_F0 hβF hαF e).symm hne
      | gt => exact absurd e h
    · intro h
      unfold Lt at h
      rw [h]
      decide
  rw [hβα]
  simp

/-- `Ψ_c(δ)` 自身は `C(δ, Ψ_c(δ))` に入らない -/
theorem inC_self_false (s k δ : Tm) : inC (.Psi s k δ) δ (.Psi s k δ) = false := by
  cases h : inC (.Psi s k δ) δ (.Psi s k δ)
  · rfl
  · rw [inC_psi_iff] at h
    rcases h with h | ⟨-, -, -, h⟩
    · exact absurd h (Lt.irrefl _)
    · exact absurd h (Lt.irrefl _)

/-! ### `t = Ψ_c(γ)` での IC：`Ω_c ∈ C(g, t)` -/

theorem F0NF.plus_head {a b : Tm} (h : F0NF (.plus a b)) {h' : Tm} {rest : List Tm}
    (hs : summands b = h' :: rest) : cmp h' a ≠ .gt := by
  have hn := h.1
  simp only [isNF, Bool.and_eq_true] at hn
  have h2 := hn.2
  rw [hs] at h2
  simpa using h2

/-- `w ⊑ c` なら `w` は `Ψ_c(·)` ではない -/
theorem not_psi_c_of_mem_subs {c w α : Tm} (hw : w ∈ subs c) : w ≠ Tm.Psi .zero (.Om c) α := by
  intro e
  subst e
  have := size_le_of_mem_subs hw
  simp only [Tm.size] at this
  omega

theorem intCutPair_of_sub {q p c γ : Tm} (hq : q ∈ subs c) :
    IntCutPair q p (Tm.Psi .zero (.Om c) γ) := by
  intro c' α β γ' ht hq' _ _ _
  cases ht
  exact absurd hq' (not_psi_c_of_mem_subs hq)

theorem lt_head_of_lt_plus {a b t : Tm} (htp : isPrincipal t = true) (h : Lt (.plus a b) t) :
    cmpP a t = .lt := by
  unfold Lt at h
  rw [cmp_eq, summands, summands_principal' htp] at h
  rcases cmpList_lt_cases h with e | ⟨_, e⟩
  · exact e
  · cases hs : summands b with
    | nil => rw [hs, cmpList_nil_nil] at e; cases e
    | cons _ _ => rw [hs, cmpList_cons_nil] at e; cases e

theorem lt_of_head_lt {b t h : Tm} {rest : List Tm} (htp : isPrincipal t = true)
    (hs : summands b = h :: rest) (h1 : cmpP h t = .lt) : Lt b t := by
  unfold Lt
  rw [cmp_eq, hs, summands_principal' htp, cmpList_cons_cons_ne _ _ (by rw [h1]; decide), h1]

/-- `t = Ψ_c(γ)`、`w ⊑ c` で `w < t` なら `w ∈ C(g, t)` -/
theorem bl_c {S : List Tm} (hS : LinOn S) (hNF : ∀ s, s ∈ S → F0NF s)
    (hcl : ∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S) {c γ : Tm} (ht : F0NF (.Psi .zero (.Om c) γ))
    (hsub : ∀ s, s ∈ subs (.Psi .zero (.Om c) γ) → s ≠ .Psi .zero (.Om c) γ → s ∈ S) :
    ∀ w, w ∈ subs c → Lt w (.Psi .zero (.Om c) γ) → ∀ g, inC w g (.Psi .zero (.Om c) γ) = true := by
  have hS' : ∀ w, w ∈ subs c → w ∈ S := fun w hw =>
    hsub w (subs_trans (mem_subs_psi_c .zero c γ) hw) (fun e => not_psi_c_of_mem_subs hw e)
  intro w
  induction w with
  | zero => intro _ _ g; exact inC_zero g _
  | one => intro _ _ g; exact inC_one g _
  | K n => intro _ _ g; exact inC_K n g _
  | plus a b iha ihb =>
    intro hw hlt g
    have ha : a ∈ subs c := subs_trans hw (by simp [subs, self_mem_subs])
    have hb : b ∈ subs c := subs_trans hw (by simp [subs, self_mem_subs])
    have hwF := hNF _ (hS' _ hw)
    obtain ⟨haF, hbF, hap, hb0⟩ := hwF.plus
    have hat := lt_head_of_lt_plus rfl hlt
    cases hs : summands b with
    | nil => exact absurd hs (summands_ne_nil hb0)
    | cons h rest =>
      have hmem : h ∈ summands b := by rw [hs]; exact List.mem_cons_self
      have hh : h ∈ subs c := subs_trans hb (mem_subs_of_mem_summands hmem)
      obtain ⟨hhF, hhp⟩ := summands_F0NF b hbF h hmem
      have hht : cmpP h (.Psi .zero (.Om c) γ) = .lt := by
        have hle := hwF.plus_head hs
        rw [← lt_principal_iff hhp rfl]
        rcases le_of_not_lt' haF hhF (fun h' => hle (by unfold Lt at h'; rw [cmp_swap_F0 haF hhF, h']; rfl))
          with e | e
        · rw [e]; exact (lt_principal_iff hap rfl).mpr hat
        · exact cutP hS hNF hcl ht rfl hsub (intCutPair_of_sub hh) (hS' a ha) (hS' h hh) hap hhp e
            ((lt_principal_iff hap rfl).mpr hat)
      rw [inC_plus, iha ha ((lt_principal_iff hap rfl).mpr hat) g,
        ihb hb (lt_of_head_lt rfl hs hht) g]
      rfl
  | Om e ihe =>
    intro hw hlt g
    have he : e ∈ subs c := subs_trans hw (mem_subs_om e)
    have hwF := hNF _ (hS' _ hw)
    have het : Lt e (.Psi .zero (.Om c) γ) :=
      cutGen hS hNF hcl ht hsub (fun q _ hq _ => intCutPair_of_sub
        (subs_trans he (mem_subs_of_mem_summands hq))) (hS' _ hw) (hS' _ he) hwF.om.2.2 hlt
    rw [inC_om]
    exact ihe he het g
  | Xi n a _ =>
    intro hw _ _
    exact ((hNF _ (hS' _ hw)).not_xi).elim
  | Psi s k a _ _ _ =>
    intro _ hlt g
    exact inC_psi_iff.mpr (Or.inl hlt)

/-- IC：`t = Ψ_c(γ)` について `Ω_c ∈ C(g, t)` -/
theorem ic_t {S : List Tm} (hS : LinOn S) (hNF : ∀ s, s ∈ S → F0NF s)
    (hcl : ∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S) {c γ : Tm} (ht : F0NF (.Psi .zero (.Om c) γ))
    (hsub : ∀ s, s ∈ subs (.Psi .zero (.Om c) γ) → s ≠ .Psi .zero (.Om c) γ → s ∈ S) (g : Tm) :
    inC (.Om c) g (.Psi .zero (.Om c) γ) = true := by
  rw [inC_om]
  exact bl_c hS hNF hcl ht hsub c (self_mem_subs c) (cx _ c γ (Nat.le_refl _) ht) g

/-! ### K2：`γ ∈ C(γ, Ψ_c(γ))` -/

/-- `S` の `Ψ` について K2 が成り立つ -/
def K2On (S : List Tm) : Prop :=
  ∀ c α, Tm.Psi .zero (.Om c) α ∈ S → inC α α (.Psi .zero (.Om c) α) = true

/-- `S` の `Ψ_c(α)` について `Ω_c ∈ C(g, Ψ_c(α))` -/
def ICOn (S : List Tm) : Prop :=
  ∀ c α g, Tm.Psi .zero (.Om c) α ∈ S → inC (.Om c) g (.Psi .zero (.Om c) α) = true

def argOf : Tm → Tm
  | .Psi _ _ a => a
  | t => t

/-- K2 の証明で `C(g, d)` の `d` に使う項：`Ω_c` か `S` の `Ψ_c(δ)` -/
def AllowedD (S : List Tm) (c d : Tm) : Prop := d = .Om c ∨ ∃ δ, d = .Psi .zero (.Om c) δ ∧ d ∈ S

theorem find_first (P : Tm → Prop) [DecidablePred P] : ∀ l : List Tm,
    (∀ x, x ∈ l → ¬ P x) ∨ ∃ pre x post, l = pre ++ x :: post ∧ P x ∧ ∀ y, y ∈ pre → ¬ P y
  | [] => Or.inl (fun _ h => absurd h List.not_mem_nil)
  | x :: xs => by
    by_cases hx : P x
    · exact Or.inr ⟨[], x, xs, rfl, hx, fun _ h => absurd h List.not_mem_nil⟩
    · rcases find_first P xs with h | ⟨pre, y, post, e, hy, hpre⟩
      · refine Or.inl (fun z hz => ?_)
        rcases List.mem_cons.mp hz with e | e
        · subst e; exact hx
        · exact h z e
      · refine Or.inr ⟨x :: pre, y, post, by rw [e]; rfl, hy, fun z hz => ?_⟩
        rcases List.mem_cons.mp hz with e | e
        · subst e; exact hx
        · exact hpre z e

theorem inC_params {s k δ g d : Tm} (h : inC (.Psi s k δ) g d = true) (hn : ¬ Lt (.Psi s k δ) d) :
    inC k g d = true ∧ inC s g d = true ∧ inC δ g d = true ∧ Lt δ g := by
  rcases inC_psi_iff.mp h with h | h
  · exact absurd h hn
  · exact h

theorem lt_psi_om_self (c δ : Tm) : Lt (.Psi .zero (.Om c) δ) (.Om c) :=
  (lt_psi_om c c δ rfl).mpr (Lt.irrefl c)

theorem k2_aux {S : List Tm} (hS : LinOn S) (hNF : ∀ s, s ∈ S → F0NF s)
    (hcl : ∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S) (hK2 : K2On S) (hIC : ICOn S)
    {c γ : Tm} (ht : F0NF (.Psi .zero (.Om c) γ)) (htS : Tm.Psi .zero (.Om c) γ ∉ S)
    (hOm : Tm.Om c ∈ S) (hγS : γ ∈ S) (hICt : ∀ g, inC (.Om c) g (.Psi .zero (.Om c) γ) = true) :
    ∀ w, w ∈ S → ∀ fr : List Tm,
      (∀ f, f ∈ fr → ∃ δ, f = .Psi .zero (.Om c) δ ∧ f ∈ S ∧
        Lt (.Psi .zero (.Om c) γ) f ∧ Lt δ γ) →
      (∀ g d, AllowedD S c d → (∀ f, f ∈ fr → ¬ Lt f d) → inC γ g d = true →
        inC w g d = true) →
      (∀ pre f post, fr = pre ++ f :: post → ∀ g d, AllowedD S c d →
        (∀ f', f' ∈ pre → ¬ Lt f' d) → inC (argOf f) g d = true → inC w g d = true) →
      inC w γ (.Psi .zero (.Om c) γ) = true := by
  -- `Ω_c` 以上の項は許される `d` より小さくない
  have notlt : ∀ u, u ∈ S → ¬ Lt u (.Om c) → ∀ d, AllowedD S c d → ¬ Lt u d := by
    intro u hu huO d hd hlt
    rcases hd with rfl | ⟨δ, rfl, hdS⟩
    · exact huO hlt
    · exact huO (hS u hu _ hdS _ hOm hlt (lt_psi_om_self c δ))
  intro w
  induction w with
  | zero => intros; exact inC_zero _ _
  | one => intros; exact inC_one _ _
  | K n => intros; exact inC_K n _ _
  | plus a b iha ihb =>
    intro hw fr hF hTop hFr
    have ha := hcl _ hw a (by simp [subs, self_mem_subs])
    have hb := hcl _ hw b (by simp [subs, self_mem_subs])
    have pa : ∀ g d, inC (.plus a b) g d = true → inC a g d = true := fun g d h => by
      rw [inC_plus, Bool.and_eq_true] at h; exact h.1
    have pb : ∀ g d, inC (.plus a b) g d = true → inC b g d = true := fun g d h => by
      rw [inC_plus, Bool.and_eq_true] at h; exact h.2
    rw [inC_plus,
      iha ha fr hF (fun g d hd hf h => pa g d (hTop g d hd hf h))
        (fun pre f post e g d hd hp h => pa g d (hFr pre f post e g d hd hp h)),
      ihb hb fr hF (fun g d hd hf h => pb g d (hTop g d hd hf h))
        (fun pre f post e g d hd hp h => pb g d (hFr pre f post e g d hd hp h))]
    rfl
  | Om e ihe =>
    intro hw fr hF hTop hFr
    have he := hcl _ hw e (mem_subs_om e)
    rw [inC_om]
    exact ihe he fr hF (fun g d hd hf h => by rw [← inC_om]; exact hTop g d hd hf h)
      (fun pre f post eq g d hd hp h => by rw [← inC_om]; exact hFr pre f post eq g d hd hp h)
  | Xi n a _ => intro hw; exact ((hNF _ hw).not_xi).elim
  | Psi s k δ _ ihk ihδ =>
    intro hw fr hF hTop hFr
    have huF := hNF _ hw
    obtain ⟨hs0, e, hke, heF, -, hδF, -, -⟩ := huF.psi
    subst hs0 hke
    have hkS := hcl _ hw (.Om e) (by simp [subs])
    have hδS := hcl _ hw δ (mem_subs_psi_a _ _ δ)
    by_cases hut : Lt (.Psi .zero (.Om e) δ) (.Psi .zero (.Om c) γ)
    · exact inC_psi_iff.mpr (Or.inl hut)
    have htu : Lt (.Psi .zero (.Om c) γ) (.Psi .zero (.Om e) δ) := by
      rcases tri ht huF with h | h | h
      · exact h
      · rw [h] at htS; exact absurd hw htS
      · exact absurd h hut
    by_cases huO : Lt (.Psi .zero (.Om e) δ) (.Om c)
    · -- `t < u < Ω_c`：`u` は同じ区間
      have hl1 := lev_le_of_cmpP_lt ((lt_principal_iff rfl rfl).mp htu)
      have hl2 := lev_le_of_cmpP_lt ((lt_principal_iff rfl rfl).mp huO)
      simp only [lev] at hl1 hl2
      have hl : lev e = lev c := by omega
      have hcF : F0NF c := by
        obtain ⟨-, c', hc', hcF', -⟩ := ht.psi
        cases hc'
        exact hcF'.om.1
      have hec : c = e := by
        rcases tri heF.om.1 hcF with h | h | h
        · exact absurd (lt_psi_psi_of_lt e c δ γ hl h) hut
        · exact h.symm
        · exact absurd h ((lt_psi_om c e δ hl.symm).mp huO)
      subst hec
      have hδγ : Lt δ γ := by
        rcases find_first (fun f => Lt f (.Psi .zero (.Om c) δ)) fr with
          hnone | ⟨pre, f, post, hfr, hfu, hpre⟩
        · have h1 := hTop δ (.Psi .zero (.Om c) δ) (Or.inr ⟨δ, rfl, hw⟩) hnone
          have h2 : inC γ δ (.Psi .zero (.Om c) δ) = false := by
            cases h3 : inC γ δ (.Psi .zero (.Om c) δ)
            · rfl
            · have := h1 h3; rw [inC_self_false] at this; cases this
          have hne : γ ≠ δ := by intro h; subst h; exact Lt.irrefl _ htu
          rcases (lt_psi_same_iff ht huF hne hICt (fun g => hIC c δ g hw)).mp htu with
            ⟨_, h⟩ | ⟨h, _⟩
          · rw [h2] at h; cases h
          · exact h
        · obtain ⟨δf, rfl, hfS, _, hδf⟩ := hF f (by rw [hfr]; simp)
          have h1 := hFr pre (.Psi .zero (.Om c) δf) post hfr δ (.Psi .zero (.Om c) δ)
            (Or.inr ⟨δ, rfl, hw⟩) hpre
          have h2 : inC δf δ (.Psi .zero (.Om c) δ) = false := by
            cases h3 : inC δf δ (.Psi .zero (.Om c) δ)
            · rfl
            · have := h1 h3; rw [inC_self_false] at this; cases this
          have hne : δf ≠ δ := by intro h; subst h; exact Lt.irrefl _ hfu
          rcases (lt_psi_same_iff (hNF _ hfS) huF hne (fun g => hIC c δf g hfS)
            (fun g => hIC c δ g hw)).mp hfu with ⟨_, h⟩ | ⟨h, _⟩
          · rw [h2] at h; cases h
          · exact hS δ hδS δf (hcl _ hfS δf (mem_subs_psi_a _ _ δf)) γ hγS h hδf
      refine inC_psi_iff.mpr (Or.inr ⟨hICt γ, inC_zero _ _, ?_, hδγ⟩)
      exact ihδ hδS (.Psi .zero (.Om c) δ :: fr)
        (fun f hf => by
          rcases List.mem_cons.mp hf with h | h
          · subst h; exact ⟨δ, rfl, hw, htu, hδγ⟩
          · exact hF f h)
        (fun g d hd hf h => by
          have h1 := hTop g d hd (fun f' hf' => hf f' (List.mem_cons_of_mem _ hf')) h
          exact (inC_params h1 (hf _ List.mem_cons_self)).2.2.1)
        (fun pre f post e g d hd hp h => by
          cases pre with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at e
            obtain ⟨rfl, rfl⟩ := e
            exact h
          | cons p pre' =>
            simp only [List.cons_append, List.cons.injEq] at e
            obtain ⟨rfl, e⟩ := e
            have h1 := hFr pre' f post e g d hd (fun f' hf' => hp f' (List.mem_cons_of_mem _ hf')) h
            exact (inC_params h1 (hp _ List.mem_cons_self)).2.2.1)
    · -- `u ≥ Ω_c`
      have hδγ : Lt δ γ := by
        cases fr with
        | nil =>
          have hnf : inC γ γ (.Om c) = true := by
            obtain ⟨-, c', hc', -, -, -, hCa, -⟩ := ht.psi
            cases hc'
            exact hCa
          have h1 := hTop γ (.Om c) (Or.inl rfl) (fun f hf => absurd hf List.not_mem_nil) hnf
          exact (inC_params h1 huO).2.2.2
        | cons f rest =>
          obtain ⟨δf, rfl, hfS, _, hδf⟩ := hF f List.mem_cons_self
          have h1 := hFr [] (.Psi .zero (.Om c) δf) rest rfl δf (.Psi .zero (.Om c) δf)
            (Or.inr ⟨δf, rfl, hfS⟩) (fun f' hf' => absurd hf' List.not_mem_nil) (hK2 c δf hfS)
          have h2 := (inC_params h1 (notlt _ hw huO _ (Or.inr ⟨δf, rfl, hfS⟩))).2.2.2
          exact hS δ hδS δf (hcl _ hfS δf (mem_subs_psi_a _ _ δf)) γ hγS h2 hδf
      have pk : ∀ g d, AllowedD S c d → inC (.Psi .zero (.Om e) δ) g d = true →
          inC (.Om e) g d = true ∧ inC δ g d = true := fun g d hd h =>
        let r := inC_params h (notlt _ hw huO d hd)
        ⟨r.1, r.2.2.1⟩
      refine inC_psi_iff.mpr (Or.inr ⟨?_, inC_zero _ _, ?_, hδγ⟩)
      · exact ihk hkS fr hF (fun g d hd hf h => (pk g d hd (hTop g d hd hf h)).1)
          (fun pre f post e g d hd hp h => (pk g d hd (hFr pre f post e g d hd hp h)).1)
      · exact ihδ hδS fr hF (fun g d hd hf h => (pk g d hd (hTop g d hd hf h)).2)
          (fun pre f post e g d hd hp h => (pk g d hd (hFr pre f post e g d hd hp h)).2)


/-- K2：`t = Ψ_c(γ)` について `γ ∈ C(γ, t)` -/
theorem k2_t {S : List Tm} (hS : LinOn S) (hNF : ∀ s, s ∈ S → F0NF s)
    (hcl : ∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S) (hK2 : K2On S) (hIC : ICOn S)
    {c γ : Tm} (ht : F0NF (.Psi .zero (.Om c) γ)) (htS : Tm.Psi .zero (.Om c) γ ∉ S)
    (hOm : Tm.Om c ∈ S) (hγS : γ ∈ S) (hICt : ∀ g, inC (.Om c) g (.Psi .zero (.Om c) γ) = true) :
    inC γ γ (.Psi .zero (.Om c) γ) = true :=
  k2_aux hS hNF hcl hK2 hIC ht htS hOm hγS hICt γ hγS []
    (fun _ h => absurd h List.not_mem_nil) (fun _ _ _ _ h => h)
    (fun pre _ _ e => by cases pre <;> simp at e)

/-! ### `C` の単調性 -/

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

/-! ### 同じ区間の `Ψ` どうしの切断性 -/

theorem lev_le_of_lt_psi {x y : Tm} (hx : isPrincipal x = true) (hy : isPrincipal y = true)
    (h : Lt x y) : lev x ≤ lev y :=
  lev_le_of_cmpP_lt ((lt_principal_iff hx hy).mp h)

/-- (c2, c2) の場合の否定：`x < y < z`、`γ < β` で、`w ⊑ γ` が `C(γ, z)` と `C(α, x)` に入り
    `C(β, y)` に入らないことはない -/
theorem rlemma {S : List Tm} (hS : LinOn S) (hNF : ∀ s, s ∈ S → F0NF s)
    (hcl : ∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S) (hIC : ICOn S)
    {c α β γ : Tm} (hx : Tm.Psi .zero (.Om c) α ∈ S) (hy : Tm.Psi .zero (.Om c) β ∈ S)
    (hz : F0NF (.Psi .zero (.Om c) γ)) (hγS : γ ∈ S)
    (hxy : Lt (.Psi .zero (.Om c) α) (.Psi .zero (.Om c) β)) (hγβ : Lt γ β) :
    ∀ w, w ∈ subs γ → inC w γ (.Psi .zero (.Om c) γ) = true →
      inC w α (.Psi .zero (.Om c) α) = true → inC w β (.Psi .zero (.Om c) β) = false → False := by
  have hβS := hcl _ hy β (mem_subs_psi_a _ _ β)
  intro w
  induction w with
  | zero => intro _ _ _ h3; rw [inC_zero] at h3; cases h3
  | one => intro _ _ _ h3; rw [inC_one] at h3; cases h3
  | K n => intro _ _ _ h3; rw [inC_K] at h3; cases h3
  | plus a b iha ihb =>
    intro hw h1 h2 h3
    rw [inC_plus, Bool.and_eq_true] at h1 h2
    rw [inC_plus] at h3
    have ha : a ∈ subs γ := subs_trans hw (by simp [subs, self_mem_subs])
    have hb : b ∈ subs γ := subs_trans hw (by simp [subs, self_mem_subs])
    cases e : inC a β (.Psi .zero (.Om c) β)
    · exact iha ha h1.1 h2.1 e
    · rw [e, Bool.true_and] at h3
      exact ihb hb h1.2 h2.2 h3
  | Om e ihe =>
    intro hw h1 h2 h3
    rw [inC_om] at h1 h2 h3
    exact ihe (subs_trans hw (mem_subs_om e)) h1 h2 h3
  | Xi n a _ =>
    intro hw
    exact ((hNF _ (hcl _ hγS _ hw)).not_xi).elim
  | Psi s k δ _ ihk ihδ =>
    intro hw h1 h2 h3
    have hwS := hcl _ hγS _ hw
    have hwF := hNF _ hwS
    obtain ⟨hs0, e, hke, heF, -, hδF, -, -⟩ := hwF.psi
    subst hs0 hke
    have hδS := hcl _ hwS δ (mem_subs_psi_a _ _ δ)
    have hxF := hNF _ hx
    have hyF := hNF _ hy
    -- `w ≥ y`
    have h3' : ¬ (Lt (.Psi .zero (.Om e) δ) (.Psi .zero (.Om c) β) ∨
        (inC (.Om e) β (.Psi .zero (.Om c) β) = true ∧ inC .zero β (.Psi .zero (.Om c) β) = true ∧
          inC δ β (.Psi .zero (.Om c) β) = true ∧ Lt δ β)) := by
      intro h
      rw [← inC_psi_iff, h3] at h
      cases h
    have hwy : ¬ Lt (.Psi .zero (.Om e) δ) (.Psi .zero (.Om c) β) := fun h => h3' (Or.inl h)
    have hyw := le_of_not_lt' hwF hyF hwy
    have hxw : Lt (.Psi .zero (.Om c) α) (.Psi .zero (.Om e) δ) := by
      rcases hyw with h | h
      · rw [← h]; exact hxy
      · exact hS _ hx _ hy _ hwS hxy h
    rcases inC_psi_iff.mp h2 with h | ⟨_, _, hδα, hlα⟩
    · exact Lt.asymm hxF hwF hxw h
    rcases inC_psi_iff.mp h1 with h | ⟨hkγ, _, hδγ', hlγ⟩
    · -- `y ≤ w < z`：`w` は同じ区間で `w < x`
      have l1 : lev (Tm.Psi .zero (.Om c) β) ≤ lev (.Psi .zero (.Om e) δ) := by
        rcases hyw with h' | h'
        · rw [h']; exact Nat.le_refl _
        · exact lev_le_of_lt_psi rfl rfl h'
      have l2 := lev_le_of_lt_psi rfl rfl h
      simp only [lev] at l1 l2
      have hl : lev e = lev c := by omega
      have hcF : F0NF c := by
        obtain ⟨-, c', hc', hcF', -⟩ := hz.psi
        cases hc'
        exact hcF'.om.1
      have hec : c = e := by
        rcases tri heF.om.1 hcF with h' | h' | h'
        · exact absurd (lt_psi_psi_of_lt e c δ β hl h') hwy
        · exact h'.symm
        · exact absurd h (Lt.asymm hz hwF (lt_psi_psi_of_lt c e γ δ hl.symm h'))
      subst hec
      have hne : δ ≠ α := by intro h'; subst h'; exact Lt.irrefl _ hxw
      have hwx := (lt_psi_same_iff hwF hxF hne (fun g => hIC c δ g hwS) (fun g => hIC c α g hx)).mpr
        (Or.inl ⟨hlα, hδα⟩)
      exact Lt.asymm hxF hwF hxw hwx
    · -- 引数のどれかが `C(β, y)` に入らない
      have hδβ : Lt δ β := hS δ hδS γ hγS β hβS hlγ hγβ
      have hkS : (Tm.Om e) ∈ subs γ := subs_trans hw (by simp [subs, self_mem_subs])
      have hδs : δ ∈ subs γ := subs_trans hw (mem_subs_psi_a _ _ δ)
      obtain ⟨hkα, -, -, -⟩ := inC_params h2 (fun h => Lt.asymm hxF hwF hxw h)
      cases ek : inC (.Om e) β (.Psi .zero (.Om c) β)
      · exact ihk hkS hkγ hkα ek
      · cases eδ : inC δ β (.Psi .zero (.Om c) β)
        · exact ihδ hδs hδγ' hδα eδ
        · exact h3' (Or.inr ⟨ek, inC_zero _ _, eδ, hδβ⟩)

/-- 同じ区間の `Ψ` どうしの切断性：`x < y < t` なら `x < t`（`t = Ψ_c(γ)`、`x, y ∈ S`） -/
theorem intCut {S : List Tm} (hS : LinOn S) (hNF : ∀ s, s ∈ S → F0NF s)
    (hcl : ∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S) (hK2 : K2On S) (hIC : ICOn S)
    {c γ : Tm} (ht : F0NF (.Psi .zero (.Om c) γ)) (htS : Tm.Psi .zero (.Om c) γ ∉ S)
    (hsub : ∀ s, s ∈ subs (.Psi .zero (.Om c) γ) → s ≠ .Psi .zero (.Om c) γ → s ∈ S) :
    ∀ n α β, (Tm.Psi .zero (.Om c) α).size + (Tm.Psi .zero (.Om c) β).size ≤ n →
      Tm.Psi .zero (.Om c) α ∈ S → Tm.Psi .zero (.Om c) β ∈ S →
      Lt (.Psi .zero (.Om c) α) (.Psi .zero (.Om c) β) →
      Lt (.Psi .zero (.Om c) β) (.Psi .zero (.Om c) γ) →
      Lt (.Psi .zero (.Om c) α) (.Psi .zero (.Om c) γ) := by
  have hOm : Tm.Om c ∈ S := hsub _ (by simp [subs, self_mem_subs])
    (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))
  have hγS : γ ∈ S := hsub _ (mem_subs_psi_a _ _ γ)
    (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))
  have hICt := ic_t hS hNF hcl ht hsub
  have hK2t := k2_t hS hNF hcl hK2 hIC ht htS hOm hγS hICt
  intro n
  induction n with
  | zero =>
    intro α _ h
    have := Tm.size_pos (.Psi .zero (.Om c) α)
    omega
  | succ n ih =>
    intro α β hn hx hy hxy hyz
    have hxF := hNF _ hx
    have hyF := hNF _ hy
    have hαS := hcl _ hx α (mem_subs_psi_a _ _ α)
    have hβS := hcl _ hy β (mem_subs_psi_a _ _ β)
    -- `t` を上端とする切断性（大きさの和が `n` 以下の組）
    have cutT : ∀ a b, a ∈ S → b ∈ S → a.size + b.size ≤ n →
        Lt b a → Lt a (.Psi .zero (.Om c) γ) → Lt b (.Psi .zero (.Om c) γ) := by
      intro a b ha hb hs h1 h2
      refine cutGen hS hNF hcl ht hsub (fun q p hq hp => ?_) ha hb h1 h2
      intro c' α' β' γ' het hq' hp' h1' h2'
      cases het
      subst hq' hp'
      have s1 := size_le_of_mem_subs (mem_subs_of_mem_summands hq)
      have s2 := size_le_of_mem_subs (mem_subs_of_mem_summands hp)
      exact ih α' β' (by omega) (hcl _ hb _ (mem_subs_of_mem_summands hq))
        (hcl _ ha _ (mem_subs_of_mem_summands hp)) h1' h2'
    have hne_αγ : α ≠ γ := by intro e; subst e; exact htS hx
    have hne_βγ : β ≠ γ := by intro e; subst e; exact htS hy
    have hne_αβ : α ≠ β := by intro e; subst e; exact Lt.irrefl _ hxy
    have cxy := (lt_psi_same_iff hxF hyF hne_αβ (fun g => hIC c α g hx)
      (fun g => hIC c β g hy)).mp hxy
    have cyz := (lt_psi_same_iff hyF ht hne_βγ (fun g => hIC c β g hy) hICt).mp hyz
    rw [lt_psi_same_iff hxF ht hne_αγ (fun g => hIC c α g hx) hICt]
    rcases tri (hNF _ hαS) (hNF _ hγS) with hαγ | hαγ | hγα
    · -- `α < γ`：K2(x) と単調性
      refine Or.inl ⟨hαγ, inC_mono α α (.Psi .zero (.Om c) α) γ (.Psi .zero (.Om c) γ) (hK2 c α hx) (fun v hv hvx => ?_)
        (fun v hv hvα => hS v (hcl _ hαS v hv) α hαS γ hγS hvα hαγ)⟩
      have hvS := hcl _ hαS v hv
      have hvy := hS v hvS _ hx _ hy hvx hxy
      have := size_le_of_mem_subs hv
      exact cutT _ v hy hvS (by simp only [Tm.size] at hn ⊢; omega) hvy hyz
    · exact absurd hαγ hne_αγ
    · -- `γ < α`：`γ ∉ C(α, x)` を示す
      refine Or.inr ⟨hγα, ?_⟩
      cases e : inC γ α (.Psi .zero (.Om c) α)
      · rfl
      exfalso
      rcases cxy with ⟨hab, hIab⟩ | ⟨hba, hIba⟩ <;> rcases cyz with ⟨hbg, hIbg⟩ | ⟨hgb, hIgb⟩
      · exact Lt.asymm (hNF _ hγS) (hNF _ hαS) hγα (hS α hαS β hβS γ hγS hab hbg)
      · have := inC_mono γ α (.Psi .zero (.Om c) α) β (.Psi .zero (.Om c) β) e
          (fun v hv hvx => hS v (hcl _ hγS v hv) _ hx _ hy hvx hxy)
          (fun v hv hvα => hS v (hcl _ hγS v hv) α hαS β hβS hvα hab)
        rw [hIgb] at this
        cases this
      · have hzx : Lt (.Psi .zero (.Om c) γ) (.Psi .zero (.Om c) α) :=
          (lt_psi_same_iff ht hxF (fun h => hne_αγ h.symm) hICt (fun g => hIC c α g hx)).mpr
            (Or.inl ⟨hγα, e⟩)
        have := inC_mono β γ (.Psi .zero (.Om c) γ) α (.Psi .zero (.Om c) α) hIbg (fun v hv hvz => ?_)
          (fun v hv hvγ => hS v (hcl _ hβS v hv) γ hγS α hαS hvγ hγα)
        · rw [hIba] at this
          cases this
        · have hvS := hcl _ hβS v hv
          rcases tri (hNF _ hvS) hxF with h' | h' | h'
          · exact h'
          · subst h'
            exact absurd hvz (Lt.asymm ht hxF hzx)
          · have := size_le_of_mem_subs hv
            exact absurd (cutT v _ hvS hx (by simp only [Tm.size] at hn ⊢; omega) h' hvz)
              (Lt.asymm ht hxF hzx)
      · exact rlemma hS hNF hcl hIC hx hy ht hγS hxy hgb γ (self_mem_subs γ) hK2t e hIgb

/-! ### 部分項で閉じた有限集合についての帰納法 -/

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

/-- 部分項で閉じた `F0` の標準形の有限集合の上で `<` は推移的（K2・IC も成り立つ） -/
theorem lin_closed : ∀ n, ∀ S : List Tm, S.length ≤ n →
    (∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S) → (∀ s, s ∈ S → F0NF s) →
    LinOn S ∧ K2On S ∧ ICOn S := by
  intro n
  induction n with
  | zero =>
    intro S hl _ _
    have hS : S = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst hS
    exact ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ h => absurd h List.not_mem_nil,
      fun _ _ _ h => absurd h List.not_mem_nil⟩
  | succ n ih =>
    intro S hl hcl hNF
    by_cases hS0 : S = []
    · subst hS0
      exact ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ h => absurd h List.not_mem_nil,
        fun _ _ _ h => absurd h List.not_mem_nil⟩
    obtain ⟨t, htS, hmax⟩ := exists_max_size S hS0
    have hmem : ∀ s, s ∈ S.filter (fun s => s != t) ↔ s ∈ S ∧ s ≠ t := by
      intro s
      rw [List.mem_filter, bne_iff_ne]
    have hl' : (S.filter (fun s => s != t)).length ≤ n := by
      have := length_filter_ne_lt htS
      omega
    have hcl' : ∀ s, s ∈ S.filter (fun s => s != t) → ∀ r, r ∈ subs s →
        r ∈ S.filter (fun s => s != t) := by
      intro s hs r hr
      obtain ⟨hsS, hst⟩ := (hmem s).mp hs
      refine (hmem r).mpr ⟨hcl s hsS r hr, ?_⟩
      intro e
      subst e
      exact hst (eq_of_mem_subs_size hr (hmax s hsS)).symm
    have hNF' : ∀ s, s ∈ S.filter (fun s => s != t) → F0NF s := fun s hs =>
      hNF s ((hmem s).mp hs).1
    obtain ⟨hLin', hK2', hIC'⟩ := ih _ hl' hcl' hNF'
    have htF := hNF t htS
    have hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S.filter (fun s => s != t) := fun s hs hne =>
      (hmem s).mpr ⟨hcl t htS s hs, hne⟩
    have htS' : t ∉ S.filter (fun s => s != t) := fun h => ((hmem t).mp h).2 rfl
    -- `t` は `S'` を切断する
    have cut : ∀ a b, a ∈ S.filter (fun s => s != t) → b ∈ S.filter (fun s => s != t) →
        Lt b a → Lt a t → Lt b t := by
      intro a b ha hb h1 h2
      refine cutGen hLin' hNF' hcl' htF hsub (fun q p hq hp => ?_) ha hb h1 h2
      intro c α β γ het hq' hp' h1' h2'
      subst het hq' hp'
      exact intCut hLin' hNF' hcl' hK2' hIC' htF htS' hsub _ α β (Nat.le_refl _)
        (hcl' _ hb _ (mem_subs_of_mem_summands hq)) (hcl' _ ha _ (mem_subs_of_mem_summands hp))
        h1' h2'
    have inS' : ∀ s, s ∈ S → s ≠ t → s ∈ S.filter (fun s => s != t) := fun s hs hne =>
      (hmem s).mpr ⟨hs, hne⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a ha b hb c hc hab hbc
      have haF := hNF a ha
      have hbF := hNF b hb
      have hcF := hNF c hc
      by_cases eat : a = t <;> by_cases ebt : b = t <;> by_cases ect : c = t
      · subst eat; subst ebt; exact absurd hab (Lt.irrefl _)
      · subst eat; subst ebt; exact absurd hab (Lt.irrefl _)
      · subst eat; subst ect; exact absurd hbc (Lt.asymm haF hbF hab)
      · subst eat
        rcases tri haF hcF with h | h | h
        · exact h
        · exact absurd h.symm ect
        · exact absurd hab (Lt.asymm hbF haF (cut c b (inS' c hc ect) (inS' b hb ebt) hbc h))
      · subst ebt; subst ect; exact absurd hbc (Lt.irrefl _)
      · subst ebt
        rcases tri haF hcF with h | h | h
        · exact h
        · subst h; exact absurd hbc (Lt.asymm haF hbF hab)
        · exact absurd hbc (Lt.asymm hcF hbF (cut a c (inS' a ha eat) (inS' c hc ect) h hab))
      · subst ect
        exact cut b a (inS' b hb ebt) (inS' a ha eat) hab hbc
      · exact hLin' a (inS' a ha eat) b (inS' b hb ebt) c (inS' c hc ect) hab hbc
    · intro c α hx
      by_cases e : Tm.Psi .zero (.Om c) α = t
      · subst e
        have hOm := hsub (.Om c) (by simp [subs, self_mem_subs])
          (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))
        have hαS := hsub α (mem_subs_psi_a _ _ α) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))
        exact k2_t hLin' hNF' hcl' hK2' hIC' htF htS' hOm hαS (ic_t hLin' hNF' hcl' htF hsub)
      · exact hK2' c α (inS' _ hx e)
    · intro c α g hx
      by_cases e : Tm.Psi .zero (.Om c) α = t
      · subst e
        exact ic_t hLin' hNF' hcl' htF hsub g
      · exact hIC' c α g (inS' _ hx e)

/-- `F0` の標準形の上で `<` は推移的 -/
theorem lt_trans_F0 {a b c : Tm} (ha : F0NF a) (hb : F0NF b) (hc : F0NF c)
    (h1 : Lt a b) (h2 : Lt b c) : Lt a c := by
  let S := subs a ++ subs b ++ subs c
  have hcl : ∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S := by
    intro s hs r hr
    simp only [S, List.mem_append] at hs ⊢
    rcases hs with (hs | hs) | hs
    · exact Or.inl (Or.inl (subs_trans hs hr))
    · exact Or.inl (Or.inr (subs_trans hs hr))
    · exact Or.inr (subs_trans hs hr)
  have hNF : ∀ s, s ∈ S → F0NF s := by
    intro s hs
    simp only [S, List.mem_append] at hs
    rcases hs with (hs | hs) | hs
    · exact ha.of_mem_subs hs
    · exact hb.of_mem_subs hs
    · exact hc.of_mem_subs hs
  have hLin := (lin_closed _ S (Nat.le_refl _) hcl hNF).1
  exact hLin a (by simp [S, self_mem_subs]) b (by simp [S, self_mem_subs])
    c (by simp [S, self_mem_subs]) h1 h2

end RTKA
