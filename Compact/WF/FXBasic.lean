import Compact.WF.FX
import Compact.WF.F0Lin

/-! 断片 `FX` の推移性の証明の道具（`F0Lin.lean` の `F0` 用の補題を `FX` に広げたもの）。

* 三分律・非対称性（`triX`・`Lt.asymmX`）。
* 主要項の形（`shape_FX`）と、`Ξ` を含む比較の言い換え（`lt_om_xi`・`lt_xi_om`・`lt_xi_xi_same`・
  `lt_psi_xi`）。
* 辞書式比較の推移性（`lexTransX`）と、主要項の切断性から一般の項の切断性を導く `cutGenX`。 -/

namespace RTKA

open Tm

/-! ### 三分律 -/

theorem Lt.asymmX {a b : Tm} (ha : FXNF a) (hb : FXNF b) (h : Lt a b) : ¬ Lt b a := by
  unfold Lt at *
  rw [cmp_swap_FX ha hb, h]
  decide

theorem lt_of_gtX {a b : Tm} (ha : FXNF a) (hb : FXNF b) (h : cmp a b = .gt) : Lt b a := by
  unfold Lt
  rw [cmp_swap_FX ha hb, h]
  rfl

theorem triX {a b : Tm} (ha : FXNF a) (hb : FXNF b) : Lt a b ∨ a = b ∨ Lt b a := by
  cases e : cmp a b with
  | lt => exact Or.inl e
  | eq => exact Or.inr (Or.inl (eq_of_cmp_eq_FX ha hb e))
  | gt => exact Or.inr (Or.inr (lt_of_gtX ha hb e))

/-- `¬ a < b` なら `b ≤ a` -/
theorem le_of_not_ltX {a b : Tm} (ha : FXNF a) (hb : FXNF b) (h : ¬ Lt a b) : b = a ∨ Lt b a := by
  rcases triX ha hb with h' | h' | h'
  · exact absurd h' h
  · exact Or.inl h'.symm
  · exact Or.inr h'

/-- `cmp a b ≠ .gt` なら `a = b` か `a < b` -/
theorem le_of_ne_gtX {a b : Tm} (ha : FXNF a) (hb : FXNF b) (h : cmp a b ≠ .gt) : a = b ∨ Lt a b := by
  cases e : cmp a b with
  | lt => exact Or.inr e
  | eq => exact Or.inl (eq_of_cmp_eq_FX ha hb e)
  | gt => exact absurd e h

theorem ne_gt_of_le {a b : Tm} (h : a = b ∨ Lt a b) : cmp a b ≠ .gt := by
  rcases h with rfl | h
  · rw [cmp_self]; decide
  · unfold Lt at h; rw [h]; decide

/-! ### 部分項 -/

theorem FXNF.of_mem_subs : ∀ {t s : Tm}, FXNF t → s ∈ subs t → FXNF s
  | .zero, s, ht, h | .one, s, ht, h | .K _, s, ht, h => by
    simp only [subs, List.mem_singleton] at h
    rw [h]
    exact ht
  | .plus a b, s, ht, h => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    obtain ⟨ha, hb, -, -⟩ := ht.plus
    rcases h with h | h | h
    · rw [h]; exact ht
    · exact FXNF.of_mem_subs ha h
    · exact FXNF.of_mem_subs hb h
  | .Om a, s, ht, h => by
    simp only [subs, List.mem_cons] at h
    rcases h with h | h
    · rw [h]; exact ht
    · exact FXNF.of_mem_subs ht.om.1 h
  | .Xi _ a, s, ht, h => by
    simp only [subs, List.mem_cons] at h
    rcases h with h | h
    · rw [h]; exact ht
    · exact FXNF.of_mem_subs ht.xi.2.1 h
  | .Psi x p a, s, ht, h => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    obtain ⟨hx, c, hp, hc, -, ha, -, -⟩ := ht.psi
    subst hx hp
    rcases h with h | (h | h) | h
    · rw [h]; exact ht
    · simp only [subs, List.mem_singleton] at h
      rw [h]
      exact ⟨rfl, rfl⟩
    · exact FXNF.of_mem_subs hc h
    · exact FXNF.of_mem_subs ha h

theorem mem_subs_xi (n : Nat) (a : Tm) : a ∈ subs (.Xi n a) := by
  simp [subs, self_mem_subs]

/-! ### 底（同じ階の最小元） -/

theorem lt_of_isBotX {x y : Tm} (hl : lev x = lev y) (hx : isBot x = true) (hy : isBot y = false)
    (hpy : isPrincipal y = true) (hyF : FXNF y) : cmpP x y = .lt := by
  rw [cmpP.eq_def]
  simp only [hl, Nat.lt_irrefl, ↓reduceIte]
  cases x <;> cases y <;> simp_all [isBot, isPrincipal]
  exact hyF.om_ne_k

theorem not_lt_isBotX {x y : Tm} (hl : lev x = lev y) (hy : isBot y = true) (hx : FXNF x)
    (hyF : FXNF y) :
    cmpP x y ≠ .lt := by
  rw [cmpP.eq_def]
  simp only [hl, Nat.lt_irrefl, ↓reduceIte]
  cases x <;> cases y <;> simp_all [isBot]
  all_goals first
    | (split <;> simp)
    | (have := hyF.k; simp only [lev] at hl; omega)

theorem isBot_eqX {x y : Tm} (hl : lev x = lev y) (hx : isBot x = true) (hy : isBot y = true)
    (hxF : FXNF x) (hyF : FXNF y) : x = y := by
  cases x <;> cases y <;> simp_all [isBot, lev]
  · have := hyF.k; omega
  · have := hxF.k; omega

/-! ### `Ξ` を含む比較 -/

theorem lt_om_xi (a b : Tm) (n : Nat) (hl : lev a = n) :
    Lt (.Om a) (.Xi n b) ↔ Lt a (.Xi n b) := by
  rw [lt_principal_iff rfl rfl, cmpP_om_xi hl]
  rfl

theorem lt_xi_om {a b : Tm} {n : Nat} (hl : lev a = n) (ha : FXNF a) (hb : FXNF (.Xi n b)) :
    Lt (.Xi n b) (.Om a) ↔ Lt (.Xi n b) a := by
  rw [lt_principal_iff rfl rfl, cmpP_xi_om hl]
  constructor
  · intro h
    apply lt_of_gtX ha hb
    cases e : cmp a (Tm.Xi n b) <;> rw [e] at h <;> first | rfl | cases h
  · intro h
    unfold Lt at h
    rw [cmp_swap_FX hb ha, h]
    rfl

/-- 同じ階の `Ξ` どうしの比較（Lemma 4.14） -/
theorem lt_xi_xi_same {n : Nat} {α β : Tm} (hα : FXNF α) (hβ : FXNF β) (hne : α ≠ β) :
    Lt (.Xi n α) (.Xi n β) ↔
      (Lt α β ∧ inC α β (.Xi n β) = true) ∨ (Lt β α ∧ inC β α (.Xi n α) = false) := by
  rw [lt_principal_iff rfl rfl, cmpP_xi_xi, xiLtXi_eq]
  simp only [hne, ↓reduceIte]
  rw [ite_lt_gt_eq_lt]
  rcases triX hα hβ with h | h | h
  · have h' : cmp β α = .gt := by unfold Lt at h; rw [cmp_swap_FX hα hβ, h]; rfl
    unfold Lt at h
    simp [h, h', Lt]
  · exact absurd h hne
  · have h' : cmp α β = .gt := by unfold Lt at h; rw [cmp_swap_FX hβ hα, h]; rfl
    unfold Lt at h
    cases inC β α (Tm.Xi n α) <;> simp [h, h', Lt]

/-- 同じ階の `Ψ^0_{Ω_c}(α)` と `Ξ_n(β)` の比較（Prop. 4.21） -/
theorem lt_psi_xi {c α β : Tm} {n : Nat} (hl : lev c = n) :
    Lt (.Psi .zero (.Om c) α) (.Xi n β) ↔
      cmp c (.Xi n β) ≠ .gt ∨ (Lt β α ∧ inC β α (.Psi .zero (.Om c) α) = false) := by
  rw [lt_principal_iff rfl rfl, cmpP_psi_xi (pi := .Om c) hl, psiLtXi_eq]
  have e : cmp (Tm.Om c) (.Xi n β) = cmp c (.Xi n β) := by
    rw [cmp_principal rfl rfl, cmpP_om_xi hl]
  rw [e, ite_lt_gt_eq_lt]
  unfold Lt
  cases cmp c (Tm.Xi n β) <;> cases cmp β α <;> cases inC β α (Tm.Psi .zero (.Om c) α) <;> simp

theorem lt_xi_psi {c α β : Tm} {n : Nat} (hl : lev c = n) :
    Lt (.Xi n β) (.Psi .zero (.Om c) α) ↔ ¬ Lt (.Psi .zero (.Om c) α) (.Xi n β) := by
  rw [lt_principal_iff rfl rfl, lt_principal_iff rfl rfl, cmpP_xi_psi (pi := .Om c) hl,
    cmpP_psi_xi (pi := .Om c) hl]
  cases psiLtXi (Tm.Psi .zero (.Om c) α) (.Xi n β) <;> simp

/-- `Ψ_d(α) < Ψ_e(β)` なら `d ≤ e` -/
theorem le_of_lt_psi_psiX {d e α β : Tm} (hd : FXNF d) (he : FXNF e) (hl : lev d = lev e)
    (hpsi : FXNF (.Psi .zero (.Om d) α)) (hpsi' : FXNF (.Psi .zero (.Om e) β))
    (h : Lt (.Psi .zero (.Om d) α) (.Psi .zero (.Om e) β)) : d = e ∨ Lt d e := by
  rcases triX hd he with h' | h' | h'
  · exact Or.inr h'
  · exact Or.inl h'
  · exact absurd (lt_psi_psi_of_lt _ _ _ _ hl.symm h') (Lt.asymmX hpsi hpsi' h)

/-! ### 主要項の形 -/

theorem shape_FX {x : Tm} (hx : FXNF x) (hp : isPrincipal x = true) (hb : isBot x = false) :
    (∃ a, x = .Om a) ∨ (∃ n a, x = .Xi n a) ∨ (∃ c α, x = .Psi .zero (.Om c) α) := by
  cases x with
  | Om a => exact Or.inl ⟨a, rfl⟩
  | Xi n a => exact Or.inr (Or.inl ⟨n, a, rfl⟩)
  | Psi xi pi α =>
    obtain ⟨hxi, c, hpi, -⟩ := hx.psi
    subst hxi hpi
    exact Or.inr (Or.inr ⟨c, α, rfl⟩)
  | _ => simp_all [isPrincipal, isBot]

/-! ### 辞書式比較 -/

theorem eq_of_cmpP_eqX {x y : Tm} (hx : FXNF x) (hy : FXNF y) (hpx : isPrincipal x = true)
    (hpy : isPrincipal y = true) (h : cmpP x y = .eq) : x = y := by
  apply eq_of_cmp_eq_FX hx hy
  rw [cmp_principal hpx hpy, h]

/-- 主要項の列の辞書式比較の推移性（元が全て `S` に入るとき） -/
theorem lexTransX {S : List Tm} (hS : LinOn S) (hNF : ∀ s, s ∈ S → FXNF s) :
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
    · have := eq_of_cmpP_eqX (hNF y hy.1) (hNF z hz.1) hy.2 hz.2 e2
      subst this
      rw [cmpList_cons_cons_ne _ _ (by rw [e1]; decide), e1]
    · have := eq_of_cmpP_eqX (hNF x hx.1) (hNF y hy.1) hx.2 hy.2 e1
      subst this
      rw [cmpList_cons_cons_ne _ _ (by rw [e2]; decide), e2]
    · have := eq_of_cmpP_eqX (hNF x hx.1) (hNF y hy.1) hx.2 hy.2 e1
      subst this
      have := eq_of_cmpP_eqX (hNF x hx.1) (hNF z hz.1) hx.2 hz.2 e2
      subst this
      rw [cmpList_cons_cons_eq _ _ (cmpP_self x)]
      exact lexTransX hS hNF xs ys zs (fun w hw => h1 w (List.mem_cons_of_mem _ hw))
        (fun w hw => h2 w (List.mem_cons_of_mem _ hw)) (fun w hw => h3 w (List.mem_cons_of_mem _ hw))
        r1 r2

/-- 一般の項 `t` の切断性：主要項の組についての切断性 `hP` から -/
theorem cutGenX {S : List Tm} (hS : LinOn S) (hNF : ∀ s, s ∈ S → FXNF s)
    (hcl : ∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S)
    {t : Tm} (ht : FXNF t) (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S)
    {a b : Tm}
    (hP : isPrincipal t = true → ∀ q p, q ∈ summands b → p ∈ summands a →
      Lt q p → Lt p t → Lt q t)
    (ha : a ∈ S) (hb : b ∈ S) (h1 : Lt b a) (h2 : Lt a t) : Lt b t := by
  have hsa : ∀ x, x ∈ summands a → x ∈ S ∧ isPrincipal x = true := fun x hx =>
    ⟨hcl a ha x (mem_subs_of_mem_summands hx), (summands_FXNF a (hNF a ha) x hx).2⟩
  have hsb : ∀ x, x ∈ summands b → x ∈ S ∧ isPrincipal x = true := fun x hx =>
    ⟨hcl b hb x (mem_subs_of_mem_summands hx), (summands_FXNF b (hNF b hb) x hx).2⟩
  unfold Lt at h1 h2 ⊢
  rw [cmp_eq] at h1 h2 ⊢
  cases htp : isPrincipal t
  · cases t with
    | zero =>
      exfalso
      cases hs : summands a with
      | nil => rw [hs, summands, cmpList_nil_nil] at h2; cases h2
      | cons _ _ => rw [hs, summands, cmpList_cons_nil] at h2; cases h2
    | plus h r =>
      have hst : ∀ x, x ∈ summands (.plus h r) → x ∈ S ∧ isPrincipal x = true := by
        intro x hx
        refine ⟨hsub x (mem_subs_of_mem_summands hx) ?_, (summands_FXNF _ ht x hx).2⟩
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
      exact lexTransX hS hNF _ _ _ hsb hsa hst h1 h2
    | _ => simp [isPrincipal] at htp
  · rw [summands_principal' htp] at h2 ⊢
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
            exact hP htp q p (by rw [hsb']; exact List.mem_cons_self)
              (by rw [hsa']; exact List.mem_cons_self)
              ((lt_principal_iff hq.2 hp.2).mpr e) ((lt_principal_iff hp.2 htp).mpr hpt)
          · have := eq_of_cmpP_eqX (hNF q hq.1) (hNF p hp.1) hq.2 hp.2 e
            subst this
            exact hpt
        rw [cmpList_cons_cons_ne _ _ (by rw [hqt]; decide), hqt]

end RTKA
