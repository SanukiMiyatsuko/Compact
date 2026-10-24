import Compact.WF.FWL0
import Compact.WF.FXStep

/-! 体系全体の順序の性質の証明：切断性の枠組みと、`S` の中での比較の道具。

* `lexTransY`・`cutGenY`・`cut_of_principalY`：主要項の組の切断性から一般の切断性へ（`FX` と同じ）。
* `S` の中の比較：`Ω` の不動点と `Ω_e`（`lt_OF_om`）、KL（`lt_OF_psiOm`）、`Ψ^0_{Ω_c}` と `Ω_e`。
* `cut_omY`：`t = Ω_e` の切断性。
* `antiOn_of`・`linOn_of_cutY`：`t` との反対称性と切断性から、`S ∪ {t}` の反対称性と推移性。 -/

namespace RTKA.W

open Tm

/-! ### 底と主要項の形 -/

theorem lt_of_isBotY {x y : Tm} (hl : lev x = lev y) (hx : isBot x = true) (hy : isBot y = false)
    (hpy : isPrincipal y = true) (hyF : WNF y) : cmpP x y = .lt := by
  rw [cmpP.eq_def]
  simp only [hl, Nat.lt_irrefl, ↓reduceIte]
  cases x <;> cases y <;> simp_all [isBot, isPrincipal]
  exact hyF.om_ne_k

theorem shape_FY {x : Tm} (hx : WNF x) (hp : isPrincipal x = true) (hb : isBot x = false) :
    (∃ a, x = .Om a) ∨ IsOF x ∨ (∃ c α, x = .Psi .zero (.Om c) α) := by
  cases x with
  | Om a => exact Or.inl ⟨a, rfl⟩
  | Xi n a => exact Or.inr (Or.inl (Or.inl ⟨n, a, rfl⟩))
  | Psi xi pi α =>
    rcases hx.shape with ⟨c, rfl, rfl⟩ | hsh
    · exact Or.inr (Or.inr ⟨c, α, rfl⟩)
    · exact Or.inr (Or.inl (IsOF.psi hx (notOm_of_shape hsh)))
  | _ => simp_all [isPrincipal, isBot]

namespace GoodY

variable {S : List Tm} (G : GoodY S)
include G

/-! ### `S` の中の比較 -/

theorem lt_OF_omS {X e : Tm} (hX : IsOF X) (hXS : X ∈ S) (heS : e ∈ S) :
    Lt X (.Om e) ↔ Lt X e := by
  rcases Nat.lt_trichotomy (lev e) (lev X) with hl | hl | hl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · intro h; have := lev_le_of_lt_gen h; exfalso; omega
  · rw [lt_principal_iff hX.principal rfl, cmpP_OF_om hX hl]
    unfold Lt
    rw [G.swap hXS heS]
    cases cmp X e <;> simp
  · exact ⟨fun _ => lt_of_lev_lt' hl, fun _ => lt_of_lev_lt' (by simp only [lev]; exact hl)⟩

theorem lt_om_iffS {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) : Lt (.Om a) (.Om b) ↔ Lt a b := by
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
    · intro h'; exact absurd (lt_of_lev_lt' h) (G.asymm ha hb h')

/-- `Ψ^0_{Ω_c}(β) < Ω_e` ⟺ `c ≤ e` -/
theorem lt_psi_omS {c β e : Tm} (hψ : Tm.Psi .zero (.Om c) β ∈ S) (heS : e ∈ S) :
    Lt (.Psi .zero (.Om c) β) (.Om e) ↔ Le c e := by
  have hcS := G.sub hψ (mem_subs_psi_c _ c β)
  rcases Nat.lt_trichotomy (lev e) (lev c) with hl | hl | hl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · rintro (rfl | h)
      · exact absurd hl (Nat.lt_irrefl _)
      · exact absurd (lev_le_of_lt_gen h) (by omega)
  · rw [lt_psi_om e c β hl]
    constructor
    · intro h; exact G.le_of_not_lt heS hcS h
    · intro h; exact G.not_lt_of_le hcS heS h
  · constructor
    · intro _; exact Or.inr (lt_of_lev_lt' hl)
    · intro _; exact lt_of_lev_lt' (by simp only [lev]; exact hl)

/-- KL：`Ω` の不動点 `X` について `X < Ψ^0_{Ω_c}(β)` ⟺ `X < c` -/
theorem lt_OF_psiOmS {X c β : Tm} (hX : IsOF X) (hXS : X ∈ S)
    (hψ : Tm.Psi .zero (.Om c) β ∈ S) :
    Lt X (.Psi .zero (.Om c) β) ↔ Lt X c := by
  have hcS := G.sub hψ (mem_subs_psi_c _ c β)
  have hσS : Tm.Om c ∈ S := G.sub hψ (by simp [subs])
  constructor
  · intro h
    exact (G.lt_OF_omS hX hXS hcS).mp (G.trans hXS hψ hσS h (lt_psi_om_self c β))
  · intro h
    exact G.trans hXS hcS hψ h (G.cx c β hψ)

/-- `Ψ^0_{Ω_d}(α) < Ψ^0_{Ω_e}(β)` なら `d ≤ e` -/
theorem le_of_lt_psi_psi {d e α β : Tm} (hx : Tm.Psi .zero (.Om d) α ∈ S)
    (hy : Tm.Psi .zero (.Om e) β ∈ S) (h : Lt (.Psi .zero (.Om d) α) (.Psi .zero (.Om e) β)) :
    Le d e := by
  have hd := G.sub hx (mem_subs_psi_c _ d α)
  have he := G.sub hy (mem_subs_psi_c _ e β)
  rcases G.tri hd he with h' | h' | h'
  · exact Or.inr h'
  · exact Or.inl h'
  · exact absurd (lt_psi_psiG h') (G.asymm hx hy h)

/-! ### 辞書式比較と切断性 -/

theorem lexTrans : ∀ l1 l2 l3 : List Tm,
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
    · have : Lt x z := G.trans hx.1 hy.1 hz.1 ((lt_principal_iff hx.2 hy.2).mpr e1)
        ((lt_principal_iff hy.2 hz.2).mpr e2)
      rw [lt_principal_iff hx.2 hz.2] at this
      rw [cmpList_cons_cons_ne _ _ (by rw [this]; decide), this]
    · have := G.eq_of_cmpP_eq hy.1 hz.1 hy.2 hz.2 e2
      subst this
      rw [cmpList_cons_cons_ne _ _ (by rw [e1]; decide), e1]
    · have := G.eq_of_cmpP_eq hx.1 hy.1 hx.2 hy.2 e1
      subst this
      rw [cmpList_cons_cons_ne _ _ (by rw [e2]; decide), e2]
    · have := G.eq_of_cmpP_eq hx.1 hy.1 hx.2 hy.2 e1
      subst this
      have := G.eq_of_cmpP_eq hx.1 hz.1 hx.2 hz.2 e2
      subst this
      rw [cmpList_cons_cons_eq _ _ (cmpP_self x)]
      exact lexTrans xs ys zs (fun w hw => h1 w (List.mem_cons_of_mem _ hw))
        (fun w hw => h2 w (List.mem_cons_of_mem _ hw)) (fun w hw => h3 w (List.mem_cons_of_mem _ hw))
        r1 r2

/-- 一般の項 `t` の切断性：主要項の組についての切断性 `hP` から -/
theorem cutGen {t : Tm} (ht : WNF t) (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S)
    {a b : Tm}
    (hP : isPrincipal t = true → ∀ q p, q ∈ summands b → p ∈ summands a →
      Lt q p → Lt p t → Lt q t)
    (ha : a ∈ S) (hb : b ∈ S) (h1 : Lt b a) (h2 : Lt a t) : Lt b t := by
  have hsa : ∀ x, x ∈ summands a → x ∈ S ∧ isPrincipal x = true := fun x hx =>
    ⟨G.sub ha (mem_subs_of_mem_summands hx), (summands_WNF a (G.nf a ha) x hx).2⟩
  have hsb : ∀ x, x ∈ summands b → x ∈ S ∧ isPrincipal x = true := fun x hx =>
    ⟨G.sub hb (mem_subs_of_mem_summands hx), (summands_WNF b (G.nf b hb) x hx).2⟩
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
        refine ⟨hsub x (mem_subs_of_mem_summands hx) ?_, (summands_WNF _ ht x hx).2⟩
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
      exact G.lexTrans _ _ _ hsb hsa hst h1 h2
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
          · have := G.eq_of_cmpP_eq hq.1 hp.1 hq.2 hp.2 e
            subst this
            exact hpt
        rw [cmpList_cons_cons_ne _ _ (by rw [hqt]; decide), hqt]

/-- 主要項の組についての切断性から一般の切断性へ（大きさの和についての帰納法） -/
theorem cut_of_principal {t : Tm} (ht : WNF t)
    (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S)
    (hP : ∀ N, (∀ a b, a ∈ S → b ∈ S → a.size + b.size < N → Lt b a → Lt a t → Lt b t) →
      isPrincipal t = true → ∀ q p, q ∈ S → p ∈ S → isPrincipal q = true →
        isPrincipal p = true → q.size + p.size ≤ N → Lt q p → Lt p t → Lt q t) :
    CutT S t := by
  have key : ∀ N, ∀ a b, a ∈ S → b ∈ S → a.size + b.size ≤ N → Lt b a → Lt a t → Lt b t := by
    intro N
    induction N with
    | zero =>
      intro a _ _ _ h
      have := Tm.size_pos a
      omega
    | succ N ih =>
      intro a b ha hb hs h1 h2
      refine G.cutGen ht hsub (fun htp q p hq hp => ?_) ha hb h1 h2
      exact hP (a.size + b.size) (fun a' b' ha' hb' hs' => ih a' b' ha' hb' (by omega)) htp q p
        (G.sub hb (mem_subs_of_mem_summands hq)) (G.sub ha (mem_subs_of_mem_summands hp))
        (summands_WNF b (G.nf b hb) q hq).2 (summands_WNF a (G.nf a ha) p hp).2
        (by have := size_le_of_mem_summands b q hq; have := size_le_of_mem_summands a p hp; omega)
  exact fun a b ha hb => key _ a b ha hb (Nat.le_refl _)

end GoodY

/-- 主要項の組の場合分けの前処理：階が下がる場合と底の場合を片付ける -/
theorem cut_reduceY {t : Tm} (ht : WNF t) (htp : isPrincipal t = true) (htb : isBot t = false)
    {q p : Tm} (hq : WNF q) (hp : WNF p) (hqp : isPrincipal q = true)
    (hpp : isPrincipal p = true) (h1 : Lt q p) (h2 : Lt p t)
    (core : lev q = lev t → lev p = lev t → isBot q = false → isBot p = false → Lt q t) :
    Lt q t := by
  have l1 := lev_le_of_lt_gen h1
  have l2 := lev_le_of_lt_gen h2
  by_cases hl : lev q < lev t
  · exact lt_of_lev_lt' hl
  have lq : lev q = lev t := by omega
  have lp : lev p = lev t := by omega
  cases hbq : isBot q
  · cases hbp : isBot p
    · exact core lq lp hbq hbp
    · exact absurd ((lt_principal_iff hqp hpp).mp h1) (not_lt_isBotY (by omega) hbp hq hp)
  · exact (lt_principal_iff hqp htp).mpr (lt_of_isBotY (by omega) hbq htb htp ht)

/-- 底（`1`・`K_n`）や `0` は切断する -/
theorem cut_botY {S : List Tm} (G : GoodY S) {t : Tm} (ht : WNF t)
    (htb : isBot t = true ∨ t = .zero)
    (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S) : CutT S t := by
  refine G.cut_of_principal ht hsub (fun _ _ htp q p hqS hpS hqp hpp _ h1 h2 => ?_)
  have hqF := G.nf q hqS
  have hpF := G.nf p hpS
  rcases htb with htb | rfl
  · have l1 := lev_le_of_lt_gen h1
    have l2 := lev_le_of_lt_gen h2
    rcases Nat.lt_or_eq_of_le l2 with l2 | l2
    · exact lt_of_lev_lt' (by omega)
    · exact absurd ((lt_principal_iff hpp htp).mp h2) (not_lt_isBotY l2 htb hpF ht)
  · exact absurd h2 (not_lt_zero p)

end RTKA.W
