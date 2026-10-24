import Compact.WF.FXGood

/-! 断片 `FX` の推移性の証明：新しい項 `t` による切断性の枠組みと、`t` が `Ω_e` などの場合。

`CutT S t`：`t` は `S` を切断する（`b < a < t`、`a, b ∈ S` なら `b < t`）。和の先頭の項に帰着させ、
主要項の組についての場合分けは、大きさの和についての帰納法の中で行う（`cut_of_principal`）。 -/

namespace RTKA

open Tm

/-! ### 和の道具 -/

theorem FXNF.plus_head {a b : Tm} (h : FXNF (.plus a b)) {h' : Tm} {rest : List Tm}
    (hs : summands b = h' :: rest) : cmp h' a ≠ .gt := by
  have hn := h.1
  simp only [isNF, Bool.and_eq_true] at hn
  have h2 := hn.2
  rw [hs] at h2
  simpa using h2

theorem lt_plus_leftX {a b : Tm} (h : FXNF (.plus a b)) : Lt a (.plus a b) := by
  obtain ⟨-, -, hap, hb0⟩ := h.plus
  unfold Lt
  rw [cmp_eq, summands_principal' hap, summands_plus, cmpList_cons_cons_eq _ _ (cmpP_self a)]
  cases hs : summands b with
  | nil => exact absurd hs (summands_ne_nil hb0)
  | cons _ _ => exact cmpList_nil_cons _ _

theorem lt_plus_rightX : ∀ {a b : Tm}, FXNF (.plus a b) → Lt b (.plus a b)
  | a, b, h => by
    obtain ⟨-, hb, hap, hb0⟩ := h.plus
    cases hs : summands b with
    | nil => exact absurd hs (summands_ne_nil hb0)
    | cons x xs =>
      have hxa := h.plus_head hs
      have hx := summands_FXNF b hb x (by rw [hs]; exact List.mem_cons_self)
      have hxa' : cmpP x a ≠ .gt := by rwa [← cmp_principal hx.2 hap]
      unfold Lt
      rw [cmp_eq, hs, summands_plus, hs]
      cases e : cmpP x a with
      | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]
      | gt => exact absurd e hxa'
      | eq =>
        rw [cmpList_cons_cons_eq _ _ e]
        have hxe : x = a := eq_of_cmpP_eqX hx.1 (summands_FXNF _ h a (by simp [summands])).1 hx.2 hap e
        subst hxe
        cases b with
        | zero => exact absurd rfl hb0
        | plus p q =>
          rw [summands_plus, List.cons.injEq] at hs
          obtain ⟨rfl, hq⟩ := hs
          have := lt_plus_rightX hb
          unfold Lt at this
          rw [cmp_eq, summands_plus] at this
          rwa [← hq]
        | _ =>
          simp only [summands, List.cons.injEq] at hs
          rw [← hs.2]
          exact cmpList_nil_cons _ _

/-- 先頭の項は和以下 -/
theorem head_leX {t h : Tm} {rest : List Tm} (ht : FXNF t) (hs : summands t = h :: rest) : Le h t := by
  cases t with
  | zero => simp [summands] at hs
  | plus a b =>
    rw [summands_plus, List.cons.injEq] at hs
    rw [← hs.1]
    exact Or.inr (lt_plus_leftX ht)
  | _ =>
    simp only [summands, List.cons.injEq] at hs
    rw [hs.1]
    exact Le.refl _

/-- 主要項 `t` より小さい和は、先頭の項も `t` より小さい -/
theorem cmpP_head_of_lt {w h t : Tm} {rest : List Tm} (hs : summands w = h :: rest)
    (htp : isPrincipal t = true) (hlt : Lt w t) : cmpP h t = .lt := by
  unfold Lt at hlt
  rw [cmp_eq, hs, summands_principal' htp] at hlt
  rcases cmpList_lt_cases hlt with e | ⟨_, e⟩
  · exact e
  · cases rest with
    | nil => rw [cmpList_nil_nil] at e; cases e
    | cons _ _ => rw [cmpList_cons_nil] at e; cases e

/-- `w < c` なら `w` の先頭の項も `c` より小さい -/
theorem head_lt_of_lt {w h c : Tm} {rest : List Tm} (hw : FXNF w) (hc : FXNF c)
    (hs : summands w = h :: rest) (hlt : Lt w c) : Lt h c := by
  have hh := summands_FXNF w hw h (by rw [hs]; exact List.mem_cons_self)
  cases hsc : summands c with
  | nil =>
    have : c = .zero := by cases c <;> simp_all [summands]
    subst this
    exact absurd hlt (not_lt_zero w)
  | cons k ks =>
    have hk := summands_FXNF c hc k (by rw [hsc]; exact List.mem_cons_self)
    unfold Lt at hlt
    rw [cmp_eq, hs, hsc] at hlt
    rcases cmpList_lt_cases hlt with e | ⟨e, e'⟩
    · exact lt_of_lt_head hsc ((lt_principal_iff hh.2 hk.2).mpr e) hk.2
    · have := eq_of_cmpP_eqX hh.1 hk.1 hh.2 hk.2 e
      subst this
      cases c with
      | zero => simp [summands] at hsc
      | plus a b =>
        rw [summands_plus, List.cons.injEq] at hsc
        rw [← hsc.1]
        exact lt_plus_leftX hc
      | _ =>
        simp only [summands, List.cons.injEq] at hsc
        rw [← hsc.2] at e'
        cases rest with
        | nil => rw [cmpList_nil_nil] at e'; cases e'
        | cons _ _ => rw [cmpList_cons_nil] at e'; cases e'

theorem not_lt_of_leX {a b : Tm} (ha : FXNF a) (hb : FXNF b) (h : Le a b) : ¬ Lt b a := by
  rcases h with rfl | h
  · exact Lt.irrefl _
  · exact Lt.asymmX ha hb h

/-! ### 切断性 -/

/-- `t` は `S` を切断する -/
def CutT (S : List Tm) (t : Tm) : Prop :=
  ∀ a b, a ∈ S → b ∈ S → Lt b a → Lt a t → Lt b t

/-- 主要項の組についての切断性から一般の切断性へ（大きさの和についての帰納法） -/
theorem cut_of_principal {S : List Tm} (G : GoodX S) {t : Tm} (ht : FXNF t)
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
      refine cutGenX G.lin G.nf G.cl ht hsub (fun htp q p hq hp => ?_) ha hb h1 h2
      exact hP (a.size + b.size) (fun a' b' ha' hb' hs' => ih a' b' ha' hb' (by omega)) htp q p
        (G.sub hb (mem_subs_of_mem_summands hq)) (G.sub ha (mem_subs_of_mem_summands hp))
        (summands_FXNF b (G.nf b hb) q hq).2 (summands_FXNF a (G.nf a ha) p hp).2
        (by have := size_le_of_mem_summands b q hq; have := size_le_of_mem_summands a p hp; omega)
  exact fun a b ha hb => key _ a b ha hb (Nat.le_refl _)

/-- 主要項の組の場合分けの前処理：階が下がる場合と底の場合を片付ける -/
theorem cut_reduce {t : Tm} (ht : FXNF t) (htp : isPrincipal t = true) (htb : isBot t = false)
    {q p : Tm} (hq : FXNF q) (hp : FXNF p) (hqp : isPrincipal q = true)
    (hpp : isPrincipal p = true) (h1 : Lt q p) (h2 : Lt p t)
    (core : lev q = lev t → lev p = lev t → isBot q = false → isBot p = false → Lt q t) :
    Lt q t := by
  have l1 := lev_le_of_ltX hq hp h1
  have l2 := lev_le_of_ltX hp ht h2
  by_cases hl : lev q < lev t
  · exact lt_of_lev_lt' hl
  have lq : lev q = lev t := by omega
  have lp : lev p = lev t := by omega
  cases hbq : isBot q
  · cases hbp : isBot p
    · exact core lq lp hbq hbp
    · exact absurd ((lt_principal_iff hqp hpp).mp h1) (not_lt_isBotX (by omega) hbp hq hp)
  · exact (lt_principal_iff hqp htp).mpr (lt_of_isBotX (by omega) hbq htb htp ht)

/-- 底（`1`・`K_n`）や `0` は切断する -/
theorem cut_bot {S : List Tm} (G : GoodX S) {t : Tm} (ht : FXNF t) (htb : isBot t = true ∨ t = .zero)
    (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S) : CutT S t := by
  refine cut_of_principal G ht hsub (fun _ _ htp q p hqS hpS hqp hpp _ h1 h2 => ?_)
  have hqF := G.nf q hqS
  have hpF := G.nf p hpS
  rcases htb with htb | rfl
  · have l1 := lev_le_of_ltX hqF hpF h1
    have l2 := lev_le_of_ltX hpF ht h2
    rcases Nat.lt_or_eq_of_le l2 with l2 | l2
    · exact lt_of_lev_lt' (by omega)
    · exact absurd ((lt_principal_iff hpp htp).mp h2) (not_lt_isBotX l2 htb hpF ht)
  · exact absurd h2 (not_lt_zero p)

/-! ### `t = Ω_e` -/

theorem cut_om {S : List Tm} (G : GoodX S) {e : Tm} (ht : FXNF (.Om e))
    (hsub : ∀ s, s ∈ subs (.Om e) → s ≠ .Om e → s ∈ S) : CutT S (.Om e) := by
  have heS : e ∈ S := hsub e (mem_subs_om e) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))
  have heF := ht.om.1
  refine cut_of_principal G ht hsub (fun _ _ _ q p hqS hpS hqp hpp _ h1 h2 => ?_)
  have hqF := G.nf q hqS
  have hpF := G.nf p hpS
  refine cut_reduce ht rfl rfl hqF hpF hqp hpp h1 h2 (fun lq lp bq bp => ?_)
  simp only [lev] at lq lp
  rcases shape_FX hpF hpp bp with ⟨x, rfl⟩ | ⟨n, f, rfl⟩ | ⟨d, β, rfl⟩ <;>
    rcases shape_FX hqF hqp bq with ⟨y, rfl⟩ | ⟨m, f', rfl⟩ | ⟨d', α, rfl⟩ <;>
    simp only [lev] at lq lp
  · -- `Ω_y < Ω_x < Ω_e`
    have hx := G.sub hpS (mem_subs_om x)
    have hy := G.sub hqS (mem_subs_om y)
    rw [lt_om_om x e lp] at h2
    rw [lt_om_om y x (lq.trans lp.symm)] at h1
    exact (lt_om_om y e lq).mpr (G.trans hy hx heS h1 h2)
  · -- `Ξ < Ω_x < Ω_e`
    have hx := G.sub hpS (mem_subs_om x)
    rw [lt_om_om x e lp] at h2
    rw [lt_xi_om (lp.trans lq.symm) (G.nf _ hx) hqF] at h1
    exact (lt_xi_om lq.symm heF hqF).mpr (G.trans hqS hx heS h1 h2)
  · -- `Ψ_{d'} < Ω_x < Ω_e`
    have hx := G.sub hpS (mem_subs_om x)
    have hd := G.sub hqS (mem_subs_psi_c _ d' α)
    rw [lt_om_om x e lp] at h2
    rw [lt_psi_om x d' α (lp.trans lq.symm)] at h1
    rw [lt_psi_om e d' α lq.symm]
    intro hed
    rcases le_of_not_ltX (G.nf _ hx) (G.nf _ hd) h1 with h | h
    · subst h; exact Lt.asymmX heF (G.nf _ hx) hed h2
    · exact Lt.asymmX heF (G.nf _ hx) (G.trans heS hd hx hed h) h2
  · -- `Ω_y < Ξ < Ω_e`
    have hy := G.sub hqS (mem_subs_om y)
    rw [lt_xi_om lp.symm heF hpF] at h2
    rw [lt_om_xi y f n (lq.trans lp.symm)] at h1
    exact (lt_om_om y e lq).mpr (G.trans hy hpS heS h1 h2)
  · -- `Ξ' < Ξ < Ω_e`
    rw [lt_xi_om lp.symm heF hpF] at h2
    exact (lt_xi_om lq.symm heF hqF).mpr (G.trans hqS hpS heS h1 h2)
  · -- `Ψ_{d'} < Ξ < Ω_e`
    have hd := G.sub hqS (mem_subs_psi_c _ d' α)
    rw [lt_xi_om lp.symm heF hpF] at h2
    rw [G.kl d' α n f hqS hpS (lq.trans lp.symm)] at h1
    rw [lt_psi_om e d' α lq.symm]
    intro hed
    rcases le_of_ne_gtX (G.nf _ hd) hpF h1 with h | h
    · subst h; exact Lt.asymmX heF hpF hed h2
    · exact Lt.asymmX heF hpF (G.trans heS hd hpS hed h) h2
  · -- `Ω_y < Ψ_d < Ω_e`
    have hy := G.sub hqS (mem_subs_om y)
    have hd := G.sub hpS (mem_subs_psi_c _ d β)
    rw [lt_psi_om e d β lp.symm] at h2
    rw [lt_om_psi y d β (lq.trans lp.symm)] at h1
    refine (lt_om_om y e lq).mpr ?_
    rcases le_of_not_ltX heF (G.nf _ hd) h2 with h | h
    · subst h; exact h1
    · exact G.trans hy hd heS h1 h
  · -- `Ξ < Ψ_d < Ω_e`
    have hd := G.sub hpS (mem_subs_psi_c _ d β)
    rw [lt_psi_om e d β lp.symm] at h2
    rw [G.xi_lt_psi hpS hqS (lp.trans lq.symm)] at h1
    refine (lt_xi_om lq.symm heF hqF).mpr ?_
    rcases le_of_not_ltX heF (G.nf _ hd) h2 with h | h
    · subst h; exact h1
    · exact G.trans hqS hd heS h1 h
  · -- `Ψ_{d'} < Ψ_d < Ω_e`
    have hd := G.sub hpS (mem_subs_psi_c _ d β)
    have hd' := G.sub hqS (mem_subs_psi_c _ d' α)
    rw [lt_psi_om e d β lp.symm] at h2
    rw [lt_psi_om e d' α lq.symm]
    intro hed
    rcases le_of_lt_psi_psiX (G.nf _ hd') (G.nf _ hd) (lq.trans lp.symm) hqF hpF h1 with h | h
    · subst h; exact h2 hed
    · exact h2 (G.trans heS hd' hd hed h)

end RTKA
