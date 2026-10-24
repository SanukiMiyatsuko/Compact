import Compact.WF.FXStep

/-! 断片 `FX` の推移性の証明：新しい項が `t = Ψ_c(γ)` の場合。

`S` は部分項で閉じ、不変条件 `GoodX S` を満たし、`t ∉ S` で `t` の真の部分項は全て `S` に入る。

1. `below_kl`：`v < c` なら `v < t`、および `S` の `Ξ` について KL（`t < Ξ ⟺ c ≤ Ξ`）。同時の帰納法。
2. `cx`・`ic`・`notbelow`：`c < t`、`Ω_c ∈ C(g, t)`、`t` 未満の元は `Ω_c` 未満。
3. `ff`：`S` の `Ψ_c(δ)` と `t` の比較の前線による言い換え。
4. `lemA`：`γ` の前線のどれか以下の元は `t` 未満（補題 A）。
5. `k2`：`γ` の前線は全て `t` 未満。
6. `cut`：`t` は `S` を切断する。 -/

namespace RTKA

open Tm

/-- 新しい項 `t = Ψ_c(γ)` の文脈 -/
structure PsiCtx (S : List Tm) (c γ : Tm) : Prop where
  G : GoodX S
  ht : FXNF (.Psi .zero (.Om c) γ)
  hsub : ∀ s, s ∈ subs (Tm.Psi .zero (.Om c) γ) → s ≠ .Psi .zero (.Om c) γ → s ∈ S
  htS : Tm.Psi .zero (.Om c) γ ∉ S

namespace PsiCtx

variable {S : List Tm} {c γ : Tm} (P : PsiCtx S c γ)
include P

theorem OmS : Tm.Om c ∈ S :=
  P.hsub _ (by simp [subs]) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))

theorem cS : c ∈ S := P.G.sub P.OmS (mem_subs_om c)

theorem γS : γ ∈ S :=
  P.hsub _ (mem_subs_psi_a _ _ γ) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))

theorem cF : FXNF c := P.G.nf _ P.cS

theorem γF : FXNF γ := P.G.nf _ P.γS

theorem OmF : FXNF (.Om c) := P.G.nf _ P.OmS

theorem ne_of_mem {s : Tm} (hs : s ∈ S) : s ≠ .Psi .zero (.Om c) γ := fun e => P.htS (e ▸ hs)

/-- 底は `t` 未満 -/
theorem bot_lt {h : Tm} (hhF : FXNF h) (hb : isBot h = true) (hl : lev h ≤ lev c) :
    Lt h (.Psi .zero (.Om c) γ) := by
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
  · have hp : isPrincipal h = true := by cases h <;> simp_all [isBot, isPrincipal]
    exact (lt_principal_iff hp rfl).mpr (lt_of_isBotX hl hb rfl rfl P.ht)

/-- `c` 未満なら `t` 未満、と `S` の `Ξ` についての KL -/
theorem below_kl : ∀ N, ∀ v, v ∈ S → v.size ≤ N →
    (Lt v c → Lt v (.Psi .zero (.Om c) γ)) ∧
      (∀ n ξ, v = .Xi n ξ → lev c = n →
        (Lt (.Psi .zero (.Om c) γ) v ↔ cmp c v ≠ .gt)) := by
  intro N
  induction N with
  | zero => intro v _ h; exact absurd h (by have := Tm.size_pos v; omega)
  | succ N ih =>
    have klN : ∀ n ξ, Tm.Xi n ξ ∈ S → (Tm.Xi n ξ).size ≤ N + 1 → lev c = n →
        (Lt (.Psi .zero (.Om c) γ) (.Xi n ξ) ↔ cmp c (.Xi n ξ) ≠ .gt) := by
      intro n ξ hX hs hl
      have hXF := P.G.nf _ hX
      have hξS := P.G.sub hX (mem_subs_xi n ξ)
      rw [ff_kl hXF hl (P.G.argTrans hξS P.γS)]
      constructor
      · rintro (h | ⟨-, w, hw, hin⟩)
        · exact h
        · cases e : cmp c (Tm.Xi n ξ) with
          | lt => decide
          | eq => decide
          | gt =>
            exfalso
            have hwS := P.G.sub hξS (fr_spec hw).1
            have hwX := P.G.k2x n ξ hX w hw
            have hXc : Lt (.Xi n ξ) c := lt_of_gtX P.cF hXF e
            have hwc := P.G.trans hwS hX P.cS hwX hXc
            have hsz := size_le_of_mem_subs (fr_spec hw).1
            have hwt := (ih w hwS (by simp only [Tm.size] at hs; omega)).1 hwc
            rw [inC_of_lt_node (fr_node hw) hwt] at hin
            cases hin
      · exact Or.inl
    intro v hvS hs
    refine ⟨fun hvc => ?_, fun n ξ hv hl => by subst hv; exact klN n ξ hvS hs hl⟩
    have hvF := P.G.nf _ hvS
    cases hsv : summands v with
    | nil =>
      have : v = .zero := by cases v <;> simp_all [summands]
      subst this
      exact zero_lt (by intro e; cases e)
    | cons h rest =>
      have hmem : h ∈ summands v := by rw [hsv]; exact List.mem_cons_self
      have hhS := P.G.sub hvS (mem_subs_of_mem_summands hmem)
      obtain ⟨hhF, hhp⟩ := summands_FXNF v hvF h hmem
      have hhs := size_le_of_mem_summands v h hmem
      have hhc : Lt h c := head_lt_of_lt hvF P.cF hsv hvc
      have hht : Lt h (.Psi .zero (.Om c) γ) := by
        have hl := lev_le_of_ltX hhF P.cF hhc
        rcases Nat.lt_or_eq_of_le hl with hl | hl
        · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
        cases hb : isBot h
        · rcases shape_FX hhF hhp hb with ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨d, δ, rfl⟩
          · have hx := P.G.sub hhS (mem_subs_om x)
            exact (lt_om_psi x c γ hl).mpr (P.G.trans hx hhS P.cS hhF.om.2.2 hhc)
          · simp only [lev] at hl
            have hcX : cmp c (.Xi m f) = .gt := by
              unfold Lt at hhc
              rw [cmp_swap_FX hhF P.cF, hhc]
              rfl
            have hn : ¬ Lt (.Psi .zero (.Om c) γ) (.Xi m f) := fun h' =>
              (klN m f hhS (by omega) hl.symm).mp h' (by rw [hcX])
            rcases triX hhF P.ht with h' | h' | h'
            · exact h'
            · exact absurd h' (P.ne_of_mem hhS)
            · exact absurd h' hn
          · have hd := P.G.sub hhS (mem_subs_psi_c _ d δ)
            exact lt_psi_psi_of_lt d c δ γ hl
              (P.G.trans hd hhS P.cS (P.G.cx d δ hhS) hhc)
        · exact P.bot_lt hhF hb (Nat.le_of_eq hl)
      exact lt_of_head_lt rfl hsv ((lt_principal_iff hhp rfl).mp hht)

theorem below {v : Tm} (hv : v ∈ S) (h : Lt v c) : Lt v (.Psi .zero (.Om c) γ) :=
  (P.below_kl _ v hv (Nat.le_refl _)).1 h

theorem kl {n : Nat} {ξ : Tm} (hX : Tm.Xi n ξ ∈ S) (hl : lev c = n) :
    Lt (.Psi .zero (.Om c) γ) (.Xi n ξ) ↔ cmp c (.Xi n ξ) ≠ .gt :=
  (P.below_kl _ _ hX (Nat.le_refl _)).2 n ξ rfl hl

/-- `S` の `Ξ` が `t` 未満なら `c` 未満 -/
theorem xi_lt_c {n : Nat} {ξ : Tm} (hX : Tm.Xi n ξ ∈ S) (hl : lev c = n)
    (h : Lt (.Xi n ξ) (.Psi .zero (.Om c) γ)) : Lt (.Xi n ξ) c := by
  have hXF := P.G.nf _ hX
  have hn : ¬ (cmp c (.Xi n ξ) ≠ .gt) := fun h' => Lt.asymmX hXF P.ht h ((P.kl hX hl).mpr h')
  cases e : cmp c (Tm.Xi n ξ) with
  | gt => exact lt_of_gtX P.cF hXF e
  | lt => exact absurd (by rw [e]; decide) hn
  | eq => exact absurd (by rw [e]; decide) hn

/-- CX：`c < t` -/
theorem cx : Lt c (.Psi .zero (.Om c) γ) := by
  obtain ⟨-, c', hc', -, hs, -⟩ := P.ht.psi
  cases hc'
  have hcF := P.cF
  cases c with
  | one => exact P.bot_lt hcF rfl (Nat.le_refl _)
  | plus a b =>
    obtain ⟨-, -, hap, -⟩ := hcF.plus
    have haS := P.G.sub P.cS (show a ∈ subs (.plus a b) by simp [subs, self_mem_subs])
    have := P.below haS (lt_plus_leftX hcF)
    exact lt_of_head_lt rfl (summands_plus a b) ((lt_principal_iff hap rfl).mp this)
  | _ => simp [isSucc, summands] at hs

/-- IC：`Ω_c ∈ C(g, t)` -/
theorem ic (g : Tm) : inC (.Om c) g (.Psi .zero (.Om c) γ) = true := by
  have key : ∀ x, x ∈ S → (Lt x c ∨ x = c) → inC x g (.Psi .zero (.Om c) γ) = true := by
    intro x
    induction x with
    | zero => intros; exact inC_zero _ _
    | one => intros; exact inC_one _ _
    | K n => intros; exact inC_K n _ _
    | plus a b iha ihb =>
      intro hx hxc
      have hxF := P.G.nf _ hx
      have ha := P.G.sub hx (show a ∈ subs (.plus a b) by simp [subs, self_mem_subs])
      have hb := P.G.sub hx (show b ∈ subs (.plus a b) by simp [subs, self_mem_subs])
      have hxc' : ∀ y, y ∈ S → Lt y (.plus a b) → Lt y c := fun y hy h => by
        rcases hxc with hxc | hxc
        · exact P.G.trans hy hx P.cS h hxc
        · rw [← hxc]; exact h
      rw [inC_plus, iha ha (Or.inl (hxc' a ha (lt_plus_leftX hxF))),
        ihb hb (Or.inl (hxc' b hb (lt_plus_rightX hxF)))]
      rfl
    | Om y ihy =>
      intro hx hxc
      have hxF := P.G.nf _ hx
      have hy := P.G.sub hx (mem_subs_om y)
      rw [inC_om]
      refine ihy hy (Or.inl ?_)
      rcases hxc with hxc | hxc
      · exact P.G.trans hy hx P.cS hxF.om.2.2 hxc
      · rw [← hxc]; exact hxF.om.2.2
    | Xi m f _ =>
      intro hx hxc
      rcases hxc with hxc | hxc
      · exact inC_xi_iff.mpr (Or.inl (P.below hx hxc))
      · obtain ⟨-, c', hc', -, hs, -⟩ := P.ht.psi
        cases hc'
        rw [← hxc] at hs
        simp [isSucc, summands] at hs
    | Psi s p a _ _ _ =>
      intro hx hxc
      rcases hxc with hxc | hxc
      · exact inC_psi_iff.mpr (Or.inl (P.below hx hxc))
      · obtain ⟨-, c', hc', -, hs, -⟩ := P.ht.psi
        cases hc'
        rw [← hxc] at hs
        simp [isSucc, summands] at hs
  rw [inC_om]
  exact key c P.cS (Or.inr rfl)

/-- `t` 未満の `S` の元は `Ω_c` 未満 -/
theorem notbelow {w : Tm} (hw : w ∈ S) (hlt : Lt w (.Psi .zero (.Om c) γ)) : Lt w (.Om c) := by
  have hwF := P.G.nf _ hw
  cases hsw : summands w with
  | nil =>
    have : w = .zero := by cases w <;> simp_all [summands]
    subst this
    exact zero_lt (by intro e; cases e)
  | cons h rest =>
    have hmem : h ∈ summands w := by rw [hsw]; exact List.mem_cons_self
    have hhS := P.G.sub hw (mem_subs_of_mem_summands hmem)
    obtain ⟨hhF, hhp⟩ := summands_FXNF w hwF h hmem
    have hht : Lt h (.Psi .zero (.Om c) γ) :=
      (lt_principal_iff hhp rfl).mpr (cmpP_head_of_lt hsw rfl hlt)
    have hhO : Lt h (.Om c) := by
      have hl := lev_le_of_ltX hhF P.ht hht
      simp only [lev] at hl
      rcases Nat.lt_or_eq_of_le hl with hl | hl
      · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
      cases hb : isBot h
      · rcases shape_FX hhF hhp hb with ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨d, δ, rfl⟩
        · exact (lt_om_om x c hl).mpr ((lt_om_psi x c γ hl).mp hht)
        · simp only [lev] at hl
          exact (lt_xi_om hl.symm P.cF hhF).mpr (P.xi_lt_c hhS hl.symm hht)
        · simp only [lev] at hl
          have hdS := P.G.sub hhS (mem_subs_psi_c _ d δ)
          refine (lt_psi_om c d δ hl.symm).mpr ?_
          rcases le_of_lt_psi_psiX (P.G.nf _ hdS) P.cF hl hhF P.ht hht with e | e
          · subst e; exact Lt.irrefl _
          · exact Lt.asymmX (P.G.nf _ hdS) P.cF e
      · exact (lt_principal_iff hhp rfl).mpr (lt_of_isBotX hl hb rfl rfl P.OmF)
    exact lt_of_head_lt rfl hsw ((lt_principal_iff hhp rfl).mp hhO)

/-- `S` の `Ψ_c(δ)` と `t` の比較の前線による言い換え -/
theorem ff {δ : Tm} (hψ : Tm.Psi .zero (.Om c) δ ∈ S) :
    Lt (.Psi .zero (.Om c) δ) (.Psi .zero (.Om c) γ) ↔
      (Lt δ γ ∧ ∀ w, w ∈ fr (.Om c) δ → Lt w (.Psi .zero (.Om c) γ)) ∨
        (Lt γ δ ∧ ∃ w, w ∈ fr (.Om c) γ ∧ ¬ Lt w (.Psi .zero (.Om c) δ)) := by
  have hδS := P.G.sub hψ (mem_subs_psi_a _ _ δ)
  have hne : δ ≠ γ := fun e => P.ne_of_mem hψ (by rw [e])
  exact RTKA.ff_psi (P.G.nf _ hψ) P.ht hne (fun g => P.G.ic c δ g hψ) P.ic
    (fun w hw h h' => h (P.notbelow (P.G.sub hδS hw) h'))
    (fun w hw h h' => h (P.G.trans (P.G.sub P.γS hw) hψ P.OmS h' (lt_psi_om_self c δ)))
    (P.G.argTrans hδS P.γS) (P.G.argTrans P.γS hδS)

/-- 補題 A：`γ` の前線のどれか以下の `S` の元は `t` 未満 -/
theorem lemA_aux : ∀ N, ∀ v, v ∈ S → v.size ≤ N →
    (∃ w, w ∈ fr (.Om c) γ ∧ Le v w) → Lt v (.Psi .zero (.Om c) γ) := by
  intro N
  induction N with
  | zero => intro v _ h; exact absurd h (by have := Tm.size_pos v; omega)
  | succ N ih =>
    intro v hvS hs ⟨w, hw, hvw⟩
    have hvF := P.G.nf _ hvS
    have hwS := P.G.sub P.γS (fr_spec hw).1
    cases hsv : summands v with
    | nil =>
      have : v = .zero := by cases v <;> simp_all [summands]
      subst this
      exact zero_lt (by intro e; cases e)
    | cons h rest =>
      have hmem : h ∈ summands v := by rw [hsv]; exact List.mem_cons_self
      have hhS := P.G.sub hvS (mem_subs_of_mem_summands hmem)
      obtain ⟨hhF, hhp⟩ := summands_FXNF v hvF h hmem
      have hhs := size_le_of_mem_summands v h hmem
      have hhw : Le h w := P.G.le_trans hhS hvS hwS (head_leX hvF hsv) hvw
      have hhO : Lt h (.Om c) := P.G.lt_of_le_of_lt hhS hwS P.OmS hhw (fr_spec hw).2
      have hht : Lt h (.Psi .zero (.Om c) γ) := by
        have hl := lev_le_of_ltX hhF P.OmF hhO
        simp only [lev] at hl
        rcases Nat.lt_or_eq_of_le hl with hl | hl
        · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
        cases hb : isBot h
        · rcases shape_FX hhF hhp hb with ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨d, δ, rfl⟩
          · exact (lt_om_psi x c γ hl).mpr ((lt_om_om x c hl).mp hhO)
          · simp only [lev] at hl
            exact P.below hhS ((lt_xi_om hl.symm P.cF hhF).mp hhO)
          · simp only [lev] at hl
            have hdS := P.G.sub hhS (mem_subs_psi_c _ d δ)
            have hδS := P.G.sub hhS (mem_subs_psi_a _ _ δ)
            have hcd := (lt_psi_om c d δ hl.symm).mp hhO
            rcases le_of_not_ltX P.cF (P.G.nf _ hdS) hcd with e | e
            · subst e
              refine (P.ff hhS).mpr ?_
              have hne : δ ≠ γ := fun e => P.ne_of_mem hhS (by rw [e])
              rcases triX (P.G.nf _ hδS) P.γF with h' | h' | h'
              · refine Or.inl ⟨h', fun u hu => ?_⟩
                have huS := P.G.sub hδS (fr_spec hu).1
                have := size_le_of_mem_subs (fr_spec hu).1
                exact ih u huS (by simp only [Tm.size] at hhs; omega)
                  ⟨w, hw, Or.inr (P.G.lt_of_lt_of_le huS hhS hwS (P.G.k2 d δ hhS u hu) hhw)⟩
              · exact absurd h' hne
              · exact Or.inr ⟨h', w, hw, not_lt_of_leX hhF (P.G.nf _ hwS) hhw⟩
            · exact lt_psi_psi_of_lt d c δ γ hl e
        · exact P.bot_lt hhF hb (Nat.le_of_eq hl)
      exact lt_of_head_lt rfl hsv ((lt_principal_iff hhp rfl).mp hht)

theorem lemA {v : Tm} (hv : v ∈ S) (h : ∃ w, w ∈ fr (.Om c) γ ∧ Le v w) :
    Lt v (.Psi .zero (.Om c) γ) :=
  P.lemA_aux _ v hv (Nat.le_refl _) h

/-- K2：`γ` の前線は全て `t` 未満 -/
theorem k2 : ∀ w, w ∈ fr (.Om c) γ → Lt w (.Psi .zero (.Om c) γ) := fun w hw =>
  P.lemA (P.G.sub P.γS (fr_spec hw).1) ⟨w, hw, Le.refl _⟩

/-- `t = Ψ_c(γ)` は `S` を切断する -/
theorem cut : CutT S (.Psi .zero (.Om c) γ) := by
  have G := P.G
  refine cut_of_principal G P.ht P.hsub (fun N ih _ q p hqS hpS hqp hpp hN h1 h2 => ?_)
  have hqF := G.nf q hqS
  have hpF := G.nf p hpS
  refine cut_reduce P.ht rfl rfl hqF hpF hqp hpp h1 h2 (fun lq lp bq bp => ?_)
  simp only [lev] at lq lp
  -- `q` の鍵が `c` 未満なら `q < t`
  have viaC : ∀ d α, Tm.Psi .zero (.Om d) α ∈ S → lev d = lev c → Lt d c →
      Lt (.Psi .zero (.Om d) α) (.Psi .zero (.Om c) γ) := fun d α _ hl h =>
    lt_psi_psi_of_lt d c α γ hl h
  rcases shape_FX hpF hpp bp with ⟨x, rfl⟩ | ⟨n, f, rfl⟩ | ⟨d, δ, rfl⟩ <;>
    simp only [lev] at lp
  · -- `p = Ω_x`：`x < c`
    have hx := G.sub hpS (mem_subs_om x)
    have hxc := (lt_om_psi x c γ lp).mp h2
    rcases shape_FX hqF hqp bq with ⟨y, rfl⟩ | ⟨m, f', rfl⟩ | ⟨d', α, rfl⟩ <;>
      simp only [lev] at lq
    · have hy := G.sub hqS (mem_subs_om y)
      exact (lt_om_psi y c γ lq).mpr (G.trans hy hx P.cS ((lt_om_om y x (lq.trans lp.symm)).mp h1) hxc)
    · exact P.below hqS (G.trans hqS hx P.cS
        ((lt_xi_om (lp.trans lq.symm) (G.nf _ hx) hqF).mp h1) hxc)
    · have hd := G.sub hqS (mem_subs_psi_c _ d' α)
      refine viaC d' α hqS lq ?_
      rcases le_of_not_ltX (G.nf _ hx) (G.nf _ hd) ((lt_psi_om x d' α (lp.trans lq.symm)).mp h1)
        with e | e
      · rw [e]; exact hxc
      · exact G.trans hd hx P.cS e hxc
  · -- `p = Ξ`：`Ξ < c`
    have hXc := P.xi_lt_c hpS lp.symm h2
    rcases shape_FX hqF hqp bq with ⟨y, rfl⟩ | ⟨m, f', rfl⟩ | ⟨d', α, rfl⟩ <;>
      simp only [lev] at lq
    · have hy := G.sub hqS (mem_subs_om y)
      exact (lt_om_psi y c γ lq).mpr
        (G.trans hy hpS P.cS ((lt_om_xi y f n (lq.trans lp.symm)).mp h1) hXc)
    · exact P.below hqS (G.trans hqS hpS P.cS h1 hXc)
    · have hd := G.sub hqS (mem_subs_psi_c _ d' α)
      refine viaC d' α hqS lq ?_
      rcases le_of_ne_gtX (G.nf _ hd) hpF ((G.kl d' α n f hqS hpS (lq.trans lp.symm)).mp h1) with e | e
      · rw [e]; exact hXc
      · exact G.trans hd hpS P.cS e hXc
  · -- `p = Ψ_d(δ)`：`d ≤ c`
    have hdS := G.sub hpS (mem_subs_psi_c _ d δ)
    have hδS := G.sub hpS (mem_subs_psi_a _ _ δ)
    have hdc := le_of_lt_psi_psiX (G.nf _ hdS) P.cF lp hpF P.ht h2
    rcases shape_FX hqF hqp bq with ⟨y, rfl⟩ | ⟨m, f', rfl⟩ | ⟨d', α, rfl⟩ <;>
      simp only [lev] at lq
    · have hy := G.sub hqS (mem_subs_om y)
      have hyd := (lt_om_psi y d δ (lq.trans lp.symm)).mp h1
      refine (lt_om_psi y c γ lq).mpr ?_
      rcases hdc with e | e
      · rw [← e]; exact hyd
      · exact G.trans hy hdS P.cS hyd e
    · have hXd := (G.xi_lt_psi hpS hqS (lp.trans lq.symm)).mp h1
      refine P.below hqS ?_
      rcases hdc with e | e
      · rw [← e]; exact hXd
      · exact G.trans hqS hdS P.cS hXd e
    · have hd'S := G.sub hqS (mem_subs_psi_c _ d' α)
      have hαS := G.sub hqS (mem_subs_psi_a _ _ α)
      have hd'd := le_of_lt_psi_psiX (G.nf _ hd'S) (G.nf _ hdS) (lq.trans lp.symm) hqF hpF h1
      rcases hdc with e | e
      · subst e
        rcases hd'd with e' | e'
        · subst e'
          -- 同じ区間の `Ψ_c(α) < Ψ_c(δ) < t`
          have hαδ : α ≠ δ := fun e => by subst e; exact Lt.irrefl _ h1
          rcases (P.ff hpS).mp h2 with ⟨hδγ, hfr⟩ | ⟨hγδ, w, hw, hwn⟩
          · rcases (G.ff_psi hqS hpS hαδ).mp h1 with ⟨hαδ', hfrα⟩ | ⟨-, w', hw', hw'n⟩
            · refine (P.ff hqS).mpr (Or.inl ⟨G.trans hαS hδS P.γS hαδ' hδγ, fun u hu => ?_⟩)
              have huS := G.sub hαS (fr_spec hu).1
              have := size_le_of_mem_subs (fr_spec hu).1
              exact ih _ u hpS huS (by simp only [Tm.size] at hN ⊢; omega) (hfrα u hu) h2
            · have hw'S := G.sub hδS (fr_spec hw').1
              have hw't := hfr w' hw'
              rcases le_of_not_ltX (G.nf _ hw'S) hqF hw'n with e | e
              · rw [e]; exact hw't
              · have := size_le_of_mem_subs (fr_spec hw').1
                exact ih w' _ hw'S hqS (by simp only [Tm.size] at hN ⊢; omega) e hw't
          · have hwS := G.sub P.γS (fr_spec hw).1
            have hpw := le_of_not_ltX (G.nf _ hwS) hpF hwn
            have hqw := G.lt_of_lt_of_le hqS hpS hwS h1 hpw
            have hne : α ≠ γ := fun e => P.ne_of_mem hqS (by rw [e])
            rcases triX (G.nf _ hαS) P.γF with h' | h' | h'
            · refine (P.ff hqS).mpr (Or.inl ⟨h', fun u hu => ?_⟩)
              have huS := G.sub hαS (fr_spec hu).1
              exact P.lemA huS ⟨w, hw, Or.inr (G.trans huS hqS hwS (G.k2 _ α hqS u hu) hqw)⟩
            · exact absurd h' hne
            · exact (P.ff hqS).mpr (Or.inr ⟨h', w, hw, Lt.asymmX hqF (G.nf _ hwS) hqw⟩)
        · exact viaC d' α hqS lq e'
      · refine viaC d' α hqS lq ?_
        rcases hd'd with e' | e'
        · rw [e']; exact e
        · exact G.trans hd'S hdS P.cS e' e

end PsiCtx

end RTKA
