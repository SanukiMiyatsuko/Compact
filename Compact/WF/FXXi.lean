import Compact.WF.FXPsi

/-! 断片 `FX` の推移性の証明：新しい項が `t = Ξ_n(γ)` の場合。

`Ξ_n(γ)` は `Ω` の不動点なので、`Ω_a < t ⟺ a < t` のように比較が `t` 自身に戻ってくる。
この自己参照は補題 A で断ち切る。

1. `lemA`：`γ` の前線（`K_n` について）のどれか以下の `S` の元は `t` 未満。大きさの帰納法。
2. `kl`：`S` の `Ψ_c(β)` について `Ψ_c(β) < t ⟺ c ≤ t`。`c` が前線以下になることを補題 A に渡す。
3. `k2x`：`γ` の前線は全て `t` 未満。
4. `cut`：`t` は `S` を切断する。 -/

namespace RTKA

open Tm

/-- 新しい項 `t = Ξ_n(γ)` の文脈 -/
structure XiCtx (S : List Tm) (n : Nat) (γ : Tm) : Prop where
  G : GoodX S
  ht : FXNF (.Xi n γ)
  hsub : ∀ s, s ∈ subs (Tm.Xi n γ) → s ≠ .Xi n γ → s ∈ S
  htS : Tm.Xi n γ ∉ S

namespace XiCtx

variable {S : List Tm} {n : Nat} {γ : Tm} (P : XiCtx S n γ)
include P

theorem γS : γ ∈ S :=
  P.hsub _ (mem_subs_xi n γ) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))

theorem γF : FXNF γ := P.G.nf _ P.γS

theorem hn : 1 ≤ n := P.ht.xi.1

theorem ne_of_mem {s : Tm} (hs : s ∈ S) : s ≠ .Xi n γ := fun e => P.htS (e ▸ hs)

theorem bot_lt {h : Tm} (hhF : FXNF h) (hb : isBot h = true) (hl : lev h ≤ n) :
    Lt h (.Xi n γ) := by
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
  · have hp : isPrincipal h = true := by cases h <;> simp_all [isBot, isPrincipal]
    exact (lt_principal_iff hp rfl).mpr (lt_of_isBotX hl hb rfl rfl P.ht)

/-- `S` の `Ξ_n(f)` と `t` の比較の前線による言い換え -/
theorem ff {f : Tm} (hX : Tm.Xi n f ∈ S) :
    Lt (.Xi n f) (.Xi n γ) ↔
      (Lt f γ ∧ ∀ w, w ∈ fr (.K n) f → Lt w (.Xi n γ)) ∨
        (Lt γ f ∧ ∃ w, w ∈ fr (.K n) γ ∧ ¬ Lt w (.Xi n f)) := by
  have hfS := P.G.sub hX (mem_subs_xi n f)
  have hne : f ≠ γ := fun e => P.ne_of_mem hX (by rw [e])
  exact RTKA.ff_xi (P.G.nf _ hX) P.ht hne (P.G.argTrans hfS P.γS) (P.G.argTrans P.γS hfS)

/-- 補題 A：`γ` の前線のどれか以下の `S` の元は `t` 未満 -/
theorem lemA_aux : ∀ N, ∀ v, v ∈ S → v.size ≤ N →
    (∃ w, w ∈ fr (.K n) γ ∧ Le v w) → Lt v (.Xi n γ) := by
  intro N
  induction N with
  | zero => intro v _ h; exact absurd h (by have := Tm.size_pos v; omega)
  | succ N ih =>
    intro v hvS hs ⟨w, hw, hvw⟩
    have hvF := P.G.nf _ hvS
    have hwS := P.G.sub P.γS (fr_spec hw).1
    have hwF := P.G.nf _ hwS
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
      have hlw : lev h ≤ n := by
        have := lev_le_of_lt_K P.hn hwF (fr_spec hw).2
        rcases hhw with e | e
        · rw [e]; exact this
        · exact Nat.le_trans (lev_le_of_ltX hhF hwF e) this
      have hht : Lt h (.Xi n γ) := by
        rcases Nat.lt_or_eq_of_le hlw with hl | hl
        · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
        cases hb : isBot h
        · rcases shape_FX hhF hhp hb with ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨d, δ, rfl⟩
          · simp only [lev] at hl
            have hx := P.G.sub hhS (mem_subs_om x)
            have := size_le_of_mem_subs (mem_subs_om x)
            have hxt := ih x hx (by simp only [Tm.size] at hhs this ⊢; omega)
              ⟨w, hw, Or.inr (P.G.lt_of_lt_of_le hx hhS hwS hhF.om.2.2 hhw)⟩
            exact (lt_om_xi x γ n hl).mpr hxt
          · simp only [lev] at hl
            subst hl
            have hfS := P.G.sub hhS (mem_subs_xi m f)
            have hne : f ≠ γ := fun e => P.ne_of_mem hhS (by rw [e])
            refine (P.ff hhS).mpr ?_
            rcases triX (P.G.nf _ hfS) P.γF with h' | h' | h'
            · refine Or.inl ⟨h', fun u hu => ?_⟩
              have huS := P.G.sub hfS (fr_spec hu).1
              have := size_le_of_mem_subs (fr_spec hu).1
              exact ih u huS (by simp only [Tm.size] at hhs; omega)
                ⟨w, hw, Or.inr (P.G.lt_of_lt_of_le huS hhS hwS (P.G.k2x m f hhS u hu) hhw)⟩
            · exact absurd h' hne
            · exact Or.inr ⟨h', w, hw, not_lt_of_leX hhF hwF hhw⟩
          · simp only [lev] at hl
            have hd := P.G.sub hhS (mem_subs_psi_c _ d δ)
            have := size_le_of_mem_subs (mem_subs_psi_c .zero d δ)
            have hdt := ih d hd (by simp only [Tm.size] at hhs this ⊢; omega)
              ⟨w, hw, Or.inr (P.G.lt_of_lt_of_le hd hhS hwS (P.G.cx d δ hhS) hhw)⟩
            exact (lt_psi_xi hl).mpr (Or.inl (ne_gt_of_le (Or.inr hdt)))
        · exact P.bot_lt hhF hb (Nat.le_of_eq hl)
      exact lt_of_head_lt rfl hsv ((lt_principal_iff hhp rfl).mp hht)

theorem lemA {v : Tm} (hv : v ∈ S) (h : ∃ w, w ∈ fr (.K n) γ ∧ Le v w) : Lt v (.Xi n γ) :=
  P.lemA_aux _ v hv (Nat.le_refl _) h

/-- KL：`S` の `Ψ_c(β)` について `Ψ_c(β) < t ⟺ c ≤ t` -/
theorem kl {c β : Tm} (hψ : Tm.Psi .zero (.Om c) β ∈ S) (hl : lev c = n) :
    Lt (.Psi .zero (.Om c) β) (.Xi n γ) ↔ cmp c (.Xi n γ) ≠ .gt := by
  have hβS := P.G.sub hψ (mem_subs_psi_a _ _ β)
  have hcS := P.G.sub hψ (mem_subs_psi_c _ c β)
  rw [ff_kl P.ht hl (P.G.argTrans P.γS hβS)]
  constructor
  · rintro (h | ⟨-, w, hw, hin⟩)
    · exact h
    · have hwS := P.G.sub P.γS (fr_spec hw).1
      have hwn : ¬ Lt w (.Psi .zero (.Om c) β) := fun h => by
        rw [inC_of_lt_node (fr_node hw) h] at hin
        cases hin
      have hψw := le_of_not_ltX (P.G.nf _ hwS) (P.G.nf _ hψ) hwn
      have hct := P.lemA hcS ⟨w, hw, Or.inr (P.G.lt_of_lt_of_le hcS hψ hwS (P.G.cx c β hψ) hψw)⟩
      exact ne_gt_of_le (Or.inr hct)
  · exact Or.inl

/-- `S` の `Ψ_c(β)` が `t` 未満なら `c` も `t` 未満 -/
theorem c_lt {c β : Tm} (hψ : Tm.Psi .zero (.Om c) β ∈ S) (hl : lev c = n)
    (h : Lt (.Psi .zero (.Om c) β) (.Xi n γ)) : Lt c (.Xi n γ) := by
  have hcS := P.G.sub hψ (mem_subs_psi_c _ c β)
  rcases le_of_ne_gtX (P.G.nf _ hcS) P.ht ((P.kl hψ hl).mp h) with e | e
  · exact absurd e (P.ne_of_mem hcS)
  · exact e

/-- K2X：`γ` の前線は全て `t` 未満 -/
theorem k2x : ∀ w, w ∈ fr (.K n) γ → Lt w (.Xi n γ) := fun w hw =>
  P.lemA (P.G.sub P.γS (fr_spec hw).1) ⟨w, hw, Le.refl _⟩

/-- `t = Ξ_n(γ)` は `S` を切断する -/
theorem cut : CutT S (.Xi n γ) := by
  have G := P.G
  refine cut_of_principal G P.ht P.hsub (fun N ih _ q p hqS hpS hqp hpp hN h1 h2 => ?_)
  have hqF := G.nf q hqS
  have hpF := G.nf p hpS
  refine cut_reduce P.ht rfl rfl hqF hpF hqp hpp h1 h2 (fun lq lp bq bp => ?_)
  simp only [lev] at lq lp
  -- `q` の鍵 `k` が `t` 未満なら `q < t`
  have viaΩ : ∀ y, Tm.Om y ∈ S → lev y = n → Lt y (.Xi n γ) → Lt (.Om y) (.Xi n γ) :=
    fun y _ hl h => (lt_om_xi y γ n hl).mpr h
  have viaΨ : ∀ d α, lev d = n → Lt d (.Xi n γ) → Lt (.Psi .zero (.Om d) α) (.Xi n γ) :=
    fun d α hl h => (lt_psi_xi hl).mpr (Or.inl (ne_gt_of_le (Or.inr h)))
  rcases shape_FX hpF hpp bp with ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨d, δ, rfl⟩ <;>
    simp only [lev] at lp
  · -- `p = Ω_x`：`x < t`
    have hx := G.sub hpS (mem_subs_om x)
    have hxt := (lt_om_xi x γ n lp).mp h2
    rcases shape_FX hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨d', α, rfl⟩ <;>
      simp only [lev] at lq
    · have hy := G.sub hqS (mem_subs_om y)
      exact viaΩ y hqS lq (ih x y hx hy (by simp only [Tm.size] at hN ⊢; omega)
        ((lt_om_om y x (lq.trans lp.symm)).mp h1) hxt)
    · exact ih x _ hx hqS (by simp only [Tm.size] at hN ⊢; omega)
        ((lt_xi_om (lp.trans lq.symm) (G.nf _ hx) hqF).mp h1) hxt
    · have hd := G.sub hqS (mem_subs_psi_c _ d' α)
      refine viaΨ d' α lq ?_
      rcases le_of_not_ltX (G.nf _ hx) (G.nf _ hd) ((lt_psi_om x d' α (lp.trans lq.symm)).mp h1)
        with e | e
      · rw [e]; exact hxt
      · exact ih x d' hx hd (by simp only [Tm.size] at hN ⊢; omega) e hxt
  · -- `p = Ξ_m(f)`（`m = n`）
    subst lp
    rcases shape_FX hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨d', α, rfl⟩ <;>
      simp only [lev] at lq
    · have hy := G.sub hqS (mem_subs_om y)
      exact viaΩ y hqS lq (ih _ y hpS hy (by simp only [Tm.size] at hN ⊢; omega)
        ((lt_om_xi y f m lq).mp h1) h2)
    · -- 同じ階の `Ξ(f') < Ξ(f) < t`
      subst lq
      have hfS := G.sub hpS (mem_subs_xi m' f)
      have hf'S := G.sub hqS (mem_subs_xi m' f')
      have hne : f' ≠ f := fun e => by subst e; exact Lt.irrefl _ h1
      have hne' : f' ≠ γ := fun e => P.ne_of_mem hqS (by rw [e])
      rcases (P.ff hpS).mp h2 with ⟨hfγ, hfr⟩ | ⟨hγf, w, hw, hwn⟩
      · rcases (G.ff_xi hqS hpS hne).mp h1 with ⟨hf'f, hfr'⟩ | ⟨-, w', hw', hw'n⟩
        · refine (P.ff hqS).mpr (Or.inl ⟨G.trans hf'S hfS P.γS hf'f hfγ, fun u hu => ?_⟩)
          have huS := G.sub hf'S (fr_spec hu).1
          have := size_le_of_mem_subs (fr_spec hu).1
          exact ih _ u hpS huS (by simp only [Tm.size] at hN ⊢; omega) (hfr' u hu) h2
        · have hw'S := G.sub hfS (fr_spec hw').1
          have hw't := hfr w' hw'
          rcases le_of_not_ltX (G.nf _ hw'S) hqF hw'n with e | e
          · rw [e]; exact hw't
          · have := size_le_of_mem_subs (fr_spec hw').1
            exact ih w' _ hw'S hqS (by simp only [Tm.size] at hN ⊢; omega) e hw't
      · have hwS := G.sub P.γS (fr_spec hw).1
        have hpw := le_of_not_ltX (G.nf _ hwS) hpF hwn
        have hqw := G.lt_of_lt_of_le hqS hpS hwS h1 hpw
        rcases triX (G.nf _ hf'S) P.γF with h' | h' | h'
        · refine (P.ff hqS).mpr (Or.inl ⟨h', fun u hu => ?_⟩)
          have huS := G.sub hf'S (fr_spec hu).1
          exact P.lemA huS ⟨w, hw, Or.inr (G.trans huS hqS hwS (G.k2x _ f' hqS u hu) hqw)⟩
        · exact absurd h' hne'
        · exact (P.ff hqS).mpr (Or.inr ⟨h', w, hw, Lt.asymmX hqF (G.nf _ hwS) hqw⟩)
    · have hd := G.sub hqS (mem_subs_psi_c _ d' α)
      refine viaΨ d' α lq ?_
      rcases le_of_ne_gtX (G.nf _ hd) hpF ((G.kl d' α m f hqS hpS lq).mp h1) with e | e
      · rw [e]; exact h2
      · exact ih _ d' hpS hd (by simp only [Tm.size] at hN ⊢; omega) e h2
  · -- `p = Ψ_d(δ)`：`d < t`
    have hdS := G.sub hpS (mem_subs_psi_c _ d δ)
    have hdt := P.c_lt hpS lp h2
    rcases shape_FX hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨d', α, rfl⟩ <;>
      simp only [lev] at lq
    · have hy := G.sub hqS (mem_subs_om y)
      exact viaΩ y hqS lq (ih d y hdS hy (by simp only [Tm.size] at hN ⊢; omega)
        ((lt_om_psi y d δ (lq.trans lp.symm)).mp h1) hdt)
    · exact ih d _ hdS hqS (by simp only [Tm.size] at hN ⊢; omega)
        ((G.xi_lt_psi hpS hqS (lp.trans lq.symm)).mp h1) hdt
    · have hd' := G.sub hqS (mem_subs_psi_c _ d' α)
      refine viaΨ d' α lq ?_
      rcases le_of_lt_psi_psiX (G.nf _ hd') (G.nf _ hdS) (lq.trans lp.symm) hqF hpF h1 with e | e
      · rw [e]; exact hdt
      · exact ih d d' hdS hd' (by simp only [Tm.size] at hN ⊢; omega) e hdt

end XiCtx

end RTKA
