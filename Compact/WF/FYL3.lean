import Compact.WF.FYL2
import Compact.WF.FYNr

/-! 断片 `FY` の順序の性質の証明：新しい項が `t = Ω_e` と `t = Ξ_n(γ)` の場合。

`Ξ_n(γ)` は `Ω` の不動点なので比較が `t` 自身に戻ってくる。この自己参照は補題 A（`γ` の前線のどれか
以下の元は `t` 未満）で断ち切る。`FX` と違い、`t` との非対称性を使わずに、比較を直接計算して示す。 -/

namespace RTKA

open Tm

/-! ### 主要項の形 -/

theorem shape_FY3 {x : Tm} (hx : FYNF x) (hp : isPrincipal x = true) (hb : isBot x = false) :
    (∃ a, x = .Om a) ∨ (∃ m f, x = .Xi m f) ∨ (∃ ρ δ, x = .Psi .zero ρ δ) := by
  cases x with
  | Om a => exact Or.inl ⟨a, rfl⟩
  | Xi m f => exact Or.inr (Or.inl ⟨m, f, rfl⟩)
  | Psi xi ρ δ =>
    obtain ⟨rfl, -⟩ := hx.psi
    exact Or.inr (Or.inr ⟨ρ, δ, rfl⟩)
  | _ => simp_all [isPrincipal, isBot]

theorem shape_FY4 {x : Tm} (hx : FYNF x) (hp : isPrincipal x = true) (hb : isBot x = false) :
    (∃ a, x = .Om a) ∨ (∃ m f, x = .Xi m f) ∨ (∃ c α, x = .Psi .zero (.Om c) α) ∨
      (∃ m r α, x = .Psi .zero (.Xi m r) α) := by
  rcases shape_FY3 hx hp hb with h | h | ⟨ρ, δ, rfl⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases hx.psi.2.1 with ⟨c, rfl, -⟩ | ⟨m, r, rfl⟩
    · exact Or.inr (Or.inr (Or.inl ⟨c, δ, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨m, r, δ, rfl⟩))

theorem fr_self_xi (n : Nat) (r : Tm) : fr (.Xi n r) (.Xi n r) = fr (.Xi n r) r := by
  rw [fr]
  simp [Lt.irrefl]

/-- 同じ階の `Ξ_n` どうしの比較の展開（順序の仮定なし） -/
theorem lt_xi_xi0 {n : Nat} {a b : Tm} (hne : a ≠ b) :
    Lt (.Xi n a) (.Xi n b) ↔
      (Lt a b ∧ inC a b (.Xi n b) = true) ∨ (Lt b a ∧ inC b a (.Xi n a) = false) := by
  rw [lt_principal_iff rfl rfl, cmpP_xi_xi, xiLtXi_eq]
  simp only [hne, ↓reduceIte]
  rw [ite_lt_gt_eq_lt]
  unfold Lt
  cases cmp a b <;> cases cmp b a <;> cases inC a b (Tm.Xi n b) <;> cases inC b a (Tm.Xi n a) <;>
    simp

/-- `Ψ^0_ρ(α)` の目標 `ρ` が同じ階の `Ξ_n(γ)` 未満なら `Ψ^0_ρ(α) < Ξ_n(γ)` -/
theorem lt_psi_xi_of_tgt {ρ α γ : Tm} {n : Nat} (hl : lev ρ = n) (h : Lt ρ (.Xi n γ)) :
    Lt (.Psi .zero ρ α) (.Xi n γ) :=
  (lt_psi_xiY hl).mpr (Or.inl (by unfold Lt at h; rw [h]; decide))

namespace GoodY

variable {S : List Tm} (G : GoodY S)
include G

/-- `Ψ^0_{Ω_d}(α) < X`（`X` は `Ω` の不動点）なら `d ≤ X` -/
theorem le_of_psiOm_lt_OF {d α X : Tm} (hψ : Tm.Psi .zero (.Om d) α ∈ S) (hX : IsOF X)
    (hXS : X ∈ S) (h : Lt (.Psi .zero (.Om d) α) X) : Le d X := by
  have hdS := G.sub hψ (mem_subs_psi_c _ d α)
  rcases G.tri hdS hXS with h' | h' | h'
  · exact Or.inr h'
  · exact Or.inl h'
  · exact absurd ((G.lt_OF_psiOmS hX hXS hψ).mpr h') (G.asymm hψ hXS h)

end GoodY

/-! ### `t = Ω_e` -/

theorem cut_omY {S : List Tm} (G : GoodY S) {e : Tm} (ht : FYNF (.Om e))
    (hsub : ∀ s, s ∈ subs (.Om e) → s ≠ .Om e → s ∈ S) : CutT S (.Om e) := by
  have heS : e ∈ S := hsub e (mem_subs_om e) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))
  refine G.cut_of_principal ht hsub (fun _ _ _ q p hqS hpS hqp hpp _ h1 h2 => ?_)
  have hqF := G.nf q hqS
  have hpF := G.nf p hpS
  refine cut_reduceY ht rfl rfl hqF hpF hqp hpp h1 h2 (fun _ _ bq bp => ?_)
  rcases shape_FY hpF hpp bp with ⟨x, rfl⟩ | hpX | ⟨d, β, rfl⟩ <;>
    rcases shape_FY hqF hqp bq with ⟨y, rfl⟩ | hqX | ⟨d', α, rfl⟩
  · have hx := G.sub hpS (mem_subs_om x)
    have hy := G.sub hqS (mem_subs_om y)
    exact (G.lt_om_iffS hy heS).mpr (G.trans hy hx heS ((G.lt_om_iffS hy hx).mp h1)
      ((G.lt_om_iffS hx heS).mp h2))
  · have hx := G.sub hpS (mem_subs_om x)
    exact (G.lt_OF_omS hqX hqS heS).mpr (G.trans hqS hx heS ((G.lt_OF_omS hqX hqS hx).mp h1)
      ((G.lt_om_iffS hx heS).mp h2))
  · have hx := G.sub hpS (mem_subs_om x)
    have hd' := G.sub hqS (mem_subs_psi_c _ d' α)
    exact (G.lt_psi_omS hqS heS).mpr (G.le_trans hd' hx heS ((G.lt_psi_omS hqS hx).mp h1)
      (Or.inr ((G.lt_om_iffS hx heS).mp h2)))
  · have hy := G.sub hqS (mem_subs_om y)
    exact (G.lt_om_iffS hy heS).mpr (G.trans hy hpS heS ((lt_om_OFG hpX).mp h1)
      ((G.lt_OF_omS hpX hpS heS).mp h2))
  · exact (G.lt_OF_omS hqX hqS heS).mpr (G.trans hqS hpS heS h1 ((G.lt_OF_omS hpX hpS heS).mp h2))
  · have hd' := G.sub hqS (mem_subs_psi_c _ d' α)
    exact (G.lt_psi_omS hqS heS).mpr (G.le_trans hd' hpS heS (G.le_of_psiOm_lt_OF hqS hpX hpS h1)
      (Or.inr ((G.lt_OF_omS hpX hpS heS).mp h2)))
  · have hy := G.sub hqS (mem_subs_om y)
    have hd := G.sub hpS (mem_subs_psi_c _ d β)
    exact (G.lt_om_iffS hy heS).mpr (G.lt_of_lt_of_le hy hd heS ((lt_om_psiY hpF).mp h1)
      ((G.lt_psi_omS hpS heS).mp h2))
  · have hd := G.sub hpS (mem_subs_psi_c _ d β)
    exact (G.lt_OF_omS hqX hqS heS).mpr (G.lt_of_lt_of_le hqS hd heS
      ((G.lt_OF_psiOmS hqX hqS hpS).mp h1) ((G.lt_psi_omS hpS heS).mp h2))
  · have hd := G.sub hpS (mem_subs_psi_c _ d β)
    have hd' := G.sub hqS (mem_subs_psi_c _ d' α)
    exact (G.lt_psi_omS hqS heS).mpr (G.le_trans hd' hd heS (G.le_of_lt_psi_psi hqS hpS h1)
      ((G.lt_psi_omS hpS heS).mp h2))

/-! ### `t = Ξ_n(γ)` -/

theorem xiOF (n : Nat) (γ : Tm) : IsOF (.Xi n γ) := Or.inl ⟨n, γ, rfl⟩

/-- `Ξ_n(r) ∈ S` の引数の前線（`K_n` について）の元は `Ξ_n(r)` についての前線の元 -/
theorem GoodY.fr_xi_sub {S : List Tm} (G : GoodY S) {n : Nat} {r u : Tm} (hX : Tm.Xi n r ∈ S)
    (hu : u ∈ fr (.K n) r) : u ∈ fr (.Xi n r) (.Xi n r) := by
  have hn := (G.nf _ hX).xi.1
  have hrS := G.sub hX (mem_subs_xi n r)
  rw [fr_self_xi]
  refine fr_subG (fun v hv h => (lt_K_iffY (G.nf _ (G.sub hrS hv)) hn).mpr ?_) hu
    (G.k2x n r hX u hu)
  have := lev_le_of_lt_gen h
  simp only [lev] at this
  exact this

/-- 新しい項 `t = Ξ_n(γ)` の文脈 -/
structure XiCtxY (S : List Tm) (n : Nat) (γ : Tm) : Prop where
  G : GoodY S
  ht : FYNF (.Xi n γ)
  hsub : ∀ s, s ∈ subs (Tm.Xi n γ) → s ≠ .Xi n γ → s ∈ S
  htS : Tm.Xi n γ ∉ S

namespace XiCtxY

variable {S : List Tm} {n : Nat} {γ : Tm} (P : XiCtxY S n γ)
include P

theorem γS : γ ∈ S :=
  P.hsub _ (mem_subs_xi n γ) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))

theorem hn : 1 ≤ n := P.ht.xi.1

theorem ne_of_mem {s : Tm} (hs : s ∈ S) : s ≠ .Xi n γ := fun e => P.htS (e ▸ hs)

theorem lt_of_ne_gt {z : Tm} (hz : z ∈ S) (h : cmp z (.Xi n γ) ≠ .gt) : Lt z (.Xi n γ) :=
  P.G.lt_of_ne_gt_new P.ht P.hsub P.htS hz h

/-- `γ ∉ C(g, d)`（`γ ≤ g`）なら、`γ` の前線（`K_n` について）に `d` 未満でない元がある -/
theorem wit {g d : Tm} (hg : Le γ g) (hgS : g ∈ S) (hn' : inC γ g d = false) :
    ∃ w, w ∈ fr (.K n) γ ∧ ¬ Lt w d :=
  wit_of_not_inC P.ht.xi.2.2.2.2
    (fun _ hv h => P.G.lt_of_lt_of_le (P.G.sub P.γS hv) P.γS hgS h hg) hn'

/-- `S` の `Ξ_n(f)` と `t` の比較 -/
theorem lt_xi_t {f : Tm} (hX : Tm.Xi n f ∈ S) :
    Lt (.Xi n f) (.Xi n γ) ↔
      (Lt f γ ∧ inC f γ (.Xi n γ) = true) ∨ (Lt γ f ∧ inC γ f (.Xi n f) = false) :=
  lt_xi_xi0 (fun e => P.ne_of_mem hX (by rw [e]))

/-- `r < γ` で `r` の前線（`K_n` について）が `t` 未満なら `Ξ_n(r) < t` -/
theorem xi_lt_of {r : Tm} (hX : Tm.Xi n r ∈ S) (hrγ : Lt r γ)
    (hfr : ∀ u, u ∈ fr (.K n) r → Lt u (.Xi n γ)) : Lt (.Xi n r) (.Xi n γ) := by
  have G := P.G
  have hrS := G.sub hX (mem_subs_xi n r)
  exact (P.lt_xi_t hX).mpr (Or.inl ⟨hrγ, inC_of_fr r (G.nf _ hX).xi.2.2.2.2
    (fun v hv h => G.trans (G.sub hrS hv) hrS P.γS h hrγ)
    (fun u hu => inC_of_lt_node (fr_node hu) (hfr u hu))⟩)

/-- 補題 A の主要項の場合 -/
theorem lemA_head {h w : Tm} (hhS : h ∈ S) (hhp : isPrincipal h = true) (hlw : lev h ≤ n)
    (hw : w ∈ fr (.K n) γ) (hhw : Le h w)
    (IH : ∀ u, u ∈ S → u.size < h.size → Le u w → Lt u (.Xi n γ)) : Lt h (.Xi n γ) := by
  have G := P.G
  have hhF := G.nf _ hhS
  have hwS := G.sub P.γS (fr_spec hw).1
  rcases Nat.lt_or_eq_of_le hlw with hl | hl
  · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
  by_cases hb : isBot h = true
  · exact bot_ltY hb (by simp only [lev]; omega) rfl rfl P.ht
  rcases shape_FY4 hhF hhp (Bool.eq_false_iff.mpr hb) with ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨d, δ, rfl⟩ | ⟨m, r, δ, rfl⟩
  · have hx := G.sub hhS (mem_subs_om x)
    exact (lt_om_OFG (xiOF _ _)).mpr (IH x hx (by simp only [Tm.size]; omega)
      (Or.inr (G.lt_of_lt_of_le hx hhS hwS hhF.om.2.2 hhw)))
  · simp only [lev] at hl
    have hm := hl.symm
    subst hm
    have hfS := G.sub hhS (mem_subs_xi n f)
    rcases G.tri hfS P.γS with h' | h' | h'
    · refine P.xi_lt_of hhS h' (fun u hu => ?_)
      have huS := G.sub hfS (fr_spec hu).1
      have := size_le_of_mem_subs (fr_spec hu).1
      exact IH u huS (by simp only [Tm.size]; omega)
        (Or.inr (G.lt_of_lt_of_le huS hhS hwS (G.k2x n f hhS u hu) hhw))
    · exact absurd (by rw [h']) (P.ne_of_mem hhS)
    · refine (P.lt_xi_t hhS).mpr (Or.inr ⟨h', ?_⟩)
      cases e : inC γ f (Tm.Xi n f)
      · rfl
      · exfalso
        have := fr_of_inC γ (fun w' _ hn' => not_lt_of_not_lt_K rfl hn') e w hw
        exact G.not_lt_of_le hhS hwS hhw (coll_xi0 hhF w (G.nf _ hwS) this (fr_spec hw).2)
  · have hd := G.sub hhS (mem_subs_psi_c _ d δ)
    have hdt := IH d hd (by simp only [Tm.size]; omega)
      (Or.inr (G.lt_of_lt_of_le hd hhS hwS (G.cx d δ hhS) hhw))
    simp only [lev] at hl
    refine lt_psi_xi_of_tgt (ρ := .Om d) hl ?_
    rw [lt_principal_iff rfl rfl, cmpP_om_xi hl]
    exact hdt
  · simp only [lev] at hl
    have hm := hl.symm
    subst hm
    have hρS : Tm.Xi n r ∈ S := G.sub hhS (by simp [subs])
    have hrS := G.sub hρS (mem_subs_xi n r)
    have hδS := G.sub hhS (mem_subs_psi_a _ _ δ)
    obtain ⟨-, -, -, -, -, hC⟩ := hhF.psi
    have hrδ : Lt r δ := by
      rcases inC_xi_iff.mp hC with h' | ⟨-, h'⟩
      · exact absurd h' (Lt.irrefl _)
      · exact h'
    -- `δ ≤ γ` なら `Ξ_n(r) < t`
    have viaLe : Le δ γ → Lt (.Psi .zero (.Xi n r) δ) (.Xi n γ) := fun hδγ => by
      refine lt_psi_xi_of_tgt rfl (P.xi_lt_of hρS (G.lt_of_lt_of_le hrS hδS P.γS hrδ hδγ)
        (fun u hu => ?_))
      have huS := G.sub hrS (fr_spec hu).1
      have hu' := G.fr_xi_sub hρS hu
      have := size_le_of_mem_subs (fr_spec hu).1
      exact IH u huS (by simp only [Tm.size]; omega)
        (Or.inr (G.lt_of_lt_of_le huS hhS hwS (G.k2t _ δ hhS u hu') hhw))
    rcases G.tri hδS P.γS with h' | h' | h'
    · exact viaLe (Or.inr h')
    · exact viaLe (Or.inl h')
    · rcases G.tri hρS hwS with h'' | h'' | h''
      · exact lt_psi_xi_of_tgt rfl (IH _ hρS (by simp only [Tm.size]; omega) (Or.inr h''))
      · exact lt_psi_xi_of_tgt rfl (IH _ hρS (by simp only [Tm.size]; omega) (Or.inl h''))
      · refine (lt_psi_xiY rfl).mpr (Or.inr ⟨h', ?_⟩)
        cases e : inC γ δ (Tm.Psi .zero (.Xi n r) δ)
        · rfl
        · exfalso
          have := fr_of_inC γ (fun w' _ hn' => not_lt_of_not_lt_K rfl hn') e w hw
          exact G.not_lt_of_le hhS hwS hhw (G.coll_psiS hhS w hwS this h'')

/-- 補題 A：`γ` の前線のどれか以下の `S` の元は `t` 未満 -/
theorem lemA_aux : ∀ N, ∀ v, v ∈ S → v.size ≤ N →
    (∃ w, w ∈ fr (.K n) γ ∧ Le v w) → Lt v (.Xi n γ) := by
  have G := P.G
  intro N
  induction N with
  | zero => intro v _ h; exact absurd h (by have := Tm.size_pos v; omega)
  | succ N ih =>
    intro v hvS hs ⟨w, hw, hvw⟩
    have hvF := G.nf _ hvS
    have hwS := G.sub P.γS (fr_spec hw).1
    have hwF := G.nf _ hwS
    cases hsv : summands v with
    | nil =>
      have : v = .zero := by cases v <;> simp_all [summands]
      subst this
      exact zero_lt (by intro e; cases e)
    | cons h rest =>
      have hmem : h ∈ summands v := by rw [hsv]; exact List.mem_cons_self
      have hhS := G.sub hvS (mem_subs_of_mem_summands hmem)
      obtain ⟨-, hhp⟩ := summands_FYNF v hvF h hmem
      have hhs := size_le_of_mem_summands v h hmem
      have hhw : Le h w := G.le_trans hhS hvS hwS (head_leY hvF hsv) hvw
      have hlw : lev h ≤ n := by
        have := (lt_K_iffY hwF P.hn).mp (fr_spec hw).2
        rcases hhw with e | e
        · rw [e]; exact this
        · exact Nat.le_trans (lev_le_of_lt_gen e) this
      have hht := P.lemA_head hhS hhp hlw hw hhw (fun u hu hus huw =>
        ih u hu (by omega) ⟨w, hw, huw⟩)
      exact lt_of_head_lt rfl hsv ((lt_principal_iff hhp rfl).mp hht)

theorem lemA {v : Tm} (hv : v ∈ S) (h : ∃ w, w ∈ fr (.K n) γ ∧ Le v w) : Lt v (.Xi n γ) :=
  P.lemA_aux _ v hv (Nat.le_refl _) h

/-- K2X：`γ` の前線は全て `t` 未満 -/
theorem k2x : ∀ w, w ∈ fr (.K n) γ → Lt w (.Xi n γ) := fun w hw =>
  P.lemA (P.G.sub P.γS (fr_spec hw).1) ⟨w, hw, Le.refl _⟩

/-- `t = Ξ_n(γ)` は `S` を切断する -/
theorem cut : CutT S (.Xi n γ) := by
  have G := P.G
  refine G.cut_of_principal P.ht P.hsub (fun N ih _ q p hqS hpS hqp hpp hN h1 h2 => ?_)
  have hqF := G.nf q hqS
  have hpF := G.nf p hpS
  refine cut_reduceY P.ht rfl rfl hqF hpF hqp hpp h1 h2 (fun lq lp bq bp => ?_)
  -- 前線の証人があれば補題 A
  have viaW : ∀ w, w ∈ fr (.K n) γ → ¬ Lt w p → Lt q (.Xi n γ) := fun w hw hwn => by
    have hwS := G.sub P.γS (fr_spec hw).1
    exact P.lemA hqS ⟨w, hw, Or.inr (G.lt_of_lt_of_le hqS hpS hwS h1 (G.le_of_not_lt hwS hpS hwn))⟩
  -- `w < t` で `q ≤ w` なら `q < t`
  have viaLe : ∀ w, w ∈ S → w.size < p.size → Lt w (.Xi n γ) → Le q w → Lt q (.Xi n γ) :=
    fun w hwS hws hwt hqw => by
      rcases hqw with e | e
      · rw [e]; exact hwt
      · exact ih w q hwS hqS (by omega) e hwt
  rcases shape_FY3 hpF hpp bp with ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨ρ, δ, rfl⟩
  · -- `p = Ω_x`：`x < t`
    have hx := G.sub hpS (mem_subs_om x)
    have hxt : Lt x (.Xi n γ) := (lt_om_OFG (xiOF _ _)).mp h2
    have hxs : x.size < (Tm.Om x).size := by simp only [Tm.size]; omega
    rcases shape_FY4 hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨d, α, rfl⟩ | ⟨m', r, α, rfl⟩
    · have hy := G.sub hqS (mem_subs_om y)
      exact (lt_om_OFG (xiOF _ _)).mpr (ih x y hx hy (by simp only [Tm.size] at hN ⊢; omega)
        ((G.lt_om_iffS hy hx).mp h1) hxt)
    · exact ih x _ hx hqS (by omega) ((G.lt_OF_omS (Or.inl ⟨m', f', rfl⟩) hqS hx).mp h1) hxt
    · have hd := G.sub hqS (mem_subs_psi_c _ d α)
      have hdt : Lt d (.Xi n γ) := by
        rcases (G.lt_psi_omS hqS hx).mp h1 with e | e
        · rw [e]; exact hxt
        · exact ih x d hx hd (by simp only [Tm.size] at hN ⊢; omega) e hxt
      refine lt_psi_xi_of_tgt (ρ := .Om d) lq ?_
      exact (lt_om_OFG (xiOF _ _)).mpr hdt
    · exact ih x _ hx hqS (by omega)
        ((G.lt_OF_omS (Or.inr ⟨m', r, α, rfl⟩) hqS hx).mp h1) hxt
  · -- `p = Ξ_m(f)`
    simp only [lev] at lp
    subst lp
    have hfS := G.sub hpS (mem_subs_xi m f)
    rcases (P.lt_xi_t hpS).mp h2 with ⟨hfγ, hinf⟩ | ⟨hγf, hn'⟩
    · rcases shape_FY3 hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨ρ, α, rfl⟩
      · have hy := G.sub hqS (mem_subs_om y)
        exact (lt_om_OFG (xiOF _ _)).mpr (ih _ y hpS hy (by simp only [Tm.size] at hN ⊢; omega)
          ((lt_om_OFG (Or.inl ⟨m, f, rfl⟩)).mp h1) h2)
      · simp only [lev] at lq
        subst lq
        have hf'S := G.sub hqS (mem_subs_xi m' f')
        have hne : f' ≠ f := fun e => by subst e; exact Lt.irrefl _ h1
        rcases (lt_xi_xi0 hne).mp h1 with ⟨hf'f, hin⟩ | ⟨hff', hn''⟩
        · refine (P.lt_xi_t hqS).mpr (Or.inl ⟨G.trans hf'S hfS P.γS hf'f hfγ, ?_⟩)
          refine inC_mono f' f (.Xi m' f) γ (.Xi m' γ) hin (fun v hv hvp => ?_)
            (fun v hv hvf => G.trans (G.sub hf'S hv) hfS P.γS hvf hfγ)
          have := size_le_of_mem_subs hv
          exact ih _ v hpS (G.sub hf'S hv) (by simp only [Tm.size] at hN ⊢; omega) hvp h2
        · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hpF.xi.2.2.2.2
            (fun v hv h => G.trans (G.sub hfS hv) hfS hf'S h hff') hn''
          have hwS := G.sub hfS (fr_spec hw).1
          have hwt : Lt w (.Xi m' γ) := coll_xi0 P.ht w (G.nf _ hwS)
            (fr_of_inC f (fun w' _ hn' => not_lt_of_not_lt_K rfl hn') hinf w hw) (fr_spec hw).2
          have := size_le_of_mem_subs (fr_spec hw).1
          exact viaLe w hwS (by simp only [Tm.size]; omega) hwt (G.le_of_not_lt hwS hqS hwn)
      · have hρS : ρ ∈ S := G.sub hqS (by simp [subs, self_mem_subs])
        rcases (lt_psi_xiY (π := ρ) (a := α) lq).mp h1 with h' | ⟨hfα, hn''⟩
        · have hρt : Lt ρ (.Xi m γ) := by
            rcases G.le_of_ne_gt hρS hpS h' with e | e
            · rw [e]; exact h2
            · have := size_le_of_mem_subs (show ρ ∈ subs (Tm.Psi .zero ρ α) by
                simp [subs, self_mem_subs])
              exact ih _ ρ hpS hρS (by simp only [Tm.size] at hN this ⊢; omega) e h2
          exact lt_psi_xi_of_tgt (ρ := ρ) (α := α) lq hρt
        · have hαS := G.sub hqS (mem_subs_psi_a _ _ α)
          obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hpF.xi.2.2.2.2
            (fun v hv h => G.trans (G.sub hfS hv) hfS hαS h hfα) hn''
          have hwS := G.sub hfS (fr_spec hw).1
          have := size_le_of_mem_subs (fr_spec hw).1
          have hwt : Lt w (.Xi m γ) := coll_xi0 P.ht w (G.nf _ hwS)
            (fr_of_inC f (fun w' _ hn' => not_lt_of_not_lt_K rfl hn') hinf w hw) (fr_spec hw).2
          exact viaLe w hwS (by simp only [Tm.size]; omega) hwt (G.le_of_not_lt hwS hqS hwn)
    · obtain ⟨w, hw, hwn⟩ := P.wit (Or.inr hγf) hfS hn'
      exact viaW w hw hwn
  · -- `p = Ψ^0_ρ(δ)`
    have hρS : ρ ∈ S := G.sub hpS (by simp [subs, self_mem_subs])
    have hδS := G.sub hpS (mem_subs_psi_a _ _ δ)
    rcases (lt_psi_xiY (π := ρ) (a := δ) lp).mp h2 with h' | ⟨hγδ, hn'⟩
    · have hρt := P.lt_of_ne_gt hρS h'
      have := size_le_of_mem_subs (show ρ ∈ subs (Tm.Psi .zero ρ δ) by simp [subs, self_mem_subs])
      exact ih ρ q hρS hqS (by simp only [Tm.size] at hN this ⊢; omega)
        (G.trans hqS hpS hρS h1 (lt_psi_targetY hpF)) hρt
    · obtain ⟨w, hw, hwn⟩ := P.wit (Or.inr hγδ) hδS hn'
      exact viaW w hw hwn

/-- `t = Ξ_n(γ)` は `S` の全ての元と反対称 -/
theorem anti : ∀ z, z ∈ S → AntiT (.Xi n γ) z :=
  P.G.anti_new P.ht P.hsub P.htS (fun _ _ _ _ e => by cases e)

end XiCtxY

end RTKA
