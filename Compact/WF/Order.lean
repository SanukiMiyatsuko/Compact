import Compact.WF.Syntax

/-! 体系全体の順序の性質 `FWOrder` の証明（`instFWOrder`）。

部分項で閉じた有限集合 `S` の要素数についての帰納法で不変条件 `GoodY S` を示す。

不変条件：
* `LinOn S`・`AntiOn S`：`S` の上で `<` は推移的、`cmp` は反対称で `.eq` なら等しい。
* `K2YOn S`・`K2TOn S`・`K2SOn S`：`Ψ^ξ_π(γ) ∈ S` の引数・目標・Mahlo 添字の前線（`π` について）は
  `Ψ^ξ_π(γ)` 未満。
* `K2XYOn S`：`Ξ_n(γ) ∈ S` の引数の前線（`K_n` について）は `Ξ_n(γ)` 未満。
* `CXYOn S`：`Ψ^0_{Ω_c}(γ) ∈ S` について `c < Ψ^0_{Ω_c}(γ)`。
* `SKOn S`：`Ψ^ξ_{Ξ_n(p)}(γ) ∈ S`（`ξ ≠ 0`）なら `K_n^+ = Ω_{K_n + 1} ∈ S`（Mahlo 添字の節点の引数の評価で
  `K_n^+` と比べるため）。 -/

namespace RTKA.W

open Tm

/-- `S` の上の反対称性と相等 -/
def AntiOn (S : List Tm) : Prop :=
  ∀ a, a ∈ S → ∀ b, b ∈ S → cmp b a = (cmp a b).swap ∧ (cmp a b = .eq → a = b)

def K2YOn (S : List Tm) : Prop :=
  ∀ ξ π γ, Tm.Psi ξ π γ ∈ S → ∀ w, w ∈ fr π γ → Lt w (.Psi ξ π γ)

def K2TOn (S : List Tm) : Prop :=
  ∀ ξ π γ, Tm.Psi ξ π γ ∈ S → ∀ w, w ∈ fr π π → Lt w (.Psi ξ π γ)

def K2SOn (S : List Tm) : Prop :=
  ∀ ξ π γ, Tm.Psi ξ π γ ∈ S → ∀ w, w ∈ fr π ξ → Lt w (.Psi ξ π γ)

def K2XYOn (S : List Tm) : Prop :=
  ∀ n γ, Tm.Xi n γ ∈ S → ∀ w, w ∈ fr (.K n) γ → Lt w (.Xi n γ)

def CXYOn (S : List Tm) : Prop :=
  ∀ c γ, Tm.Psi .zero (.Om c) γ ∈ S → Lt c (.Psi .zero (.Om c) γ)

def SKOn (S : List Tm) : Prop :=
  ∀ ξ n p γ, Tm.Psi ξ (.Xi n p) γ ∈ S → ξ ≠ .zero → succK n ∈ S

/-- 体系全体の順序の性質の証明の不変条件 -/
structure GoodY (S : List Tm) : Prop where
  lin : LinOn S
  anti : AntiOn S
  nf : ∀ s, s ∈ S → WNF s
  cl : ∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S
  k2 : K2YOn S
  k2t : K2TOn S
  k2s : K2SOn S
  k2x : K2XYOn S
  cx : CXYOn S
  sk : SKOn S

namespace GoodY

variable {S : List Tm} (G : GoodY S)
include G

theorem sub {s r : Tm} (hs : s ∈ S) (hr : r ∈ subs s) : r ∈ S := G.cl s hs r hr

theorem trans {a b c : Tm} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (h1 : Lt a b) (h2 : Lt b c) :
    Lt a c :=
  G.lin a ha b hb c hc h1 h2

theorem swap {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) : cmp b a = (cmp a b).swap :=
  (G.anti a ha b hb).1

theorem eq {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) (h : cmp a b = .eq) : a = b :=
  (G.anti a ha b hb).2 h

theorem asymm {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) (h : Lt a b) : ¬ Lt b a := by
  unfold Lt at *
  rw [G.swap ha hb, h]
  decide

theorem lt_of_gt {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) (h : cmp a b = .gt) : Lt b a := by
  unfold Lt
  rw [G.swap ha hb, h]
  rfl

theorem tri {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) : Lt a b ∨ a = b ∨ Lt b a := by
  cases e : cmp a b with
  | lt => exact Or.inl e
  | eq => exact Or.inr (Or.inl (G.eq ha hb e))
  | gt => exact Or.inr (Or.inr (G.lt_of_gt ha hb e))

/-- `¬ a < b` なら `b ≤ a` -/
theorem le_of_not_lt {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) (h : ¬ Lt a b) : Le b a := by
  rcases G.tri ha hb with h' | h' | h'
  · exact absurd h' h
  · exact Or.inl h'.symm
  · exact Or.inr h'

theorem le_of_ne_gt {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) (h : cmp a b ≠ .gt) : Le a b := by
  cases e : cmp a b with
  | lt => exact Or.inr e
  | eq => exact Or.inl (G.eq ha hb e)
  | gt => exact absurd e h

theorem not_lt_of_le {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) (h : Le a b) : ¬ Lt b a := by
  rcases h with rfl | h
  · exact Lt.irrefl _
  · exact G.asymm ha hb h

theorem lt_of_lt_of_le {a b c : Tm} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (h1 : Lt a b)
    (h2 : Le b c) : Lt a c := by
  rcases h2 with rfl | h2
  · exact h1
  · exact G.trans ha hb hc h1 h2

theorem lt_of_le_of_lt {a b c : Tm} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (h1 : Le a b)
    (h2 : Lt b c) : Lt a c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact G.trans ha hb hc h1 h2

theorem le_trans {a b c : Tm} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (h1 : Le a b)
    (h2 : Le b c) : Le a c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact Or.inr (G.lt_of_lt_of_le ha hb hc h1 h2)

theorem eq_of_cmpP_eq {x y : Tm} (hx : x ∈ S) (hy : y ∈ S) (hpx : isPrincipal x = true)
    (hpy : isPrincipal y = true) (h : cmpP x y = .eq) : x = y := by
  apply G.eq hx hy
  rw [cmp_principal hpx hpy, h]

end GoodY

/-! ## 切断性の枠組みと、`S` の中での比較

* `lexTransY`・`cutGenY`・`cut_of_principalY`：主要項の組の切断性から一般の切断性へ。
* `S` の中の比較：`Ω` の不動点と `Ω_e`（`lt_OF_om`）、KL（`lt_OF_psiOm`）、`Ψ^0_{Ω_c}` と `Ω_e`。
* `cut_omY`：`t = Ω_e` の切断性。
* `antiOn_of`・`linOn_of_cutY`：`t` との反対称性と切断性から、`S ∪ {t}` の反対称性と推移性。 -/

/-! ### 底と主要項の形 -/

theorem lt_of_isBotY {x y : Tm} (hl : lev x = lev y) (hx : isBot x = true) (hy : isBot y = false)
    (hpy : isPrincipal y = true) (hyF : WNF y) : cmpP x y = .lt := by
  rw [cmpP.eq_def]
  simp only [hl, Nat.lt_irrefl, ↓reduceIte]
  cases x <;> cases y <;> simp_all [isBot, isPrincipal]
  exact hyF.om_ne_k

theorem shape_OF {x : Tm} (hx : WNF x) (hp : isPrincipal x = true) (hb : isBot x = false) :
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
  · rw [summands_principal htp] at h2 ⊢
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

/-! ## 新しい項 `t` との反対称性の枠組みと、前線の片方向の言い換え

* `inC_of_fr`・`fr_of_inC`・`wit_of_not_inC`：前線による `C` への所属の片方向ずつの言い換え。向きごとに
  必要な仮定だけを取る。
* `fr_subG`：前線の取り替え（順序の仮定の代わりに部分項についての推移性を仮定）。
* `coll_xi0`：`Ξ_n(γ)` の崩壊の性質（順序の仮定なしで成り立つ）。`GoodY.coll_psi`：`Ψ^0_π(γ)` の崩壊の性質
  （`π ∈ S` なら、`t` が `S` に入らなくてもよい）。
* `GoodY.ne_new`：`S` の元と新しい項 `t` の `cmp` は `.eq` にならない。
* `GoodY.anti_new`：大きさ `M` 以下の `Ψ` との反対称性を仮定すれば、`t` は大きさ `M` 以下の `S` の元と反対称。
* `linOn_of_cutY`：反対称性と切断性から推移性へ。 -/

/-! ### 前線の片方向の言い換え -/

/-- 前線の各節点が `C(g, d)` に入り、`R` 以上の節点の引数が `g0` 未満（したがって `g` 未満）なら、
    `x ∈ C(g, d)` -/
theorem inC_of_fr {R g0 g d : Tm} : ∀ x : Tm, inC x g0 R = true →
    (∀ v, v ∈ subs x → Lt v g0 → Lt v g) →
    (∀ w, w ∈ fr R x → inC w g d = true) → inC x g d = true
  | .zero, _, _, _ => inC_zero _ _
  | .one, _, _, _ => inC_one _ _
  | .K n, _, _, _ => inC_K n _ _
  | .plus a b, h0, hg, hw => by
    rw [inC_plus, Bool.and_eq_true] at h0 ⊢
    exact ⟨inC_of_fr a h0.1 (fun v hv => hg v (subs_plus_l hv))
        (fun w h => hw w (by rw [fr, List.mem_append]; exact Or.inl h)),
      inC_of_fr b h0.2 (fun v hv => hg v (subs_plus_r hv))
        (fun w h => hw w (by rw [fr, List.mem_append]; exact Or.inr h))⟩
  | .Om a, h0, hg, hw => by
    rw [inC_om] at h0 ⊢
    exact inC_of_fr a h0 (fun v hv => hg v (subs_om hv)) (fun w h => hw w (by rw [fr]; exact h))
  | .Xi m a, h0, hg, hw => by
    by_cases hR : Lt (.Xi m a) R
    · exact hw _ (by rw [fr]; simp [hR])
    · rcases inC_xi_iff.mp h0 with h | ⟨ha, hlt⟩
      · exact absurd h hR
      · exact inC_xi_iff.mpr (Or.inr ⟨inC_of_fr a ha (fun v hv => hg v (subs_xi hv))
          (fun w h => hw w (by rw [fr]; simp only [hR, ↓reduceIte]; exact h)),
          hg a (mem_subs_xi m a) hlt⟩)
  | .Psi s p a, h0, hg, hw => by
    by_cases hR : Lt (.Psi s p a) R
    · exact hw _ (by rw [fr]; simp [hR])
    · rcases inC_psi_iff.mp h0 with h | ⟨hp, hs, ha, hlt⟩
      · exact absurd h hR
      · have hw' : ∀ w, w ∈ fr R s ++ fr R p ++ fr R a → inC w g d = true := fun w h =>
          hw w (by rw [fr]; simp only [hR, ↓reduceIte]; exact h)
        refine inC_psi_iff.mpr (Or.inr ⟨?_, ?_, ?_, hg a (mem_subs_psi_a s p a) hlt⟩)
        · exact inC_of_fr p hp (fun v hv => hg v (subs_psi_p hv)) (fun w h => hw' w (by simp [h]))
        · exact inC_of_fr s hs (fun v hv => hg v (subs_psi_s hv)) (fun w h => hw' w (by simp [h]))
        · exact inC_of_fr a ha (fun v hv => hg v (subs_psi_a hv)) (fun w h => hw' w (by simp [h]))

/-- `R` 以上の節点が `d` 未満でなければ、`x ∈ C(g, d)` から前線の各節点が `C(g, d)` に入る -/
theorem fr_of_inC {R g d : Tm} : ∀ x : Tm,
    (∀ w, w ∈ subs x → ¬ Lt w R → ¬ Lt w d) → inC x g d = true →
    ∀ w, w ∈ fr R x → inC w g d = true
  | .zero, _, _, w, h | .one, _, _, w, h | .K _, _, _, w, h => by simp [fr] at h
  | .plus a b, hd, hx, w, h => by
    rw [inC_plus, Bool.and_eq_true] at hx
    rw [fr, List.mem_append] at h
    rcases h with h | h
    · exact fr_of_inC a (fun v hv => hd v (subs_plus_l hv)) hx.1 w h
    · exact fr_of_inC b (fun v hv => hd v (subs_plus_r hv)) hx.2 w h
  | .Om a, hd, hx, w, h => by
    rw [inC_om] at hx
    rw [fr] at h
    exact fr_of_inC a (fun v hv => hd v (subs_om hv)) hx w h
  | .Xi m a, hd, hx, w, h => by
    rw [fr] at h
    by_cases hR : Lt (.Xi m a) R
    · simp only [hR, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact hx
    · simp only [hR, ↓reduceIte] at h
      rcases inC_xi_iff.mp hx with h' | ⟨ha, _⟩
      · exact absurd h' (hd _ (self_mem_subs _) hR)
      · exact fr_of_inC a (fun v hv => hd v (subs_xi hv)) ha w h
  | .Psi s p a, hd, hx, w, h => by
    rw [fr] at h
    by_cases hR : Lt (.Psi s p a) R
    · simp only [hR, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact hx
    · simp only [hR, ↓reduceIte, List.mem_append] at h
      rcases inC_psi_iff.mp hx with h' | ⟨hp, hs, ha, _⟩
      · exact absurd h' (hd _ (self_mem_subs _) hR)
      · rcases h with (h | h) | h
        · exact fr_of_inC s (fun v hv => hd v (subs_psi_s hv)) hs w h
        · exact fr_of_inC p (fun v hv => hd v (subs_psi_p hv)) hp w h
        · exact fr_of_inC a (fun v hv => hd v (subs_psi_a hv)) ha w h

/-- `x ∉ C(g, d)` なら前線に `d` 未満でない節点がある -/
theorem wit_of_not_inC {R g0 g d x : Tm} (h0 : inC x g0 R = true)
    (hg : ∀ v, v ∈ subs x → Lt v g0 → Lt v g) (hn : inC x g d = false) :
    ∃ w, w ∈ fr R x ∧ ¬ Lt w d := by
  by_cases h : ∀ w, w ∈ fr R x → inC w g d = true
  · rw [inC_of_fr x h0 hg h] at hn
    cases hn
  · obtain ⟨w, hw, hw'⟩ := exists_of_not_forall_mem _ h
    exact ⟨w, hw, fun h' => hw' (inC_of_lt_node (fr_node hw) h')⟩

/-- 前線の取り替え：`x` の部分項について `v < R' → v < R` なら、`R` についての前線の `R'` 未満の元は
    `R'` についての前線の元 -/
theorem fr_subG {R R' : Tm} : ∀ {x w : Tm}, (∀ v, v ∈ subs x → Lt v R' → Lt v R) →
    w ∈ fr R x → Lt w R' → w ∈ fr R' x
  | .zero, _, _, h, _ | .one, _, _, h, _ | .K _, _, _, h, _ => by simp [fr] at h
  | .plus a b, w, hR, h, hw => by
    rw [fr, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (fr_subG (fun v hv => hR v (subs_plus_l hv)) h hw)
    · exact Or.inr (fr_subG (fun v hv => hR v (subs_plus_r hv)) h hw)
  | .Om a, w, hR, h, hw => by
    rw [fr] at h ⊢
    exact fr_subG (fun v hv => hR v (subs_om hv)) h hw
  | .Xi m a, w, hR, h, hw => by
    rw [fr] at h ⊢
    by_cases hl : Lt (.Xi m a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      subst h
      simp only [hw, ↓reduceIte, List.mem_singleton]
    · simp only [hl, ↓reduceIte] at h
      have hl' : ¬ Lt (.Xi m a) R' := fun h' => hl (hR _ (self_mem_subs _) h')
      simp only [hl', ↓reduceIte]
      exact fr_subG (fun v hv => hR v (subs_xi hv)) h hw
  | .Psi s p a, w, hR, h, hw => by
    rw [fr] at h ⊢
    by_cases hl : Lt (.Psi s p a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      subst h
      simp only [hw, ↓reduceIte, List.mem_singleton]
    · simp only [hl, ↓reduceIte, List.mem_append] at h
      have hl' : ¬ Lt (.Psi s p a) R' := fun h' => hl (hR _ (self_mem_subs _) h')
      simp only [hl', ↓reduceIte, List.mem_append]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (fr_subG (fun v hv => hR v (subs_psi_s hv)) h hw))
      · exact Or.inl (Or.inr (fr_subG (fun v hv => hR v (subs_psi_p hv)) h hw))
      · exact Or.inr (fr_subG (fun v hv => hR v (subs_psi_a hv)) h hw)

/-- 引数の前線が全て `Ψ^ξ_π(γ)` 未満なら `γ ∈ C(γ, Ψ^ξ_π(γ))` -/
theorem inC_arg_of_k2 {ξ π γ : Tm} (h : WNF (.Psi ξ π γ))
    (hk : ∀ w, w ∈ fr π γ → Lt w (.Psi ξ π γ)) : inC γ γ (.Psi ξ π γ) = true :=
  inC_of_fr γ h.psi.Ca (fun _ _ h => h)
    (fun w hw => inC_of_lt_node (fr_node hw) (hk w hw))

/-- 目標の前線が全て `Ψ^ξ_π(γ)` 未満なら `π ∈ C(γ, Ψ^ξ_π(γ))` -/
theorem inC_tgt_of_k2t {ξ π γ : Tm} (h : WNF (.Psi ξ π γ))
    (hk : ∀ w, w ∈ fr π π → Lt w (.Psi ξ π γ)) : inC π γ (.Psi ξ π γ) = true :=
  inC_of_fr π h.psi.Cpi (fun _ _ h => h)
    (fun w hw => inC_of_lt_node (fr_node hw) (hk w hw))

/-! ### 崩壊の性質 -/

/-- 底は同じ階以上の底でない主要項より小さい -/
theorem bot_ltY {h t : Tm} (hb : isBot h = true) (hl : lev h ≤ lev t) (htp : isPrincipal t = true)
    (htb : isBot t = false) (ht : WNF t) : Lt h t := by
  have hp : isPrincipal h = true := by cases h <;> simp_all [isBot, isPrincipal]
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · exact lt_of_lev_lt' hl
  · exact (lt_principal_iff hp htp).mpr (lt_of_isBotY hl hb htb htp ht)

theorem lev_pos_psi {ξ π γ : Tm} (ht : WNF (.Psi ξ π γ)) : 1 ≤ lev (.Psi ξ π γ) :=
  lev_posY ht (by intro e; cases e)

/-- `Ξ_n(γ)` の崩壊の性質（順序の仮定なし） -/
theorem coll_xi0 {n : Nat} {γ : Tm} (ht : WNF (.Xi n γ)) :
    ∀ z, WNF z → inC z γ (.Xi n γ) = true → Lt z (.K n) → Lt z (.Xi n γ) := by
  obtain ⟨hn, -, -, -, -⟩ := ht.xi
  intro z
  induction z with
  | zero => intros; exact zero_lt (by intro e; cases e)
  | one => intros; exact bot_ltY rfl (by simp only [lev]; omega) rfl rfl ht
  | K m =>
    intro hz _ hlt
    exact bot_ltY rfl ((lt_K_iffY hz hn).mp hlt) rfl rfl ht
  | plus a b iha _ =>
    intro hz hin hlt
    rw [inC_plus, Bool.and_eq_true] at hin
    obtain ⟨haF, -, -, -⟩ := hz.plus
    have hl := (lt_K_iffY hz hn).mp hlt
    exact (lt_plus_prin_iffY hz rfl).mpr (iha haF hin.1 ((lt_K_iffY haF hn).mpr hl))
  | Om g ihg =>
    intro hz hin hlt
    rw [inC_om] at hin
    have hgF := hz.om.1
    have hl := (lt_K_iffY hz hn).mp hlt
    exact (lt_om_OFG (Or.inl ⟨n, γ, rfl⟩)).mpr (ihg hgF hin ((lt_K_iffY hgF hn).mpr hl))
  | Xi m f _ =>
    intro hz hin hlt
    rcases inC_xi_iff.mp hin with h | ⟨hf, hfγ⟩
    · exact h
    have hl := (lt_K_iffY hz hn).mp hlt
    simp only [lev] at hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · subst hl
      have hne : f ≠ γ := fun e => by subst e; exact Lt.irrefl _ hfγ
      rw [lt_principal_iff rfl rfl, cmpP_xi_xi, xiLtXi_eq]
      unfold Lt at hfγ
      simp [hne, hfγ, hf]
  | Psi s κ β _ ihκ _ =>
    intro hz hin hlt
    have hκF := hz.psi.piF
    rcases inC_psi_iff.mp hin with h | ⟨hκ, -, -, -⟩
    · exact h
    have hl := (lt_K_iffY hz hn).mp hlt
    simp only [lev] at hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · have hκX := ihκ hκF hκ ((lt_K_iffY hκF hn).mpr (by omega))
      refine (lt_psi_xiY hl).mpr (Or.inl ?_)
      unfold Lt at hκX
      rw [hκX]
      decide

namespace GoodY

variable {S : List Tm} (G : GoodY S)
include G

/-- `Ψ^ξ_π(γ)` の崩壊の性質（`π ∈ S`。`Ψ^ξ_π(γ)` 自身は `S` に入らなくてよい） -/
theorem coll_psi {ξ π γ : Tm} (ht : WNF (.Psi ξ π γ)) (hπS : π ∈ S) :
    ∀ z, z ∈ S → inC z γ (.Psi ξ π γ) = true → Lt z π → Lt z (.Psi ξ π γ) := by
  have hm := ht.shape
  have hlt0 := lev_pos_psi ht
  intro z
  induction z with
  | zero => intros; exact zero_lt (by intro e; cases e)
  | one => intros; exact bot_ltY rfl hlt0 rfl rfl ht
  | K m =>
    intro _ _ hlt
    exact bot_ltY rfl (lev_le_of_lt_gen (y := π) hlt) rfl rfl ht
  | plus a b iha _ =>
    intro hz hin hlt
    rw [inC_plus, Bool.and_eq_true] at hin
    have hzF := G.nf _ hz
    have haS := G.sub hz (show a ∈ subs (.plus a b) by simp [subs, self_mem_subs])
    have hao : Lt a π := G.trans haS hz hπS (lt_plus_leftY hzF) hlt
    exact (lt_plus_prin_iffY hzF rfl).mpr (iha haS hin.1 hao)
  | Om e ihe =>
    intro hz hin hlt
    rw [inC_om] at hin
    have hzF := G.nf _ hz
    have heS := G.sub hz (mem_subs_om e)
    rcases hm with ⟨c, rfl, rfl⟩ | hsh
    · have hcS := G.sub hπS (mem_subs_om c)
      exact (lt_om_psiY ht).mpr ((G.lt_om_iffS heS hcS).mp hlt)
    · exact (lt_om_OFG (IsOF.psi ht (notOm_of_shape hsh))).mpr
        (ihe heS hin (G.trans heS hz hπS hzF.om.2.2 hlt))
  | Xi m f _ =>
    intro hz hin hlt
    rcases inC_xi_iff.mp hin with h | ⟨hf, hfγ⟩
    · exact h
    have hl := lev_le_of_lt_gen hlt
    simp only [lev] at hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · have hgt : cmp π (.Xi m f) = .gt := by
        unfold Lt at hlt; rw [G.swap hz hπS, hlt]; rfl
      rw [lt_xi_psiY hl.symm, lt_psi_xiY hl.symm]
      rintro (h | ⟨-, h⟩)
      · exact h hgt
      · rw [hf] at h; cases h
  | Psi s κ β _ _ _ =>
    intro hz hin hlt
    rcases inC_psi_iff.mp hin with h | ⟨hκ, hs, hβ, hβγ⟩
    · exact h
    have hl := lev_le_of_lt_gen hlt
    simp only [lev] at hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · have hne : Tm.Psi s κ β ≠ .Psi ξ π γ := by
        intro e; cases e; exact Lt.irrefl _ hβγ
      rw [lt_psi_psiY hl hne]
      by_cases h1 : Lt (.Psi ξ π γ) κ
      · exact Or.inr ⟨h1, hlt, Or.inl ⟨hβγ, hβ, hs, hκ⟩⟩
      · exact Or.inl h1

/-- `S` の元の崩壊 `Ψ^ξ_π(γ)` の性質 -/
theorem coll_psiS {ξ π γ : Tm} (ht : Tm.Psi ξ π γ ∈ S) :
    ∀ z, z ∈ S → inC z γ (.Psi ξ π γ) = true → Lt z π → Lt z (.Psi ξ π γ) :=
  G.coll_psi (G.nf _ ht) (G.sub ht (by simp [subs, self_mem_subs]))

theorem inC_argS {ξ π γ : Tm} (ht : Tm.Psi ξ π γ ∈ S) : inC γ γ (.Psi ξ π γ) = true :=
  inC_arg_of_k2 (G.nf _ ht) (G.k2 ξ π γ ht)

theorem inC_tgtS {ξ π γ : Tm} (ht : Tm.Psi ξ π γ ∈ S) : inC π γ (.Psi ξ π γ) = true :=
  inC_tgt_of_k2t (G.nf _ ht) (G.k2t ξ π γ ht)

/-- `S` での前線の取り替え -/
theorem fr_sub {R R' x w : Tm} (hR : R ∈ S) (hR' : R' ∈ S) (hx : x ∈ S) (hle : Le R' R)
    (hw : w ∈ fr R x) (hwR : Lt w R') : w ∈ fr R' x :=
  fr_subG (fun _ hv h => G.lt_of_lt_of_le (G.sub hx hv) hR' hR h hle) hw hwR

end GoodY

/-! ### 新しい項 `t` との反対称性 -/

/-- `t` と `s` の反対称性と相等 -/
def AntiT (t s : Tm) : Prop := cmp s t = (cmp t s).swap ∧ (cmp t s = .eq → t = s)

/-- `Ω_X`（`X` は `Ω` の不動点）は標準形でない -/
theorem not_WNF_om_OF {X : Tm} (hX : IsOF X) (h : WNF (.Om X)) : False := by
  have := h.om.2.2
  rw [cmp_principal hX.principal rfl, cmpP_OF_om hX rfl, cmp_self] at this
  exact absurd this (by decide)

/-- `cmpPsi` が `.eq` なら等しい -/
theorem cmpPsi_eq {xi pi a sg ka b : Tm} (h : cmpPsi (.Psi xi pi a) (.Psi sg ka b) = .eq) :
    Tm.Psi xi pi a = .Psi sg ka b := by
  rw [cmpPsi.eq_def] at h
  simp only [] at h
  by_cases h1 : (Tm.Psi xi pi a == Tm.Psi sg ka b) = true
  · exact eq_of_beq h1
  · exfalso
    simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    revert h
    split
    · intro h; cases h
    · split
      · intro h; cases h
      · split <;> intro h <;> cases h

theorem swap_eq_eq {o : Ordering} (h : o.swap = .eq) : o = .eq := by
  cases o <;> first | rfl | cases h

namespace GoodY

variable {S : List Tm} (G : GoodY S)
include G

/-- 同じ階の主要項どうしの、`t` の側の相等（`.eq` にならない） -/
theorem eqP_new {t y : Tm} (ht : WNF t) (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S)
    (hy : y ∈ S) (hne : y ≠ t) (htp : isPrincipal t = true) (hyp : isPrincipal y = true)
    (ih : ∀ u, u ∈ S → u.size < y.size → cmp u t ≠ .eq) :
    cmpP t y ≠ .eq ∧ cmpP y t ≠ .eq := by
  have hyF := G.nf y hy
  by_cases h1 : lev t < lev y
  · rw [cmpP_of_lev_lt h1, cmpP_of_lev_gt h1]; exact ⟨by decide, by decide⟩
  by_cases h2 : lev y < lev t
  · rw [cmpP_of_lev_gt h2, cmpP_of_lev_lt h2]; exact ⟨by decide, by decide⟩
  have hl : lev t = lev y := by omega
  have sub1 : ∀ e, e ∈ subs t → e.size < t.size → e ∈ S := fun e he hs =>
    hsub e he (ne_of_mem_subs_lt hs)
  cases t <;> cases y
  all_goals first
    | (exfalso; simp [isPrincipal] at htp hyp; done)
    | skip
  case one.one => exact absurd rfl hne
  case K.K m n =>
    have : n = m := by simp only [lev] at hl; omega
    subst this
    exact absurd rfl hne
  case Om.Om e a =>
    have heS := sub1 e (mem_subs_om e) (by simp only [Tm.size]; omega)
    have haS := G.sub hy (mem_subs_om a)
    have hl' : lev e = lev a := hl
    rw [cmpP_om_om hl', cmpP_om_om hl'.symm]
    refine ⟨fun h => hne ?_, fun h => hne ?_⟩
    · rw [G.eq heS haS h]
    · rw [G.eq haS heS h]
  case Om.Xi e n b =>
    have heS := sub1 e (mem_subs_om e) (by simp only [Tm.size]; omega)
    have hl' : lev e = n := hl
    rw [cmpP_om_xi hl', cmpP_xi_om hl']
    have key : cmp e (.Xi n b) ≠ .eq := fun h => by
      have := G.eq heS hy h
      subst this
      exact not_WNF_om_OF (Or.inl ⟨n, b, rfl⟩) ht
    exact ⟨key, fun h => key (swap_eq_eq h)⟩
  case Xi.Om n b a =>
    have haS := G.sub hy (mem_subs_om a)
    have hl' : lev a = n := hl.symm
    rw [cmpP_om_xi hl', cmpP_xi_om hl']
    have key := ih a haS (by simp only [Tm.size]; omega)
    exact ⟨fun h => key (swap_eq_eq h), key⟩
  case Om.Psi e xi κ β =>
    have heS := sub1 e (mem_subs_om e) (by simp only [Tm.size]; omega)
    rcases hyF.shape with ⟨c, rfl, rfl⟩ | hsh
    · have h' : lev e = lev c := hl
      rw [cmpP_om_psi0 h', cmpP_psi0_om h']
      by_cases h : cmp e c = .lt <;> simp [h]
    · have hX : IsOF (.Psi xi κ β) := IsOF.psi hyF (notOm_of_shape hsh)
      have hl' : lev e = lev (Tm.Psi xi κ β) := hl
      rw [cmpP_om_OF hX hl', cmpP_OF_om hX hl']
      have key : cmp e (.Psi xi κ β) ≠ .eq := fun h => by
        have := G.eq heS hy h
        subst this
        exact not_WNF_om_OF hX ht
      exact ⟨key, fun h => key (swap_eq_eq h)⟩
  case Psi.Om xi π γ a =>
    have haS := G.sub hy (mem_subs_om a)
    rcases ht.shape with ⟨c, rfl, rfl⟩ | hsh
    · have h' : lev a = lev c := hl.symm
      rw [cmpP_om_psi0 h', cmpP_psi0_om h']
      by_cases h : cmp a c = .lt <;> simp [h]
    · have hX : IsOF (.Psi xi π γ) := IsOF.psi ht (notOm_of_shape hsh)
      have hl' : lev a = lev (Tm.Psi xi π γ) := hl.symm
      rw [cmpP_om_OF hX hl', cmpP_OF_om hX hl']
      have key := ih a haS (by simp only [Tm.size]; omega)
      exact ⟨fun h => key (swap_eq_eq h), key⟩
  case Xi.Xi n γ m b =>
    have : n = m := hl
    subst this
    rw [cmpP_xi_xi, cmpP_xi_xi]
    have h1 : γ ≠ b := fun e => hne (by rw [e])
    have h2 : b ≠ γ := fun e => h1 e.symm
    simp only [h1, h2, ↓reduceIte]
    exact ⟨by split <;> decide, by split <;> decide⟩
  case Psi.Xi xi π γ m b =>
    have hl' : lev π = m := hl
    rw [cmpP_psi_xi hl', cmpP_xi_psi hl']
    exact ⟨by split <;> decide, by split <;> decide⟩
  case Xi.Psi m b xi κ β =>
    have hl' : lev κ = m := hl.symm
    rw [cmpP_psi_xi hl', cmpP_xi_psi hl']
    exact ⟨by split <;> decide, by split <;> decide⟩
  case Psi.Psi xi π γ sg κ β =>
    have hl' : lev π = lev κ := hl
    rw [cmpP_psi_psi hl', cmpP_psi_psi hl'.symm]
    exact ⟨fun h => hne (cmpPsi_eq h).symm, fun h => hne (cmpPsi_eq h)⟩
  case K.Om m b =>
    have hne' := hyF.om_ne_k (m := m)
    rw [cmpP.eq_def, cmpP.eq_def]
    simp [hl, hne']
  case Om.K a m =>
    have hne' := ht.om_ne_k (m := m)
    rw [cmpP.eq_def, cmpP.eq_def]
    simp [hl, hne']
  all_goals
    simp only [cmpP.eq_def]
    simp_all [lev]

/-- `S` の元と新しい項 `t` の `cmp` は `.eq` にならない -/
theorem ne_new {t : Tm} (ht : WNF t) (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S) (htS : t ∉ S) :
    ∀ z, z ∈ S → cmp z t ≠ .eq ∧ cmp t z ≠ .eq := by
  have key : ∀ N, ∀ z, z ∈ S → z.size ≤ N → cmp z t ≠ .eq ∧ cmp t z ≠ .eq := by
    intro N
    induction N with
    | zero => intro z _ h; exact absurd h (by have := Tm.size_pos z; omega)
    | succ N ih =>
      intro z hz hs
      have hzF := G.nf z hz
      have hP : ∀ x, x ∈ summands z → ∀ w, w ∈ summands t →
          (cmpP x w = .eq → x = w) ∧ (cmpP w x = .eq → w = x) := by
        intro x hx w hw
        have hxS := G.sub hz (mem_subs_of_mem_summands hx)
        obtain ⟨-, hxp⟩ := summands_WNF z hzF x hx
        obtain ⟨-, hwp⟩ := summands_WNF t ht w hw
        cases htp : isPrincipal t
        · have hwS : w ∈ S := hsub w (mem_subs_of_mem_summands hw) (by
            intro e; subst e; rw [hwp] at htp; cases htp)
          exact ⟨G.eq_of_cmpP_eq hxS hwS hxp hwp, G.eq_of_cmpP_eq hwS hxS hwp hxp⟩
        · rw [summands_principal htp, List.mem_singleton] at hw
          subst hw
          have hxs := size_le_of_mem_summands z x hx
          have := G.eqP_new ht hsub hxS (fun e => htS (e ▸ hxS)) htp hxp
            (fun u hu hus => (ih u hu (by omega)).1)
          exact ⟨fun h => absurd h this.2, fun h => absurd h this.1⟩
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [cmp_eq] at h
        have := eq_of_summands_eq hzF ht
          (eq_of_cmpList_eq _ _ (fun x hx w hw => (hP x hx w hw).1) h)
        exact htS (this ▸ hz)
      · rw [cmp_eq] at h
        have := eq_of_summands_eq ht hzF
          (eq_of_cmpList_eq _ _ (fun w hw x hx => (hP x hx w hw).2) h)
        exact htS (this ▸ hz)
  exact fun z hz => key _ z hz (Nat.le_refl _)

/-- `S` の元 `z` が `cmp z t ≠ .gt` なら `z < t` -/
theorem lt_of_ne_gt_new {t z : Tm} (ht : WNF t) (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S)
    (htS : t ∉ S) (hz : z ∈ S) (h : cmp z t ≠ .gt) : Lt z t := by
  have := (G.ne_new ht hsub htS z hz).1
  unfold Lt
  cases e : cmp z t
  · rfl
  · exact absurd e this
  · exact absurd e h

/-- 同じ階の主要項どうしの、`t` との反対称性（`Ψ` どうしは仮定 `hPsi`） -/
theorem swapP_new {t y : Tm} (ht : WNF t) (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S)
    (hy : y ∈ S) (htp : isPrincipal t = true) (hyp : isPrincipal y = true)
    (hPsi : ∀ ξ π γ σ κ β, t = .Psi ξ π γ → y = .Psi σ κ β → lev π = lev κ →
      cmpPsi y t = (cmpPsi t y).swap) :
    cmpP y t = (cmpP t y).swap := by
  have hyF := G.nf y hy
  by_cases h1 : lev t < lev y
  · rw [cmpP_of_lev_lt h1, cmpP_of_lev_gt h1]; rfl
  by_cases h2 : lev y < lev t
  · rw [cmpP_of_lev_gt h2, cmpP_of_lev_lt h2]; rfl
  have hl : lev t = lev y := by omega
  have sub1 : ∀ e, e ∈ subs t → e.size < t.size → e ∈ S := fun e he hs =>
    hsub e he (ne_of_mem_subs_lt hs)
  cases t <;> cases y
  all_goals first
    | (exfalso; simp [isPrincipal] at htp hyp; done)
    | skip
  case one.one => rw [cmpP_self]; rfl
  case Om.Om e a =>
    have heS := sub1 e (mem_subs_om e) (by simp only [Tm.size]; omega)
    have haS := G.sub hy (mem_subs_om a)
    have hl' : lev e = lev a := hl
    rw [cmpP_om_om hl', cmpP_om_om hl'.symm]
    exact G.swap heS haS
  case Om.Xi e n b =>
    have hl' : lev e = n := hl
    rw [cmpP_om_xi hl', cmpP_xi_om hl']
  case Xi.Om n b a =>
    have hl' : lev a = n := hl.symm
    rw [cmpP_om_xi hl', cmpP_xi_om hl', Ordering.swap_swap]
  case Om.Psi e xi κ β =>
    rcases hyF.shape with ⟨c, rfl, rfl⟩ | hsh
    · have h' : lev e = lev c := hl
      rw [cmpP_om_psi0 h', cmpP_psi0_om h']
    · have hX : IsOF (.Psi xi κ β) := IsOF.psi hyF (notOm_of_shape hsh)
      have hl' : lev e = lev (Tm.Psi xi κ β) := hl
      rw [cmpP_om_OF hX hl', cmpP_OF_om hX hl']
  case Psi.Om xi π γ a =>
    rcases ht.shape with ⟨c, rfl, rfl⟩ | hsh
    · have h' : lev a = lev c := hl.symm
      rw [cmpP_om_psi0 h', cmpP_psi0_om h', Ordering.swap_swap]
    · have hX : IsOF (.Psi xi π γ) := IsOF.psi ht (notOm_of_shape hsh)
      have hl' : lev a = lev (Tm.Psi xi π γ) := hl.symm
      rw [cmpP_om_OF hX hl', cmpP_OF_om hX hl', Ordering.swap_swap]
  case Xi.Xi n γ m b =>
    have : n = m := hl
    subst this
    have hγS := sub1 γ (mem_subs_xi n γ) (by simp only [Tm.size]; omega)
    have hbS := G.sub hy (mem_subs_xi n b)
    exact (xi_SE (G.anti γ hγS b hbS)).1
  case Psi.Xi xi π γ m b =>
    have hl' : lev π = m := hl
    rw [cmpP_psi_xi hl', cmpP_xi_psi hl']
    split <;> rfl
  case Xi.Psi m b xi κ β =>
    have hl' : lev κ = m := hl.symm
    rw [cmpP_psi_xi hl', cmpP_xi_psi hl']
    split <;> rfl
  case Psi.Psi xi π γ sg κ β =>
    have hl' : lev π = lev κ := hl
    rw [cmpP_psi_psi hl', cmpP_psi_psi hl'.symm]
    exact hPsi xi π γ sg κ β rfl rfl hl'
  case K.Om m b =>
    have hne' := hyF.om_ne_k (m := m)
    rw [cmpP.eq_def, cmpP.eq_def]
    simp [hl, hne']
  case Om.K a m =>
    have hne' := ht.om_ne_k (m := m)
    rw [cmpP.eq_def, cmpP.eq_def]
    simp [hl, hne']
  all_goals
    simp only [cmpP.eq_def]
    simp_all [lev]

/-- `Ψ` どうしの反対称性を大きさ `M` 以下で仮定すれば、新しい項 `t` は大きさ `M` 以下の `S` の元と反対称 -/
theorem anti_new {t : Tm} (ht : WNF t) (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S) (htS : t ∉ S)
    (M : Nat)
    (hPsi : ∀ ξ π γ σ κ β, t = .Psi ξ π γ → Tm.Psi σ κ β ∈ S → (Tm.Psi σ κ β).size ≤ M →
      lev π = lev κ → cmpPsi (.Psi σ κ β) t = (cmpPsi t (.Psi σ κ β)).swap) :
    ∀ z, z ∈ S → z.size ≤ M → AntiT t z := by
  intro z hz hzM
  have hzF := G.nf z hz
  refine ⟨?_, fun h => absurd h (G.ne_new ht hsub htS z hz).2⟩
  rw [cmp_eq z t, cmp_eq t z]
  apply cmpList_swap
  intro x hx y hy
  have hyS := G.sub hz (mem_subs_of_mem_summands hy)
  have hys := size_le_of_mem_summands z y hy
  obtain ⟨-, hyp⟩ := summands_WNF z hzF y hy
  obtain ⟨-, hxp⟩ := summands_WNF t ht x hx
  cases htp : isPrincipal t
  · have hxS : x ∈ S := hsub x (mem_subs_of_mem_summands hx) (by
      intro e; subst e; rw [hxp] at htp; cases htp)
    rw [← cmp_principal hyp hxp, ← cmp_principal hxp hyp]
    exact G.swap hxS hyS
  · rw [summands_principal htp, List.mem_singleton] at hx
    subst hx
    exact G.swapP_new ht hsub hyS htp hyp (fun ξ π γ σ κ β e1 e2 hl => by
      subst e2; exact hPsi ξ π γ σ κ β e1 hyS (by omega) hl)

end GoodY

/-! ### 反対称性と切断性から推移性へ -/

theorem AntiOn.asymm {S : List Tm} (hA : AntiOn S) {a b : Tm} (ha : a ∈ S) (hb : b ∈ S)
    (h : Lt a b) : ¬ Lt b a := by
  unfold Lt at *
  rw [(hA a ha b hb).1, h]
  decide

theorem AntiOn.tri {S : List Tm} (hA : AntiOn S) {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) :
    Lt a b ∨ a = b ∨ Lt b a := by
  cases e : cmp a b with
  | lt => exact Or.inl e
  | eq => exact Or.inr (Or.inl ((hA a ha b hb).2 e))
  | gt =>
    refine Or.inr (Or.inr ?_)
    unfold Lt
    rw [(hA a ha b hb).1, e]
    rfl

theorem linOn_of_cutY {S S' : List Tm} {t : Tm} (hA : AntiOn S) (hLin : LinOn S')
    (inS' : ∀ s, s ∈ S → s ≠ t → s ∈ S') (cut : CutT S' t) : LinOn S := by
  intro a ha b hb c hc hab hbc
  by_cases eat : a = t <;> by_cases ebt : b = t <;> by_cases ect : c = t
  · subst eat; subst ebt; exact absurd hab (Lt.irrefl _)
  · subst eat; subst ebt; exact absurd hab (Lt.irrefl _)
  · subst eat; subst ect; exact absurd hbc (hA.asymm ha hb hab)
  · subst eat
    rcases hA.tri ha hc with h | h | h
    · exact h
    · exact absurd h.symm ect
    · exact absurd hab (hA.asymm hb ha (cut c b (inS' c hc ect) (inS' b hb ebt) hbc h))
  · subst ebt; subst ect; exact absurd hbc (Lt.irrefl _)
  · subst ebt
    rcases hA.tri ha hc with h | h | h
    · exact h
    · subst h; exact absurd hbc (hA.asymm ha hb hab)
    · exact absurd hbc (hA.asymm hc hb (cut a c (inS' a ha eat) (inS' c hc ect) h hab))
  · subst ect
    exact cut b a (inS' b hb ebt) (inS' a ha eat) hab hbc
  · exact hLin a (inS' a ha eat) b (inS' b hb ebt) c (inS' c hc ect) hab hbc

/-! ## 新しい項が `t = Ω_e` と `t = Ξ_n(γ)` の場合

`Ξ_n(γ)` は `Ω` の不動点なので比較が `t` 自身に戻ってくる。この自己参照は補題 A（`γ` の前線のどれか
以下の元は `t` 未満）で断ち切る。`t` との非対称性を使わずに、比較を直接計算して示す。 -/

/-! ### 主要項の形 -/

theorem shape_prin {x : Tm} (hx : WNF x) (hp : isPrincipal x = true) (hb : isBot x = false) :
    (∃ a, x = .Om a) ∨ (∃ m f, x = .Xi m f) ∨ (∃ τ ρ δ, x = .Psi τ ρ δ) := by
  cases x with
  | Om a => exact Or.inl ⟨a, rfl⟩
  | Xi m f => exact Or.inr (Or.inl ⟨m, f, rfl⟩)
  | Psi xi ρ δ =>
    exact Or.inr (Or.inr ⟨xi, ρ, δ, rfl⟩)
  | _ => simp_all [isPrincipal, isBot]

theorem shape_prinOF {x : Tm} (hx : WNF x) (hp : isPrincipal x = true) (hb : isBot x = false) :
    (∃ a, x = .Om a) ∨ (∃ m f, x = .Xi m f) ∨ (∃ c α, x = .Psi .zero (.Om c) α) ∨
      (∃ τ ρ α, x = .Psi τ ρ α ∧ IsOF (.Psi τ ρ α)) := by
  rcases shape_prin hx hp hb with h | h | ⟨τ, ρ, δ, rfl⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases hx.shape with ⟨c, rfl, rfl⟩ | hsh
    · exact Or.inr (Or.inr (Or.inl ⟨c, δ, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨τ, ρ, δ, rfl, IsOF.psi hx (notOm_of_shape hsh)⟩))

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
theorem lt_psi_xi_of_tgt {τ ρ α γ : Tm} {n : Nat} (hl : lev ρ = n) (h : Lt ρ (.Xi n γ)) :
    Lt (.Psi τ ρ α) (.Xi n γ) :=
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

theorem cut_omY {S : List Tm} (G : GoodY S) {e : Tm} (ht : WNF (.Om e))
    (hsub : ∀ s, s ∈ subs (.Om e) → s ≠ .Om e → s ∈ S) : CutT S (.Om e) := by
  have heS : e ∈ S := hsub e (mem_subs_om e) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))
  refine G.cut_of_principal ht hsub (fun _ _ _ q p hqS hpS hqp hpp _ h1 h2 => ?_)
  have hqF := G.nf q hqS
  have hpF := G.nf p hpS
  refine cut_reduceY ht rfl rfl hqF hpF hqp hpp h1 h2 (fun _ _ bq bp => ?_)
  rcases shape_OF hpF hpp bp with ⟨x, rfl⟩ | hpX | ⟨d, β, rfl⟩ <;>
    rcases shape_OF hqF hqp bq with ⟨y, rfl⟩ | hqX | ⟨d', α, rfl⟩
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
  ht : WNF (.Xi n γ)
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
  rcases shape_prinOF hhF hhp (Bool.eq_false_iff.mpr hb) with ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨d, δ, rfl⟩ | ⟨τ, ρ, δ, rfl, -⟩
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
    have hρS : ρ ∈ S := G.sub hhS (by simp [subs, self_mem_subs])
    have hδS := G.sub hhS (mem_subs_psi_a _ _ δ)
    have hρF := G.nf _ hρS
    -- `δ ≤ γ` なら `ρ ∈ C(γ, t)` で `ρ < t`
    have viaLe : Le δ γ → Lt (.Psi τ ρ δ) (.Xi n γ) := fun hδγ => by
      refine lt_psi_xi_of_tgt hl (coll_xi0 P.ht ρ hρF ?_
        ((lt_K_iffY hρF P.hn).mpr (Nat.le_of_eq hl)))
      refine inC_of_fr ρ hhF.psi.Cpi
        (fun v hv hvδ => G.lt_of_lt_of_le (G.sub hρS hv) hδS P.γS hvδ hδγ) (fun u hu => ?_)
      have huS := G.sub hρS (fr_spec hu).1
      have := size_le_of_mem_subs (fr_spec hu).1
      exact inC_of_lt_node (fr_node hu) (IH u huS (by simp only [Tm.size]; omega)
        (Or.inr (G.lt_of_lt_of_le huS hhS hwS (G.k2t _ _ δ hhS u hu) hhw)))
    rcases G.tri hδS P.γS with h' | h' | h'
    · exact viaLe (Or.inr h')
    · exact viaLe (Or.inl h')
    · rcases G.tri hρS hwS with h'' | h'' | h''
      · exact lt_psi_xi_of_tgt hl (IH _ hρS (by simp only [Tm.size]; omega) (Or.inr h''))
      · exact lt_psi_xi_of_tgt hl (IH _ hρS (by simp only [Tm.size]; omega) (Or.inl h''))
      · refine (lt_psi_xiY hl).mpr (Or.inr ⟨h', ?_⟩)
        cases e : inC γ δ (Tm.Psi τ ρ δ)
        · rfl
        · exfalso
          have := fr_of_inC γ (fun w' _ hn' => not_lt_of_not_lt_K (y := Tm.Psi τ ρ δ) hl hn') e w hw
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
      obtain ⟨-, hhp⟩ := summands_WNF v hvF h hmem
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
  rcases shape_prin hpF hpp bp with ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨τ, ρ, δ, rfl⟩
  · -- `p = Ω_x`：`x < t`
    have hx := G.sub hpS (mem_subs_om x)
    have hxt : Lt x (.Xi n γ) := (lt_om_OFG (xiOF _ _)).mp h2
    have hxs : x.size < (Tm.Om x).size := by simp only [Tm.size]; omega
    rcases shape_prinOF hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨d, α, rfl⟩ | ⟨τ', ρ', α, rfl, hOFq⟩
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
        ((G.lt_OF_omS hOFq hqS hx).mp h1) hxt
  · -- `p = Ξ_m(f)`
    simp only [lev] at lp
    subst lp
    have hfS := G.sub hpS (mem_subs_xi m f)
    rcases (P.lt_xi_t hpS).mp h2 with ⟨hfγ, hinf⟩ | ⟨hγf, hn'⟩
    · rcases shape_prin hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨τ', ρ, α, rfl⟩
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
            · have := size_le_of_mem_subs (show ρ ∈ subs (Tm.Psi τ' ρ α) by
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
      have := size_le_of_mem_subs (show ρ ∈ subs (Tm.Psi τ ρ δ) by simp [subs, self_mem_subs])
      exact ih ρ q hρS hqS (by simp only [Tm.size] at hN this ⊢; omega)
        (G.trans hqS hpS hρS h1 (lt_psi_targetY hpF)) hρt
    · obtain ⟨w, hw, hwn⟩ := P.wit (Or.inr hγδ) hδS hn'
      exact viaW w hw hwn

end XiCtxY

/-! ## 新しい項が `t = Ψ^ξ_π(γ)` の場合の準備

目標 `π`（や `S` の `Ψ` の目標）には Mahlo 添字が `0` でない `Ψ` も入る。

1. `GoodY.mi_tgt`（MI）：目標 `π ∈ S` について、`m(π)` 未満で `C(m(π), π)` に入る `x` は `C(x, π)` に入る。
   `π = Ψ^ζ_κ(b)` なら、`x` の `π` 以上の節点は `C(b, π)` に入るので（崩壊の性質）`κ` 以上で、`κ` の MI に
   帰着する。列の下端 `Ξ_n(p)` では `K_n^+ ∈ S` を使う。
2. `t` と目標 `ρ` の比較（`tgt_lt`・`not_lt_tgt`）は、`ρ` が `Ψ` のとき `t` との反対称性を仮定する。
3. `tgt_contra`（`t < ρ ≤ v < π` の矛盾）は、`ρ = Ψ^σ_κ(β)` のとき Prop. 4.20 の (1)〜(4) で分ける：
   (2)・(4) は `ρ` の前線の証人、(1)・(3) は `v ∈ C(β, ρ)`（または `v < t`）と崩壊の性質で、`κ ≤ v` なら
   `κ` について再帰する。
4. `lemA`（補題 A）・`k2`・`k2t`・`k2s`・`ms`・`cx`、`below`（`π = Ω_c` のとき `c` 未満なら `t` 未満）。 -/

/-! ### 道具 -/

theorem psiOm_lt_om_iff {c γ x : Tm} (hl : lev x = lev c) :
    Lt (.Psi .zero (.Om c) γ) (.Om x) ↔ ¬ Lt x c := by
  rw [lt_principal_iff rfl rfl, cmpP_psi0_om hl]
  unfold Lt
  cases cmp x c <;> simp

theorem OF_lt_om_iff {X x : Tm} (hX : IsOF X) (hl : lev x = lev X) :
    Lt X (.Om x) ↔ cmp x X = .gt := by
  rw [lt_principal_iff hX.principal rfl, cmpP_OF_om hX hl]
  cases cmp x X <;> simp

theorem IsTgt.principal {ρ : Tm} (h : IsTgt ρ) : isPrincipal ρ = true := by
  rcases h with ⟨c, rfl, -⟩ | ⟨n, r, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩ <;> rfl

theorem IsTgt.not_bot {ρ : Tm} (h : IsTgt ρ) : isBot ρ = false := by
  rcases h with ⟨c, rfl, -⟩ | ⟨n, r, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩ <;> rfl

theorem IsTgt.ne_zero {ρ : Tm} (h : IsTgt ρ) : ρ ≠ .zero := by
  rcases h with ⟨c, rfl, -⟩ | ⟨n, r, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩ <;> intro e <;> cases e

/-- 目標は `Ω_c` か `Ω` の不動点 -/
theorem IsTgt.cases {ρ : Tm} (h : IsTgt ρ) (hw : WNF ρ) : (∃ c, ρ = .Om c) ∨ IsOF ρ := by
  rcases h with ⟨c, rfl, -⟩ | ⟨n, r, rfl⟩ | ⟨ζ, κ, b, rfl, hζ⟩
  · exact Or.inl ⟨c, rfl⟩
  · exact Or.inr (Or.inl ⟨n, r, rfl⟩)
  · refine Or.inr (IsOF.psi hw ?_)
    rcases hw.shape with ⟨c, rfl, e⟩ | hsh
    · exact absurd e hζ
    · exact notOm_of_shape hsh

/-- 後者は目標でない -/
theorem not_tgt_of_succ {c : Tm} (hs : isSucc c = true) : ¬ IsTgt c := by
  rintro (⟨c', rfl, -⟩ | ⟨n, r, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩) <;> simp [isSucc, summands] at hs

namespace GoodY

variable {S : List Tm} (G : GoodY S)
include G

/-- `b < a + b`（`S` の中で） -/
theorem lt_plus_right : ∀ {a b : Tm}, Tm.plus a b ∈ S → Lt b (.plus a b)
  | a, b, hS => by
    have h := G.nf _ hS
    obtain ⟨-, hb, hap, hb0⟩ := h.plus
    have hbS := G.sub hS (show b ∈ subs (.plus a b) by simp [subs, self_mem_subs])
    have haS := G.sub hS (show a ∈ subs (.plus a b) by simp [subs, self_mem_subs])
    cases hs : summands b with
    | nil => exact absurd hs (summands_ne_nil hb0)
    | cons x xs =>
      have hxa := h.plus_head hs
      have hxm : x ∈ summands b := by rw [hs]; exact List.mem_cons_self
      have hx := summands_WNF b hb x hxm
      have hxS := G.sub hbS (mem_subs_of_mem_summands hxm)
      have hxa' : cmpP x a ≠ .gt := by rwa [← cmp_principal hx.2 hap]
      unfold Lt
      rw [cmp_eq, hs, summands_plus, hs]
      cases e : cmpP x a with
      | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]
      | gt => exact absurd e hxa'
      | eq =>
        rw [cmpList_cons_cons_eq _ _ e]
        have hxe : x = a := G.eq_of_cmpP_eq hxS haS hx.2 hap e
        subst hxe
        cases b with
        | zero => exact absurd rfl hb0
        | plus p q =>
          rw [summands_plus, List.cons.injEq] at hs
          obtain ⟨rfl, hq⟩ := hs
          have := lt_plus_right hbS
          unfold Lt at this
          rw [cmp_eq, summands_plus] at this
          rwa [← hq]
        | _ =>
          simp only [summands, List.cons.injEq] at hs
          rw [← hs.2]
          exact cmpList_nil_cons _ _

/-- `z < c` なら `z + 1 ≤ c`（`S` の中で） -/
theorem succT_le {z c : Tm} (hcS : c ∈ S) (hsS : succT z ∈ S) (h : Lt z c) :
    Le (succT z) c := by
  refine G.le_of_ne_gt hsS hcS ?_
  rw [cmp_eq, summands_succT]
  unfold Lt at h
  rw [cmp_eq] at h
  exact cmpList_succ_ne_gtY _ _ (summands_WNF c (G.nf c hcS)) h

/-- 階 `n + 1` の `Ω` の不動点は `K_n^+` より大きい -/
theorem succK_lt_OF {n : Nat} {X : Tm} (hX : IsOF X) (hXF : WNF X) (hl : lev X = n + 1)
    (hK1S : Tm.plus (.K n) .one ∈ S) : Lt (succK n) X := by
  have hKF : WNF (.plus (.K n) .one) := G.nf _ hK1S
  refine (lt_om_OFG hX).mpr ((lt_plus_prin_iffY hKF hX.principal).mpr ?_)
  exact bot_ltY rfl (by simp only [lev]; omega) hX.principal
    (by rcases hX with ⟨m, a, rfl⟩ | ⟨ξ, π, a, rfl, -, -⟩ <;> rfl) hXF

/-- MI（`Ξ_n(p)`）：`p` 未満で `C(p, Ξ_n(p))` に入る `S` の元 `x` は `C(x, Ξ_n(p))` に入る（`K_n^+ ∈ S` のとき） -/
theorem mi_xi {x p : Tm} {n : Nat} (hπS : Tm.Xi n p ∈ S) (hKS : succK n ∈ S) (hξS : x ∈ S)
    (hξp : Lt x p) (hξC : inC x p (.Xi n p) = true) : inC x x (.Xi n p) = true := by
  have hπF := G.nf _ hπS
  obtain ⟨hn, -, -, hpK, -⟩ := hπF.xi
  have hpS := G.sub hπS (mem_subs_xi n p)
  have hK1S : Tm.plus (.K n) .one ∈ S := G.sub hKS (by simp [succK, subs])
  have hKnS : Tm.K n ∈ S := G.sub hK1S (by simp [subs])
  have hpKp : Le p (succK n) := G.le_of_ne_gt hpS hKS hpK
  have hξK : Lt x (succK n) := G.lt_of_lt_of_le hξS hpS hKS hξp hpKp
  -- 主張：`x` 以下の `S` の元 `y` について `y ∈ C(p, Ξ_n(p))` なら `y ∈ C(x, Ξ_n(p))`
  have key : ∀ N, ∀ y, y ∈ S → y.size ≤ N → Le y x → inC y p (.Xi n p) = true →
      inC y x (.Xi n p) = true := by
    intro N
    induction N with
    | zero => intro y _ h; exact absurd h (by have := Tm.size_pos y; omega)
    | succ N ih =>
      intro y hyS hs hyξ hy
      have hyF := G.nf _ hyS
      have hyK : Lt y (succK n) := G.lt_of_le_of_lt hyS hξS hKS hyξ hξK
      have hly : lev y ≤ n + 1 := by
        have := lev_le_of_lt_gen hyK; simp only [succK, lev] at this; exact this
      cases y with
      | zero => exact inC_zero _ _
      | one => exact inC_one _ _
      | K m => exact inC_K m _ _
      | plus a b =>
        rw [inC_plus, Bool.and_eq_true] at hy ⊢
        have haS := G.sub hyS (show a ∈ subs (.plus a b) by simp [subs, self_mem_subs])
        have hbS := G.sub hyS (show b ∈ subs (.plus a b) by simp [subs, self_mem_subs])
        exact ⟨ih a haS (by simp only [Tm.size] at hs; omega)
            (G.le_trans haS hyS hξS (Or.inr (lt_plus_leftY hyF)) hyξ) hy.1,
          ih b hbS (by simp only [Tm.size] at hs; omega)
            (G.le_trans hbS hyS hξS (Or.inr (G.lt_plus_right hyS)) hyξ) hy.2⟩
      | Om e =>
        rw [inC_om] at hy ⊢
        have heS := G.sub hyS (mem_subs_om e)
        exact ih e heS (by simp only [Tm.size] at hs; omega)
          (G.le_trans heS hyS hξS (Or.inr hyF.om.2.2) hyξ) hy
      | Xi m f =>
        refine inC_xi_iff.mpr (Or.inl ?_)
        rcases inC_xi_iff.mp hy with h | -
        · exact h
        simp only [lev] at hly
        rcases Nat.lt_trichotomy m n with hm | hm | hm
        · exact lt_of_lev_lt' (by simp only [lev]; exact hm)
        · subst hm
          exact coll_xi0 hπF _ hyF hy ((lt_K_iffY hyF hn).mpr (Nat.le_refl _))
        · exfalso
          have hm' : m = n + 1 := by omega
          subst hm'
          exact G.asymm hKS hyS (G.succK_lt_OF (xiOF _ _) hyF rfl hK1S) hyK
      | Psi τ κ β =>
        by_cases hlt : Lt (.Psi τ κ β) (.Xi n p)
        · exact inC_psi_iff.mpr (Or.inl hlt)
        rcases inC_psi_iff.mp hy with h | ⟨hκ, hτ, hβ, hβp⟩
        · exact absurd h hlt
        have hP := hyF.psi
        have hlκ : lev κ = n + 1 := by
          simp only [lev] at hly
          rcases Nat.lt_trichotomy (lev κ) n with h1 | h1 | h1
          · exact absurd (lt_of_lev_lt' (by simp only [lev]; exact h1)) hlt
          · exact absurd (coll_xi0 hπF _ hyF hy ((lt_K_iffY hyF hn).mpr
              (by simp only [lev]; omega))) hlt
          · omega
        rcases hyF.shape with ⟨c, rfl, rfl⟩ | hsh
        · -- 目標は `Ω_c` で、`c = K_n + 1`
          have hcS := G.sub hyS (mem_subs_psi_c _ c β)
          have hβS := G.sub hyS (mem_subs_psi_a _ _ β)
          have hcF := G.nf _ hcS
          have hlc : lev c = n + 1 := hlκ
          have hKc : Lt (.K n) c := by
            rcases G.tri hKnS hcS with h | h | h
            · exact h
            · exact absurd h.symm (hP.piF.om_ne_k)
            · exfalso
              have := (lt_K_iffY hcF hn).mp h
              omega
          have hKc' : Le (.plus (.K n) .one) c := G.succT_le (z := .K n) hcS hK1S hKc
          have hcK : Le c (.plus (.K n) .one) := (G.lt_psi_omS hyS hK1S).mp hyK
          have hceq : c = .plus (.K n) .one := by
            rcases hcK with e | h
            · exact e
            · exact absurd h (G.not_lt_of_le hK1S hcS hKc')
          subst hceq
          have hβΩ : Lt β (.Om (.plus (.K n) .one)) :=
            G.lt_of_lt_of_le hβS hpS hKS hβp hpKp
          have hβy := G.coll_psiS hyS β hβS (G.inC_argS hyS) hβΩ
          have hβξ : Lt β x := G.lt_of_lt_of_le hβS hyS hξS hβy hyξ
          refine inC_psi_iff.mpr (Or.inr ⟨?_, inC_zero _ _, ?_, hβξ⟩)
          · simp [inC_om, inC_plus, inC_K, inC_one]
          · exact ih β hβS (by simp only [Tm.size] at hs; omega) (Or.inr hβξ) hβ
        · -- 目標が `Ω_c` でなければ、階 `n + 1` の `Ω` の不動点で `K_n^+` より大きい
          exfalso
          exact G.asymm hKS hyS (G.succK_lt_OF (IsOF.psi hyF (notOm_of_shape hsh)) hyF hlκ hK1S)
            hyK
  exact key _ x hξS (Nat.le_refl _) (Or.inl rfl) hξC

/-- MI：目標 `π ∈ S` について、`m(π)` 未満で `C(m(π), π)` に入る `S` の元 `x` は `C(x, π)` に入る -/
theorem mi_tgt : ∀ π, π ∈ S → IsTgt π → (∀ n p, π = .Xi n p → succK n ∈ S) → ∀ x, x ∈ S → Lt x (mi π) →
    inC x (mi π) π = true → inC x x π = true := by
  intro π
  induction π using size_induction with
  | h π ih =>
  intro hπS hT hsk x hxS hxm hxC
  rcases hT with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ | ⟨ζ, κ, b, rfl, hζ⟩
  · have := lt_oneY (G.nf _ hxS) hxm
    subst this
    exact inC_zero _ _
  · exact G.mi_xi hπS (hsk n p rfl) hxS hxm hxC
  · have hπF := G.nf _ hπS
    have hP := hπF.psi
    have hκS : κ ∈ S := G.sub hπS (by simp [subs, self_mem_subs])
    have hζS : ζ ∈ S := G.sub hπS (by simp [subs, self_mem_subs])
    have hbS := G.sub hπS (mem_subs_psi_a _ _ b)
    have hπκ : Lt (.Psi ζ κ b) κ := lt_psi_targetY hπF
    have hmκS : mi κ ∈ S := by
      rcases hP.tgt with ⟨c, rfl, -⟩ | ⟨n, q, rfl⟩ | ⟨ζ', κ', b', rfl, -⟩
      · exact absurd (lt_oneY hP.xiF hP.mlt) hζ
      · exact (G.sub hκS (mem_subs_xi n q) : q ∈ S)
      · exact (G.sub hκS (by simp [subs, self_mem_subs]) : ζ' ∈ S)
    have hζκ : Lt ζ (mi κ) := hP.mlt
    have hxmκ : Lt x (mi κ) := G.trans hxS hζS hmκS hxm hζκ
    have hxCκ : inC x (mi κ) κ = true :=
      inC_mono x ζ (.Psi ζ κ b) (mi κ) κ hxC
        (fun v hv h => G.trans (G.sub hxS hv) hπS hκS h hπκ)
        (fun v hv h => G.trans (G.sub hxS hv) hζS hmκS h hζκ)
    have hκ := ih κ (by simp only [Tm.size]; omega) hκS hP.tgt
      (fun n p e => by subst e; exact G.sk ζ n p b hπS hζ) x hxS hxmκ hxCκ
    have hζb : Le ζ b := G.le_of_ne_gt hζS hbS hP.le
    refine inC_of_fr x hκ (fun _ _ h => h) (fun w hw => inC_of_lt_node (fr_node hw) ?_)
    have hwS := G.sub hxS (fr_spec hw).1
    have hd : ∀ v, v ∈ subs x → ¬ Lt v κ → ¬ Lt v (.Psi ζ κ b) := fun v hv hvκ hvπ =>
      hvκ (G.trans (G.sub hxS hv) hπS hκS hvπ hπκ)
    have hwC : inC w ζ (.Psi ζ κ b) = true := fr_of_inC x hd hxC w hw
    have hwC' : inC w b (.Psi ζ κ b) = true :=
      inC_mono w ζ _ b _ hwC (fun _ _ h => h)
        (fun v hv h => G.lt_of_lt_of_le (G.sub hwS hv) hζS hbS h hζb)
    exact G.coll_psiS hπS w hwS hwC' (fr_spec hw).2

/-- `S` の元 `Ψ^ξ_π(γ)` について `ξ ∈ C(ξ, π)` -/
theorem miS {ξ π γ : Tm} (ht : Tm.Psi ξ π γ ∈ S) : inC ξ ξ π = true := by
  by_cases hξ : ξ = .zero
  · subst hξ; exact inC_zero _ _
  have hP := (G.nf _ ht).psi
  exact G.mi_tgt π (G.sub ht (by simp [subs, self_mem_subs])) hP.tgt
    (fun n p e => by subst e; exact G.sk ξ n p γ ht hξ) ξ
    (G.sub ht (by simp [subs, self_mem_subs])) hP.mlt hP.mC

/-- `S` の元 `Ψ^ξ_π(γ)` について `ξ ∈ C(ξ, Ψ^ξ_π(γ))` -/
theorem msS {ξ π γ : Tm} (ht : Tm.Psi ξ π γ ∈ S) : inC ξ ξ (.Psi ξ π γ) = true :=
  inC_of_fr ξ (G.miS ht) (fun _ _ h => h)
    (fun w hw => inC_of_lt_node (fr_node hw) (G.k2s ξ π γ ht w hw))

end GoodY

/-- 新しい項 `t = Ψ^ξ_π(γ)` の文脈 -/
structure PsiCtxY (S : List Tm) (ξ π γ : Tm) : Prop where
  G : GoodY S
  ht : WNF (.Psi ξ π γ)
  hsub : ∀ s, s ∈ subs (Tm.Psi ξ π γ) → s ≠ .Psi ξ π γ → s ∈ S
  htS : Tm.Psi ξ π γ ∉ S
  hsk : ∀ n p, π = .Xi n p → ξ ≠ .zero → succK n ∈ S

/-- `t < ρ ≤ v < π` の矛盾の追加の仮定：大きさ `N` 以下の目標 `ρ' < π` について `t` の成分が `C(β', ρ')` に
    入れば `v` も入る、または `v < t` で、大きさ `N` 以下の `v` 以下の元は `t` 未満かつ `t` と反対称 -/
def HCv (S : List Tm) (ξ π γ v : Tm) (N : Nat) : Prop :=
  (∀ ρ' β', ρ' ∈ S → ρ'.size ≤ N → Lt ρ' π → inC γ β' ρ' = true → inC ξ β' ρ' = true →
      inC π β' ρ' = true → inC v β' ρ' = true) ∨
    (Lt v (.Psi ξ π γ) ∧ ∀ ρ', ρ' ∈ S → ρ'.size ≤ N → Le ρ' v →
      Lt ρ' (.Psi ξ π γ) ∧ AntiT (.Psi ξ π γ) ρ')

theorem HCv.mono {S : List Tm} {ξ π γ v : Tm} {N N' : Nat} (h : HCv S ξ π γ v N)
    (hN : N' ≤ N) : HCv S ξ π γ v N' := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl (fun ρ' β' hS hs => h ρ' β' hS (by omega))
  · exact Or.inr ⟨h1, fun ρ' hS hs => h2 ρ' hS (by omega)⟩

namespace PsiCtxY

variable {S : List Tm} {ξ π γ : Tm} (P : PsiCtxY S ξ π γ)
include P

theorem πS : π ∈ S :=
  P.hsub π (by simp [subs, self_mem_subs]) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))

theorem γS : γ ∈ S :=
  P.hsub γ (mem_subs_psi_a _ _ γ) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))

theorem ξS : ξ ∈ S :=
  P.hsub ξ (by simp [subs, self_mem_subs]) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))

theorem hT : IsTgt π := P.ht.psi.tgt

theorem πF : WNF π := P.ht.psi.piF

theorem ne_of_mem {s : Tm} (hs : s ∈ S) : s ≠ .Psi ξ π γ := fun e => P.htS (e ▸ hs)

theorem lt_of_ne_gt {z : Tm} (hz : z ∈ S) (h : cmp z (.Psi ξ π γ) ≠ .gt) :
    Lt z (.Psi ξ π γ) :=
  P.G.lt_of_ne_gt_new P.ht P.hsub P.htS hz h

/-- 主要項 `y`（`Ψ` なら `t` と反対称）について `y < t ⟺ ¬ t < y` -/
theorem lt_iff_of {y : Tm} (hy : y ∈ S) (hyp : isPrincipal y = true)
    (hA : ∀ σ κ β, y = .Psi σ κ β → AntiT (.Psi ξ π γ) y) :
    Lt y (.Psi ξ π γ) ↔ ¬ Lt (.Psi ξ π γ) y := by
  have hne := (P.G.ne_new P.ht P.hsub P.htS y hy).1
  have hs : cmp y (.Psi ξ π γ) = (cmp (.Psi ξ π γ) y).swap := by
    cases y with
    | Psi σ κ β => exact (hA σ κ β rfl).1
    | _ =>
      have := P.G.swapP_new P.ht P.hsub hy rfl hyp (fun _ _ _ σ κ β _ e => by cases e)
      rw [cmp_principal hyp rfl, cmp_principal rfl hyp, this]
  unfold Lt
  rw [hs]
  rw [hs] at hne
  revert hne
  cases cmp (Tm.Psi ξ π γ) y <;> decide

theorem tgt_lt {ρ : Tm} (hρS : ρ ∈ S) (hρT : IsTgt ρ)
    (hA : ∀ σ κ β, ρ = .Psi σ κ β → AntiT (.Psi ξ π γ) ρ) (h : ¬ Lt (.Psi ξ π γ) ρ) :
    Lt ρ (.Psi ξ π γ) :=
  (P.lt_iff_of hρS hρT.principal hA).mpr h

theorem not_lt_tgt {ρ : Tm} (hρS : ρ ∈ S) (hρT : IsTgt ρ)
    (hA : ∀ σ κ β, ρ = .Psi σ κ β → AntiT (.Psi ξ π γ) ρ) (h : Lt ρ (.Psi ξ π γ)) :
    ¬ Lt (.Psi ξ π γ) ρ :=
  (P.lt_iff_of hρS hρT.principal hA).mp h

/-- MI：`ξ ∈ C(ξ, π)` -/
theorem mi : inC ξ ξ π = true := by
  by_cases hξ : ξ = .zero
  · rw [hξ]; exact inC_zero _ _
  exact P.G.mi_tgt π P.πS P.hT (fun n p e => P.hsk n p e hξ) ξ P.ξS P.ht.psi.mlt P.ht.psi.mC

/-! ### `S` の `Ψ` が `t` 未満になる条件 -/

theorem psi_lt_of_tgt {τ ρ α : Tm} (hq : Tm.Psi τ ρ α ∈ S) (hl : lev ρ = lev π)
    (h : ¬ Lt (.Psi ξ π γ) ρ) : Lt (.Psi τ ρ α) (.Psi ξ π γ) :=
  (lt_psi_psiY hl (P.ne_of_mem hq)).mpr (Or.inl h)

theorem psi_lt_of_c1 {τ ρ α : Tm} (hq : Tm.Psi τ ρ α ∈ S) (hl : lev ρ = lev π)
    (htρ : Lt (.Psi ξ π γ) ρ) (hqπ : Lt (.Psi τ ρ α) π) (hαγ : Lt α γ)
    (h1 : inC α γ (.Psi ξ π γ) = true) (h2 : inC τ γ (.Psi ξ π γ) = true)
    (h3 : inC ρ γ (.Psi ξ π γ) = true) :
    Lt (.Psi τ ρ α) (.Psi ξ π γ) :=
  (lt_psi_psiY hl (P.ne_of_mem hq)).mpr (Or.inr ⟨htρ, hqπ, Or.inl ⟨hαγ, h1, h2, h3⟩⟩)

theorem psi_lt_of_c2 {τ ρ α : Tm} (hq : Tm.Psi τ ρ α ∈ S) (hl : lev ρ = lev π)
    (htρ : Lt (.Psi ξ π γ) ρ) (hqπ : Lt (.Psi τ ρ α) π) (hγα : cmp γ α ≠ .gt)
    (hn : ¬ (inC γ α (.Psi τ ρ α) = true ∧ inC ξ α (.Psi τ ρ α) = true ∧
      inC π α (.Psi τ ρ α) = true)) :
    Lt (.Psi τ ρ α) (.Psi ξ π γ) :=
  (lt_psi_psiY hl (P.ne_of_mem hq)).mpr (Or.inr ⟨htρ, hqπ, Or.inr (Or.inl ⟨hγα, hn⟩)⟩)

theorem psi_lt_of_c3 {τ α : Tm} (hq : Tm.Psi τ π α ∈ S) (he : cmp α γ = .eq)
    (hτξ : Lt τ ξ) (hC : inC τ γ (.Psi ξ π γ) = true) :
    Lt (.Psi τ π α) (.Psi ξ π γ) :=
  (lt_psi_psiY rfl (P.ne_of_mem hq)).mpr (Or.inr ⟨lt_psi_targetY P.ht,
    lt_psi_targetY (P.G.nf _ hq), Or.inr (Or.inr (Or.inl ⟨he, rfl, hτξ, hC⟩))⟩)

/-- `Ξ_m(f) < t` の条件 -/
theorem xi_lt_t {m : Nat} {f : Tm} (hX : Tm.Xi m f ∈ S) (hl : lev π = m)
    (hXπ : Lt (.Xi m f) π)
    (hfr : Lt f γ → ∀ u, u ∈ fr (.K m) f → Lt u (.Psi ξ π γ)) :
    Lt (.Xi m f) (.Psi ξ π γ) := by
  have G := P.G
  have hfS := G.sub hX (mem_subs_xi m f)
  rw [lt_xi_psiY hl, lt_psi_xiY hl]
  rintro (h | ⟨hfγ, hn⟩)
  · apply h
    unfold Lt at hXπ
    rw [G.swap hX P.πS, hXπ]
    decide
  · rw [inC_of_fr f (G.nf _ hX).xi.2.2.2.2 (fun v hv h' => G.trans (G.sub hfS hv) hfS P.γS h' hfγ)
      (fun u hu => inC_of_lt_node (fr_node hu) (hfr hfγ u hu))] at hn
    cases hn

theorem xi_lt_t_inv {m : Nat} {f : Tm} (hX : Tm.Xi m f ∈ S) (hl : lev π = m)
    (h : Lt (.Xi m f) (.Psi ξ π γ)) :
    Lt (.Xi m f) π ∧ (Lt f γ → inC f γ (.Psi ξ π γ) = true) := by
  rw [lt_xi_psiY hl, lt_psi_xiY hl] at h
  refine ⟨P.G.lt_of_gt P.πS hX ?_, fun hfγ => ?_⟩
  · cases e : cmp π (Tm.Xi m f)
    · exact absurd (Or.inl (by rw [e]; decide)) h
    · exact absurd (Or.inl (by rw [e]; decide)) h
    · rfl
  · cases e : inC f γ (Tm.Psi ξ π γ)
    · exact absurd (Or.inr ⟨hfγ, e⟩) h
    · rfl

/-- 前線の証人：`γ ≤ g` で `γ`・`ξ`・`π` のどれかが `C(g, d)` に入らなければ、その前線に `d` 未満でない元がある -/
theorem wit {g d : Tm} (hg : Le γ g) (hgS : g ∈ S)
    (hn : ¬ (inC γ g d = true ∧ inC ξ g d = true ∧ inC π g d = true)) :
    ∃ w, (w ∈ fr π γ ∨ w ∈ fr π π ∨ w ∈ fr π ξ) ∧ ¬ Lt w d := by
  have G := P.G
  have hP := P.ht.psi
  cases e1 : inC γ g d
  · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hP.Ca
      (fun v hv h => G.lt_of_lt_of_le (G.sub P.γS hv) P.γS hgS h hg) e1
    exact ⟨w, Or.inl hw, hwn⟩
  · cases e2 : inC ξ g d
    · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hP.Cxi
        (fun v hv h => G.lt_of_lt_of_le (G.sub P.ξS hv) P.γS hgS h hg) e2
      exact ⟨w, Or.inr (Or.inr hw), hwn⟩
    · cases e3 : inC π g d
      · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hP.Cpi
          (fun v hv h => G.lt_of_lt_of_le (G.sub P.πS hv) P.γS hgS h hg) e3
        exact ⟨w, Or.inr (Or.inl hw), hwn⟩
      · exact absurd ⟨e1, e2, e3⟩ hn

/-- 前線の証人（(4) の形）：`ξ < τ` で `ξ ∉ C(τ, d)` なら、`ξ` の前線（`π` について）に `d` 未満でない元がある -/
theorem wit4 {τ d : Tm} (hτS : τ ∈ S) (hξτ : Lt ξ τ) (hn : inC ξ τ d = false) :
    ∃ w, w ∈ fr π ξ ∧ ¬ Lt w d :=
  wit_of_not_inC P.mi (fun _ hv h => P.G.trans (P.G.sub P.ξS hv) P.ξS hτS h hξτ) hn

theorem F_spec {w : Tm} (hw : w ∈ fr π γ ∨ w ∈ fr π π ∨ w ∈ fr π ξ) : w ∈ S ∧ Lt w π := by
  rcases hw with hw | hw | hw
  · exact ⟨P.G.sub P.γS (fr_spec hw).1, (fr_spec hw).2⟩
  · exact ⟨P.G.sub P.πS (fr_spec hw).1, (fr_spec hw).2⟩
  · exact ⟨P.G.sub P.ξS (fr_spec hw).1, (fr_spec hw).2⟩

/-- 前線の元は `HCv` の一つ目の形を満たす -/
theorem hcF {w : Tm} (hw : w ∈ fr π γ ∨ w ∈ fr π π ∨ w ∈ fr π ξ) (N : Nat) :
    HCv S ξ π γ w N := by
  have G := P.G
  refine Or.inl (fun ρ' β' hρ'S _ hρ'π h1 h2 h3 => ?_)
  have hd : ∀ x, x ∈ S → ∀ v, v ∈ subs x → ¬ Lt v π → ¬ Lt v ρ' := fun x hx v hv hvπ hvρ =>
    hvπ (G.trans (G.sub hx hv) hρ'S P.πS hvρ hρ'π)
  rcases hw with hw | hw | hw
  · exact fr_of_inC γ (hd γ P.γS) h1 w hw
  · exact fr_of_inC π (hd π P.πS) h3 w hw
  · exact fr_of_inC ξ (hd ξ P.ξS) h2 w hw

/-! ### `t` 未満の元は `π` 未満 -/

theorem tb_aux : ∀ N, ∀ z, z ∈ S → z.size ≤ N →
    (Lt z (.Psi ξ π γ) → Lt z π) ∧
      (isPrincipal z = true → ¬ Lt (.Psi ξ π γ) z → Lt z π) := by
  have G := P.G
  have hπp := P.hT.principal
  have hπb := P.hT.not_bot
  intro N
  induction N with
  | zero => intro z _ h; exact absurd h (by have := Tm.size_pos z; omega)
  | succ N ih =>
    have prin : ∀ y, y ∈ S → y.size ≤ N + 1 → isPrincipal y = true →
        (Lt y (.Psi ξ π γ) → Lt y π) ∧ (¬ Lt (.Psi ξ π γ) y → Lt y π) := by
      intro y hy hs hyp
      have hyF := G.nf y hy
      by_cases hl1 : lev y < lev π
      · exact ⟨fun _ => lt_of_lev_lt' hl1, fun _ => lt_of_lev_lt' hl1⟩
      by_cases hl2 : lev π < lev y
      · refine ⟨fun h => absurd (lev_le_of_lt_gen h) (by simp only [lev]; omega),
          fun h => absurd (lt_of_lev_lt' (by simp only [lev]; omega)) h⟩
      have hl : lev y = lev π := by omega
      by_cases hb : isBot y = true
      · have := bot_ltY hb (Nat.le_of_eq hl) hπp hπb P.πF
        exact ⟨fun _ => this, fun _ => this⟩
      rcases shape_prin hyF hyp (Bool.eq_false_iff.mpr hb) with
        ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨τ, ρ, δ, rfl⟩
      · have hx := G.sub hy (mem_subs_om x)
        have ihx := ih x hx (by simp only [Tm.size] at hs; omega)
        rcases P.ht.shape with ⟨c, rfl, rfl⟩ | hsh
        · have hcS := G.sub P.πS (mem_subs_om c)
          have hl' : lev x = lev c := hl
          refine ⟨fun h => (G.lt_om_iffS hx hcS).mpr ((lt_om_psiY P.ht).mp h), fun h => ?_⟩
          refine (G.lt_om_iffS hx hcS).mpr ?_
          by_cases hxc : Lt x c
          · exact hxc
          · exact absurd ((psiOm_lt_om_iff hl').mpr hxc) h
        · have hOF := IsOF.psi P.ht (notOm_of_shape hsh)
          have hπOF : IsOF π := by
            rcases P.hT.cases P.πF with ⟨c, e⟩ | h
            · exact absurd e (notOm_of_shape hsh c)
            · exact h
          have hl' : lev x = lev (Tm.Psi ξ π γ) := hl
          refine ⟨fun h => (lt_om_OFG hπOF).mpr (ihx.1 ((lt_om_OFG hOF).mp h)), fun h => ?_⟩
          refine (lt_om_OFG hπOF).mpr (ihx.1 (P.lt_of_ne_gt hx ?_))
          intro e
          exact h ((OF_lt_om_iff hOF hl').mpr e)
      · have hl' : lev π = m := hl.symm
        have key : ¬ Lt (.Psi ξ π γ) (.Xi m f) → Lt (.Xi m f) π := fun h => by
          rw [lt_psi_xiY hl'] at h
          refine G.lt_of_gt P.πS hy ?_
          cases e : cmp π (Tm.Xi m f)
          · exact absurd (Or.inl (by rw [e]; decide)) h
          · exact absurd (Or.inl (by rw [e]; decide)) h
          · rfl
        exact ⟨fun h => key ((lt_xi_psiY hl').mp h), key⟩
      · have hyF' := hyF.psi
        have hρS : ρ ∈ S := G.sub hy (by simp [subs, self_mem_subs])
        have hl' : lev ρ = lev π := hl
        have hne := P.ne_of_mem hy
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rcases (lt_psi_psiY hl' hne).mp h with h' | ⟨-, h', -⟩
          · have := (ih ρ hρS (by simp only [Tm.size] at hs; omega)).2 hyF'.tgt.principal h'
            exact G.trans hy hρS P.πS (lt_psi_targetY hyF) this
          · exact h'
        · by_cases h' : Lt (.Psi τ ρ δ) π
          · exact h'
          · exact absurd ((lt_psi_psiY hl'.symm (fun e => hne e.symm)).mpr (Or.inl h')) h
    intro z hz hs
    have hzF := G.nf z hz
    refine ⟨fun hzt => ?_, fun hzp => (prin z hz hs hzp).2⟩
    cases hsz : summands z with
    | nil =>
      have : z = .zero := by cases z <;> simp_all [summands]
      subst this
      exact zero_lt P.hT.ne_zero
    | cons h rest =>
      have hmem : h ∈ summands z := by rw [hsz]; exact List.mem_cons_self
      have hhS := G.sub hz (mem_subs_of_mem_summands hmem)
      obtain ⟨-, hhp⟩ := summands_WNF z hzF h hmem
      have hhs := size_le_of_mem_summands z h hmem
      have hht : Lt h (.Psi ξ π γ) :=
        (lt_principal_iff hhp rfl).mpr (cmpP_head_of_lt hsz rfl hzt)
      have := (prin h hhS (by omega) hhp).1 hht
      exact lt_of_head_lt hπp hsz ((lt_principal_iff hhp hπp).mp this)

/-- `t` 未満の `S` の元は `π` 未満 -/
theorem tb {z : Tm} (hz : z ∈ S) (h : Lt z (.Psi ξ π γ)) : Lt z π :=
  (P.tb_aux _ z hz (Nat.le_refl _)).1 h

/-- `t` が上にない主要項は `π` 未満 -/
theorem tbge {z : Tm} (hz : z ∈ S) (hzp : isPrincipal z = true)
    (h : ¬ Lt (.Psi ξ π γ) z) : Lt z π :=
  (P.tb_aux _ z hz (Nat.le_refl _)).2 hzp h

/-! ### `t < ρ ≤ v < π` の矛盾 -/

theorem tgt_contra_aux : ∀ M, ∀ ρ v, ρ ∈ S → ρ.size ≤ M → IsTgt ρ → lev ρ = lev π →
    Lt (.Psi ξ π γ) ρ → v ∈ S → Le ρ v → Lt v π →
    (∀ u, u ∈ S → u.size < ρ.size → Lt u v → Lt u (.Psi ξ π γ)) →
    HCv S ξ π γ v ρ.size → False := by
  have G := P.G
  intro M
  induction M with
  | zero => intro ρ v _ h; exact absurd h (by have := Tm.size_pos ρ; omega)
  | succ M ihM =>
  intro ρ v hρS hρM hρT hl htρ hvS hρv hvπ H hC
  rcases hρT with ⟨d, rfl, -⟩ | ⟨m, r, rfl⟩ | ⟨σ, κ', β, rfl, hσ⟩
  · -- `ρ = Ω_d`
    have hdS := G.sub hρS (mem_subs_om d)
    rcases P.ht.shape with ⟨c, rfl, rfl⟩ | hsh
    · have hl' : lev d = lev c := hl
      have hcS := G.sub P.πS (mem_subs_om c)
      exact (psiOm_lt_om_iff hl').mp htρ
        ((G.lt_om_iffS hdS hcS).mp (G.lt_of_le_of_lt hρS hvS P.πS hρv hvπ))
    · have hOF := IsOF.psi P.ht (notOm_of_shape hsh)
      have hl' : lev d = lev (Tm.Psi ξ π γ) := hl
      have e := (OF_lt_om_iff hOF hl').mp htρ
      have hdv : Lt d v := G.lt_of_lt_of_le hdS hρS hvS (G.nf _ hρS).om.2.2 hρv
      have := H d hdS (by simp only [Tm.size]; omega) hdv
      unfold Lt at this
      rw [this] at e
      cases e
  · -- `ρ = Ξ_m(r)`
    have hrS := G.sub hρS (mem_subs_xi m r)
    have hl' : lev π = m := hl.symm
    rcases (lt_psi_xiY hl').mp htρ with h | ⟨hrγ, hn⟩
    · apply h
      have := G.lt_of_le_of_lt hρS hvS P.πS hρv hvπ
      unfold Lt at this
      rw [G.swap hρS P.πS, this]
      decide
    · obtain ⟨u, hu, hun⟩ := wit_of_not_inC (G.nf _ hρS).xi.2.2.2.2
        (fun w hw h' => G.trans (G.sub hrS hw) hrS P.γS h' hrγ) hn
      have huS := G.sub hrS (fr_spec hu).1
      have := size_le_of_mem_subs (fr_spec hu).1
      exact hun (H u huS (by simp only [Tm.size]; omega)
        (G.lt_of_lt_of_le huS hρS hvS (G.k2x m r hρS u hu) hρv))
  · -- `ρ = Ψ^σ_κ'(β)`
    have hρF := G.nf _ hρS
    have hρP := hρF.psi
    have hκS : κ' ∈ S := G.sub hρS (by simp [subs, self_mem_subs])
    have hσS : σ ∈ S := G.sub hρS (by simp [subs, self_mem_subs])
    have hβS := G.sub hρS (mem_subs_psi_a _ _ β)
    have hlκ : lev κ' = lev π := hl
    have hρπ : Lt (.Psi σ κ' β) π := G.lt_of_le_of_lt hρS hvS P.πS hρv hvπ
    have hne : Tm.Psi ξ π γ ≠ .Psi σ κ' β := fun e => P.ne_of_mem hρS e.symm
    -- 証人 `u < ρ` で `u < t` でないものがあれば矛盾
    have viaU : ∀ u, u ∈ S → u.size < (Tm.Psi σ κ' β).size → Lt u (.Psi σ κ' β) →
        ¬ Lt u (.Psi ξ π γ) → False :=
      fun u hu hus hur hun => hun (H u hu hus (G.lt_of_lt_of_le hu hρS hvS hur hρv))
    -- `t` の成分が `C(β, ρ)` に入り `v < κ'` なら矛盾
    have viaHC : inC γ β (.Psi σ κ' β) = true → inC ξ β (.Psi σ κ' β) = true →
        inC π β (.Psi σ κ' β) = true → Lt v κ' → False := fun h1 h2 h3 hvκ => by
      rcases hC with hC | ⟨-, hC⟩
      · exact G.not_lt_of_le hρS hvS hρv (G.coll_psiS hρS v hvS
          (hC _ β hρS (Nat.le_refl _) hρπ h1 h2 h3) hvκ)
      · obtain ⟨hρt, hA⟩ := hC _ hρS (Nat.le_refl _) hρv
        unfold Lt at hρt htρ
        rw [hA.1, htρ] at hρt
        exact absurd hρt (by decide)
    rcases (lt_psi_psiY hlκ.symm hne).mp htρ with h1 | ⟨-, htκ, hc⟩
    · exact h1 hρπ
    · rcases hc with ⟨-, hinγ, hinξ, hinπ⟩ | ⟨hβγ, hn⟩ | ⟨he, e, -, hinξ⟩ | ⟨hσξ, hn⟩
      · -- (1)
        by_cases hvκ : Lt v κ'
        · exact viaHC hinγ hinξ hinπ hvκ
        · exact ihM κ' v hκS (by simp only [Tm.size] at hρM; omega) hρP.tgt hlκ htκ hvS
            (G.le_of_not_lt hvS hκS hvκ) hvπ
            (fun u hu hus huv => H u hu (by simp only [Tm.size]; omega) huv)
            (hC.mono (by simp only [Tm.size]; omega))
      · -- (2)：`ρ` の前線の証人
        have hβγ' : Le β γ := G.le_of_ne_gt hβS P.γS hβγ
        have hg : ∀ x, x ∈ S → ∀ v, v ∈ subs x → Lt v β → Lt v γ := fun x hx v hv h =>
          G.lt_of_lt_of_le (G.sub hx hv) hβS P.γS h hβγ'
        cases e1 : inC β γ (Tm.Psi ξ π γ)
        · obtain ⟨u, hu, hun⟩ := wit_of_not_inC hρP.Ca (hg β hβS) e1
          have := size_le_of_mem_subs (fr_spec hu).1
          exact viaU u (G.sub hβS (fr_spec hu).1) (by simp only [Tm.size]; omega)
            (G.k2 _ _ _ hρS u hu) hun
        · cases e2 : inC σ γ (Tm.Psi ξ π γ)
          · obtain ⟨u, hu, hun⟩ := wit_of_not_inC hρP.Cxi (hg σ hσS) e2
            have := size_le_of_mem_subs (fr_spec hu).1
            exact viaU u (G.sub hσS (fr_spec hu).1) (by simp only [Tm.size]; omega)
              (G.k2s _ _ _ hρS u hu) hun
          · cases e3 : inC κ' γ (Tm.Psi ξ π γ)
            · obtain ⟨u, hu, hun⟩ := wit_of_not_inC hρP.Cpi (hg κ' hκS) e3
              have := size_le_of_mem_subs (fr_spec hu).1
              exact viaU u (G.sub hκS (fr_spec hu).1) (by simp only [Tm.size]; omega)
                (G.k2t _ _ _ hρS u hu) hun
            · exact absurd ⟨e1, e2, e3⟩ hn
      · -- (3)：`β = γ`、`κ' = π`
        have hγβ := G.eq P.γS hβS he
        subst hγβ
        have hvκ : Lt v κ' := by rw [e]; exact hvπ
        exact viaHC (G.inC_argS hρS) hinξ (by rw [← e]; exact G.inC_tgtS hρS) hvκ
      · -- (4)：`ρ` の Mahlo 添字の前線の証人
        obtain ⟨u, hu, hun⟩ := wit_of_not_inC (G.miS hρS)
          (fun w hw h => G.trans (G.sub hσS hw) hσS P.ξS h hσξ) hn
        have := size_le_of_mem_subs (fr_spec hu).1
        exact viaU u (G.sub hσS (fr_spec hu).1) (by simp only [Tm.size]; omega)
          (G.k2s _ _ _ hρS u hu) hun

theorem tgt_contra {ρ v : Tm} (hρS : ρ ∈ S) (hρT : IsTgt ρ) (hl : lev ρ = lev π)
    (htρ : Lt (.Psi ξ π γ) ρ) (hvS : v ∈ S) (hρv : Le ρ v) (hvπ : Lt v π)
    (H : ∀ u, u ∈ S → u.size < ρ.size → Lt u v → Lt u (.Psi ξ π γ))
    (hC : HCv S ξ π γ v ρ.size) : False :=
  P.tgt_contra_aux _ ρ v hρS (Nat.le_refl _) hρT hl htρ hvS hρv hvπ H hC

/-! ### `π = Ω_c` のとき：`c` 未満なら `t` 未満 -/

theorem below_aux {c : Tm} (hπ : π = .Om c) : ∀ N, ∀ v, v ∈ S → v.size ≤ N →
    Lt v c → Lt v (.Psi ξ π γ) := by
  subst hπ
  have hξ0 : ξ = .zero := P.ht.psiOm.2.2.2.2.2
  subst hξ0
  have G := P.G
  have hcS := G.sub P.πS (mem_subs_om c)
  have hcΩ : Lt c (.Om c) := P.πF.om.2.2
  have hsc : isSucc c = true := P.ht.psiOm.2.2.1
  intro N
  induction N with
  | zero => intro v _ h; exact absurd h (by have := Tm.size_pos v; omega)
  | succ N ih =>
    intro v hvS hs hvc
    have hvF := G.nf _ hvS
    cases hsv : summands v with
    | nil =>
      have : v = .zero := by cases v <;> simp_all [summands]
      subst this
      exact zero_lt (by intro e; cases e)
    | cons h rest =>
      have hmem : h ∈ summands v := by rw [hsv]; exact List.mem_cons_self
      have hhS := G.sub hvS (mem_subs_of_mem_summands hmem)
      obtain ⟨hhF, hhp⟩ := summands_WNF v hvF h hmem
      have hhs := size_le_of_mem_summands v h hmem
      have hhc : Lt h c := G.lt_of_le_of_lt hhS hvS hcS (head_leY hvF hsv) hvc
      have IH : ∀ u, u ∈ S → u.size < h.size → Lt u c → Lt u (.Psi .zero (.Om c) γ) :=
        fun u hu hus huc => ih u hu (by omega) huc
      have hht : Lt h (.Psi .zero (.Om c) γ) := by
        have hl := lev_le_of_lt_gen hhc
        rcases Nat.lt_or_eq_of_le hl with hl | hl
        · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
        by_cases hb : isBot h = true
        · exact bot_ltY hb (by simp only [lev]; omega) rfl rfl P.ht
        rcases shape_prinOF hhF hhp (Bool.eq_false_iff.mpr hb) with
          ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨d, δ, rfl⟩ | ⟨τ, ρ, δ, rfl, -⟩
        · have hx := G.sub hhS (mem_subs_om x)
          exact (lt_om_psiY P.ht).mpr (G.trans hx hhS hcS hhF.om.2.2 hhc)
        · simp only [lev] at hl
          refine P.xi_lt_t hhS hl.symm (G.trans hhS hcS P.πS hhc hcΩ) (fun _ u hu => ?_)
          have hfS := G.sub hhS (mem_subs_xi m f)
          have huS := G.sub hfS (fr_spec hu).1
          have := size_le_of_mem_subs (fr_spec hu).1
          exact IH u huS (by simp only [Tm.size]; omega)
            (G.trans huS hhS hcS (G.k2x m f hhS u hu) hhc)
        · have hdS := G.sub hhS (mem_subs_psi_c _ d δ)
          have hdc := G.trans hdS hhS hcS (G.cx d δ hhS) hhc
          simp only [lev] at hl
          exact P.psi_lt_of_tgt hhS hl (fun h' => (psiOm_lt_om_iff hl).mp h' hdc)
        · simp only [lev] at hl
          have hρS : ρ ∈ S := G.sub hhS (by simp [subs, self_mem_subs])
          have hτS : τ ∈ S := G.sub hhS (by simp [subs, self_mem_subs])
          have hδS := G.sub hhS (mem_subs_psi_a _ _ δ)
          have hhπ : Lt (.Psi τ ρ δ) (.Om c) := G.trans hhS hcS P.πS hhc hcΩ
          have hP := hhF.psi
          by_cases htρ' : ¬ Lt (.Psi .zero (.Om c) γ) ρ
          · exact P.psi_lt_of_tgt hhS hl htρ'
          have htρ : Lt (.Psi .zero (.Om c) γ) ρ := Decidable.of_not_not htρ'
          -- `c < ρ`（`ρ ≤ c` なら `t < ρ ≤ c < Ω_c` の矛盾）
          have hcρ : Lt c ρ := by
            rcases G.tri hcS hρS with h' | e | h'
            · exact h'
            · exfalso; subst e; exact not_tgt_of_succ hsc hP.tgt
            · exfalso
              refine P.tgt_contra hρS hP.tgt hl htρ hcS (Or.inr h') hcΩ
                (fun u hu hus huc => IH u hu (by simp only [Tm.size]; omega) huc)
                (Or.inl (fun ρ' β' _ _ _ _ _ h3 => by rw [inC_om] at h3; exact h3))
          have frIH : ∀ x, x ∈ S → x.size < (Tm.Psi τ ρ δ).size →
              (∀ w, w ∈ fr ρ x → Lt w (.Psi τ ρ δ)) →
              ∀ u, u ∈ fr ρ x → inC u γ (.Psi .zero (.Om c) γ) = true :=
            fun x hx hxs hk u hu => by
              refine inC_of_lt_node (fr_node hu) ?_
              have huS := G.sub hx (fr_spec hu).1
              have := size_le_of_mem_subs (fr_spec hu).1
              exact IH u huS (by omega) (G.trans huS hhS hcS (hk u hu) hhc)
          rcases G.tri hδS P.γS with h' | h' | h'
          · refine P.psi_lt_of_c1 hhS hl htρ hhπ h' ?_ ?_ ?_
            · exact inC_of_fr δ hP.Ca (fun v hv hv' => G.trans (G.sub hδS hv) hδS P.γS hv' h')
                (frIH δ hδS (by simp only [Tm.size]; omega) (G.k2 _ _ δ hhS))
            · exact inC_of_fr τ hP.Cxi (fun v hv hv' => G.trans (G.sub hτS hv) hδS P.γS hv' h')
                (frIH τ hτS (by simp only [Tm.size]; omega) (G.k2s _ _ δ hhS))
            · exact inC_of_fr _ hP.Cpi (fun v hv hv' => G.trans (G.sub hρS hv) hδS P.γS hv' h')
                (frIH _ hρS (by simp only [Tm.size]; omega) (G.k2t _ _ δ hhS))
          all_goals
            refine P.psi_lt_of_c2 hhS hl htρ hhπ (ne_gt_of_le ?_) (fun ⟨_, _, hin⟩ => ?_)
            · first | exact Or.inl h'.symm | exact Or.inr h'
            · rw [inC_om] at hin
              exact G.asymm hcS hhS (G.coll_psiS hhS c hcS hin hcρ) hhc
      exact lt_of_head_lt rfl hsv ((lt_principal_iff hhp rfl).mp hht)

/-- `π = Ω_c` なら、`c` 未満の `S` の元は `t` 未満 -/
theorem below {c v : Tm} (hπ : π = .Om c) (hv : v ∈ S) (h : Lt v c) : Lt v (.Psi ξ π γ) :=
  P.below_aux hπ _ v hv (Nat.le_refl _) h

/-! ### 補題 A -/

/-- 補題 A の主要項の場合 -/
theorem lemA_head {h w : Tm} (hhS : h ∈ S) (hhp : isPrincipal h = true)
    (hw : w ∈ fr π γ ∨ w ∈ fr π π ∨ w ∈ fr π ξ) (hhw : Le h w)
    (IH : ∀ u, u ∈ S → u.size < h.size → Le u w → Lt u (.Psi ξ π γ)) :
    Lt h (.Psi ξ π γ) := by
  have G := P.G
  have hhF := G.nf _ hhS
  obtain ⟨hwS, hwπ⟩ := P.F_spec hw
  have hhπ : Lt h π := G.lt_of_le_of_lt hhS hwS P.πS hhw hwπ
  have hl := lev_le_of_lt_gen hhπ
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
  by_cases hb : isBot h = true
  · exact bot_ltY hb (by simp only [lev]; omega) rfl rfl P.ht
  rcases shape_prin hhF hhp (Bool.eq_false_iff.mpr hb) with ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨τ, ρ, δ, rfl⟩
  · have hx := G.sub hhS (mem_subs_om x)
    rcases P.ht.shape with ⟨c, rfl, rfl⟩ | hsh
    · have hcS := G.sub P.πS (mem_subs_om c)
      exact (lt_om_psiY P.ht).mpr ((G.lt_om_iffS hx hcS).mp hhπ)
    · exact (lt_om_OFG (IsOF.psi P.ht (notOm_of_shape hsh))).mpr
        (IH x hx (by simp only [Tm.size]; omega)
          (Or.inr (G.lt_of_lt_of_le hx hhS hwS hhF.om.2.2 hhw)))
  · simp only [lev] at hl
    refine P.xi_lt_t hhS hl.symm hhπ (fun _ u hu => ?_)
    have hfS := G.sub hhS (mem_subs_xi m f)
    have huS := G.sub hfS (fr_spec hu).1
    have := size_le_of_mem_subs (fr_spec hu).1
    exact IH u huS (by simp only [Tm.size]; omega)
      (Or.inr (G.lt_of_lt_of_le huS hhS hwS (G.k2x m f hhS u hu) hhw))
  · have hρS : ρ ∈ S := G.sub hhS (by simp [subs, self_mem_subs])
    have hτS : τ ∈ S := G.sub hhS (by simp [subs, self_mem_subs])
    have hδS := G.sub hhS (mem_subs_psi_a _ _ δ)
    have hP := hhF.psi
    have hl' : lev ρ = lev π := hl
    by_cases htρ' : ¬ Lt (.Psi ξ π γ) ρ
    · exact P.psi_lt_of_tgt hhS hl' htρ'
    have htρ : Lt (.Psi ξ π γ) ρ := Decidable.of_not_not htρ'
    have frIH : ∀ x, x ∈ S → x.size < (Tm.Psi τ ρ δ).size →
        (∀ u, u ∈ fr ρ x → Lt u (.Psi τ ρ δ)) →
        ∀ u, u ∈ fr ρ x → inC u γ (.Psi ξ π γ) = true :=
      fun x hx hxs hk u hu => by
        refine inC_of_lt_node (fr_node hu) ?_
        have huS := G.sub hx (fr_spec hu).1
        have := size_le_of_mem_subs (fr_spec hu).1
        exact IH u huS (by omega) (Or.inr (G.lt_of_lt_of_le huS hhS hwS (hk u hu) hhw))
    rcases G.tri hδS P.γS with h' | h' | h'
    · refine P.psi_lt_of_c1 hhS hl' htρ hhπ h' ?_ ?_ ?_
      · exact inC_of_fr δ hP.Ca (fun v hv hv' => G.trans (G.sub hδS hv) hδS P.γS hv' h')
          (frIH δ hδS (by simp only [Tm.size]; omega) (G.k2 _ _ δ hhS))
      · exact inC_of_fr τ hP.Cxi (fun v hv hv' => G.trans (G.sub hτS hv) hδS P.γS hv' h')
          (frIH τ hτS (by simp only [Tm.size]; omega) (G.k2s _ _ δ hhS))
      · exact inC_of_fr ρ hP.Cpi (fun v hv hv' => G.trans (G.sub hρS hv) hδS P.γS hv' h')
          (frIH ρ hρS (by simp only [Tm.size]; omega) (G.k2t _ _ δ hhS))
    all_goals
      -- `w < ρ`
      have hwρ : Lt w ρ := by
        rcases G.tri hwS hρS with e | e | e
        · exact e
        all_goals
          exfalso
          refine P.tgt_contra hρS hP.tgt hl' htρ hwS (by first | exact Or.inl e.symm | exact Or.inr e)
            hwπ (fun u hu hus huw => IH u hu (by simp only [Tm.size]; omega) (Or.inr huw))
            (P.hcF hw _)
      refine P.psi_lt_of_c2 hhS hl' htρ hhπ
        (ne_gt_of_le (by first | exact Or.inl h'.symm | exact Or.inr h'))
        (fun ⟨hin1, hin2, hin3⟩ => ?_)
      have hd : ∀ x, x ∈ S → ∀ w', w' ∈ subs x → ¬ Lt w' π →
          ¬ Lt w' (.Psi τ ρ δ) := fun x hx w' hw' hn hlt =>
        hn (G.trans (G.sub hx hw') hhS P.πS hlt hhπ)
      have hinw : inC w δ (.Psi τ ρ δ) = true := by
        rcases hw with hw | hw | hw
        · exact fr_of_inC γ (hd γ P.γS) hin1 w hw
        · exact fr_of_inC π (hd π P.πS) hin3 w hw
        · exact fr_of_inC ξ (hd ξ P.ξS) hin2 w hw
      exact G.not_lt_of_le hhS hwS hhw (G.coll_psiS hhS w hwS hinw hwρ)

/-- 補題 A：`γ`・`π`・`ξ` の前線のどれか以下の `S` の元は `t` 未満 -/
theorem lemA_aux : ∀ N, ∀ v, v ∈ S → v.size ≤ N →
    (∃ w, (w ∈ fr π γ ∨ w ∈ fr π π ∨ w ∈ fr π ξ) ∧ Le v w) → Lt v (.Psi ξ π γ) := by
  have G := P.G
  intro N
  induction N with
  | zero => intro v _ h; exact absurd h (by have := Tm.size_pos v; omega)
  | succ N ih =>
    intro v hvS hs ⟨w, hw, hvw⟩
    have hvF := G.nf _ hvS
    obtain ⟨hwS, -⟩ := P.F_spec hw
    cases hsv : summands v with
    | nil =>
      have : v = .zero := by cases v <;> simp_all [summands]
      subst this
      exact zero_lt (by intro e; cases e)
    | cons h rest =>
      have hmem : h ∈ summands v := by rw [hsv]; exact List.mem_cons_self
      have hhS := G.sub hvS (mem_subs_of_mem_summands hmem)
      obtain ⟨-, hhp⟩ := summands_WNF v hvF h hmem
      have hhs := size_le_of_mem_summands v h hmem
      have hhw : Le h w := G.le_trans hhS hvS hwS (head_leY hvF hsv) hvw
      have hht := P.lemA_head hhS hhp hw hhw (fun u hu hus huw => ih u hu (by omega) ⟨w, hw, huw⟩)
      exact lt_of_head_lt rfl hsv ((lt_principal_iff hhp rfl).mp hht)

theorem lemA {v : Tm} (hv : v ∈ S)
    (h : ∃ w, (w ∈ fr π γ ∨ w ∈ fr π π ∨ w ∈ fr π ξ) ∧ Le v w) : Lt v (.Psi ξ π γ) :=
  P.lemA_aux _ v hv (Nat.le_refl _) h

/-- K2：`γ` の前線は全て `t` 未満 -/
theorem k2 : ∀ w, w ∈ fr π γ → Lt w (.Psi ξ π γ) := fun w hw =>
  P.lemA (P.F_spec (Or.inl hw)).1 ⟨w, Or.inl hw, Le.refl _⟩

/-- K2T：`π` の前線は全て `t` 未満 -/
theorem k2t : ∀ w, w ∈ fr π π → Lt w (.Psi ξ π γ) := fun w hw =>
  P.lemA (P.F_spec (Or.inr (Or.inl hw))).1 ⟨w, Or.inr (Or.inl hw), Le.refl _⟩

/-- K2S：`ξ` の前線は全て `t` 未満 -/
theorem k2s : ∀ w, w ∈ fr π ξ → Lt w (.Psi ξ π γ) := fun w hw =>
  P.lemA (P.F_spec (Or.inr (Or.inr hw))).1 ⟨w, Or.inr (Or.inr hw), Le.refl _⟩

/-- CX：`π = Ω_c` なら `c < t` -/
theorem cx {c : Tm} (hπ : π = .Om c) : Lt c (.Psi ξ π γ) := by
  have G := P.G
  have hΩS : Tm.Om c ∈ S := hπ ▸ P.πS
  have hcS := G.sub hΩS (mem_subs_om c)
  have hΩF := G.nf _ hΩS
  have hs : isSucc c = true := by
    rcases P.hT with ⟨c', e, hs⟩ | ⟨n, r, e⟩ | ⟨ζ, κ, b, e, -⟩
    · rw [hπ] at e; cases e; exact hs
    · rw [hπ] at e; cases e
    · rw [hπ] at e; cases e
  have hlt : lev c = lev π := by rw [hπ]; rfl
  cases c with
  | one => exact bot_ltY rfl (Nat.le_of_eq hlt) rfl rfl P.ht
  | plus a b =>
    have hcF := G.nf _ hcS
    obtain ⟨-, -, hap, -⟩ := hcF.plus
    have haS := G.sub hcS (show a ∈ subs (.plus a b) by simp [subs, self_mem_subs])
    have haF := G.nf _ haS
    have hac : Lt a (.plus a b) := lt_plus_leftY hcF
    have haΩ : Lt a (.Om (.plus a b)) := G.trans haS hcS hΩS hac hΩF.om.2.2
    have hat : Lt a (.Psi ξ π γ) := by
      have hl : lev a = lev π := hlt
      by_cases hb : isBot a = true
      · exact bot_ltY hb (Nat.le_of_eq hl) rfl rfl P.ht
      rcases shape_prin haF hap (Bool.eq_false_iff.mpr hb) with
        ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨τ, ρ, δ, rfl⟩
      · have hx := G.sub haS (mem_subs_om x)
        have hxc := G.trans hx haS hcS haF.om.2.2 hac
        have ht' := P.ht
        rw [hπ] at ht' ⊢
        have hξ0 := ht'.psiOm.2.2.2.2.2
        subst hξ0
        exact (lt_om_psiY ht').mpr hxc
      · refine P.k2t _ ?_
        rw [hπ]
        simp [fr, haΩ]
      · refine P.k2t _ ?_
        rw [hπ]
        simp [fr, haΩ]
    exact lt_of_head_lt rfl (summands_plus a b) ((lt_principal_iff hap rfl).mp hat)
  | _ => simp [isSucc, summands] at hs

end PsiCtxY

/-! ## 新しい項が `t = Ψ^ξ_π(γ)` の場合の切断性と反対称性

目標が `Ψ` になりうるので、`t` と `S` の `Ψ` の反対称性と `t` の切断性を、`S` の元の大きさについて同時に示す。
大きさ `M` 未満の元との反対称性から、大きさ `M` 以下の組の切断性（`cut_le`）が出て、それと大きさ `M` 未満の元との
反対称性から、大きさ `M` の `Ψ` との反対称性（`psi_swap_le`）が出る。

切断性の帰納法の測度は、組の大きさの最大値と和の辞書式順序。`p = Ψ^τ_ρ(δ) < t` を Prop. 4.20 の
(1)〜(4) で分け、(2)・(4) は `t` の前線の証人（補題 A）、(1)・(3) は `p` の前線が `t` 未満であること
（`p` の真部分項どうしの切断性）を使う。 -/

/-- 大きさ `M` 以下の組についての `t` の切断性 -/
def CutLe (S : List Tm) (t : Tm) (M : Nat) : Prop :=
  ∀ a b, a ∈ S → b ∈ S → a.size ≤ M → b.size ≤ M → Lt b a → Lt a t → Lt b t

/-- 切断性：主要項の組についての切断性から一般の切断性へ（組の大きさの最大値と和の辞書式の帰納法。
    大きさ `M` 以下の組に限る）。`ihA` は `p` より小さい項どうし、`ihB` は大きさがどちらも `p`・`q` の大きい方
    以下で和が小さい組。 -/
theorem GoodY.cut_le_of_principal_lex {S : List Tm} (G : GoodY S) {t : Tm} (ht : WNF t)
    (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S) (M : Nat)
    (hP : ∀ q p, q ∈ S → p ∈ S → q.size ≤ M → p.size ≤ M → isPrincipal t = true →
      isPrincipal q = true → isPrincipal p = true →
      (∀ a b, a ∈ S → b ∈ S → a.size < p.size → b.size < p.size → Lt b a → Lt a t → Lt b t) →
      (∀ a b, a ∈ S → b ∈ S → a.size + b.size < q.size + p.size →
        (a.size ≤ p.size ∨ a.size ≤ q.size) → (b.size ≤ p.size ∨ b.size ≤ q.size) →
        Lt b a → Lt a t → Lt b t) →
      Lt q p → Lt p t → Lt q t) : CutLe S t M := by
  have key : ∀ M', M' ≤ M → ∀ N, ∀ a b, a ∈ S → b ∈ S → a.size ≤ M' → b.size ≤ M' →
      a.size + b.size ≤ N → Lt b a → Lt a t → Lt b t := by
    intro M'
    induction M' with
    | zero => intro _ N a _ _ _ h; exact absurd h (by have := Tm.size_pos a; omega)
    | succ M' ihM =>
      intro hM' N
      induction N with
      | zero => intro a _ _ _ _ _ h; exact absurd h (by have := Tm.size_pos a; omega)
      | succ N ihN =>
        intro a b ha hb hMa hMb hN h1 h2
        refine G.cutGen ht hsub (fun htp q p hq hp => ?_) ha hb h1 h2
        have hqS := G.sub hb (mem_subs_of_mem_summands hq)
        have hpS := G.sub ha (mem_subs_of_mem_summands hp)
        have hqs := size_le_of_mem_summands b q hq
        have hps := size_le_of_mem_summands a p hp
        refine hP q p hqS hpS (by omega) (by omega) htp (summands_WNF b (G.nf b hb) q hq).2
          (summands_WNF a (G.nf a ha) p hp).2 (fun a' b' ha' hb' h1' h2' => ?_)
          (fun a' b' ha' hb' hs' h1' h2' => ?_)
        · exact ihM (by omega) (a'.size + b'.size) a' b' ha' hb' (by omega) (by omega)
            (Nat.le_refl _)
        · exact ihN a' b' ha' hb' (by omega) (by omega) (by omega)
  exact fun a b ha hb hMa hMb => key M (Nat.le_refl _) (a.size + b.size) a b ha hb hMa hMb
    (Nat.le_refl _)

/-- `cmp` が `.eq` でない二つの項について、`x < y ⟺ ¬ y < x` なら反対称 -/
theorem swap_of_iff {x y : Tm} (h1 : cmp x y ≠ .eq) (h2 : cmp y x ≠ .eq)
    (h : Lt x y ↔ ¬ Lt y x) : cmp y x = (cmp x y).swap := by
  unfold Lt at h
  revert h1 h2 h
  cases cmp x y <;> cases cmp y x <;> decide

/-- `Ξ_j(d) < π`（`π ∈ S` は `Ω` の不動点の目標、階 `j`）、`π ∈ C(a, π)`、`a ≤ d` なら、`π` の前線
    （`π` について）に `Ξ_j(d)` 未満でない元がある -/
theorem GoodY.wit_xi_tgtS {S : List Tm} (G : GoodY S) : ∀ π, π ∈ S → IsOF π → IsTgt π →
    ∀ {j : Nat} {d a : Tm}, Tm.Xi j d ∈ S → a ∈ S → Lt (.Xi j d) π → lev π = j →
      inC π a π = true → Le a d → ∃ w, w ∈ fr π π ∧ ¬ Lt w (.Xi j d) := by
  intro π
  induction π using size_induction with
  | h π ih =>
  intro hπS hOF hT j d a hxS haS hlt hl hC had
  have hdS := G.sub hxS (mem_subs_xi j d)
  rcases hT with ⟨c, rfl, -⟩ | ⟨m, q, rfl⟩ | ⟨ζ, κ, b, rfl, hζ⟩
  · rcases hOF with ⟨n, a', e⟩ | ⟨ξ', π', a', e, -, -⟩ <;> cases e
  · simp only [lev] at hl
    subst hl
    have hqS := G.sub hπS (mem_subs_xi m q)
    rcases inC_xi_iff.mp hC with h | ⟨-, hqa⟩
    · exact absurd h (Lt.irrefl _)
    have hqd : Lt q d := G.lt_of_lt_of_le hqS haS hdS hqa had
    have hne : d ≠ q := fun e => by subst e; exact Lt.irrefl _ hqd
    rcases (lt_xi_xi0 hne).mp hlt with ⟨hdq, -⟩ | ⟨-, hn⟩
    · exact absurd hdq (G.asymm hqS hdS hqd)
    · obtain ⟨u, hu, hun⟩ := wit_of_not_inC (G.nf _ hπS).xi.2.2.2.2
        (fun v hv h' => G.trans (G.sub hqS hv) hqS hdS h' hqd) hn
      exact ⟨u, G.fr_xi_sub hπS hu, hun⟩
  · have hκS : κ ∈ S := G.sub hπS (by simp [subs, self_mem_subs])
    have wπ := G.nf _ hπS
    have hlκ : lev κ = j := hl
    have hxκ : Lt (.Xi j d) κ := by
      have h1 := (lt_xi_psiY (π := κ) hlκ).mp hlt
      rw [lt_psi_xiY hlκ] at h1
      cases e : cmp κ (.Xi j d) with
      | gt => exact G.lt_of_gt hκS hxS e
      | _ => exact absurd (Or.inl (by rw [e]; decide)) h1
    have hπκ : Lt (.Psi ζ κ b) κ := lt_psi_targetY wπ
    have hκC : inC κ a κ = true := by
      rcases inC_psi_iff.mp hC with h | ⟨h, -, -, -⟩
      · exact absurd h (Lt.irrefl _)
      · exact inC_mono κ a _ a κ h (fun v hv h' => G.trans (G.sub hκS hv) hπS hκS h' hπκ)
          (fun _ _ h => h)
    have hκOF : IsOF κ := by
      rcases wπ.psi.tgt.cases wπ.psi.piF with ⟨c, rfl⟩ | h
      · exact absurd (lt_oneY wπ.psi.xiF wπ.psi.mlt) hζ
      · exact h
    obtain ⟨w, hw, hwn⟩ := ih κ (by simp only [Tm.size]; omega) hκS hκOF wπ.psi.tgt hxS haS hxκ
      hlκ hκC had
    exact ⟨w, fr_mem_psi_p (Lt.irrefl _)
      (G.fr_sub hκS hπS hκS (Or.inr hπκ) hw (G.k2t _ _ _ hπS w hw)), hwn⟩

/-- 大きさ `N` 以下の `S` の元と新しい項 `Ψ^ξ_π(γ)` の反対称性 -/
def ABle (S : List Tm) (ξ π γ : Tm) (N : Nat) : Prop :=
  ∀ z, z ∈ S → z.size ≤ N → AntiT (.Psi ξ π γ) z

theorem ABle.tgt {S : List Tm} {ξ π γ : Tm} {N : Nat} (hA : ABle S ξ π γ N) {ρ : Tm}
    (hρS : ρ ∈ S) (hρ : ρ.size ≤ N) : ∀ σ κ β, ρ = .Psi σ κ β → AntiT (.Psi ξ π γ) ρ :=
  fun _ _ _ _ => hA ρ hρS hρ

namespace PsiCtxY

variable {S : List Tm} {ξ π γ : Tm} (P : PsiCtxY S ξ π γ)
include P

/-- `t < ρ` で `x ∈ S` の `ρ` 以上の部分項は `t` 未満でない（`ρ` 以下の項との切断性と反対称性の下で） -/
theorem hd_of_tgt {ρ x : Tm} (hρS : ρ ∈ S) (hρT : IsTgt ρ) (hl : lev ρ = lev π)
    (htρ : Lt (.Psi ξ π γ) ρ) (hxS : x ∈ S)
    (ihA : ∀ a b, a ∈ S → b ∈ S → a.size ≤ x.size → b.size ≤ ρ.size → Lt b a →
      Lt a (.Psi ξ π γ) → Lt b (.Psi ξ π γ))
    (hA : ABle S ξ π γ ρ.size) :
    ∀ v, v ∈ subs x → ¬ Lt v ρ → ¬ Lt v (.Psi ξ π γ) := fun v hv hvρ hvt => by
  have G := P.G
  have hvS := G.sub hxS hv
  have hvs := size_le_of_mem_subs hv
  refine P.tgt_contra hρS hρT hl htρ hvS (G.le_of_not_lt hvS hρS hvρ) (P.tb hvS hvt)
    (fun u huS hus huv => ihA v u hvS huS hvs (Nat.le_of_lt hus) huv hvt)
    (Or.inr ⟨hvt, fun ρ' hρ'S hρ's hρ'v => ⟨?_, hA ρ' hρ'S hρ's⟩⟩)
  rcases hρ'v with e | e
  · rw [e]; exact hvt
  · exact ihA v ρ' hvS hρ'S hvs hρ's e hvt

/-- `p = Ψ^τ_ρ(δ) < t` が (1) の形（`δ < γ`、`δ, τ, ρ ∈ C(γ, t)`）なら、`p` の前線（`ρ` について）の元は
    `t` 未満（`p` の真部分項どうしの切断性と反対称性の下で） -/
theorem fr_lt_c1 {τ ρ δ : Tm} (hpS : Tm.Psi τ ρ δ ∈ S) (hl : lev ρ = lev π)
    (htρ : Lt (.Psi ξ π γ) ρ) (hinδ : inC δ γ (.Psi ξ π γ) = true)
    (hinτ : inC τ γ (.Psi ξ π γ) = true)
    (hinρ : inC ρ γ (.Psi ξ π γ) = true) (hpπ : Lt (.Psi τ ρ δ) π)
    (ihA : ∀ a b, a ∈ S → b ∈ S → a.size < (Tm.Psi τ ρ δ).size →
      b.size < (Tm.Psi τ ρ δ).size → Lt b a → Lt a (.Psi ξ π γ) →
      Lt b (.Psi ξ π γ))
    (hA : ABle S ξ π γ ρ.size) :
    ∀ w, (w ∈ fr ρ δ ∨ w ∈ fr ρ ρ ∨ w ∈ fr ρ τ) → Lt w (.Psi ξ π γ) := by
  have G := P.G
  have hρS : ρ ∈ S := G.sub hpS (by simp [subs, self_mem_subs])
  have hτS : τ ∈ S := G.sub hpS (by simp [subs, self_mem_subs])
  have hδS := G.sub hpS (mem_subs_psi_a _ _ δ)
  have hρT := (G.nf _ hpS).psi.tgt
  have hd : ∀ x, x ∈ S → x.size < (Tm.Psi τ ρ δ).size → ∀ v, v ∈ subs x → ¬ Lt v ρ →
      ¬ Lt v (.Psi ξ π γ) := fun x hx hxs =>
    P.hd_of_tgt hρS hρT hl htρ hx (fun a b ha hb has hbs h1 h2 =>
      ihA a b ha hb (by omega) (by simp only [Tm.size] at hbs ⊢; omega) h1 h2) hA
  intro w hw
  have hwS : w ∈ S := by
    rcases hw with hw | hw | hw
    · exact G.sub hδS (fr_spec hw).1
    · exact G.sub hρS (fr_spec hw).1
    · exact G.sub hτS (fr_spec hw).1
  have hwp : Lt w (.Psi τ ρ δ) := by
    rcases hw with hw | hw | hw
    · exact G.k2 _ _ δ hpS w hw
    · exact G.k2t _ _ δ hpS w hw
    · exact G.k2s _ _ δ hpS w hw
  have hin : inC w γ (.Psi ξ π γ) = true := by
    rcases hw with hw | hw | hw
    · exact fr_of_inC δ (hd δ hδS (by simp only [Tm.size]; omega)) hinδ w hw
    · exact fr_of_inC ρ (hd ρ hρS (by simp only [Tm.size]; omega)) hinρ w hw
    · exact fr_of_inC τ (hd τ hτS (by simp only [Tm.size]; omega)) hinτ w hw
  exact G.coll_psi P.ht P.πS w hwS hin (G.trans hwS hpS P.πS hwp hpπ)

/-- `τ ∈ C(γ, t)` なら `τ` の前線（`π` について）の元は `t` 未満 -/
theorem fr_lt_of_inC {τ : Tm} (hτS : τ ∈ S) (hin : inC τ γ (.Psi ξ π γ) = true) :
    ∀ w, w ∈ fr π τ → Lt w (.Psi ξ π γ) := fun w hw => by
  have G := P.G
  have hwS := G.sub hτS (fr_spec hw).1
  have hd : ∀ v, v ∈ subs τ → ¬ Lt v π → ¬ Lt v (.Psi ξ π γ) :=
    fun v hv hvπ hvt => hvπ (P.tb (G.sub hτS hv) hvt)
  exact G.coll_psi P.ht P.πS w hwS (fr_of_inC τ hd hin w hw) (fr_spec hw).2

/-- `t` の目標は `Ω_c` か `Ω` の不動点で、`t` 自身は後者のとき `Ω` の不動点 -/
theorem tshape : (∃ c, π = .Om c ∧ ξ = .zero) ∨ (IsOF π ∧ IsOF (.Psi ξ π γ)) := by
  rcases P.ht.shape with ⟨c, rfl, rfl⟩ | hsh
  · exact Or.inl ⟨c, rfl, rfl⟩
  · refine Or.inr ⟨?_, IsOF.psi P.ht (notOm_of_shape hsh)⟩
    rcases P.hT.cases P.πF with ⟨c, e⟩ | h
    · exact absurd e (notOm_of_shape hsh c)
    · exact h

/-- `t = Ψ^ξ_π(γ)` は大きさ `M` 以下の組について `S` を切断する（大きさ `M` 未満の元との反対称性の下で） -/
theorem cut_le (M : Nat) (hA : ABle S ξ π γ (M - 1)) : CutLe S (.Psi ξ π γ) M := by
  have G := P.G
  refine G.cut_le_of_principal_lex P.ht P.hsub M
    (fun q p hqS hpS hqM hpM _ hqp hpp ihA ihB h1 h2 => ?_)
  have hqF := G.nf q hqS
  have hpF := G.nf p hpS
  refine cut_reduceY P.ht rfl rfl hqF hpF hqp hpp h1 h2 (fun lq lp bq bp => ?_)
  have hpπ := P.tb hpS h2
  have hqπ := G.trans hqS hpS P.πS h1 hpπ
  -- 大きさが `p`・`q` 未満の元との反対称性
  have hAp : ∀ N, N < p.size → ABle S ξ π γ N := fun N hN z hz hzN => hA z hz (by omega)
  have hAq : ∀ N, N < q.size → ABle S ξ π γ N := fun N hN z hz hzN => hA z hz (by omega)
  -- `q` の真部分項 `v < p` は `t` 未満
  have ihq : ∀ v, v ∈ S → v.size < q.size → Lt v p → Lt v (.Psi ξ π γ) :=
    fun v hv hvs hvp => ihB p v hpS hv (by omega) (Or.inl (Nat.le_refl _)) (Or.inr (by omega)) hvp h2
  -- 前線の元以下なら補題 A
  have viaF : ∀ w, (w ∈ fr π γ ∨ w ∈ fr π π ∨ w ∈ fr π ξ) → Le p w → Lt q (.Psi ξ π γ) :=
    fun w hw hpw => P.lemA hqS ⟨w, hw, Or.inr (G.lt_of_lt_of_le hqS hpS (P.F_spec hw).1 h1 hpw)⟩
  -- `p` の真部分項 `w < t` で `q ≤ w`
  have viaLe : ∀ w, w ∈ S → w.size < p.size → Lt w (.Psi ξ π γ) → Le q w →
      Lt q (.Psi ξ π γ) := fun w hwS hws hwt hqw => by
    rcases hqw with e | e
    · rw [e]; exact hwt
    · exact ihB w q hwS hqS (by omega) (Or.inl (by omega)) (Or.inr (Nat.le_refl _)) e hwt
  -- `q = Ξ`
  have viaXi : ∀ m f', q = .Xi m f' → Lt q (.Psi ξ π γ) := fun m f' e => by
    subst e
    have hf'S := G.sub hqS (mem_subs_xi m f')
    refine P.xi_lt_t hqS lq.symm hqπ (fun _ u hu => ?_)
    have huS := G.sub hf'S (fr_spec hu).1
    have := size_le_of_mem_subs (fr_spec hu).1
    exact ihq u huS (by simp only [Tm.size]; omega) (G.trans huS hqS hpS (G.k2x m f' hqS u hu) h1)
  -- `q = Ψ` で目標が `t` 未満
  have viaT : ∀ τ' ρ' α, q = .Psi τ' ρ' α → Lt ρ' (.Psi ξ π γ) → Lt q (.Psi ξ π γ) :=
    fun τ' ρ' α e h => by
      subst e
      have hρ'S : ρ' ∈ S := G.sub hqS (by simp [subs, self_mem_subs])
      exact P.psi_lt_of_tgt hqS lq (P.not_lt_tgt hρ'S hqF.psi.tgt
        ((hAq ρ'.size (by simp only [Tm.size]; omega)).tgt hρ'S (Nat.le_refl _)) h)
  -- `q` の成分が `C(g, p)` に入れば `C(γ, t)` に入る（`g ≤ γ`）
  have mono : ∀ x g, x ∈ S → x.size < q.size → g ∈ S → Le g γ → inC x g p = true →
      inC x γ (.Psi ξ π γ) = true := fun x g hxS hxs hgS hgγ hin =>
    inC_mono x g p γ _ hin (fun v hv hvp => by
        have := size_le_of_mem_subs hv
        exact ihq v (G.sub hxS hv) (by omega) hvp)
      (fun v hv hvg => G.lt_of_lt_of_le (G.sub hxS hv) hgS P.γS hvg hgγ)
  rcases shape_prin hpF hpp bp with ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨τ, ρ, δ, rfl⟩
  · -- `p = Ω_x`
    have hx := G.sub hpS (mem_subs_om x)
    rcases P.tshape with ⟨c, rfl, rfl⟩ | ⟨hπOF, hOF⟩
    · have hcS := G.sub P.πS (mem_subs_om c)
      have hxc : Lt x c := (lt_om_psiY P.ht).mp h2
      rcases shape_prinOF hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨d, α, rfl⟩ |
        ⟨τ', ρ', α, rfl, hOFq⟩
      · have hy := G.sub hqS (mem_subs_om y)
        exact (lt_om_psiY P.ht).mpr (G.trans hy hx hcS ((G.lt_om_iffS hy hx).mp h1) hxc)
      · exact viaXi m' f' rfl
      · have hdS := G.sub hqS (mem_subs_psi_c _ d α)
        have hdc : Lt d c := G.lt_of_le_of_lt hdS hx hcS ((G.lt_psi_omS hqS hx).mp h1) hxc
        have hl : lev d = lev c := lq
        exact P.psi_lt_of_tgt hqS lq (fun h' => (psiOm_lt_om_iff hl).mp h' hdc)
      · exact P.below rfl hqS
          (G.trans hqS hx hcS ((G.lt_OF_omS hOFq hqS hx).mp h1) hxc)
    · have hxt : Lt x (.Psi ξ π γ) := (lt_om_OFG hOF).mp h2
      have hxs : x.size < (Tm.Om x).size := by simp only [Tm.size]; omega
      rcases shape_prinOF hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨d, α, rfl⟩ |
        ⟨τ', ρ', α, rfl, hOFq⟩
      · have hy := G.sub hqS (mem_subs_om y)
        exact (lt_om_OFG hOF).mpr (ihB x y hx hy (by simp only [Tm.size]; omega)
          (Or.inl (by omega)) (Or.inr (by simp only [Tm.size]; omega))
          ((G.lt_om_iffS hy hx).mp h1) hxt)
      · exact viaXi m' f' rfl
      · have hdS := G.sub hqS (mem_subs_psi_c _ d α)
        have hdt : Lt d (.Psi ξ π γ) := by
          rcases (G.lt_psi_omS hqS hx).mp h1 with e | e
          · rw [e]; exact hxt
          · exact ihB x d hx hdS (by simp only [Tm.size]; omega) (Or.inl (by omega))
              (Or.inr (by simp only [Tm.size]; omega)) e hxt
        exact viaT .zero (.Om d) α rfl ((lt_om_OFG hOF).mpr hdt)
      · exact ihB x _ hx hqS (by omega) (Or.inl (by omega)) (Or.inr (Nat.le_refl _))
          ((G.lt_OF_omS hOFq hqS hx).mp h1) hxt
  · -- `p = Ξ_m(f)`
    have hfS := G.sub hpS (mem_subs_xi m f)
    obtain ⟨-, hinf⟩ := P.xi_lt_t_inv hpS lp.symm h2
    rcases P.tshape with ⟨c, rfl, rfl⟩ | ⟨hπOF, hOF⟩
    · have hcS := G.sub P.πS (mem_subs_om c)
      exact P.below rfl hqS (G.trans hqS hpS hcS h1 ((G.lt_OF_omS (xiOF _ _) hpS hcS).mp hpπ))
    · have lp' : lev π = m := lp.symm
      by_cases hfγ : Lt f γ
      · have hinf' := hinf hfγ
        rcases shape_prin hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨τ', ρ', α, rfl⟩
        · have hy := G.sub hqS (mem_subs_om y)
          exact (lt_om_OFG hOF).mpr (ihq y hy (by simp only [Tm.size]; omega)
            ((lt_om_OFG (xiOF _ _)).mp h1))
        · exact viaXi m' f' rfl
        · have hρ'S : ρ' ∈ S := G.sub hqS (by simp [subs, self_mem_subs])
          rcases (lt_psi_xiY (π := ρ') (a := α) (lq.trans lp.symm)).mp h1 with h' | ⟨hfα, hn⟩
          · refine viaT τ' ρ' α rfl ?_
            rcases G.le_of_ne_gt hρ'S hpS h' with e | e
            · rw [e]; exact h2
            · exact ihq ρ' hρ'S (by simp only [Tm.size]; omega) e
          · have hαS := G.sub hqS (mem_subs_psi_a _ _ α)
            obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hpF.xi.2.2.2.2
              (fun v hv h' => G.trans (G.sub hfS hv) hfS hαS h' hfα) hn
            have hwS := G.sub hfS (fr_spec hw).1
            have := size_le_of_mem_subs (fr_spec hw).1
            have hin := fr_of_inC f
              (fun w' _ hn' => not_lt_of_not_lt_K (y := Tm.Psi ξ π γ) lp' hn') hinf' w hw
            have hwt := G.coll_psi P.ht P.πS w hwS hin
              (G.trans hwS hpS P.πS (G.k2x _ f hpS w hw) hpπ)
            exact viaLe w hwS (by simp only [Tm.size]; omega) hwt (G.le_of_not_lt hwS hqS hwn)
      · -- `γ ≤ f`：`p < π` から `p` 以上の `π` の前線の元
        have hγf : Le γ f := G.le_of_not_lt hfS P.γS hfγ
        obtain ⟨u, hu, hun⟩ := G.wit_xi_tgtS π P.πS hπOF P.hT hpS P.γS hpπ lp' P.ht.psi.Cpi hγf
        have huS := G.sub P.πS (fr_spec hu).1
        exact viaF u (Or.inr (Or.inl hu)) (G.le_of_not_lt huS hpS hun)
  · -- `p = Ψ^τ_ρ(δ)`
    have hρS : ρ ∈ S := G.sub hpS (by simp [subs, self_mem_subs])
    have hτS : τ ∈ S := G.sub hpS (by simp [subs, self_mem_subs])
    have hδS := G.sub hpS (mem_subs_psi_a _ _ δ)
    have hpP := hpF.psi
    have lp' : lev ρ = lev π := lp
    have hAρ : ABle S ξ π γ ρ.size := hAp ρ.size (by simp only [Tm.size]; omega)
    rcases (lt_psi_psiY lp' (P.ne_of_mem hpS)).mp h2 with
      h' | ⟨htρ, -, hc1 | ⟨hγδ, hn⟩ | ⟨he, e, hτξ, hinτ⟩ | ⟨hξτ, hn⟩⟩
    · -- 目標 `ρ` が `t` 未満
      have hρt := P.tgt_lt hρS hpP.tgt (hAρ.tgt hρS (Nat.le_refl _)) h'
      exact ihB ρ q hρS hqS (by simp only [Tm.size]; omega) (Or.inl (by simp only [Tm.size]; omega))
        (Or.inr (Nat.le_refl _)) (G.trans hqS hpS hρS h1 (lt_psi_targetY hpF)) hρt
    · -- (1)：`δ < γ`、`δ, τ, ρ ∈ C(γ, t)`
      obtain ⟨hδγ, hinδ, hinτ, hinρ⟩ := hc1
      have frP := P.fr_lt_c1 hpS lp' htρ hinδ hinτ hinρ hpπ ihA hAρ
      rcases shape_prin hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨τ', ρ', α, rfl⟩
      · have hy := G.sub hqS (mem_subs_om y)
        rcases hpF.shape with ⟨d, rfl, rfl⟩ | hshp
        · have hyd : Lt y d := (lt_om_psiY hpF).mp h1
          have hdS := G.sub hρS (mem_subs_om d)
          rcases P.tshape with ⟨c, rfl, rfl⟩ | ⟨hπOF, hOF⟩
          · have hcS := G.sub P.πS (mem_subs_om c)
            exact (lt_om_psiY P.ht).mpr
              (G.lt_of_lt_of_le hy hdS hcS hyd ((G.lt_psi_omS hpS hcS).mp hpπ))
          · rw [inC_om] at hinρ
            have hdt := G.coll_psi P.ht P.πS d hdS hinρ
              (G.trans hdS hpS P.πS (G.cx d δ hpS) hpπ)
            exact (lt_om_OFG hOF).mpr (ihB d y hdS hy
              (by simp only [Tm.size] at lq ⊢; omega) (Or.inl (by simp only [Tm.size]; omega))
              (Or.inr (by simp only [Tm.size]; omega)) hyd hdt)
        · have hOFp := IsOF.psi hpF (notOm_of_shape hshp)
          have hyp : Lt y (.Psi τ ρ δ) := (lt_om_OFG hOFp).mp h1
          rcases P.tshape with ⟨c, rfl, rfl⟩ | ⟨hπOF, hOF⟩
          · have hcS := G.sub P.πS (mem_subs_om c)
            exact (lt_om_psiY P.ht).mpr (G.trans hy hpS hcS hyp
              ((G.lt_OF_omS hOFp hpS hcS).mp hpπ))
          · exact (lt_om_OFG hOF).mpr (ihq y hy (by simp only [Tm.size]; omega) hyp)
      · exact viaXi m' f' rfl
      · have hρ'S : ρ' ∈ S := G.sub hqS (by simp [subs, self_mem_subs])
        have hτ'S : τ' ∈ S := G.sub hqS (by simp [subs, self_mem_subs])
        have hαS := G.sub hqS (mem_subs_psi_a _ _ α)
        have lq' : lev ρ' = lev ρ := lq.trans lp.symm
        by_cases htρ'' : ¬ Lt (.Psi ξ π γ) ρ'
        · exact P.psi_lt_of_tgt hqS lq htρ''
        have htρ' := Decidable.of_not_not htρ''
        rcases (lt_psi_psiY lq' h1.ne).mp h1 with
          h'' | ⟨-, -, ⟨hαδ, hinα, hinτ', hinρ'⟩ | ⟨hδα, hn'⟩ | ⟨he', e', hτ'τ, hinτ'⟩ |
            ⟨hττ', hn'⟩⟩
        · refine viaT τ' ρ' α rfl ?_
          rcases G.le_of_not_lt hpS hρ'S h'' with e | e
          · rw [e]; exact h2
          · exact ihq ρ' hρ'S (by simp only [Tm.size]; omega) e
        · -- (1)(1)
          refine P.psi_lt_of_c1 hqS lq htρ' hqπ (G.trans hαS hδS P.γS hαδ hδγ)
            (mono α δ hαS (by simp only [Tm.size]; omega) hδS (Or.inr hδγ) hinα)
            (mono τ' δ hτ'S (by simp only [Tm.size]; omega) hδS (Or.inr hδγ) hinτ')
            (mono ρ' δ hρ'S (by simp only [Tm.size]; omega) hδS (Or.inr hδγ) hinρ')
        · -- (1)(2)：`p` の前線の証人
          have hδα' : Le δ α := G.le_of_ne_gt hδS hαS hδα
          have hg : ∀ x, x ∈ S → ∀ v, v ∈ subs x → Lt v δ → Lt v α := fun x hx v hv h =>
            G.lt_of_lt_of_le (G.sub hx hv) hδS hαS h hδα'
          have hw : ∃ w, (w ∈ fr ρ δ ∨ w ∈ fr ρ ρ ∨ w ∈ fr ρ τ) ∧ ¬ Lt w (.Psi τ' ρ' α) := by
            cases e1 : inC δ α (Tm.Psi τ' ρ' α)
            · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hpP.Ca (hg δ hδS) e1
              exact ⟨w, Or.inl hw, hwn⟩
            · cases e2 : inC τ α (Tm.Psi τ' ρ' α)
              · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hpP.Cxi (hg τ hτS) e2
                exact ⟨w, Or.inr (Or.inr hw), hwn⟩
              · cases e3 : inC ρ α (Tm.Psi τ' ρ' α)
                · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hpP.Cpi (hg ρ hρS) e3
                  exact ⟨w, Or.inr (Or.inl hw), hwn⟩
                · exact absurd ⟨e1, e2, e3⟩ hn'
          obtain ⟨w, hw, hwn⟩ := hw
          have hwS : w ∈ S := by
            rcases hw with hw | hw | hw
            · exact G.sub hδS (fr_spec hw).1
            · exact G.sub hρS (fr_spec hw).1
            · exact G.sub hτS (fr_spec hw).1
          have hws : w.size < (Tm.Psi τ ρ δ).size := by
            rcases hw with hw | hw | hw <;>
              (have := size_le_of_mem_subs (fr_spec hw).1; simp only [Tm.size]; omega)
          exact viaLe w hwS hws (frP w hw) (G.le_of_not_lt hwS hqS hwn)
        · -- (1)(3)：`q = Ψ^{τ'}_ρ(δ)`、`τ' < τ`
          have hαδ := G.eq hαS hδS he'
          subst hαδ e'
          exact P.psi_lt_of_c1 hqS lq htρ' hqπ hδγ hinδ
            (mono τ' α hτ'S (by simp only [Tm.size]; omega) hαS (Or.inr hδγ) hinτ') hinρ
        · -- (1)(4)：`τ < τ'` で `τ ∉ C(τ', q)`
          obtain ⟨w, hw, hwn⟩ := wit_of_not_inC (G.miS hpS)
            (fun v hv h => G.trans (G.sub hτS hv) hτS hτ'S h hττ') hn'
          have hwS := G.sub hτS (fr_spec hw).1
          have := size_le_of_mem_subs (fr_spec hw).1
          exact viaLe w hwS (by simp only [Tm.size]; omega) (frP w (Or.inr (Or.inr hw)))
            (G.le_of_not_lt hwS hqS hwn)
    · -- (2)：前線の証人
      obtain ⟨w, hw, hwn⟩ := P.wit (G.le_of_ne_gt P.γS hδS hγδ) hδS hn
      exact viaF w hw (G.le_of_not_lt (P.F_spec hw).1 hpS hwn)
    · -- (3)：`p = Ψ^τ_π(γ)`、`τ < ξ`、`τ ∈ C(γ, t)`
      have hδγ := G.eq hδS P.γS he
      subst hδγ e
      have frP3 := P.fr_lt_of_inC hτS hinτ
      rcases shape_prin hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨τ', ρ', α, rfl⟩
      · have hy := G.sub hqS (mem_subs_om y)
        rcases P.tshape with ⟨c, rfl, rfl⟩ | ⟨-, hOF⟩
        · exact absurd hτξ (not_lt_zero _)
        · have hOFp : IsOF (.Psi τ π δ) := by
            rcases hOF with ⟨n, a, e⟩ | ⟨ξ', π', a', e, hw', hπ'⟩
            · cases e
            · cases e; exact IsOF.psi hpF hπ'
          exact (lt_om_OFG hOF).mpr (ihq y hy (by simp only [Tm.size]; omega)
            ((lt_om_OFG hOFp).mp h1))
      · exact viaXi m' f' rfl
      · have hρ'S : ρ' ∈ S := G.sub hqS (by simp [subs, self_mem_subs])
        have hτ'S : τ' ∈ S := G.sub hqS (by simp [subs, self_mem_subs])
        have hαS := G.sub hqS (mem_subs_psi_a _ _ α)
        have lq' : lev ρ' = lev π := lq
        by_cases htρ'' : ¬ Lt (.Psi ξ π δ) ρ'
        · exact P.psi_lt_of_tgt hqS lq htρ''
        have htρ' := Decidable.of_not_not htρ''
        rcases (lt_psi_psiY lq' h1.ne).mp h1 with
          h'' | ⟨-, -, ⟨hαδ, hinα, hinτ', hinρ'⟩ | ⟨hδα, hn'⟩ | ⟨he', e', hτ'τ, hinτ'⟩ |
            ⟨hττ', hn'⟩⟩
        · refine viaT τ' ρ' α rfl ?_
          rcases G.le_of_not_lt hpS hρ'S h'' with e | e
          · rw [e]; exact h2
          · exact ihq ρ' hρ'S (by simp only [Tm.size]; omega) e
        · -- (3)(1)
          exact P.psi_lt_of_c1 hqS lq htρ' hqπ hαδ
            (mono α δ hαS (by simp only [Tm.size]; omega) P.γS (Or.inl rfl) hinα)
            (mono τ' δ hτ'S (by simp only [Tm.size]; omega) P.γS (Or.inl rfl) hinτ')
            (mono ρ' δ hρ'S (by simp only [Tm.size]; omega) P.γS (Or.inl rfl) hinρ')
        · -- (3)(2)：`p` の前線の証人（`γ`・`π` は `t` と共通、`τ` は `C(γ, t)` に入る）
          have hδα' : Le δ α := G.le_of_ne_gt P.γS hαS hδα
          have hg : ∀ x, x ∈ S → ∀ v, v ∈ subs x → Lt v δ → Lt v α := fun x hx v hv h =>
            G.lt_of_lt_of_le (G.sub hx hv) P.γS hαS h hδα'
          cases e1 : inC δ α (Tm.Psi τ' ρ' α)
          · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hpP.Ca (hg δ P.γS) e1
            have hwS := G.sub P.γS (fr_spec hw).1
            exact P.lemA hqS ⟨w, Or.inl hw, G.le_of_not_lt hwS hqS hwn⟩
          · cases e2 : inC τ α (Tm.Psi τ' ρ' α)
            · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hpP.Cxi (hg τ hτS) e2
              have hwS := G.sub hτS (fr_spec hw).1
              have := size_le_of_mem_subs (fr_spec hw).1
              exact viaLe w hwS (by simp only [Tm.size]; omega) (frP3 w hw)
                (G.le_of_not_lt hwS hqS hwn)
            · cases e3 : inC π α (Tm.Psi τ' ρ' α)
              · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hpP.Cpi (hg π P.πS) e3
                have hwS := G.sub P.πS (fr_spec hw).1
                exact P.lemA hqS ⟨w, Or.inr (Or.inl hw), G.le_of_not_lt hwS hqS hwn⟩
              · exact absurd ⟨e1, e2, e3⟩ hn'
        · -- (3)(3)：`q = Ψ^{τ'}_π(γ)`、`τ' < τ < ξ`
          have hαδ := G.eq hαS P.γS he'
          subst hαδ e'
          exact P.psi_lt_of_c3 hqS (cmp_self _) (G.trans hτ'S hτS P.ξS hτ'τ hτξ)
            (mono τ' α hτ'S (by simp only [Tm.size]; omega) P.γS (Or.inl rfl) hinτ')
        · -- (3)(4)：`τ < τ'` で `τ ∉ C(τ', q)`
          obtain ⟨w, hw, hwn⟩ := wit_of_not_inC (G.miS hpS)
            (fun v hv h => G.trans (G.sub hτS hv) hτS hτ'S h hττ') hn'
          have hwS := G.sub hτS (fr_spec hw).1
          have := size_le_of_mem_subs (fr_spec hw).1
          exact viaLe w hwS (by simp only [Tm.size]; omega) (frP3 w hw)
            (G.le_of_not_lt hwS hqS hwn)
    · -- (4)：`ξ < τ` で `ξ ∉ C(τ, p)`
      obtain ⟨w, hw, hwn⟩ := P.wit4 hτS hξτ hn
      exact viaF w (Or.inr (Or.inr hw)) (G.le_of_not_lt (P.F_spec (Or.inr (Or.inr hw))).1 hpS hwn)

/-- `Ψ` どうしの反対称性（`s` より小さい元との反対称性と、`s` 以下の組の切断性の下で） -/
theorem psi_swap_le {σ κ β : Tm} (hs : Tm.Psi σ κ β ∈ S) (hl : lev π = lev κ)
    (hA : ABle S ξ π γ ((Tm.Psi σ κ β).size - 1)) (hcut : CutLe S (.Psi ξ π γ) (Tm.Psi σ κ β).size) :
    cmpPsi (.Psi σ κ β) (.Psi ξ π γ) = (cmpPsi (.Psi ξ π γ) (.Psi σ κ β)).swap := by
  have G := P.G
  have hsF := G.nf _ hs
  have hsP := hsF.psi
  have hκS : κ ∈ S := G.sub hs (by simp [subs, self_mem_subs])
  have hσS : σ ∈ S := G.sub hs (by simp [subs, self_mem_subs])
  have hβS := G.sub hs (mem_subs_psi_a _ _ β)
  have hκT := hsP.tgt
  have hAκ : ∀ σ' κ'' β', κ = .Psi σ' κ'' β' → AntiT (.Psi ξ π γ) κ :=
    fun _ _ _ _ => hA κ hκS (by simp only [Tm.size]; omega)
  have hne : Tm.Psi ξ π γ ≠ .Psi σ κ β := fun e => P.ne_of_mem hs e.symm
  have hne' : Tm.Psi σ κ β ≠ .Psi ξ π γ := fun e => hne e.symm
  have Ats := lt_psi_psiY hl hne
  have Ast := lt_psi_psiY hl.symm hne'
  have caseA : ¬ Lt (.Psi σ κ β) π → ¬ Lt (.Psi ξ π γ) κ → False := fun h1 h2 => by
    have hπκ := G.lt_of_le_of_lt P.πS hs hκS (G.le_of_not_lt hs P.πS h1) (lt_psi_targetY hsF)
    exact G.asymm P.πS hκS hπκ (P.tbge hκS hκT.principal h2)
  -- `s` の前線の証人 `u < s`（`u < t` でない）があれば、`s < t` と切断性で矛盾
  have cutW : Lt (.Psi σ κ β) (.Psi ξ π γ) → ∀ u, u ∈ S → Lt u (.Psi σ κ β) →
      u.size < (Tm.Psi σ κ β).size → ¬ Lt u (.Psi ξ π γ) → False :=
    fun hst u hu hus hus' hun => hun (hcut _ u hs hu (Nat.le_refl _) (Nat.le_of_lt hus') hus hst)
  -- `t < s` の (2) の証人
  have W2t : Le β γ → ¬ (inC β γ (.Psi ξ π γ) = true ∧ inC σ γ (.Psi ξ π γ) = true ∧
      inC κ γ (.Psi ξ π γ) = true) →
      ∃ u, u ∈ S ∧ Lt u (.Psi σ κ β) ∧ u.size < (Tm.Psi σ κ β).size ∧
        ¬ Lt u (.Psi ξ π γ) := by
    intro hβγ hn
    have hg : ∀ x, x ∈ S → ∀ v, v ∈ subs x → Lt v β → Lt v γ := fun x hx v hv h =>
      G.lt_of_lt_of_le (G.sub hx hv) hβS P.γS h hβγ
    cases e1 : inC β γ (Tm.Psi ξ π γ)
    · obtain ⟨u, hu, hun⟩ := wit_of_not_inC hsP.Ca (hg β hβS) e1
      have := size_le_of_mem_subs (fr_spec hu).1
      exact ⟨u, G.sub hβS (fr_spec hu).1, G.k2 _ _ _ hs u hu, by simp only [Tm.size]; omega, hun⟩
    · cases e2 : inC σ γ (Tm.Psi ξ π γ)
      · obtain ⟨u, hu, hun⟩ := wit_of_not_inC hsP.Cxi (hg σ hσS) e2
        have := size_le_of_mem_subs (fr_spec hu).1
        exact ⟨u, G.sub hσS (fr_spec hu).1, G.k2s _ _ _ hs u hu, by simp only [Tm.size]; omega,
          hun⟩
      · cases e3 : inC κ γ (Tm.Psi ξ π γ)
        · obtain ⟨u, hu, hun⟩ := wit_of_not_inC hsP.Cpi (hg κ hκS) e3
          have := size_le_of_mem_subs (fr_spec hu).1
          exact ⟨u, G.sub hκS (fr_spec hu).1, G.k2t _ _ _ hs u hu, by simp only [Tm.size]; omega,
            hun⟩
        · exact absurd ⟨e1, e2, e3⟩ hn
  -- `t < s` の (4) の証人
  have W4t : Lt σ ξ → inC σ ξ (.Psi ξ π γ) = false →
      ∃ u, u ∈ S ∧ Lt u (.Psi σ κ β) ∧ u.size < (Tm.Psi σ κ β).size ∧
        ¬ Lt u (.Psi ξ π γ) := by
    intro hσξ hn
    obtain ⟨u, hu, hun⟩ := wit_of_not_inC (G.miS hs)
      (fun v hv h => G.trans (G.sub hσS hv) hσS P.ξS h hσξ) hn
    have := size_le_of_mem_subs (fr_spec hu).1
    exact ⟨u, G.sub hσS (fr_spec hu).1, G.k2s _ _ _ hs u hu, by simp only [Tm.size]; omega, hun⟩
  -- `t < κ` なら `ξ` の前線（`π` について）は `κ` 未満（補題 A と `κ` との反対称性）
  have frξκ : Lt (.Psi ξ π γ) κ → ∀ w, w ∈ fr π ξ → Lt w κ := fun htκ w hw => by
    have hwS := G.sub P.ξS (fr_spec hw).1
    rcases G.tri hwS hκS with h | e | h
    · exact h
    · subst e
      exact absurd htκ (P.not_lt_tgt hwS hκT hAκ (P.k2s w hw))
    · exact absurd htκ (P.not_lt_tgt hκS hκT hAκ
        (P.lemA hκS ⟨w, Or.inr (Or.inr hw), Or.inr h⟩))
  -- `ξ ∈ C(β, s)` と `s < t` の (4) は両立しない
  have c4s_contra : Lt (.Psi σ κ β) π → Lt (.Psi ξ π γ) κ → inC ξ β (.Psi σ κ β) = true →
      Lt ξ σ → inC ξ σ (.Psi σ κ β) = false → False := by
    intro hsπ htκ hinξ hξσ hn
    have hd : ∀ v, v ∈ subs ξ → ¬ Lt v π → ¬ Lt v (.Psi σ κ β) := fun v hv hvπ hvs =>
      hvπ (G.trans (G.sub P.ξS hv) hs P.πS hvs hsπ)
    rw [inC_of_fr ξ P.mi (fun v hv h => G.trans (G.sub P.ξS hv) P.ξS hσS h hξσ)
      (fun w hw => inC_of_lt_node (fr_node hw)
        (G.coll_psiS hs w (G.sub P.ξS (fr_spec hw).1) (fr_of_inC ξ hd hinξ w hw)
          (frξκ htκ w hw)))] at hn
    cases hn
  -- `s < t` と `t < s` は両立しない
  have asym : Lt (.Psi ξ π γ) (.Psi σ κ β) → Lt (.Psi σ κ β) (.Psi ξ π γ) → False := by
    intro h h'
    rcases Ats.mp h with a1 | ⟨hsπ, htκ, hc⟩ <;> rcases Ast.mp h' with b1 | ⟨htκ', hsπ', hc'⟩
    · exact caseA a1 b1
    · exact a1 hsπ'
    · exact b1 htκ
    · rcases hc with ⟨hγβ, hinγ, hinξ, hinπ⟩ | ⟨hβγ, hn⟩ | ⟨he, e, hξσ, hinξ⟩ | ⟨hσξ, hn⟩
      · rcases hc' with ⟨hβγ', -⟩ | ⟨-, hn'⟩ | ⟨he', -⟩ | ⟨hξσ', hn'⟩
        · exact G.asymm P.γS hβS hγβ hβγ'
        · exact hn' ⟨hinγ, hinξ, hinπ⟩
        · have := G.eq hβS P.γS he'
          subst this
          exact Lt.irrefl _ hγβ
        · exact c4s_contra hsπ htκ hinξ hξσ' hn'
      · obtain ⟨u, hu, hus, hus', hun⟩ := W2t (G.le_of_ne_gt hβS P.γS hβγ) hn
        exact cutW h' u hu hus hus' hun
      · have hγβ := G.eq P.γS hβS he
        subst hγβ e
        rcases hc' with ⟨hβγ', -⟩ | ⟨-, hn'⟩ | ⟨-, -, hσξ', -⟩ | ⟨hξσ', hn'⟩
        · exact Lt.irrefl _ hβγ'
        · exact hn' ⟨G.inC_argS hs, hinξ, G.inC_tgtS hs⟩
        · exact G.asymm P.ξS hσS hξσ hσξ'
        · exact c4s_contra hsπ htκ hinξ hξσ' hn'
      · obtain ⟨u, hu, hus, hus', hun⟩ := W4t hσξ hn
        exact cutW h' u hu hus hus' hun
  -- どちらかは成り立つ
  have tot : Lt (.Psi ξ π γ) (.Psi σ κ β) ∨ Lt (.Psi σ κ β) (.Psi ξ π γ) := by
    by_cases h1 : Lt (.Psi σ κ β) π
    · by_cases h2 : Lt (.Psi ξ π γ) κ
      · rcases G.tri P.γS hβS with e | e | e
        · by_cases hin : inC γ β (.Psi σ κ β) = true ∧ inC ξ β (.Psi σ κ β) = true ∧
              inC π β (.Psi σ κ β) = true
          · exact Or.inl (Ats.mpr (Or.inr ⟨h1, h2, Or.inl ⟨e, hin.1, hin.2.1, hin.2.2⟩⟩))
          · exact Or.inr (Ast.mpr (Or.inr ⟨h2, h1, Or.inr (Or.inl
              ⟨by unfold Lt at e; rw [e]; decide, hin⟩)⟩))
        · subst e
          by_cases hA' : inC γ γ (.Psi ξ π γ) = true ∧ inC σ γ (.Psi ξ π γ) = true ∧
              inC κ γ (.Psi ξ π γ) = true
          · by_cases hB : inC γ γ (.Psi σ κ γ) = true ∧ inC ξ γ (.Psi σ κ γ) = true ∧
                inC π γ (.Psi σ κ γ) = true
            · rcases G.tri P.πS hκS with e | e | e
              · exact absurd (G.coll_psiS hs π P.πS hB.2.2 e) (G.asymm hs P.πS h1)
              · subst e
                rcases G.tri P.ξS hσS with e' | e' | e'
                · exact Or.inl (Ats.mpr (Or.inr ⟨h1, h2, Or.inr (Or.inr (Or.inl
                    ⟨cmp_self _, rfl, e', hB.2.1⟩))⟩))
                · subst e'; exact absurd rfl hne
                · exact Or.inr (Ast.mpr (Or.inr ⟨h2, h1, Or.inr (Or.inr (Or.inl
                    ⟨cmp_self _, rfl, e', hA'.2.1⟩))⟩))
              · exact absurd h2 (P.not_lt_tgt hκS hκT hAκ
                  (G.coll_psi P.ht P.πS κ hκS hA'.2.2 e))
            · exact Or.inr (Ast.mpr (Or.inr ⟨h2, h1, Or.inr (Or.inl
                ⟨by rw [cmp_self]; decide, hB⟩)⟩))
          · exact Or.inl (Ats.mpr (Or.inr ⟨h1, h2, Or.inr (Or.inl
              ⟨by rw [cmp_self]; decide, hA'⟩)⟩))
        · by_cases hin : inC β γ (.Psi ξ π γ) = true ∧ inC σ γ (.Psi ξ π γ) = true ∧
              inC κ γ (.Psi ξ π γ) = true
          · exact Or.inr (Ast.mpr (Or.inr ⟨h2, h1, Or.inl ⟨e, hin.1, hin.2.1, hin.2.2⟩⟩))
          · exact Or.inl (Ats.mpr (Or.inr ⟨h1, h2, Or.inr (Or.inl
              ⟨by unfold Lt at e; rw [e]; decide, hin⟩)⟩))
      · exact Or.inr (Ast.mpr (Or.inl h2))
    · by_cases h2 : Lt (.Psi ξ π γ) κ
      · exact Or.inl (Ats.mpr (Or.inl h1))
      · exact absurd (caseA h1 h2) id
  have ne := P.G.ne_new P.ht P.hsub P.htS _ hs
  have key := swap_of_iff ne.2 ne.1 ⟨fun h h' => asym h h', fun h => tot.resolve_right h⟩
  rw [cmp_principal rfl rfl, cmp_principal rfl rfl, cmpP_psi_psi hl, cmpP_psi_psi hl.symm] at key
  exact key

/-- 大きさについての帰納法：`t` は大きさ `N` 以下の全ての元と反対称 -/
theorem anti_le : ∀ N, ABle S ξ π γ N := by
  intro N
  induction N with
  | zero => intro z _ h; exact absurd h (by have := Tm.size_pos z; omega)
  | succ N ih =>
    refine P.G.anti_new P.ht P.hsub P.htS (N + 1) (fun _ _ _ σ κ β e hs hsN hl => ?_)
    cases e
    have hA : ABle S ξ π γ ((Tm.Psi σ κ β).size - 1) := fun z hz hzs => ih z hz (by omega)
    exact P.psi_swap_le hs hl hA (P.cut_le _ hA)

/-- `t = Ψ^ξ_π(γ)` は `S` の全ての元と反対称 -/
theorem anti : ∀ z, z ∈ S → AntiT (.Psi ξ π γ) z :=
  fun z hz => P.anti_le z.size z hz (Nat.le_refl _)

/-- `t = Ψ^ξ_π(γ)` は `S` を切断する -/
theorem cut : CutT S (.Psi ξ π γ) := fun a b ha hb =>
  P.cut_le (max a.size b.size) (fun z hz _ => P.anti z hz) a b ha hb
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)

end PsiCtxY

/-! ## 順序の性質 `FWOrder` の証明

部分項で閉じ、`Ψ^ξ_{Ξ_n(p)}(γ)`（`ξ ≠ 0`）を含めば `K_n^+` も含む有限集合 `S` の要素数についての帰納法で
`GoodY S` を示す（`lin_closedY`）。`S` から大きさ最大の項 `t` を除いた `S'` について `GoodY S'` を仮定し、
`t` の形で場合分けして、`t` の切断性・`t` と `S'` の元の反対称性・`t` についての K2・K2T・K2S・K2X・CX を
得る（`cut_omY`・`XiCtxY`・`PsiCtxY`）。 -/

theorem GoodY.nil : GoodY [] :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ _ _ h => absurd h List.not_mem_nil, fun _ _ _ h => absurd h List.not_mem_nil,
    fun _ _ _ h => absurd h List.not_mem_nil, fun _ _ h => absurd h List.not_mem_nil,
    fun _ _ h => absurd h List.not_mem_nil, fun _ _ _ _ h => absurd h List.not_mem_nil⟩

/-- `S'` が反対称で、`t` が `S'` の全ての元と反対称なら、`S' ∪ {t}` は反対称 -/
theorem antiOn_extend {S S' : List Tm} {t : Tm} (hA : AntiOn S')
    (inS' : ∀ s, s ∈ S → s ≠ t → s ∈ S') (hT : ∀ z, z ∈ S' → AntiT t z) : AntiOn S := by
  intro a ha b hb
  by_cases ea : a = t <;> by_cases eb : b = t
  · subst ea; subst eb
    rw [cmp_self]
    exact ⟨rfl, fun _ => rfl⟩
  · subst ea
    exact hT b (inS' b hb eb)
  · subst eb
    obtain ⟨h1, -⟩ := hT a (inS' a ha ea)
    refine ⟨by rw [h1, Ordering.swap_swap], fun e => ?_⟩
    have := (hT a (inS' a ha ea)).2
    rw [h1] at e
    exact (this (swap_eq_eq e)).symm
  · exact hA a (inS' a ha ea) b (inS' b hb eb)

/-- `Ψ^ξ_{Ξ_n(p)}(γ)`（`ξ ≠ 0`）は `K_n^+` より大きい -/
theorem size_succK_lt {ξ γ p : Tm} {n : Nat} (hξ : ξ ≠ .zero) :
    (succK n).size < (Tm.Psi ξ (.Xi n p) γ).size := by
  have h1 : 1 ≤ ξ.size := Tm.size_pos ξ
  have h2 := Tm.size_pos p
  have h3 := Tm.size_pos γ
  cases ξ with
  | zero => exact absurd rfl hξ
  | _ => simp only [succK, Tm.size] at *; omega

theorem lin_closedY : ∀ n, ∀ S : List Tm, S.length ≤ n →
    (∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S) → (∀ s, s ∈ S → WNF s) → SKOn S → GoodY S := by
  intro n
  induction n with
  | zero =>
    intro S hl _ _ _
    have hS : S = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst hS
    exact GoodY.nil
  | succ n ih =>
    intro S hl hcl hNF hsk
    by_cases hS0 : S = []
    · subst hS0
      exact GoodY.nil
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
    have hNF' : ∀ s, s ∈ S.filter (fun s => s != t) → WNF s := fun s hs =>
      hNF s ((hmem s).mp hs).1
    -- `K_n^+` は `t` でない（大きさが小さい）
    have skne : ∀ ξ m p γ, Tm.Psi ξ (.Xi m p) γ ∈ S → ξ ≠ .zero → succK m ≠ t :=
      fun ξ m p γ hψ hξ e => by
        have h1 := hmax _ hψ
        have h2 := size_succK_lt (γ := γ) (p := p) (n := m) hξ
        rw [e] at h2
        omega
    have hsk' : SKOn (S.filter (fun s => s != t)) := fun ξ m p γ hψ hξ =>
      (hmem _).mpr ⟨hsk ξ m p γ ((hmem _).mp hψ).1 hξ,
        skne ξ m p γ ((hmem _).mp hψ).1 hξ⟩
    have G' := ih _ hl' hcl' hNF' hsk'
    have htF := hNF t htS
    have hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S.filter (fun s => s != t) := fun s hs hne =>
      (hmem s).mpr ⟨hcl t htS s hs, hne⟩
    have htS' : t ∉ S.filter (fun s => s != t) := fun h => ((hmem t).mp h).2 rfl
    have inS' : ∀ s, s ∈ S → s ≠ t → s ∈ S.filter (fun s => s != t) := fun s hs hne =>
      (hmem s).mpr ⟨hs, hne⟩
    -- `Ψ` の文脈の `K_n^+` の条件
    have hskt : ∀ ξ π γ, t = .Psi ξ π γ → ∀ m p, π = .Xi m p → ξ ≠ .zero →
        succK m ∈ S.filter (fun s => s != t) := fun ξ π γ e m p hπ hξ => by
      subst hπ
      have hψ : Tm.Psi ξ (.Xi m p) γ ∈ S := e ▸ htS
      exact inS' _ (hsk ξ m p γ hψ hξ) (skne ξ m p γ hψ hξ)
    -- `t` は `S'` を切断する
    have cut : CutT (S.filter (fun s => s != t)) t := by
      cases t with
      | zero => exact cut_botY G' htF (Or.inr rfl) hsub
      | one => exact cut_botY G' htF (Or.inl rfl) hsub
      | K _ => exact cut_botY G' htF (Or.inl rfl) hsub
      | plus a b =>
        exact G'.cut_of_principal htF hsub (fun _ _ htp => by simp [isPrincipal] at htp)
      | Om e => exact cut_omY G' htF hsub
      | Xi m γ => exact (XiCtxY.mk G' htF hsub htS').cut
      | Psi ξ π γ =>
        exact (PsiCtxY.mk G' htF hsub htS' (fun m p hπ hξ => hskt ξ π γ rfl m p hπ hξ)).cut
    -- `t` は `S'` の全ての元と反対称
    have antiT : ∀ z, z ∈ S.filter (fun s => s != t) → AntiT t z := by
      cases t with
      | Psi ξ π γ =>
        exact (PsiCtxY.mk G' htF hsub htS' (fun m p hπ hξ => hskt ξ π γ rfl m p hπ hξ)).anti
      | _ =>
        exact fun z hz => G'.anti_new htF hsub htS' z.size (fun _ _ _ _ _ _ e => by cases e) z hz
          (Nat.le_refl _)
    have hA := antiOn_extend G'.anti inS' antiT
    have ctx : ∀ ξ π γ, Tm.Psi ξ π γ = t → PsiCtxY (S.filter (fun s => s != t)) ξ π γ :=
      fun ξ π γ e => by
        subst e
        exact PsiCtxY.mk G' htF hsub htS' (fun m p hπ hξ => hskt ξ π γ rfl m p hπ hξ)
    refine ⟨linOn_of_cutY hA G'.lin inS' cut, hA, hNF, hcl, ?_, ?_, ?_, ?_, ?_, hsk⟩
    · intro ξ π γ hx
      by_cases e : Tm.Psi ξ π γ = t
      · have P := ctx ξ π γ e
        subst e
        exact P.k2
      · exact G'.k2 ξ π γ (inS' _ hx e)
    · intro ξ π γ hx
      by_cases e : Tm.Psi ξ π γ = t
      · have P := ctx ξ π γ e
        subst e
        exact P.k2t
      · exact G'.k2t ξ π γ (inS' _ hx e)
    · intro ξ π γ hx
      by_cases e : Tm.Psi ξ π γ = t
      · have P := ctx ξ π γ e
        subst e
        exact P.k2s
      · exact G'.k2s ξ π γ (inS' _ hx e)
    · intro m γ hx
      by_cases e : Tm.Xi m γ = t
      · subst e
        exact (XiCtxY.mk G' htF hsub htS').k2x
      · exact G'.k2x m γ (inS' _ hx e)
    · intro c γ hx
      by_cases e : Tm.Psi .zero (.Om c) γ = t
      · have P := ctx _ _ _ e
        subst e
        exact P.cx rfl
      · exact G'.cx c γ (inS' _ hx e)

/-! ### 有限集合の構成 -/

theorem WNF.succK {n : Nat} (hn : 1 ≤ n) : WNF (succK n) := by
  show isNF (_root_.RTKA.succK n) = true
  have h1 : cmp (Tm.plus (.K n) .one) (.Om (.plus (.K n) .one)) = .lt := by
    rw [cmp_eq]
    simp only [summands]
    rw [cmpList_cons_cons_ne _ _ (by rw [cmpP.eq_def]; simp [lev]), cmpP.eq_def]
    simp [lev]
  have h2 : cmp .one (.K n) = .lt := by
    rw [cmp_principal rfl rfl, cmpP_of_lev_lt (by simp only [lev]; omega)]
  simp [_root_.RTKA.succK, isNF, lt, h1, h2, summands, hn, isPrincipal]

/-- `Ψ^ξ_{Ξ_n(p)}` に対して `K_n^+` の部分項を足す -/
def skx : Tm → List Tm
  | .Psi _ (.Xi n _) _ => subs (_root_.RTKA.succK n)
  | _ => []

/-- 部分項の一覧に `K_n^+` を足した有限集合 -/
def skClose (L : List Tm) : List Tm := L ++ L.flatMap skx

theorem skClose_good {L : List Tm} (hcl : ∀ s, s ∈ L → ∀ r, r ∈ subs s → r ∈ L)
    (hNF : ∀ s, s ∈ L → WNF s) : GoodY (skClose L) := by
  apply lin_closedY _ _ (Nat.le_refl _)
  · intro s hs r hr
    simp only [skClose, List.mem_append, List.mem_flatMap] at hs ⊢
    rcases hs with hs | ⟨u, hu, hs⟩
    · exact Or.inl (hcl s hs r hr)
    · refine Or.inr ⟨u, hu, ?_⟩
      cases u with
      | Psi ξ π γ =>
        cases π with
        | Xi n p => simp only [skx] at hs ⊢; exact subs_trans hs hr
        | _ => simp [skx] at hs
      | _ => simp [skx] at hs
  · intro s hs
    simp only [skClose, List.mem_append, List.mem_flatMap] at hs
    rcases hs with hs | ⟨u, hu, hs⟩
    · exact hNF s hs
    · cases u with
      | Psi ξ π γ =>
        cases π with
        | Xi n p =>
          simp only [skx] at hs
          have hπF := (hNF _ (hcl _ hu (.Xi n p) (by simp [subs])))
          exact (WNF.succK hπF.xi.1).of_mem_subs hs
        | _ => simp [skx] at hs
      | _ => simp [skx] at hs
  · intro ξ n p γ hψ _
    simp only [skClose, List.mem_append, List.mem_flatMap] at hψ ⊢
    rcases hψ with hψ | ⟨u, hu, hψ⟩
    · exact Or.inr ⟨_, hψ, by simp [skx, self_mem_subs]⟩
    · exfalso
      cases u with
      | Psi ξ' π' γ' =>
        cases π' with
        | Xi n' p' => simp [skx, _root_.RTKA.succK, subs] at hψ
        | _ => simp [skx] at hψ
      | _ => simp [skx] at hψ

/-- 三つの標準形の部分項全体（と `K_n^+`）は `GoodY` -/
theorem goodY3 {a b c : Tm} (ha : WNF a) (hb : WNF b) (hc : WNF c) :
    GoodY (skClose (subs a ++ subs b ++ subs c)) := by
  apply skClose_good
  · intro s hs r hr
    simp only [List.mem_append] at hs ⊢
    rcases hs with (hs | hs) | hs
    · exact Or.inl (Or.inl (subs_trans hs hr))
    · exact Or.inl (Or.inr (subs_trans hs hr))
    · exact Or.inr (subs_trans hs hr)
  · intro s hs
    simp only [List.mem_append] at hs
    rcases hs with (hs | hs) | hs
    · exact ha.of_mem_subs hs
    · exact hb.of_mem_subs hs
    · exact hc.of_mem_subs hs

theorem mem3_a (a b c : Tm) : a ∈ skClose (subs a ++ subs b ++ subs c) := by
  simp [skClose, self_mem_subs]

theorem mem3_b (a b c : Tm) : b ∈ skClose (subs a ++ subs b ++ subs c) := by
  simp [skClose, self_mem_subs]

theorem mem3_c (a b c : Tm) : c ∈ skClose (subs a ++ subs b ++ subs c) := by
  simp [skClose, self_mem_subs]

/-- 体系全体の標準形の上で順序の性質が成り立つ -/
instance instFWOrder : FWOrder where
  swap ha hb := (goodY3 ha hb hb).swap (mem3_a _ _ _) (mem3_b _ _ _)
  eq ha hb h := (goodY3 ha hb hb).eq (mem3_a _ _ _) (mem3_b _ _ _) h
  trans ha hb hc h1 h2 :=
    (goodY3 ha hb hc).trans (mem3_a _ _ _) (mem3_b _ _ _) (mem3_c _ _ _) h1 h2
  k2 h w hw := (goodY3 h h h).k2 _ _ _ (mem3_a _ _ _) w hw
  k2t h w hw := (goodY3 h h h).k2t _ _ _ (mem3_a _ _ _) w hw
  k2s h w hw := (goodY3 h h h).k2s _ _ _ (mem3_a _ _ _) w hw
  ms h := (goodY3 h h h).msS (mem3_a _ _ _)
  k2x h w hw := (goodY3 h h h).k2x _ _ (mem3_a _ _ _) w hw
  cx h := (goodY3 h h h).cx _ _ (mem3_a _ _ _)

end RTKA.W
