import Compact.WF.Order

/-! 体系全体の整列性 `RTKA.wellFounded_isNF`（Rathjen の区別集合の方法）。

* 順序の性質 `FWOrder`（`instFWOrder`）と `GoodY` の補題から導く比較の道具：推移性・三分律・`Ω` と `Ω` の
  不動点・崩壊の性質・前線の証人・次の正則項。
* 区別集合と最大区別集合 `Wmax`、`Good α → α ∈ Wmax` の枠組み（Lemma 3.26、目標をたどる列）。
* `Wmax` が全ての項の構成で閉じること、標準形が全て `Wmax` に入ることと整列性。 -/

namespace RTKA.W

open Tm

theorem lt_transY {a b c : Tm} (ha : WNF a) (hb : WNF b) (hc : WNF c)
    (h1 : Lt a b) (h2 : Lt b c) : Lt a c :=
  FWOrder.trans ha hb hc h1 h2

theorem Lt.asymmY {a b : Tm} (ha : WNF a) (hb : WNF b) (h : Lt a b) : ¬ Lt b a := by
  unfold Lt at *
  rw [FWOrder.swap ha hb, h]
  decide

theorem lt_of_gtY {a b : Tm} (ha : WNF a) (hb : WNF b) (h : cmp a b = .gt) : Lt b a := by
  unfold Lt
  rw [FWOrder.swap ha hb, h]
  rfl

theorem triY {a b : Tm} (ha : WNF a) (hb : WNF b) : Lt a b ∨ a = b ∨ Lt b a := by
  cases e : cmp a b with
  | lt => exact Or.inl e
  | eq => exact Or.inr (Or.inl (FWOrder.eq ha hb e))
  | gt => exact Or.inr (Or.inr (lt_of_gtY ha hb e))

/-- `¬ a < b` なら `b ≤ a` -/
theorem le_of_not_ltY {a b : Tm} (ha : WNF a) (hb : WNF b) (h : ¬ Lt a b) : Le b a := by
  rcases triY ha hb with h' | h' | h'
  · exact absurd h' h
  · exact Or.inl h'.symm
  · exact Or.inr h'

/-- `cmp a b ≠ .gt` なら `a ≤ b` -/
theorem le_of_ne_gtY {a b : Tm} (ha : WNF a) (hb : WNF b) (h : cmp a b ≠ .gt) : Le a b := by
  cases e : cmp a b with
  | lt => exact Or.inr e
  | eq => exact Or.inl (FWOrder.eq ha hb e)
  | gt => exact absurd e h

theorem not_lt_of_leY {a b : Tm} (ha : WNF a) (hb : WNF b) (h : Le a b) : ¬ Lt b a := by
  rcases h with rfl | h
  · exact Lt.irrefl _
  · exact Lt.asymmY ha hb h

theorem lt_of_lt_of_leY {a b c : Tm} (ha : WNF a) (hb : WNF b) (hc : WNF c)
    (h1 : Lt a b) (h2 : Le b c) : Lt a c := by
  rcases h2 with rfl | h2
  · exact h1
  · exact lt_transY ha hb hc h1 h2

theorem lt_of_le_of_ltY {a b c : Tm} (ha : WNF a) (hb : WNF b) (hc : WNF c)
    (h1 : Le a b) (h2 : Lt b c) : Lt a c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact lt_transY ha hb hc h1 h2

theorem le_transY {a b c : Tm} (ha : WNF a) (hb : WNF b) (hc : WNF c)
    (h1 : Le a b) (h2 : Le b c) : Le a c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact Or.inr (lt_of_lt_of_leY ha hb hc h1 h2)

theorem le_antisymmY {a b : Tm} (ha : WNF a) (hb : WNF b) (h1 : Le a b) (h2 : Le b a) :
    a = b := by
  rcases h1 with e | h1
  · exact e
  · exact absurd h1 (not_lt_of_leY hb ha h2)

theorem eq_of_cmpP_eqY {x y : Tm} (hx : WNF x) (hy : WNF y) (hpx : isPrincipal x = true)
    (hpy : isPrincipal y = true) (h : cmpP x y = .eq) : x = y := by
  apply FWOrder.eq hx hy
  rw [cmp_principal hpx hpy, h]

theorem lt_plus_rightY {a b : Tm} (h : WNF (.plus a b)) : Lt b (.plus a b) :=
  (goodY3 h h h).lt_plus_right (mem3_a _ _ _)

/-- 主要項 `x` について `x < a + b` ⟺ `x ≤ a` -/
theorem lt_prin_plus_iffY {x a b : Tm} (hx : WNF x) (hxp : isPrincipal x = true)
    (h : WNF (.plus a b)) : Lt x (.plus a b) ↔ Le x a := by
  obtain ⟨ha, -, hap, hb0⟩ := h.plus
  have hL : Lt x (.plus a b) ↔ cmpP x a ≠ .gt := by
    unfold Lt
    rw [cmp_eq, summands_principal hxp, summands_plus]
    cases e : cmpP x a with
    | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]; simp
    | eq =>
      rw [cmpList_cons_cons_eq _ _ e]
      cases hs : summands b with
      | nil => exact absurd hs (summands_ne_nil hb0)
      | cons _ _ => rw [cmpList_nil_cons]; simp
    | gt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]; simp
  rw [hL]
  constructor
  · intro h'
    exact le_of_ne_gtY hx ha (by rwa [cmp_principal hxp hap])
  · intro h'
    rw [← cmp_principal hxp hap]
    exact ne_gt_of_le h'

theorem lt_plus_plus_neY {a b a' b' : Tm} (h : WNF (.plus a b)) (h' : WNF (.plus a' b'))
    (hne : a ≠ a') : Lt (.plus a b) (.plus a' b') ↔ Lt a a' := by
  obtain ⟨ha, -, hap, -⟩ := h.plus
  obtain ⟨ha', -, hap', -⟩ := h'.plus
  have e : cmpP a a' ≠ .eq := fun e => hne (eq_of_cmpP_eqY ha ha' hap hap' e)
  rw [lt_principal_iff hap hap']
  unfold Lt
  rw [cmp_eq, summands_plus, summands_plus, cmpList_cons_cons_ne _ _ e]

theorem one_leY {c : Tm} (hc : WNF c) (h0 : c ≠ .zero) : Le .one c := by
  rcases triY WNF.one hc with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact absurd (lt_oneY hc h) h0

/-! ### `Ω` -/

theorem lt_om_iffY {a b : Tm} (ha : WNF a) (hb : WNF b) : Lt (.Om a) (.Om b) ↔ Lt a b :=
  (goodY3 ha hb hb).lt_om_iffS (mem3_a _ _ _) (mem3_b _ _ _)

theorem le_om_of_leY {a b : Tm} (ha : WNF a) (hb : WNF b) (h : Le a b) :
    Le (.Om a) (.Om b) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr ((lt_om_iffY ha hb).mpr h)

/-- `Ψ^0_{Ω_c}(β) < Ω_e` ⟺ `c ≤ e` -/
theorem lt_psi_omY {c β e : Tm} (hψ : WNF (.Psi .zero (.Om c) β)) (he : WNF e) :
    Lt (.Psi .zero (.Om c) β) (.Om e) ↔ Le c e :=
  (goodY3 hψ he he).lt_psi_omS (mem3_a _ _ _) (mem3_b _ _ _)

theorem lt_K_omY {m : Nat} {e : Tm} (hm : 1 ≤ m) (he : WNF e) :
    Lt (.K m) (.Om e) ↔ Lt (.K m) e := by
  rcases Nat.lt_trichotomy (lev e) (m + 1) with hl | hl | hl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
  · by_cases hek : e = .K m
    · subst hek
      constructor
      · intro h
        rw [lt_principal_iff rfl rfl, cmpP.eq_def] at h
        simp only [lev, Nat.lt_irrefl, ↓reduceIte] at h
        simp at h
      · intro h; exact absurd h (Lt.irrefl _)
    · constructor
      · intro _
        rcases triY (WNF.K' hm) he with h | h | h
        · exact h
        · exact absurd h.symm hek
        · have := (lt_K_iffY he hm).mp h; exfalso; omega
      · intro _
        rw [lt_principal_iff rfl rfl, cmpP.eq_def]
        simp only [lev, hl, Nat.lt_irrefl, ↓reduceIte]
        simp [hek]
  · constructor
    · intro _; exact lt_of_lev_lt' (by simp only [lev]; omega)
    · intro _; exact lt_of_lev_lt' (by simp only [lev]; omega)

/-! ### `Ω` の不動点 -/

theorem lt_OF_omG {e X : Tm} (hX : IsOF X) (hXF : WNF X) (he : WNF e) :
    Lt X (.Om e) ↔ Lt X e :=
  (goodY3 hXF he he).lt_OF_omS hX (mem3_a _ _ _) (mem3_b _ _ _)

/-- `Ω` の不動点 `X` と `Ψ^0_{Ω_c}(β)`：`X < Ψ_c(β)` ⟺ `X < c`（KL） -/
theorem lt_OF_psiOm {X c β : Tm} (hX : IsOF X) (hXF : WNF X)
    (hψ : WNF (.Psi .zero (.Om c) β)) :
    Lt X (.Psi .zero (.Om c) β) ↔ Lt X c :=
  (goodY3 hXF hψ hψ).lt_OF_psiOmS hX (mem3_a _ _ _) (mem3_b _ _ _)

/-! ### `Ξ` どうし -/

/-! ### 崩壊の性質 -/

/-- `Ψ^ξ_π(γ)` の崩壊の性質：`z ∈ C(γ, Ψ^ξ_π(γ))` で `z < π` なら `z < Ψ^ξ_π(γ)` -/
theorem coll_psiY {ξ π γ : Tm} (ht : WNF (.Psi ξ π γ)) :
    ∀ z, WNF z → inC z γ (.Psi ξ π γ) = true → Lt z π → Lt z (.Psi ξ π γ) :=
  fun z hz => (goodY3 ht hz hz).coll_psiS (mem3_a _ _ _) z (mem3_b _ _ _)

/-! ### 前線による言い換え -/

theorem inC_frY {R g0 g d x : Tm} (hx : WNF x) (hR : WNF R) (hd : WNF d) (hg0 : WNF g0)
    (hg : WNF g) (h0 : inC x g0 R = true) (hdR : Le d R) (hgg : Le g0 g) :
    inC x g d = true ↔ ∀ w, w ∈ fr R x → inC w g d = true :=
  inC_fr x h0 (fun _ hw hn hwd => hn (lt_of_lt_of_leY (hx.of_mem_subs hw) hd hR hwd hdR))
    (fun _ hv hvg => lt_of_lt_of_leY (hx.of_mem_subs hv) hg0 hg hvg hgg)

/-- 同じ階の `Ξ_n` どうしの比較の前線による言い換え -/
theorem ff_xiY {n : Nat} {α β : Tm} (hx : WNF (.Xi n α)) (hy : WNF (.Xi n β)) (hne : α ≠ β) :
    Lt (.Xi n α) (.Xi n β) ↔
      (Lt α β ∧ ∀ w, w ∈ fr (.K n) α → Lt w (.Xi n β)) ∨
        (Lt β α ∧ ∃ w, w ∈ fr (.K n) β ∧ ¬ Lt w (.Xi n α)) := by
  obtain ⟨hn, hαF, -, -, hαC⟩ := hx.xi
  obtain ⟨-, hβF, -, -, hβC⟩ := hy.xi
  have hK := WNF.K' hn
  have hxK : Lt (.Xi n α) (.K n) := (lt_K_iffY hx hn).mpr (Nat.le_refl _)
  have hyK : Lt (.Xi n β) (.K n) := (lt_K_iffY hy hn).mpr (Nat.le_refl _)
  have collx : ∀ w, w ∈ fr (.K n) β → inC w α (.Xi n α) = true → Lt w (.Xi n α) :=
    fun w hw h => coll_xi0 hx w (hβF.of_mem_subs (fr_spec hw).1) h (fr_spec hw).2
  have colly : ∀ w, w ∈ fr (.K n) α → inC w β (.Xi n β) = true → Lt w (.Xi n β) :=
    fun w hw h => coll_xi0 hy w (hαF.of_mem_subs (fr_spec hw).1) h (fr_spec hw).2
  rw [lt_xi_xi0 hne]
  constructor
  · rintro (⟨hab, h⟩ | ⟨hba, h⟩)
    · exact Or.inl ⟨hab, (fr_inC_iff colly).mp
        ((inC_frY hαF hK hy hαF hβF hαC (Or.inr hyK) (Or.inr hab)).mp h)⟩
    · refine Or.inr ⟨hba, (fr_inC_false_iff collx).mp ?_⟩
      intro h'
      rw [(inC_frY hβF hK hx hβF hαF hβC (Or.inr hxK) (Or.inr hba)).mpr h'] at h
      cases h
  · rintro (⟨hab, h⟩ | ⟨hba, h⟩)
    · exact Or.inl ⟨hab, (inC_frY hαF hK hy hαF hβF hαC (Or.inr hyK) (Or.inr hab)).mpr
        ((fr_inC_iff colly).mpr h)⟩
    · refine Or.inr ⟨hba, ?_⟩
      cases e : inC β α (Tm.Xi n α)
      · rfl
      · exact absurd ((inC_frY hβF hK hx hβF hαF hβC (Or.inr hxK) (Or.inr hba)).mp e)
          ((fr_inC_false_iff collx).mpr h)

/-! ### 前線の証人 -/

/-- `(2)`：`a ≤ d` で `a`・`ξ`・`π` のどれかが `C(d, x)` に入らない（`x < π`）なら、`Ψ^ξ_π(a)` の引数・目標・
    Mahlo 添字の前線（`π` について）に `x` 未満でない元がある -/
theorem wit_c2 {ξ π a x d : Tm} (hy : WNF (.Psi ξ π a)) (hx : WNF x) (hd : WNF d)
    (had : Le a d) (hxπ : Lt x π)
    (hn : ¬ (inC a d x = true ∧ inC ξ d x = true ∧ inC π d x = true)) :
    ∃ w, (w ∈ fr π a ∨ w ∈ fr π π ∨ w ∈ fr π ξ) ∧ ¬ Lt w x := by
  have hP := hy.psi
  by_cases ha : ∀ w, w ∈ fr π a → Lt w x
  · by_cases hπ : ∀ w, w ∈ fr π π → Lt w x
    · by_cases hξ : ∀ w, w ∈ fr π ξ → Lt w x
      · exfalso
        apply hn
        exact ⟨(inC_frY hP.aF hP.piF hx hP.aF hd hP.Ca (Or.inr hxπ) had).mpr
            (fun w hw => inC_of_lt_node (fr_node hw) (ha w hw)),
          (inC_frY hP.xiF hP.piF hx hP.aF hd hP.Cxi (Or.inr hxπ) had).mpr
            (fun w hw => inC_of_lt_node (fr_node hw) (hξ w hw)),
          (inC_frY hP.piF hP.piF hx hP.aF hd hP.Cpi (Or.inr hxπ) had).mpr
            (fun w hw => inC_of_lt_node (fr_node hw) (hπ w hw))⟩
      · obtain ⟨w, hw, hw'⟩ := exists_of_not_forall_mem _ hξ
        exact ⟨w, Or.inr (Or.inr hw), hw'⟩
    · obtain ⟨w, hw, hw'⟩ := exists_of_not_forall_mem _ hπ
      exact ⟨w, Or.inr (Or.inl hw), hw'⟩
  · obtain ⟨w, hw, hw'⟩ := exists_of_not_forall_mem _ ha
    exact ⟨w, Or.inl hw, hw'⟩

/-- `(4)`：`ξ < σ` で `ξ ∉ C(σ, x)`（`x < y = Ψ^ξ_π(a)`）なら、`ξ` の前線（`y` について）に `x` 未満でない
    元がある（`ξ ∈ C(ξ, y)` を使う） -/
theorem wit_c4 {ξ π a x σ : Tm} (hy : WNF (.Psi ξ π a)) (hx : WNF x) (hσ : WNF σ)
    (hxy : Lt x (.Psi ξ π a)) (hξσ : Lt ξ σ) (hn : inC ξ σ x = false) :
    ∃ w, w ∈ fr (.Psi ξ π a) ξ ∧ ¬ Lt w x := by
  have hP := hy.psi
  by_cases h : ∀ w, w ∈ fr (.Psi ξ π a) ξ → Lt w x
  · exfalso
    rw [(inC_frY hP.xiF hy hx hP.xiF hσ (FWOrder.ms hy) (Or.inr hxy) (Or.inr hξσ)).mpr
      (fun w hw => inC_of_lt_node (fr_node hw) (h w hw))] at hn
    cases hn
  · exact exists_of_not_forall_mem _ h

/-- `x = Ψ^ξ_π(a) < Ξ_n(b) < π` なら `b < a` で、`b` の前線（`K_n` について）に `x` 未満でない元がある -/
theorem wit_psi_xi {ξ π a b : Tm} {n : Nat} (hx : WNF (.Psi ξ π a)) (hy : WNF (.Xi n b))
    (hl : lev π = n) (h : Lt (.Psi ξ π a) (.Xi n b)) (hyπ : Lt (.Xi n b) π) :
    Lt b a ∧ ∃ w, w ∈ fr (.K n) b ∧ ¬ Lt w (.Psi ξ π a) := by
  have hπF := hx.psi.piF
  have haF := hx.psi.aF
  obtain ⟨hn, hbF, -, -, hbC⟩ := hy.xi
  rcases (lt_psi_xiY hl).mp h with h1 | ⟨hba, hn'⟩
  · exact absurd hyπ (not_lt_of_leY hπF hy (le_of_ne_gtY hπF hy h1))
  · refine ⟨hba, ?_⟩
    have hxK : Lt (.Psi ξ π a) (.K n) := (lt_K_iffY hx hn).mpr (by simp only [lev]; omega)
    by_cases hb : ∀ w, w ∈ fr (.K n) b → Lt w (.Psi ξ π a)
    · exfalso
      rw [(inC_frY hbF (WNF.K' hn) hx hbF haF hbC (Or.inr hxK) (Or.inr hba)).mpr
        (fun w hw => inC_of_lt_node (fr_node hw) (hb w hw))] at hn'
      cases hn'
    · exact exists_of_not_forall_mem _ hb

/-- 前線の取り替え：`R' ≤ R` で `R` についての前線の元が `R'` 未満なら、`R'` についての前線の元 -/
theorem fr_sub {R R' : Tm} (hR : WNF R) (hR' : WNF R') (hle : Le R' R) {x w : Tm}
    (hx : WNF x) (hw : w ∈ fr R x) (hwR : Lt w R') : w ∈ fr R' x :=
  (goodY3 hR hR' hx).fr_sub (mem3_a _ _ _) (mem3_b _ _ _) (mem3_c _ _ _) hle hw hwR

/-- `z < c` なら `z + 1 ≤ c` -/
theorem succT_leY {z c : Tm} (hz : WNF z) (hc : WNF c) (h : Lt z c) : Le (succT z) c :=
  (goodY3 (succT_WNF hz) hc hc).succT_le (mem3_b _ _ _) (mem3_a _ _ _) h

/-- `Ω` の不動点 `X` より小さい `z` について `z + 1 < X` -/
theorem succT_lt_OF {z X : Tm} (hX : IsOF X) (hz : WNF z) (hXF : WNF X) (h : Lt z X) :
    Lt (succT z) X := by
  rcases succT_leY hz hXF h with e | h'
  · exact absurd e (succT_ne_principal z hX.principal
      (by rcases hX with ⟨n, a, rfl⟩ | ⟨ξ, π, a, rfl, -, -⟩ <;> intro e <;> cases e))
  · exact h'

/-! ### `Ω_z` の標準形 -/

/-- `0`・`K_m`・`Ω` の不動点でない標準形 `z` について `Ω_z` は標準形 -/
theorem WNF.om_ofY {z : Tm} (hz : WNF z) (h0 : z ≠ .zero) (hK : ∀ m, z ≠ .K m)
    (hX : ¬ IsOF z) : WNF (.Om z) := by
  have hlt : Lt z (.Om z) := by
    cases hs : summands z with
    | nil => exact absurd hs (summands_ne_nil h0)
    | cons h rest =>
      have hh := summands_WNF z hz h (by rw [hs]; exact List.mem_cons_self)
      have hle := head_leY hz hs
      have : Lt h (.Om z) := by
        cases h with
        | zero => simp [isPrincipal] at hh
        | plus _ _ => simp [isPrincipal] at hh
        | K m =>
          rcases hle with e | e
          · exact absurd e.symm (hK m)
          · exact (lt_K_omY hh.1.k hz).mpr e
        | Xi n a =>
          rcases hle with e | e
          · exact absurd (e ▸ Or.inl ⟨n, a, rfl⟩) hX
          · exact (lt_OF_omG (Or.inl ⟨n, a, rfl⟩) hh.1 hz).mpr e
        | one =>
          have hl : 1 ≤ lev z := lev_posY hz h0
          rcases Nat.lt_or_eq_of_le hl with hl | hl
          · rw [lt_principal_iff rfl rfl, cmpP_of_lev_lt (by simp only [lev]; exact hl)]
          · rw [lt_principal_iff rfl rfl, cmpP.eq_def]
            simp only [lev, ← hl, Nat.lt_irrefl, ↓reduceIte]
        | Om x =>
          have hx := hh.1.om
          rw [lt_om_iffY hx.1 hz]
          exact lt_of_lt_of_leY hx.1 hh.1 hz hx.2.2 hle
        | Psi s p β =>
          rcases hh.1.shape with ⟨c, rfl, rfl⟩ | hsh
          · exact (lt_psi_omY hh.1 hz).mpr
              (Or.inr (lt_of_lt_of_leY hh.1.psiOm.1 hh.1 hz (FWOrder.cx hh.1) hle))
          · rcases hle with e | e
            · exact absurd (e ▸ IsOF.psi hh.1 (notOm_of_shape hsh)) hX
            · exact (lt_OF_omG (IsOF.psi hh.1 (notOm_of_shape hsh)) hh.1 hz).mpr e
      exact lt_of_head_lt rfl hs ((lt_principal_iff hh.2 rfl).mp this)
  show isNF (.Om z) = true
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq]
  refine ⟨⟨hz, h0⟩, ?_⟩
  unfold lt
  unfold Lt at hlt
  simp [hlt]

theorem WNF.om_succT {z : Tm} (hz : WNF z) : WNF (.Om (succT z)) :=
  WNF.om_ofY (succT_WNF hz) (succT_ne_zero z) (succT_ne_K z)
    (by rintro (⟨n, a, e⟩ | ⟨ξ, π, a, e, -, -⟩) <;> cases z <;> simp [succT] at e)

theorem WNF.om_one : WNF (.Om .one) :=
  WNF.om_ofY WNF.one (by intro e; cases e) (fun _ e => by cases e)
    (by rintro (⟨n, a, e⟩ | ⟨ξ, π, a, e, -, -⟩) <;> cases e)

/-! ### 次の正則項 -/

theorem nr_specY : ∀ t : Tm, WNF t → WNF (nrY t) ∧ IsRegY (nrY t) ∧ Lt t (nrY t)
  | .zero, _ => ⟨WNF.om_one, Or.inl ⟨.one, rfl, rfl⟩, zero_lt (by intro e; cases e)⟩
  | .one, _ => ⟨WNF.om_one, Or.inl ⟨.one, rfl, rfl⟩, WNF.om_one.om.2.2⟩
  | .K _, ht => ⟨WNF.om_succT ht, Or.inl ⟨_, rfl, isSucc_succT _⟩,
      (lt_K_omY ht.k (succT_WNF ht)).mpr (lt_succT _)⟩
  | .plus a _, ht => by
    obtain ⟨ha, -, -, -⟩ := ht.plus
    obtain ⟨h1, h2, h3⟩ := nr_specY a ha
    refine ⟨h1, h2, (lt_plus_prin_iffY ht ?_).mpr h3⟩
    show isPrincipal (nrY a) = true
    rcases h2 with ⟨c, e, -⟩ | ⟨n, e⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, -⟩ <;> rw [e] <;> rfl
  | .Om a, ht => ⟨WNF.om_succT ht.om.1, Or.inl ⟨_, rfl, isSucc_succT _⟩,
      (lt_om_iffY ht.om.1 (succT_WNF ht.om.1)).mpr (lt_succT _)⟩
  | .Xi n a, ht => ⟨WNF.om_succT ht, Or.inl ⟨_, rfl, isSucc_succT _⟩,
      (lt_OF_omG (Or.inl ⟨n, a, rfl⟩) ht (succT_WNF ht)).mpr (lt_succT _)⟩
  | .Psi ξ p a, ht => by
    rcases ht.shape with ⟨c, rfl, rfl⟩ | hsh
    · exact ⟨ht.psi.piF, Or.inl ⟨c, rfl, ht.psiOm.2.2.1⟩, lt_psi_om_self c a⟩
    · rw [nrY_psi (notOm_of_shape hsh)]
      exact ⟨WNF.om_succT ht, Or.inl ⟨_, rfl, isSucc_succT _⟩,
        (lt_OF_omG (IsOF.psi ht (notOm_of_shape hsh)) ht (succT_WNF ht)).mpr (lt_succT _)⟩

theorem nr_lt_KY {t : Tm} {m : Nat} (ht : WNF t) (hm : 1 ≤ m) (h : Lt t (.K m)) :
    Lt (nrY t) (.K m) := by
  rw [lt_K_iffY (nr_specY t ht).1 hm]
  by_cases h0 : t = .zero
  · subst h0
    show 1 ≤ m
    exact hm
  · rw [lev_nrY ht h0]
    exact (lt_K_iffY ht hm).mp h

theorem nr_le_omY : ∀ t : Tm, WNF t → ∀ c : Tm, WNF (.Om c) → Lt t (.Om c) →
    Le (nrY t) (.Om c)
  | .zero, _, _, hc, _ | .one, _, _, hc, _ =>
    le_om_of_leY WNF.one hc.om.1 (one_leY hc.om.1 hc.om.2.1)
  | .K _, ht, _, hc, h =>
    le_om_of_leY (succT_WNF ht) hc.om.1 (succT_leY ht hc.om.1 ((lt_K_omY ht.k hc.om.1).mp h))
  | .plus a _, ht, c, hc, h => by
    obtain ⟨ha, -, -, -⟩ := ht.plus
    exact nr_le_omY a ha c hc (lt_transY ha ht hc (lt_plus_leftY ht) h)
  | .Om _, ht, _, hc, h =>
    le_om_of_leY (succT_WNF ht.om.1) hc.om.1
      (succT_leY ht.om.1 hc.om.1 ((lt_om_iffY ht.om.1 hc.om.1).mp h))
  | .Xi n a, ht, _, hc, h =>
    le_om_of_leY (succT_WNF ht) hc.om.1
      (succT_leY ht hc.om.1 ((lt_OF_omG (Or.inl ⟨n, a, rfl⟩) ht hc.om.1).mp h))
  | .Psi ξ p a, ht, _, hc, h => by
    rcases ht.shape with ⟨c', rfl, rfl⟩ | hsh
    · exact le_om_of_leY ht.psiOm.1 hc.om.1 ((lt_psi_omY ht hc.om.1).mp h)
    · rw [nrY_psi (notOm_of_shape hsh)]
      exact le_om_of_leY (succT_WNF ht) hc.om.1
          (succT_leY ht hc.om.1 ((lt_OF_omG (IsOF.psi ht (notOm_of_shape hsh)) ht hc.om.1).mp h))

theorem nr_lt_OFY : ∀ t : Tm, WNF t → ∀ {X : Tm}, IsOF X → WNF X → Lt t X → Lt (nrY t) X
  | .zero, _, X, hO, hX, _ | .one, _, X, hO, hX, _ => by
    have h1 : Lt .one X := by
      rcases one_leY hX (by rintro rfl; rcases hO with ⟨n, a, e⟩ | ⟨ξ, π, a, e, -, -⟩ <;> cases e)
        with e | h
      · rw [← e] at hO; rcases hO with ⟨n, a, e⟩ | ⟨ξ, π, a, e, -, -⟩ <;> cases e
      · exact h
    exact (lt_om_OFG hO).mpr h1
  | .K n, ht, X, hO, hX, h => (lt_om_OFG hO).mpr (succT_lt_OF hO ht hX h)
  | .plus a _, ht, _, hO, hX, h => by
    obtain ⟨ha, -, -, -⟩ := ht.plus
    exact nr_lt_OFY a ha hO hX (lt_transY ha ht hX (lt_plus_leftY ht) h)
  | .Om a, ht, X, hO, hX, h =>
    (lt_om_OFG hO).mpr (succT_lt_OF hO ht.om.1 hX ((lt_om_OFG hO).mp h))
  | .Xi n a, ht, X, hO, hX, h => (lt_om_OFG hO).mpr (succT_lt_OF hO ht hX h)
  | .Psi ξ p a, ht, X, hO, hX, h => by
    rcases ht.shape with ⟨c, rfl, rfl⟩ | hsh
    · -- `Ψ_c(a) < X` なら `c < X`
      have hs := ht.psiOm.2.2.1
      have hcF := ht.psiOm.1
      have hc : Lt c X := by
        rcases triY hcF hX with h' | e | h'
        · exact h'
        · subst e
          rcases hO with ⟨n, a, rfl⟩ | ⟨ξ, π, a, rfl, -, -⟩ <;> simp [isSucc, summands] at hs
        · exact absurd ((lt_OF_psiOm hO hX ht).mpr h') (Lt.asymmY ht hX h)
      exact (lt_om_OFG hO).mpr hc
    · rw [nrY_psi (notOm_of_shape hsh)]
      exact (lt_om_OFG hO).mpr (succT_lt_OF hO ht hX h)

/-- 次の正則項は `t` より大きい正則項の中で最小 -/
theorem nr_leastY (t : Tm) (ht : WNF t) (σ : Tm) (hσ : WNF σ) (hR : IsRegY σ) (h : Lt t σ) :
    Le (nrY t) σ := by
  rcases hR with ⟨c, rfl, -⟩ | ⟨m, rfl⟩ | ⟨m, q, rfl⟩ | ⟨ζ, κ, b, rfl, hζ⟩
  · exact nr_le_omY t ht c hσ h
  · exact Or.inr (nr_lt_KY ht hσ.k h)
  · exact Or.inr (nr_lt_OFY t ht (Or.inl ⟨m, q, rfl⟩) hσ h)
  · refine Or.inr (nr_lt_OFY t ht (IsOF.psi hσ ?_) hσ h)
    rcases hσ.shape with ⟨c, rfl, rfl⟩ | hsh
    · exact absurd rfl hζ
    · exact notOm_of_shape hsh

/-! ### 前線の元は項以下 -/

theorem fr_leY {R : Tm} (hR : WNF R) : ∀ {x w : Tm}, WNF x → w ∈ fr R x → Le w x
  | .zero, _, _, h | .one, _, _, h | .K _, _, _, h => by simp [fr] at h
  | .plus a b, w, hx, h => by
    obtain ⟨ha, hb, -, -⟩ := hx.plus
    have hw : WNF w := hx.of_mem_subs (fr_spec h).1
    rw [fr, List.mem_append] at h
    rcases h with h | h
    · exact Or.inr (lt_of_le_of_ltY hw ha hx (fr_leY hR ha h) (lt_plus_leftY hx))
    · exact Or.inr (lt_of_le_of_ltY hw hb hx (fr_leY hR hb h) (lt_plus_rightY hx))
  | .Om a, w, hx, h => by
    have hw : WNF w := hx.of_mem_subs (fr_spec h).1
    rw [fr] at h
    exact Or.inr (lt_of_le_of_ltY hw hx.om.1 hx (fr_leY hR hx.om.1 h) hx.om.2.2)
  | .Xi m a, w, hx, h => by
    have hw : WNF w := hx.of_mem_subs (fr_spec h).1
    have hwR := (fr_spec h).2
    rw [fr] at h
    by_cases hl : Lt (.Xi m a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      exact Or.inl h
    · exact Or.inr (lt_of_lt_of_leY hw hR hx hwR (le_of_not_ltY hx hR hl))
  | .Psi s p a, w, hx, h => by
    have hw : WNF w := hx.of_mem_subs (fr_spec h).1
    have hwR := (fr_spec h).2
    rw [fr] at h
    by_cases hl : Lt (.Psi s p a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      exact Or.inl h
    · exact Or.inr (lt_of_lt_of_leY hw hR hx hwR (le_of_not_ltY hx hR hl))

end RTKA.W

/-! ## 区別集合

* `Hull α X` は `C^α(X)`：`{0, 1, K_n} ∪ (X ∩ α)` を `+`、`Ω`、`Ξ_n`（`α < K_n`）、`Ψ^ξ_π`（`α < π`）で
  閉じたもの。
* `WPart Y` は `Y` の整礎部分。
* `Dist X`：`X` は区別集合（`X` のある元以下の `α` について、`α` の次の正則項 `nrY α` 未満では、`X` は
  `Hull α X` の整礎部分と一致する）。
* `Wmax` は区別集合全ての合併、`Good α` は `α ∈ C^α(Wmax)` かつ `C^α(Wmax) ∩ α ⊆ Wmax`。

主な結果 `wmax_of_good_hyp`：`Good α` と拡張の仮定 `Hyp α` から `α ∈ Wmax`。 -/

namespace RTKA.W.WFY

open Tm

inductive Hull (α : Tm) (X : Tm → Prop) : Tm → Prop where
  | zero : Hull α X .zero
  | one : Hull α X .one
  | K {n : Nat} (hn : 1 ≤ n) : Hull α X (.K n)
  | mem {β : Tm} (hX : X β) (hw : WNF β) (hβ : Lt β α) : Hull α X β
  | plus {a b : Tm} (hw : WNF (.plus a b)) (ha : Hull α X a) (hb : Hull α X b) :
      Hull α X (.plus a b)
  | om {a : Tm} (hw : WNF (.Om a)) (ha : Hull α X a) : Hull α X (.Om a)
  | xi {n : Nat} {a : Tm} (hw : WNF (.Xi n a)) (hα : Lt α (.K n)) (ha : Hull α X a) :
      Hull α X (.Xi n a)
  | psi {ξ π a : Tm} (hw : WNF (.Psi ξ π a)) (hα : Lt α π) (hξ : Hull α X ξ)
      (hσ : Hull α X π) (ha : Hull α X a) : Hull α X (.Psi ξ π a)

def Rel (Y : Tm → Prop) (x y : Tm) : Prop := Y x ∧ Lt x y

def WPart (Y : Tm → Prop) (β : Tm) : Prop := Y β ∧ Acc (Rel Y) β

def Dist (X : Tm → Prop) : Prop :=
  (∀ β, X β → WNF β) ∧
    ∀ α, WNF α → (∃ δ, X δ ∧ Le α δ) →
      ∀ β, (WPart (Hull α X) β ∧ Lt β (nrY α)) ↔ (X β ∧ Lt β (nrY α))

def Wmax (β : Tm) : Prop := ∃ X, Dist X ∧ X β

def Good (α : Tm) : Prop := Hull α Wmax α ∧ ∀ β, Hull α Wmax β → Lt β α → Wmax β

/-! ### 生成集合 -/

theorem Hull.wf_of {α : Tm} {X : Tm → Prop} {β : Tm} (h : Hull α X β) : WNF β := by
  cases h with
  | zero => exact WNF.zero
  | one => exact WNF.one
  | K hn => exact WNF.K' hn
  | mem _ hw _ => exact hw
  | plus hw _ _ => exact hw
  | om hw _ => exact hw
  | xi hw _ _ => exact hw
  | psi hw _ _ _ _ => exact hw

/-- 生成集合の元を構成子ごとに写す（元と、添字の条件を与えて） -/
theorem Hull.map {α β : Tm} {X Y : Tm → Prop}
    (hmem : ∀ γ, X γ → WNF γ → Lt γ α → Hull β Y γ)
    (hreg : ∀ σ, WNF σ → IsRegY σ → Lt α σ → Lt β σ) {γ : Tm}
    (h : Hull α X γ) : Hull β Y γ := by
  induction h with
  | zero => exact Hull.zero
  | one => exact Hull.one
  | K hn => exact Hull.K hn
  | mem hX hw hlt => exact hmem _ hX hw hlt
  | plus hw _ _ iha ihb => exact Hull.plus hw iha ihb
  | om hw _ iha => exact Hull.om hw iha
  | xi hw hα _ iha => exact Hull.xi hw (hreg _ (WNF.K' hw.xi.1) (IsRegY.K _) hα) iha
  | psi hw hα _ _ _ ihξ ihσ iha =>
    exact Hull.psi hw (hreg _ hw.psi.piF (IsRegY.tgt hw) hα) ihξ ihσ iha

theorem Hull.mono {α : Tm} {X Y : Tm → Prop}
    (h : ∀ γ, X γ → WNF γ → Lt γ α → Y γ) {β : Tm} (hb : Hull α X β) :
    Hull α Y β :=
  hb.map (fun γ hX hw hlt => Hull.mem (h γ hX hw hlt) hw hlt) (fun _ _ _ h => h)

theorem Hull.congr {α : Tm} {X Y : Tm → Prop}
    (h : ∀ γ, WNF γ → Lt γ α → (X γ ↔ Y γ)) (β : Tm) :
    Hull α X β ↔ Hull α Y β :=
  ⟨Hull.mono (fun γ hX hw hlt => (h γ hw hlt).mp hX),
    Hull.mono (fun γ hY hw hlt => (h γ hw hlt).mpr hY)⟩

/-- `α` より大きい正則項は `nrY α` 未満の全ての項より大きい -/
theorem lt_of_lt_nr {α β σ : Tm} (wα : WNF α) (wβ : WNF β) (wσ : WNF σ)
    (hσR : IsRegY σ) (h1 : Lt α σ) (h2 : Lt β (nrY α)) : Lt β σ :=
  lt_of_lt_of_leY wβ (nr_specY α wα).1 wσ h2 (nr_leastY α wα σ wσ hσR h1)

/-- 次の正則項までの範囲でパラメタを上げる -/
theorem Hull.raise {α β : Tm} {X : Tm → Prop} (wα : WNF α) (wβ : WNF β)
    (h1 : Lt α β) (h2 : Lt β (nrY α)) {γ : Tm} (hγ : Hull α X γ) :
    Hull β X γ :=
  hγ.map (fun _ hX hw hlt => Hull.mem hX hw (lt_transY hw wα wβ hlt h1))
    (fun _ wσ hσR hσ => lt_of_lt_nr wα wβ wσ hσR hσ h2)

theorem Hull.lower_aux {X : Tm → Prop} (HX : ∀ γ, X γ → Hull γ X γ) {α : Tm}
    (wα : WNF α) : ∀ γ β : Tm, WNF β → Le α β → Hull β X γ →
      Hull α X γ ∨ (X γ ∧ Lt γ β) := by
  intro γ
  induction γ using size_induction with
  | h γ ih =>
    intro β wβ hαβ h
    have conv : ∀ c : Tm, c.size < γ.size → Hull β X c → Hull α X c := by
      intro c hc hcβ
      have wc := hcβ.wf_of
      refine (ih c hc β wβ hαβ hcβ).elim id (fun ⟨hXc, _⟩ => ?_)
      by_cases hca : Lt c α
      · exact Hull.mem hXc wc hca
      · exact (ih c hc c wc (le_of_not_ltY wc wα hca) (HX c hXc)).resolve_right
          (fun ⟨_, h⟩ => Lt.irrefl _ h)
    cases h with
    | zero => exact Or.inl Hull.zero
    | one => exact Or.inl Hull.one
    | K hn => exact Or.inl (Hull.K hn)
    | mem hX _ hlt => exact Or.inr ⟨hX, hlt⟩
    | plus hw ha hb =>
      exact Or.inl (Hull.plus hw (conv _ (by size_omega) ha) (conv _ (by size_omega) hb))
    | om hw ha => exact Or.inl (Hull.om hw (conv _ (by size_omega) ha))
    | xi hw hβK ha =>
      exact Or.inl (Hull.xi hw (lt_of_le_of_ltY wα wβ (WNF.K' hw.xi.1) hαβ hβK)
        (conv _ (by size_omega) ha))
    | psi hw hβσ hξ hσ ha =>
      exact Or.inl (Hull.psi hw (lt_of_le_of_ltY wα wβ hw.psi.piF hαβ hβσ) (conv _ (by size_omega) hξ)
        (conv _ (by size_omega) hσ) (conv _ (by size_omega) ha))

/-- `α ≤ β` なら `C^β(X) ⊆ C^α(X)`（`X` の各元が自分の生成集合に入るとき） -/
theorem Hull.lower {X : Tm → Prop} (HX : ∀ γ, X γ → Hull γ X γ) {α β : Tm}
    (wα : WNF α) (wβ : WNF β) (hαβ : Le α β) {γ : Tm} (h : Hull β X γ) :
    Hull α X γ := by
  have wγ := h.wf_of
  refine (Hull.lower_aux HX wα γ β wβ hαβ h).elim id (fun ⟨hX, _⟩ => ?_)
  by_cases hγα : Lt γ α
  · exact Hull.mem hX wγ hγα
  · exact (Hull.lower_aux HX wα γ γ wγ (le_of_not_ltY wγ wα hγα) (HX γ hX)).resolve_right
      (fun ⟨_, h⟩ => Lt.irrefl _ h)

theorem Hull.sub_of_lt_nr {X : Tm → Prop} (HX : ∀ γ, X γ → Hull γ X γ) {β γ : Tm}
    (wβ : WNF β) (wγ : WNF γ) (h : Lt γ (nrY β)) {x : Tm}
    (hx : Hull β X x) : Hull γ X x := by
  rcases triY wγ wβ with h' | rfl | h'
  · exact Hull.lower HX wγ wβ (Or.inr h') hx
  · exact hx
  · exact Hull.raise wβ wγ h' h hx

/-! ### 整礎部分 -/

theorem acc_of_below {Y Z : Tm → Prop} (hY : ∀ x, Y x → WNF x) :
    ∀ β : Tm, Acc (Rel Z) β → WNF β → (∀ x, Y x → Lt x β → Z x) →
      Acc (Rel Y) β := by
  intro β hacc
  induction hacc with
  | intro β _ ih =>
    intro wβ hb
    refine Acc.intro β ?_
    intro x hx
    exact ih x ⟨hb x hx.1 hx.2, hx.2⟩ (hY x hx.1)
      (fun x' hx' hx'x => hb x' hx' (lt_transY (hY x' hx') (hY x hx.1) wβ hx'x hx.2))

theorem acc_sub {Y Z : Tm → Prop} (h : ∀ x, Y x → Z x) :
    ∀ β : Tm, Acc (Rel Z) β → Acc (Rel Y) β := by
  intro β hacc
  induction hacc with
  | intro β _ ih =>
    exact Acc.intro β (fun x hx => ih x ⟨h x hx.1, hx.2⟩)

theorem WPart.congr {Y Z : Tm → Prop} (h : ∀ x, Y x ↔ Z x) (β : Tm) :
    WPart Y β ↔ WPart Z β :=
  Iff.intro (fun hb => ⟨(h β).mp hb.1, acc_sub (fun x hx => (h x).mpr hx) β hb.2⟩)
    (fun hb => ⟨(h β).mpr hb.1, acc_sub (fun x hx => (h x).mp hx) β hb.2⟩)

theorem WPart.down {Y : Tm → Prop} {β γ : Tm} (hβ : WPart Y β) (hγ : Y γ)
    (h : Lt γ β) : WPart Y γ :=
  ⟨hγ, hβ.2.inv ⟨hγ, h⟩⟩

/-! ### 区別集合 -/

theorem Dist.mem_wf {X : Tm → Prop} (hX : Dist X) {β : Tm} (h : X β) : WNF β :=
  hX.1 β h

theorem Dist.self {X : Tm → Prop} (hX : Dist X) {γ : Tm} (hγ : X γ) :
    WPart (Hull γ X) γ := by
  have wγ := hX.mem_wf hγ
  exact ((hX.2 γ wγ ⟨γ, hγ, Or.inl rfl⟩ γ).mpr ⟨hγ, (nr_specY γ wγ).2.2⟩).1

theorem Dist.self_hull {X : Tm → Prop} (hX : Dist X) {γ : Tm} (hγ : X γ) : Hull γ X γ :=
  (hX.self hγ).1

theorem Dist.hull {X : Tm → Prop} (hX : Dist X) {γ : Tm} (hγ : X γ) {β : Tm}
    (wβ : WNF β) : Hull β X γ := by
  have wγ := hX.mem_wf hγ
  by_cases h : Lt γ β
  · exact Hull.mem hγ wγ h
  · exact Hull.lower (fun _ h => hX.self_hull h) wβ wγ (le_of_not_ltY wγ wβ h)
      (hX.self_hull hγ)

theorem Dist.acc {X : Tm → Prop} (hX : Dist X) {δ : Tm} (hδ : X δ) : Acc (Rel X) δ := by
  have wδ := hX.mem_wf hδ
  exact acc_of_below hX.1 δ (hX.self hδ).2 wδ
    (fun x hx hxδ => Hull.mem hx (hX.mem_wf hx) hxδ)

/-- 区別集合どうしの比較（`X` と `Y` に沿った二重の帰納法） -/
theorem dist_claim {X Y : Tm → Prop} (hX : Dist X) (hY : Dist Y) :
    ∀ δ, X δ → (∃ ε, Y ε ∧ Le δ ε) → Y δ ∧ (∀ ε, Y ε → Lt ε δ → X ε) := by
  intro δ hδ
  induction hX.acc hδ with
  | intro δ _ ihX =>
    intro hδY
    obtain ⟨ε₀, hε₀, hδε₀⟩ := hδY
    have wδ := hX.mem_wf hδ
    have wε₀ := hY.mem_wf hε₀
    have s1 : ∀ x, X x → Lt x δ → Y x := fun x hx hxδ =>
      (ihX x ⟨hx, hxδ⟩ hx
        ⟨ε₀, hε₀, Or.inr (lt_of_lt_of_leY (hX.mem_wf hx) wδ wε₀ hxδ hδε₀)⟩).1
    have key2 : ∀ ε, Acc (Rel Y) ε → Y ε → Lt ε δ → X ε := by
      intro ε hacc'
      induction hacc' with
      | intro ε _ ihY =>
        intro hε hεδ
        have wε := hY.mem_wf hε
        have agree : ∀ γ, WNF γ → Lt γ ε → (X γ ↔ Y γ) := fun γ wγ hγε =>
          Iff.intro (fun hγ => s1 γ hγ (lt_transY wγ wε wδ hγε hεδ))
            (fun hγ => ihY γ ⟨hγ, hγε⟩ hγ (lt_transY wγ wε wδ hγε hεδ))
        have hxε : WPart (Hull ε X) ε :=
          (WPart.congr (Hull.congr agree) ε).mpr (hY.self hε)
        exact ((hX.2 ε wε ⟨δ, hδ, Or.inr hεδ⟩ ε).mp ⟨hxε, (nr_specY ε wε).2.2⟩).1
    have s2 : ∀ ε, Y ε → Lt ε δ → X ε := fun ε hε => key2 ε (hY.acc hε) hε
    refine ⟨?_, s2⟩
    have agree : ∀ γ, WNF γ → Lt γ δ → (X γ ↔ Y γ) := fun γ _ hγδ =>
      Iff.intro (fun hγ => s1 γ hγ hγδ) (fun hγ => s2 γ hγ hγδ)
    have hyδ : WPart (Hull δ Y) δ := (WPart.congr (Hull.congr agree) δ).mp (hX.self hδ)
    exact ((hY.2 δ wδ ⟨ε₀, hε₀, hδε₀⟩ δ).mp ⟨hyδ, (nr_specY δ wδ).2.2⟩).1

theorem dist_agree {X Y : Tm → Prop} (hX : Dist X) (hY : Dist Y) {α : Tm}
    (wα : WNF α) (hαX : ∃ δ, X δ ∧ Le α δ) (hαY : ∃ ε, Y ε ∧ Le α ε) :
    ∀ β, Lt β (nrY α) → (X β ↔ Y β) := by
  obtain ⟨δ, hδ, hαδ⟩ := hαX
  obtain ⟨ε, hε, hαε⟩ := hαY
  have agree : ∀ γ, WNF γ → Lt γ α → (X γ ↔ Y γ) := fun γ wγ hγα =>
    Iff.intro
      (fun hγ => (dist_claim hX hY γ hγ
        ⟨ε, hε, Or.inr (lt_of_lt_of_leY wγ wα (hY.mem_wf hε) hγα hαε)⟩).1)
      (fun hγ => (dist_claim hY hX γ hγ
        ⟨δ, hδ, Or.inr (lt_of_lt_of_leY wγ wα (hX.mem_wf hδ) hγα hαδ)⟩).1)
  have hc := Hull.congr agree
  intro β hβ
  exact Iff.intro
    (fun hb => ((hY.2 α wα ⟨ε, hε, hαε⟩ β).mp
      ⟨(WPart.congr hc β).mp ((hX.2 α wα ⟨δ, hδ, hαδ⟩ β).mpr ⟨hb, hβ⟩).1, hβ⟩).1)
    (fun hb => ((hX.2 α wα ⟨δ, hδ, hαδ⟩ β).mp
      ⟨(WPart.congr hc β).mpr ((hY.2 α wα ⟨ε, hε, hαε⟩ β).mpr ⟨hb, hβ⟩).1, hβ⟩).1)

/-! ### 最大区別集合 -/

theorem wmax_dist : Dist Wmax := by
  refine ⟨fun β hβ => hβ.elim (fun X h => h.1.mem_wf h.2), ?_⟩
  intro α wα hα β
  obtain ⟨δ, ⟨X₀, hX₀, hδ⟩, hαδ⟩ := hα
  have hnα := nr_specY α wα
  have agreeW : ∀ γ, Lt γ (nrY α) → (Wmax γ ↔ X₀ γ) := by
    intro γ hγ
    refine Iff.intro ?_ (fun h => ⟨X₀, hX₀, h⟩)
    intro hW
    obtain ⟨Y, hY, hγY⟩ := hW
    have wγ := hY.mem_wf hγY
    by_cases hγα : Lt γ α
    · exact (dist_agree hX₀ hY wγ
        ⟨δ, hδ, Or.inr (lt_of_lt_of_leY wγ wα (hX₀.mem_wf hδ) hγα hαδ)⟩
        ⟨γ, hγY, Or.inl rfl⟩ γ (nr_specY γ wγ).2.2).mpr hγY
    · exact (dist_agree hX₀ hY wα ⟨δ, hδ, hαδ⟩ ⟨γ, hγY, le_of_not_ltY wγ wα hγα⟩ γ hγ).mpr hγY
  have hc : ∀ x, Hull α Wmax x ↔ Hull α X₀ x :=
    Hull.congr (fun γ wγ hγα => agreeW γ (lt_transY wγ wα hnα.1 hγα hnα.2.2))
  rw [WPart.congr hc β, hX₀.2 α wα ⟨δ, hδ, hαδ⟩ β]
  exact Iff.intro (fun h => ⟨(agreeW β h.2).mpr h.1, h.2⟩)
    (fun h => ⟨(agreeW β h.2).mp h.1, h.2⟩)

theorem wmax_wf {β : Tm} (h : Wmax β) : WNF β := wmax_dist.mem_wf h

theorem wmax_self {γ : Tm} (h : Wmax γ) : WPart (Hull γ Wmax) γ := wmax_dist.self h

theorem wmax_hull {γ : Tm} (h : Wmax γ) {β : Tm} (wβ : WNF β) : Hull β Wmax γ :=
  wmax_dist.hull h wβ

theorem wmax_acc {δ : Tm} (h : Wmax δ) : Acc (Rel Wmax) δ := wmax_dist.acc h

theorem HW : ∀ γ, Wmax γ → Hull γ Wmax γ := fun _ h => wmax_dist.self_hull h

/-- `C^β(Wmax)` の元で、`β⁺` 未満の `Wmax` の元以下のものは `Wmax` に入る -/
theorem wmax_bounded {α β δ : Tm} (wβ : WNF β) (hα : Hull β Wmax α) (hδ : Wmax δ)
    (hαδ : Le α δ) (hδβ : Lt δ (nrY β)) : Wmax α := by
  have wδ := wmax_wf hδ
  have wα := hα.wf_of
  have hα' : Hull δ Wmax α := Hull.sub_of_lt_nr HW wβ wδ hδβ hα
  rcases hαδ with e | hlt
  · rw [e]
    exact hδ
  · have hw := WPart.down (wmax_self hδ) hα' hlt
    exact ((wmax_dist.2 δ wδ ⟨δ, hδ, Or.inl rfl⟩ α).mp
      ⟨hw, lt_transY wα wδ (nr_specY δ wδ).1 hlt (nr_specY δ wδ).2.2⟩).1

theorem wmax_good {γ : Tm} (h : Wmax γ) : Good γ :=
  ⟨HW γ h, fun _ hβ hlt =>
    wmax_bounded (wmax_wf h) hβ h (Or.inr hlt) (nr_specY _ (wmax_wf h)).2.2⟩

theorem acc_hull_of_wmax {μ δ : Tm} (hδ : Wmax δ)
    (h : ∀ x, Hull μ Wmax x → Lt x δ → Wmax x) : Acc (Rel (Hull μ Wmax)) δ :=
  acc_of_below (fun _ hx => hx.wf_of) δ (wmax_acc hδ) (wmax_wf hδ) h

/-! ### `Wmax` の拡張 -/

/-- 拡張の仮定：`γ⁺ ≤ α` の `C^γ(Wmax)` の整礎部分（`γ⁺` 未満）は `Wmax` に入る -/
def Hyp (α : Tm) : Prop := ∀ γ, WNF γ → Le (nrY γ) α → ∀ β,
  WPart (Hull γ Wmax) β → Lt β (nrY γ) → Wmax β

def Ext (α β : Tm) : Prop := WPart (Hull α Wmax) β ∧ Lt β (nrY α)

theorem wmax_of_good_hyp {α : Tm} (hG : Good α) (hH : Hyp α) : Wmax α := by
  have wα := hG.1.wf_of
  have hnα := nr_specY α wα
  have accα : ∀ x, Wmax x → Lt x α → Acc (Rel (Hull α Wmax)) x := fun x hx hxα =>
    acc_hull_of_wmax hx (fun x' hx' hx'x =>
      hG.2 x' hx' (lt_transY hx'.wf_of (wmax_wf hx) wα hx'x hxα))
  have agree : ∀ β, Lt β α → (Ext α β ↔ Wmax β) := fun β hβα =>
    ⟨fun hb => hG.2 β hb.1.1 hβα, fun hb => ⟨⟨Hull.mem hb (wmax_wf hb) hβα, accα β hb hβα⟩,
      lt_transY (wmax_wf hb) wα hnα.1 hβα hnα.2.2⟩⟩
  have hYwf : ∀ β, Ext α β → WNF β := fun β hb => hb.1.1.wf_of
  refine ⟨Ext α, ⟨hYwf, ?_⟩,
    ⟨⟨hG.1, Acc.intro α (fun x hx => accα x (hG.2 x hx.1 hx.2) hx.2)⟩, hnα.2.2⟩⟩
  intro γ wγ ⟨ε, hε, hγε⟩ β
  have hnγ := nr_specY γ wγ
  have hnγnα := nr_leastY γ wγ (nrY α) hnα.1 hnα.2.1
    (lt_of_le_of_ltY wγ (hYwf ε hε) hnα.1 hγε hε.2)
  have split : Le (nrY γ) α ∨ Lt α (nrY γ) :=
    (triY hnγ.1 wα).elim (fun h => Or.inl (Or.inr h))
      (fun h => h.elim (fun e => Or.inl (Or.inl e)) Or.inr)
  rcases split with hle | hgt
  · have hγα : Lt γ α := lt_of_lt_of_leY wγ hnγ.1 wα hnγ.2.2 hle
    rw [WPart.congr (Hull.congr (fun x wx hxγ => agree x (lt_transY wx wγ wα hxγ hγα))) β]
    constructor
    · intro hb
      exact ⟨(agree β (lt_of_lt_of_leY hb.1.1.wf_of hnγ.1 wα hb.2 hle)).mpr
        (hH γ wγ hle β hb.1 hb.2), hb.2⟩
    · intro hb
      have wb := hYwf β hb.1
      have hbW := (agree β (lt_of_lt_of_leY wb hnγ.1 wα hb.2 hle)).mp hb.1
      refine ⟨?_, hb.2⟩
      by_cases hβγ : Lt β γ
      · exact ⟨Hull.mem hbW wb hβγ, acc_hull_of_wmax hbW (fun x hx hxβ => wmax_bounded wb
          (Hull.lower HW wb wγ (Or.inr hβγ) hx) hbW (Or.inr hxβ) (nr_specY β wb).2.2)⟩
      · exact ((wmax_dist.2 γ wγ ⟨β, hbW, le_of_not_ltY wb wγ hβγ⟩ β).mpr ⟨hbW, hb.2⟩).1
  · have heqn : nrY γ = nrY α :=
      le_antisymmY hnγ.1 hnα.1 hnγnα (nr_leastY α wα (nrY γ) hnγ.1 hnγ.2.1 hgt)
    have hc : ∀ x, Hull γ (Ext α) x ↔ Hull α Wmax x := by
      rcases triY wγ wα with hγα | rfl | hαγ
      · intro x
        rw [Hull.congr (fun x wx hxγ => agree x (lt_transY wx wγ wα hxγ hγα)) x]
        exact ⟨Hull.raise wγ wα hγα hgt, Hull.lower HW wγ wα (Or.inr hγα)⟩
      · exact Hull.congr (fun x _ hxγ => agree x hxγ)
      · intro x
        exact ⟨Hull.map (fun _ hY _ _ => hY.1.1) (fun _ wσ _ h => lt_transY wα wγ wσ hαγ h),
          Hull.map (fun _ hW hw hlt => Hull.mem ((agree _ hlt).mpr hW) hw
            (lt_transY hw wα wγ hlt hαγ))
            (fun _ wσ hσR h => lt_of_lt_nr wα wγ wσ hσR h (by rw [← heqn]; exact hnγ.2.2))⟩
    rw [WPart.congr hc β, heqn]
    exact ⟨fun hb => ⟨⟨hb.1, hb.2⟩, hb.2⟩, fun hb => ⟨hb.1.1, hb.2⟩⟩

/-! ## `Good α → α ∈ Wmax` の枠組み

* 生成集合 `C^θ(Wmax)` の移し替え（`ν ≤ R` に一般化）・係数についての帰納法・前線は Mahlo 添字も含めて扱う。
* `(18)` の証明の場合 2（`case_two`）：`α = Ψ^ξ_π(a) < γ = Ψ^σ_κ(b)`（`γ < π ≤ β < κ`）の比較を
  Prop. 4.20 の (1)〜(4) で分ける。
* `Ψ^ξ`（`ξ > 0`）も崩壊の目標になるので、目標をたどる列 `Ch` は任意の長さになる。段階 3
  （`step_three`）は列をたどり（`chain_walk`、Arai の Lemma 6.38 の段階 3）、目標が `η` より大きい元に
  着けばそれを `C^η(Wmax)` に移して `Wmax` に入れ、列の行き着く先が `η` の崩壊になる場合だけを仮定
  `H15 η` に任せる。`H15` は次の節で `η` の形ごとに示す。 -/

theorem fr_mem_psi_s {R s p a w : Tm} (hn : ¬ Lt (.Psi s p a) R) (h : w ∈ fr R s) :
    w ∈ fr R (.Psi s p a) := by
  rw [fr]; simp only [hn, ↓reduceIte, List.mem_append]; exact Or.inl (Or.inl h)

/-! ### 生成集合の間の移し替えと係数についての帰納法 -/

/-- 前線（`R` について）が `θ` 未満の `C^θ(Wmax)` の元は、`ν ≤ R` なら `C^ν(Wmax)` に入る -/
theorem hull_transfer {θ ν R : Tm} (wν : WNF ν) (wR : WNF R) (hνR : Le ν R) (S : Nat)
    (good : ∀ x, Hull θ Wmax x → Lt x θ → x.size < S → Wmax x) :
    ∀ x, Hull θ Wmax x → x.size < S → (∀ w, w ∈ fr R x → Lt w θ) → Hull ν Wmax x := by
  intro x
  induction x using size_induction with
  | h x ih =>
    intro hx hs hfr
    by_cases hxθ : Lt x θ
    · exact wmax_hull (good x hx hxθ hs) wν
    · cases hx with
      | zero => exact Hull.zero
      | one => exact Hull.one
      | K hn => exact Hull.K hn
      | mem _ _ hlt => exact absurd hlt hxθ
      | plus hw ha hb =>
        exact Hull.plus hw
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_plus_l h)))
          (ih _ (by size_omega) hb (by size_omega) (fun w h => hfr w (fr_mem_plus_r h)))
      | om hw ha =>
        exact Hull.om hw
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_om h)))
      | @xi n a hw _ ha =>
        have hnR : ¬ Lt (.Xi n a) R := fun hl => hxθ (hfr _ (fr_mem_xi_self hl))
        have wK := WNF.K' hw.xi.1
        have hνK : Lt ν (.K n) := lt_of_le_of_ltY wν wR wK hνR
          (lt_of_le_of_ltY wR hw wK (le_of_not_ltY hw wR hnR)
            ((lt_K_iffY hw hw.xi.1).mpr (Nat.le_refl _)))
        exact Hull.xi hw hνK (ih _ (by size_omega) ha (by size_omega)
          (fun w h => hfr w (fr_mem_xi hnR h)))
      | @psi ξ π a hw _ hξ hσ ha =>
        have hnR : ¬ Lt (.Psi ξ π a) R := fun hl => hxθ (hfr _ (fr_mem_psi_self hl))
        have wπ := hw.psi.piF
        have hνσ : Lt ν π := lt_of_le_of_ltY wν wR wπ hνR
          (lt_of_le_of_ltY wR hw wπ (le_of_not_ltY hw wR hnR) (lt_psi_targetY hw))
        exact Hull.psi hw hνσ
          (ih _ (by size_omega) hξ (by size_omega) (fun w h => hfr w (fr_mem_psi_s hnR h)))
          (ih _ (by size_omega) hσ (by size_omega) (fun w h => hfr w (fr_mem_psi_p hnR h)))
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_psi_a hnR h)))

/-- `C^θ(Wmax)` の元で、前線（`R` について）が `θ` 未満、`R` 以上の節点の引数が `g` 未満のものに
    ついての帰納法 -/
theorem coeff_induction {θ R g : Tm} (P : Tm → Prop) (S : Nat)
    (good : ∀ x, Hull θ Wmax x → Lt x θ → x.size < S → P x)
    (hzero : P .zero) (hone : P .one) (hK : ∀ {n : Nat}, 1 ≤ n → P (.K n))
    (hplus : ∀ {a b : Tm}, WNF (.plus a b) → P a → P b → P (.plus a b))
    (hom : ∀ {a : Tm}, WNF (.Om a) → P a → P (.Om a))
    (hxi : ∀ {n : Nat} {a : Tm}, WNF (.Xi n a) → Lt a g → P a → P (.Xi n a))
    (hpsi : ∀ {ξ π a : Tm}, WNF (.Psi ξ π a) → Lt a g → P ξ → P π → P a →
      P (.Psi ξ π a)) :
    ∀ x, Hull θ Wmax x → x.size < S → (∀ w, w ∈ fr R x → Lt w θ) → inC x g R = true →
      P x := by
  intro x
  induction x using size_induction with
  | h x ih =>
    intro hx hs hfr hC
    by_cases hxθ : Lt x θ
    · exact good x hx hxθ hs
    · cases hx with
      | zero => exact hzero
      | one => exact hone
      | K hn => exact hK hn
      | mem _ _ hlt => exact absurd hlt hxθ
      | plus hw ha hb =>
        rw [inC_plus, Bool.and_eq_true] at hC
        exact hplus hw
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_plus_l h)) hC.1)
          (ih _ (by size_omega) hb (by size_omega) (fun w h => hfr w (fr_mem_plus_r h)) hC.2)
      | om hw ha =>
        rw [inC_om] at hC
        exact hom hw
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_om h)) hC)
      | @xi n a hw _ ha =>
        have hnR : ¬ Lt (.Xi n a) R := fun hl => hxθ (hfr _ (fr_mem_xi_self hl))
        have hC' := (inC_xi_iff.mp hC).resolve_left hnR
        exact hxi hw hC'.2 (ih _ (by size_omega) ha (by size_omega)
          (fun w h => hfr w (fr_mem_xi hnR h)) hC'.1)
      | @psi ξ π a hw _ hξ hσ ha =>
        have hnR : ¬ Lt (.Psi ξ π a) R := fun hl => hxθ (hfr _ (fr_mem_psi_self hl))
        have hC' := (inC_psi_iff.mp hC).resolve_left hnR
        exact hpsi hw hC'.2.2.2
          (ih _ (by size_omega) hξ (by size_omega) (fun w h => hfr w (fr_mem_psi_s hnR h))
            hC'.2.1)
          (ih _ (by size_omega) hσ (by size_omega) (fun w h => hfr w (fr_mem_psi_p hnR h))
            hC'.1)
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_psi_a hnR h))
            hC'.2.2.1)

/-! ### `Wmax` の元の部分 -/

theorem wmax_om_arg {c : Tm} (h : Wmax (.Om c)) : Wmax c := by
  cases (wmax_good h).1 with
  | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
  | om hw hc => exact (wmax_good h).2 c hc hw.om.2.2

theorem fr_hull_wmax {θ R : Tm}
    (IH : ∀ m, Wmax m → Lt m θ → ∀ w, w ∈ fr R m → Wmax w) :
    ∀ y, Hull θ Wmax y → ∀ w, w ∈ fr R y → Wmax w ∨ Hull θ Wmax w := by
  intro y hy
  induction hy with
  | zero => intro w h; simp [fr] at h
  | one => intro w h; simp [fr] at h
  | K _ => intro w h; simp [fr] at h
  | mem hX _ hlt => intro w h; exact Or.inl (IH _ hX hlt w h)
  | plus _ _ _ iha ihb =>
    intro w h
    rw [fr, List.mem_append] at h
    rcases h with h | h
    · exact iha w h
    · exact ihb w h
  | om _ _ iha => intro w h; rw [fr] at h; exact iha w h
  | @xi n a hw hα ha iha =>
    intro w h
    rw [fr] at h
    by_cases hl : Lt (.Xi n a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact Or.inr (Hull.xi hw hα ha)
    · simp only [hl, ↓reduceIte] at h
      exact iha w h
  | @psi ξ π a hw hα hξ hσ ha ihξ ihσ iha =>
    intro w h
    rw [fr] at h
    by_cases hl : Lt (.Psi ξ π a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact Or.inr (Hull.psi hw hα hξ hσ ha)
    · simp only [hl, ↓reduceIte, List.mem_append] at h
      rcases h with (h | h) | h
      · exact ihξ w h
      · exact ihσ w h
      · exact iha w h

/-- `Wmax` の元の前線の元は `Wmax` に入る -/
theorem fr_wmax {R : Tm} (wR : WNF R) : ∀ x, Wmax x → ∀ w, w ∈ fr R x → Wmax w := by
  intro x hx
  induction wmax_acc hx with
  | intro x _ ih =>
    intro w hw
    have hG := wmax_good hx
    rcases fr_hull_wmax (fun m hm hmx => ih m ⟨hm, hmx⟩ hm) x hG.1 w hw with h | h
    · exact h
    · rcases fr_leY wR (wmax_wf hx) hw with e | hlt
      · rw [e]; exact hx
      · exact hG.2 w h hlt

/-- `C^β(Wmax)` の元の前線の元で `γ` 未満のものは、`γ` 未満の `C^β(Wmax)` の元が `Wmax` に入るなら
    `Wmax` に入る -/
theorem fr_hull_below {β γ R y : Tm} (wR : WNF R) (hy : Hull β Wmax y)
    (MIH : ∀ ζ, Hull β Wmax ζ → Lt ζ γ → Wmax ζ) {w : Tm} (hw : w ∈ fr R y) (hwγ : Lt w γ) :
    Wmax w := by
  rcases fr_hull_wmax (fun m hm _ => fr_wmax wR m hm) y hy w hw with h | h
  · exact h
  · exact MIH w h hwγ

/-! ### Lemma 3.26 -/

/-- `(18)` の証明の場合 2（Arai の Claim 6.39 の場合 2）：添字 `π ≤ β` の崩壊 `α < γ`（`γ < π`）は、
    `γ` の作り方で場合を分けて、`Wmax` の元で上から押さえる -/
theorem case_two {β γ α : Tm} (wβ : WNF β) (hγH : Hull β Wmax γ)
    (MIH : ∀ ζ, Hull β Wmax ζ → Lt ζ γ → Wmax ζ)
    (hshape : (∃ n a, α = .Xi n a ∧ Lt γ (.K n) ∧ Le (.K n) β) ∨
      (∃ ξ π a, α = .Psi ξ π a ∧ Lt γ π ∧ Le π β))
    (hα : Hull γ Wmax α) (hαγ : Lt α γ) : Wmax α := by
  have wγ := hγH.wf_of
  have wα := hα.wf_of
  have hnγ := nr_specY γ wγ
  have hαp : isPrincipal α = true := by
    rcases hshape with ⟨n, a, rfl, -⟩ | ⟨ξ, π, a, rfl, -⟩ <;> rfl
  -- `γ` 未満の `Wmax` の元 `w ≥ α` で押さえる
  have bound : ∀ w, Wmax w → Lt w γ → ¬ Lt w α → Wmax α := fun w hW hwγ hn =>
    wmax_bounded wγ hα hW (le_of_not_ltY (wmax_wf hW) wα hn)
      (lt_transY (wmax_wf hW) wγ hnγ.1 hwγ hnγ.2.2)
  cases hγH with
  | zero => exact absurd hαγ (not_lt_zero _)
  | one =>
    have := lt_oneY wα hαγ
    subst this
    simp [isPrincipal] at hαp
  | K hj =>
    exfalso
    rcases hshape with ⟨n, a, rfl, hγK, -⟩ | ⟨ξ, π, a, rfl, hγσ, -⟩
    · have h1 := (lt_K_iffY wα hj).mp hαγ
      have h2 := (lt_K_iffY (WNF.K' hj) wα.xi.1).mp hγK
      simp only [lev] at h1 h2
      omega
    · have h1 := (lt_K_iffY wα hj).mp hαγ
      have h2 := lev_le_of_lt_gen hγσ
      simp only [lev] at h1 h2
      omega
  | mem hX _ _ => exact (wmax_good hX).2 _ hα hαγ
  | @plus g₁ g₂ hw hg₁ _ =>
    exact wmax_bounded wγ hα (MIH g₁ hg₁ (lt_plus_leftY hw))
      ((lt_prin_plus_iffY wα hαp hw).mp hαγ)
      (lt_transY hw.plus.1 hw hnγ.1 (lt_plus_leftY hw) hnγ.2.2)
  | @om e hw he =>
    have heW := MIH e he hw.om.2.2
    have hb : Lt e (nrY (.Om e)) := lt_transY hw.om.1 hw hnγ.1 hw.om.2.2 hnγ.2.2
    rcases hshape with ⟨n, a, rfl, -, -⟩ | ⟨ξ, π, a, rfl, hγσ, -⟩
    · exact wmax_bounded wγ hα heW
        (Or.inr ((lt_OF_omG (Or.inl ⟨n, a, rfl⟩) wα hw.om.1).mp hαγ)) hb
    · rcases wα.shape with ⟨c, rfl, rfl⟩ | hsh
      · exfalso
        have h1 := (lt_psi_omY wα hw.om.1).mp hαγ
        exact not_lt_of_leY wα.psiOm.2.1 hw (le_om_of_leY wα.psiOm.1 hw.om.1 h1) hγσ
      · exact wmax_bounded wγ hα heW
          (Or.inr ((lt_OF_omG (IsOF.psi wα (notOm_of_shape hsh)) wα hw.om.1).mp hαγ)) hb
  | @xi j b hw hβK hb =>
    rcases hshape with ⟨n, a, rfl, hγK, hKβ⟩ | ⟨ξ, π, a, rfl, hγσ, hσβ⟩
    · exfalso
      have h1 := (lt_K_iffY hw wα.xi.1).mp hγK
      have h2 := (lt_K_iffY (WNF.K' wα.xi.1) hw.xi.1).mp
        (lt_of_le_of_ltY (WNF.K' wα.xi.1) wβ (WNF.K' hw.xi.1) hKβ hβK)
      simp only [lev] at h1 h2
      omega
    · have wπ := wα.psi.piF
      rcases wα.shape with ⟨c, rfl, rfl⟩ | -
      · exfalso
        exact Lt.asymmY wα hw hαγ ((lt_OF_psiOm (Or.inl ⟨j, b, rfl⟩) hw wα).mpr
          ((lt_OF_omG (Or.inl ⟨j, b, rfl⟩) hw wα.psiOm.1).mp hγσ))
      · have hmj : lev π = j := by
          have h1 := lev_le_of_lt_gen hγσ
          have h2 := (lt_K_iffY wπ hw.xi.1).mp (lt_of_le_of_ltY wπ wβ (WNF.K' hw.xi.1) hσβ hβK)
          simp only [lev] at h1 h2
          omega
        obtain ⟨-, w, hwfr, hwn⟩ := wit_psi_xi wα hw hmj hαγ hγσ
        have hwγ := FWOrder.k2x hw w hwfr
        exact bound w (fr_hull_below (WNF.K' hw.xi.1) hb MIH hwfr hwγ) hwγ hwn
  | @psi σ κ b hw hβκ hσH hκ hb =>
    have wκ := hw.psi.piF
    rcases hshape with ⟨n, a, rfl, hγK, hKβ⟩ | ⟨ξ, π, a, rfl, hγσ, hσβ⟩
    · exfalso
      have h1 := (lt_K_iffY hw wα.xi.1).mp hγK
      have h2 := lev_le_of_lt_gen (lt_of_le_of_ltY (WNF.K' wα.xi.1) wβ wκ hKβ hβκ)
      simp only [lev] at h1 h2
      omega
    · have wπ := wα.psi.piF
      have hπκ : Lt π κ := lt_of_le_of_ltY wπ wβ wκ hσβ hβκ
      have hl : lev π = lev κ := by
        have h1 := lev_le_of_lt_gen hπκ
        have h2 := lev_le_of_lt_gen hγσ
        simp only [lev] at h2
        omega
      rcases (lt_psi_psiY hl hαγ.ne).mp hαγ with
        h1 | ⟨-, hακ, (⟨-, -, -, hπC⟩ | ⟨hba, hn⟩ | ⟨-, e, -⟩ | ⟨hσξ, hn⟩)⟩
      · exact absurd hγσ h1
      · exact absurd (coll_psiY hw π wπ hπC hπκ) (Lt.asymmY hw wπ hγσ)
      · obtain ⟨w, hwfr, hwn⟩ := wit_c2 hw wα wα.psi.aF (le_of_ne_gtY hw.psi.aF wα.psi.aF hba)
          hακ hn
        rcases hwfr with hwfr | hwfr | hwfr
        · have hwγ := FWOrder.k2 hw w hwfr
          exact bound w (fr_hull_below wκ hb MIH hwfr hwγ) hwγ hwn
        · have hwγ := FWOrder.k2t hw w hwfr
          exact bound w (fr_hull_below wκ hκ MIH hwfr hwγ) hwγ hwn
        · have hwγ := FWOrder.k2s hw w hwfr
          exact bound w (fr_hull_below wκ hσH MIH hwfr hwγ) hwγ hwn
      · subst e
        exact absurd hπκ (Lt.irrefl _)
      · obtain ⟨w, hwfr, hwn⟩ := wit_c4 hw wα wα.psi.xiF hαγ hσξ hn
        have hwγ := (fr_spec hwfr).2
        exact bound w (fr_hull_below hw hσH MIH hwfr hwγ) hwγ hwn

/-! ### 目標をたどる列 -/

/-- `γ` は `η` を添字とする崩壊（`η = K_n` の `Ξ_n(b)`、または `η` を目標とする `Ψ^ξ_η(b)`） -/
def IsColl (η γ : Tm) : Prop := (∃ n b, η = .K n ∧ γ = .Xi n b) ∨ ∃ ξ b, γ = .Psi ξ η b

/-- `Ch γ τ`：`τ` は `γ` から目標を 0 回以上たどって得られる（`Ψ^ξ_ρ(b)` の次は `ρ`） -/
inductive Ch : Tm → Tm → Prop
  | refl (x : Tm) : Ch x x
  | step {x ξ ρ b : Tm} : Ch x (.Psi ξ ρ b) → Ch x ρ

theorem Ch.wnf {x y : Tm} (h : Ch x y) (hx : WNF x) : WNF y := by
  induction h with
  | refl => exact hx
  | step _ ih => exact ih.psi.piF

theorem Ch.le {x y : Tm} (h : Ch x y) (hx : WNF x) : Le x y := by
  induction h with
  | refl => exact Or.inl rfl
  | step h' ih =>
    have w := h'.wnf hx
    exact le_transY hx w w.psi.piF ih (Or.inr (lt_psi_targetY w))

/-- 目標でない項に至る列は長さ 0 -/
theorem Ch.eq_of_not_tgt {x y : Tm} (h : Ch x y) (hx : WNF x) (hy : ¬ IsTgt y) : x = y := by
  cases h with
  | refl => rfl
  | step h' => exact absurd (h'.wnf hx).psi.tgt hy

theorem not_tgt_psi0 {c a : Tm} : ¬ IsTgt (.Psi .zero (.Om c) a) := by
  rintro (⟨c', e', -⟩ | ⟨n, p, e'⟩ | ⟨ζ, κ, b', e', hζ⟩) <;> cases e'
  exact hζ rfl

/-- 列の行き着く先が `η` の崩壊になるときの仮定（Arai の Lemma 6.38 の (44)） -/
def H15 (η : Tm) : Prop := ∀ γ τ, Good γ → Lt γ η → (∀ δ, Wmax δ → Le γ δ → Wmax γ) →
  IsColl η τ → Ch γ τ → Hull γ Wmax τ → (∀ w, w ∈ fr τ τ → Lt w γ) → Wmax γ

/-- `η` 未満の `Good` な崩壊 `γ` から目標をたどる：たどった先 `τ` の目標が `η` より大きければ `τ` を
    `C^η(Wmax)` に移して `τ ∈ Wmax`、`η` なら `H15`、`η` より小さければさらにたどる -/
theorem chain_walk {η γ : Tm} (hG : Good η) (h15 : H15 η) (hγ : Good γ) (hγη : Lt γ η)
    (Obs : ∀ δ, Wmax δ → Le γ δ → Wmax γ) :
    ∀ τ, Ch γ τ → Hull γ Wmax τ → Lt τ η → (∀ w, w ∈ fr τ τ → Lt w γ) →
      (τ = γ ∨ IsTgt τ) → ((∃ n b, τ = .Xi n b) ∨ ∃ s ρ a, τ = .Psi s ρ a) → Wmax γ := by
  have wη := hG.1.wf_of
  have wγ := hγ.1.wf_of
  intro τ
  induction τ using size_induction with
  | h τ ih =>
  intro hch hτH hτη hfr hτt hsh
  have wτ := hch.wnf wγ
  have hγτ := hch.le wγ
  have fin : Hull η Wmax τ → Wmax γ := fun h => Obs τ (hG.2 τ h hτη) hγτ
  rcases hsh with ⟨n, b, rfl⟩ | ⟨s, ρ, a, rfl⟩
  · cases hτH with
    | mem hX _ _ => exact Obs _ hX hγτ
    | xi hw hγK hb =>
      have wK := WNF.K' hw.xi.1
      have hτK : Lt (.Xi n b) (.K n) := (lt_K_iffY hw hw.xi.1).mpr (Nat.le_refl _)
      rcases triY wK wη with hKη | e | hηK
      · exact Obs _ (hG.2 _ (Hull.K hw.xi.1) hKη) (le_transY wγ hw wK hγτ (Or.inr hτK))
      · exact h15 γ _ hγ hγη Obs (Or.inl ⟨n, b, e.symm, rfl⟩) hch (Hull.xi hw hγK hb) hfr
      · apply fin
        refine Hull.xi hw hηK (hull_transfer wη wK (Or.inr hηK) (b.size + 1)
          (fun x hx hxγ _ => hγ.2 x hx hxγ) b hb (Nat.lt_succ_self _) ?_)
        intro w hw'
        apply hfr w
        rw [fr]
        simp only [Lt.irrefl, ↓reduceIte]
        exact fr_sub wK hw (Or.inr hτK) hw.xi.2.1 hw' (FWOrder.k2x hw w hw')
  · cases hτH with
    | mem hX _ _ => exact Obs _ hX hγτ
    | psi hw hγρ hs hρ ha =>
      have wρ := hw.psi.piF
      have hττ : ¬ Lt (.Psi s ρ a) (.Psi s ρ a) := Lt.irrefl _
      have hτρ : Le (.Psi s ρ a) ρ := Or.inr (lt_psi_targetY hw)
      have frs : ∀ w, w ∈ fr ρ s → Lt w γ := fun w h =>
        hfr w (fr_mem_psi_s hττ (fr_sub wρ hw hτρ hw.psi.xiF h (FWOrder.k2s hw w h)))
      have frp : ∀ w, w ∈ fr ρ ρ → Lt w γ := fun w h =>
        hfr w (fr_mem_psi_p hττ (fr_sub wρ hw hτρ wρ h (FWOrder.k2t hw w h)))
      have fra : ∀ w, w ∈ fr ρ a → Lt w γ := fun w h =>
        hfr w (fr_mem_psi_a hττ (fr_sub wρ hw hτρ hw.psi.aF h (FWOrder.k2 hw w h)))
      rcases triY wρ wη with hρη | e | hηρ
      · rcases hw.shape with ⟨c, rfl, rfl⟩ | ⟨n, p, rfl⟩ | ⟨ζ, κ, b, rfl, hζ⟩
        · -- `Ω_c`：`τ = γ`
          have hτγ : Tm.Psi .zero (.Om c) a = γ := by
            rcases hτt with e | ht
            · exact e
            · exact absurd ht not_tgt_psi0
          have hc : Wmax c := by
            cases hρ with
            | mem hX _ _ => exact wmax_om_arg hX
            | om _ hc => exact hγ.2 c hc (by rw [← hτγ]; exact FWOrder.cx hw)
          exact Obs _ (hG.2 _ (Hull.om wρ (wmax_hull hc wη)) hρη) (le_transY wγ hw wρ hγτ hτρ)
        · exact ih _ (by size_omega) (Ch.step hch) hρ hρη frp
            (Or.inr (Or.inr (Or.inl ⟨n, p, rfl⟩))) (Or.inl ⟨n, p, rfl⟩)
        · exact ih _ (by size_omega) (Ch.step hch) hρ hρη frp
            (Or.inr (Or.inr (Or.inr ⟨ζ, κ, b, rfl, hζ⟩))) (Or.inr ⟨ζ, κ, b, rfl⟩)
      · exact h15 γ _ hγ hγη Obs (Or.inr ⟨s, a, by rw [e]⟩) hch (Hull.psi hw hγρ hs hρ ha) hfr
      · exact fin (Hull.psi hw hηρ
          (hull_transfer wη wρ (Or.inr hηρ) (s.size + 1) (fun x hx hxγ _ => hγ.2 x hx hxγ)
            s hs (Nat.lt_succ_self _) frs)
          (hull_transfer wη wρ (Or.inr hηρ) (ρ.size + 1) (fun x hx hxγ _ => hγ.2 x hx hxγ)
            ρ hρ (Nat.lt_succ_self _) frp)
          (hull_transfer wη wρ (Or.inr hηρ) (a.size + 1) (fun x hx hxγ _ => hγ.2 x hx hxγ)
            a ha (Nat.lt_succ_self _) fra))

/-- Lemma 3.26 の証明の段階 3：`η` 未満の `Good` な項は `Wmax` に入る -/
theorem step_three {η γ : Tm} (hG : Good η) (h15 : H15 η)
    (hγ : Good γ) (hγη : Lt γ η) (Obs : ∀ δ, Wmax δ → Le γ δ → Wmax γ) : Wmax γ := by
  have wη := hG.1.wf_of
  have wγ := hγ.1.wf_of
  have frγ : ∀ w, w ∈ fr γ γ → Lt w γ := fun w h => (fr_spec h).2
  cases γ with
  | zero => exact hG.2 _ Hull.zero hγη
  | one => exact hG.2 _ Hull.one hγη
  | K n => exact hG.2 _ (Hull.K wγ.k) hγη
  | plus g₁ g₂ =>
    cases hγ.1 with
    | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
    | plus hw hg₁ hg₂ =>
      exact hG.2 _ (Hull.plus hw (wmax_hull (hγ.2 _ hg₁ (lt_plus_leftY hw)) wη)
        (wmax_hull (hγ.2 _ hg₂ (lt_plus_rightY hw)) wη)) hγη
  | Om e =>
    cases hγ.1 with
    | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
    | om hw he => exact hG.2 _ (Hull.om hw (wmax_hull (hγ.2 e he hw.om.2.2) wη)) hγη
  | Xi n b =>
    exact chain_walk hG h15 hγ hγη Obs _ (Ch.refl _) hγ.1 hγη frγ (Or.inl rfl)
      (Or.inl ⟨n, b, rfl⟩)
  | Psi s ρ a =>
    exact chain_walk hG h15 hγ hγη Obs _ (Ch.refl _) hγ.1 hγη frγ (Or.inl rfl)
      (Or.inr ⟨s, ρ, a, rfl⟩)

/-- Arai の Lemma 3.26：列の行き着く先が `η` の崩壊になる場合の仮定 `H15 η` の下で、`Good η` から拡張の
    仮定が成り立つ -/
theorem hyp_of_good {η : Tm} (hG : Good η) (h15 : H15 η) :
    Hyp η := by
  have wη := hG.1.wf_of
  intro β wβ hle γ hW hγ
  have hnβ := nr_specY β wβ
  have key : ∀ γ, Acc (Rel (Hull β Wmax)) γ → Hull β Wmax γ → Lt γ (nrY β) → Wmax γ := by
    intro γ hacc
    induction hacc with
    | intro γ hacc' MIH0 =>
      intro hγH hγ
      have wγ := hγH.wf_of
      have MIH : ∀ ζ, Hull β Wmax ζ → Lt ζ γ → Wmax ζ := fun ζ hζ hζγ =>
        MIH0 ζ ⟨hζ, hζγ⟩ hζ (lt_transY hζ.wf_of wγ hnβ.1 hζγ hγ)
      have Obs : ∀ δ, Wmax δ → Le γ δ → Wmax γ := by
        intro δ hδ hγδ
        have wδ := wmax_wf hδ
        by_cases hδβ : Lt δ β
        · exact wmax_bounded wδ (Hull.lower HW wδ wβ (Or.inr hδβ) hγH) hδ hγδ
            (nr_specY δ wδ).2.2
        · exact ((wmax_dist.2 β wβ ⟨δ, hδ, le_of_not_ltY wδ wβ hδβ⟩ γ).mp
            ⟨⟨hγH, Acc.intro γ hacc'⟩, hγ⟩).1
      have G2 : ∀ α, Hull γ Wmax α → Lt α γ → Wmax α := by
        intro α
        induction α using size_induction with
        | h α ihα =>
          intro hα hαγ
          by_cases hβnγ : Lt β (nrY γ)
          · exact MIH α (Hull.sub_of_lt_nr HW wγ wβ hβnγ hα) hαγ
          · have below : ∀ x, WNF x → Lt x α → Lt x γ :=
              fun x wx h => lt_transY wx hα.wf_of wγ h hαγ
            cases hα with
            | zero => exact MIH _ Hull.zero hαγ
            | one => exact MIH _ Hull.one hαγ
            | K hn => exact MIH _ (Hull.K hn) hαγ
            | mem hX _ _ => exact hX
            | plus hw ha hb =>
              exact MIH _ (Hull.plus hw
                (wmax_hull (ihα _ (by size_omega) ha (below _ hw.plus.1 (lt_plus_leftY hw))) wβ)
                (wmax_hull (ihα _ (by size_omega) hb
                  (below _ hw.plus.2.1 (lt_plus_rightY hw))) wβ)) hαγ
            | om hw ha =>
              exact MIH _ (Hull.om hw (wmax_hull (ihα _ (by size_omega) ha
                (below _ hw.om.1 hw.om.2.2)) wβ)) hαγ
            | @xi n a hw hγK ha =>
              have wK := WNF.K' hw.xi.1
              by_cases hβK : Lt β (.K n)
              · exact MIH _ (Hull.xi hw hβK (hull_transfer wβ wK (Or.inr hβK) _
                  (fun x hx hxγ hs => ihα x hs hx hxγ) a ha (by size_omega)
                  (fun w hw' => lt_transY (hw.of_mem_subs (subs_xi (fr_spec hw').1)) hw wγ
                    (FWOrder.k2x hw w hw') hαγ))) hαγ
              · exact case_two wβ hγH MIH (Or.inl ⟨n, a, rfl, hγK, le_of_not_ltY wβ wK hβK⟩)
                  (Hull.xi hw hγK ha) hαγ
            | @psi ξ π a hw hγσ hξ hσ ha =>
              have wπ := hw.psi.piF
              by_cases hβσ : Lt β π
              · have hξ' := hull_transfer wβ wπ (Or.inr hβσ) _ (fun x hx hxγ hs => ihα x hs hx hxγ)
                  ξ hξ (by size_omega)
                  (fun w hw' => lt_transY (hw.of_mem_subs (subs_psi_s (fr_spec hw').1)) hw wγ
                    (FWOrder.k2s hw w hw') hαγ)
                have hσ' := hull_transfer wβ wπ (Or.inr hβσ) _ (fun x hx hxγ hs => ihα x hs hx hxγ)
                  π hσ (by size_omega)
                  (fun w hw' => lt_transY (wπ.of_mem_subs (fr_spec hw').1) hw wγ
                    (FWOrder.k2t hw w hw') hαγ)
                exact MIH _ (Hull.psi hw hβσ hξ' hσ' (hull_transfer wβ wπ (Or.inr hβσ) _
                  (fun x hx hxγ hs => ihα x hs hx hxγ) a ha (by size_omega)
                  (fun w hw' => lt_transY (hw.of_mem_subs (subs_psi_a (fr_spec hw').1)) hw wγ
                    (FWOrder.k2 hw w hw') hαγ))) hαγ
              · exact case_two wβ hγH MIH (Or.inr ⟨ξ, π, a, rfl, hγσ, le_of_not_ltY wβ wπ hβσ⟩)
                  (Hull.psi hw hγσ hξ hσ ha) hαγ
      exact step_three hG h15 ⟨Hull.sub_of_lt_nr HW wβ wγ hγ hγH, G2⟩
        (lt_of_lt_of_leY wγ hnβ.1 wη hγ hle) Obs
  exact key γ hW.2 hW.1 hγ

theorem h15_nt {η : Tm} (hT : ¬ IsTgt η) (hK : ∀ n, η ≠ .K n) : H15 η := by
  intro γ τ hγ _ _ hc hch _ _
  have wτ := hch.wnf hγ.1.wf_of
  rcases hc with ⟨n, b, e, -⟩ | ⟨ξ, b, rfl⟩
  · exact absurd e (hK n)
  · exact absurd wτ.psi.tgt hT

/-- 目標にも `K_n` にもならない `Good` な項は `Wmax` に入る -/
theorem wmax_of_good_nt {η : Tm} (hG : Good η) (hT : ¬ IsTgt η) (hK : ∀ n, η ≠ .K n) :
    Wmax η :=
  wmax_of_good_hyp hG (hyp_of_good hG (h15_nt hT hK))

theorem h15_om (c : Tm) : H15 (.Om c) := by
  intro γ τ hγ _ _ hc hch _ _
  have wγ := hγ.1.wf_of
  have wτ := hch.wnf wγ
  rcases hc with ⟨n, b, e, -⟩ | ⟨ξ, b, rfl⟩
  · cases e
  · have hξ := wτ.psiOm.2.2.2.2.2
    subst hξ
    have e := hch.eq_of_not_tgt wγ not_tgt_psi0
    subst e
    exact wmax_of_good_nt hγ not_tgt_psi0 (fun n e => by cases e)

/-! ## `Wmax` の閉包と整列性

`Wmax` が `0`・`1`・`+`・`Ω`・`K_n`・`Ξ_n`・`Ψ^ξ_π` で閉じることを示す。要は、目標を
たどる列（`Ψ^ξ_π(a)`、`π`、`π` の目標、…）の上で `Good` から `Wmax` を導く部分（`H15`）。

* 列の行き着く先が `K_n` のとき（`Ξ_n(b)`）、Mahlo 添字 `b` は `K_n` 以上になりうるので `Wmax` には入っていない。
  そこで `K_n^+` 以下の `C^{K_n}(Wmax)` の元で、`K_n` 以上の節点の引数が `K_n^+` 未満のもの（`WK n`）の整礎性
  （`acc_wk`）を先に示し、`b ∈ WK n` についての帰納法で `Ξ_n(b) ∈ Wmax` を示す（`coll_wk`）。
* 列の行き着く先が `Ξ_j(a)` か `Ψ^ξ_π(a)` のとき、列の上の `Good` な `γ` の Mahlo 添字は `a` 未満の引数の
  崩壊から作られ、引数についての帰納法の仮定で `WK n` に入る。Mahlo 添字は列の上で真に減るので、Mahlo 添字に
  ついての帰納法で `γ ∈ Wmax`（`mahlo_step`）。
* 主定理は、`K_n` について帰納法で `Good K_n`・`acc_wk`・`coll_wk`・`K_n ∈ Wmax` を順に示し、最後に項の構造に
  ついての帰納法でまとめる。 -/

/-! ### 基本の項 -/

theorem not_tgt_of_shape {t : Tm} (h0 : ∀ c, t ≠ .Om c) (h1 : ∀ n p, t ≠ .Xi n p)
    (h2 : ∀ ζ κ b, t ≠ .Psi ζ κ b) : ¬ IsTgt t := by
  rintro (⟨c, e, -⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, -⟩)
  · exact h0 c e
  · exact h1 n p e
  · exact h2 ζ κ b e

theorem wmax_zero : Wmax .zero :=
  wmax_of_good_nt ⟨Hull.zero, fun _ _ h => absurd h (not_lt_zero _)⟩
    (not_tgt_of_shape (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ _ e => by cases e))
    (fun _ e => by cases e)

theorem wmax_one : Wmax .one :=
  wmax_of_good_nt ⟨Hull.one, fun _ hβ h => by
    have := lt_oneY hβ.wf_of h
    subst this
    exact wmax_zero⟩
    (not_tgt_of_shape (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ _ e => by cases e))
    (fun _ e => by cases e)

theorem wmax_add {a b : Tm} (hw : WNF (.plus a b)) (ha : Wmax a) (hb : Wmax b) :
    Wmax (.plus a b) := by
  induction wmax_acc hb with
  | intro b _ ih =>
    have hn := nr_specY _ hw
    have hap := hw.plus.2.2.1
    have ha_lt := lt_transY (wmax_wf ha) hw hn.1 (lt_plus_leftY hw) hn.2.2
    refine wmax_of_good_nt ⟨Hull.plus hw (wmax_hull ha hw) (wmax_hull hb hw), ?_⟩
      (not_tgt_of_shape (fun _ e => by cases e) (fun _ _ e => by cases e)
        (fun _ _ _ e => by cases e)) (fun _ e => by cases e)
    intro γ hγ hγlt
    have wγ := hγ.wf_of
    cases γ with
    | zero => exact wmax_zero
    | plus γ₁ γ₂ =>
      by_cases e : γ₁ = a
      · subst e
        have hγlt' := lt_plus_plus_same.mp hγlt
        cases hγ with
        | mem hX _ _ => exact hX
        | plus hw' _ hγ₂ =>
          have hγ₂W := wmax_bounded hw hγ₂ hb (Or.inr hγlt')
            (lt_transY (wmax_wf hb) hw hn.1 (lt_plus_rightY hw) hn.2.2)
          exact ih γ₂ ⟨hγ₂W, hγlt'⟩ hw' hγ₂W
      · exact wmax_bounded hw hγ ha
          (Or.inr ((lt_plus_prin_iffY wγ hap).mpr ((lt_plus_plus_neY wγ hw e).mp hγlt))) ha_lt
    | _ => exact wmax_bounded hw hγ ha ((lt_prin_plus_iffY wγ rfl hw).mp hγlt) ha_lt

theorem wmax_om : ∀ c, Wmax c → WNF (.Om c) → Wmax (.Om c) := by
  intro c hc
  induction wmax_acc hc with
  | intro c _ ihc =>
    intro hw
    have hn := nr_specY _ hw
    have wc := wmax_wf hc
    have hc_lt := lt_transY wc hw hn.1 hw.om.2.2 hn.2.2
    have hG : Good (.Om c) := by
      refine ⟨Hull.om hw (wmax_hull hc hw), ?_⟩
      intro β
      induction β using size_induction with
      | h β ihβ =>
        intro hβ hβlt
        have below : ∀ x, WNF x → Lt x β → Lt x (.Om c) :=
          fun x wx h => lt_transY wx hβ.wf_of hw h hβlt
        cases hβ with
        | zero => exact wmax_zero
        | one => exact wmax_one
        | K hn' =>
          exact wmax_bounded hw (Hull.K hn') hc (Or.inr ((lt_K_omY hn' wc).mp hβlt)) hc_lt
        | mem hX _ _ => exact hX
        | plus hw' hb₁ hb₂ =>
          exact wmax_add hw'
            (ihβ _ (by size_omega) hb₁ (below _ hw'.plus.1 (lt_plus_leftY hw')))
            (ihβ _ (by size_omega) hb₂ (below _ hw'.plus.2.1 (lt_plus_rightY hw')))
        | om hw' hd =>
          have hdW := ihβ _ (by size_omega) hd (below _ hw'.om.1 hw'.om.2.2)
          exact ihc _ ⟨hdW, (lt_om_iffY hw'.om.1 wc).mp hβlt⟩ hdW hw'
        | @xi n d hw' hK hd =>
          exact wmax_bounded hw (Hull.xi hw' hK hd) hc
            (Or.inr ((lt_OF_omG (Or.inl ⟨n, d, rfl⟩) hw' wc).mp hβlt)) hc_lt
        | @psi s π d hw' hσ hs hπ hd =>
          rcases hw'.shape with ⟨c', rfl, rfl⟩ | hsh
          · exact absurd ((lt_om_iffY wc hw'.psiOm.1).mp hσ)
              (not_lt_of_leY hw'.psiOm.1 wc ((lt_psi_omY hw' wc).mp hβlt))
          · exact wmax_bounded hw (Hull.psi hw' hσ hs hπ hd) hc
              (Or.inr ((lt_OF_omG (IsOF.psi hw' (notOm_of_shape hsh)) hw' wc).mp hβlt)) hc_lt
    exact wmax_of_good_hyp hG (hyp_of_good hG (h15_om c))

/-- `K_n` 未満の `C^{K_n}(Wmax)` の元は `Wmax` に入る（`K_j`（`j < n`）が `Wmax` に入るとき） -/
theorem goodK {n : Nat} (hn : 1 ≤ n) (ihK : ∀ j, 1 ≤ j → j < n → Wmax (.K j)) :
    Good (.K n) := by
  have hw := WNF.K' hn
  refine ⟨Hull.K hn, ?_⟩
  intro β
  induction β using size_induction with
  | h β ihβ =>
    intro hβ hβlt
    have below : ∀ x, WNF x → Lt x β → Lt x (.K n) :=
      fun x wx h => lt_transY wx hβ.wf_of hw h hβlt
    cases hβ with
    | zero => exact wmax_zero
    | one => exact wmax_one
    | @K j hj =>
      have h1 := (lt_K_iffY (WNF.K' hj) hn).mp hβlt
      simp only [lev] at h1
      exact ihK j hj (by omega)
    | mem hX _ _ => exact hX
    | plus hw' hb₁ hb₂ =>
      exact wmax_add hw'
        (ihβ _ (by size_omega) hb₁ (below _ hw'.plus.1 (lt_plus_leftY hw')))
        (ihβ _ (by size_omega) hb₂ (below _ hw'.plus.2.1 (lt_plus_rightY hw')))
    | om hw' hd =>
      exact wmax_om _ (ihβ _ (by size_omega) hd (below _ hw'.om.1 hw'.om.2.2)) hw'
    | xi hw' hK _ =>
      exfalso
      have h1 := (lt_K_iffY hw' hn).mp hβlt
      have h2 := (lt_K_iffY hw hw'.xi.1).mp hK
      simp only [lev] at h1 h2
      omega
    | psi hw' hσ _ _ _ =>
      exfalso
      have h1 := (lt_K_iffY hw' hn).mp hβlt
      have h2 := lev_le_of_lt_gen hσ
      simp only [lev] at h1 h2
      omega

/-! ### `K_n^+` 以下の Mahlo 添字の範囲 `WK n` -/

/-- `K_n^+` 以下の `C^{K_n}(Wmax)` の元で、`K_n` 以上の節点の引数が `K_n^+` 未満のもの -/
def WK (n : Nat) (x : Tm) : Prop :=
  Hull (.K n) Wmax x ∧ inC x (succK n) (.K n) = true ∧ Le x (succK n)

theorem WK.wf {n : Nat} {x : Tm} (h : WK n x) : WNF x := h.1.wf_of

theorem nrY_K (n : Nat) : nrY (.K n) = succK n := rfl

theorem K_lt_succK {n : Nat} (hn : 1 ≤ n) : Lt (.K n) (succK n) := (nr_specY _ (WNF.K' hn)).2.2

/-- `x < d` なら `x ∈ C(g, d)` -/
theorem inC_of_ltY : ∀ {x : Tm} (g : Tm) {d : Tm}, WNF x → WNF d → Lt x d → inC x g d = true
  | .zero, _, _, _, _, _ => inC_zero _ _
  | .one, _, _, _, _, _ => inC_one _ _
  | .K _, _, _, _, _, _ => inC_K _ _ _
  | .plus a b, g, d, hx, hd, h => by
    obtain ⟨ha, hb, -, -⟩ := hx.plus
    rw [inC_plus, inC_of_ltY g ha hd (lt_transY ha hx hd (lt_plus_leftY hx) h),
      inC_of_ltY g hb hd (lt_transY hb hx hd (lt_plus_rightY hx) h)]
    rfl
  | .Om a, g, d, hx, hd, h => by
    rw [inC_om]
    exact inC_of_ltY g hx.om.1 hd (lt_transY hx.om.1 hx hd hx.om.2.2 h)
  | .Xi m a, _, _, _, _, h => inC_of_lt_node (Or.inl ⟨m, a, rfl⟩) h
  | .Psi s p a, _, _, _, _, h => inC_of_lt_node (Or.inr ⟨s, p, a, rfl⟩) h

theorem hull_plus_inv {α a b : Tm} (wα : WNF α) (h : Hull α Wmax (.plus a b)) :
    Hull α Wmax a ∧ Hull α Wmax b := by
  cases h with
  | mem hX _ _ =>
    have hG := wmax_good hX
    cases hG.1 with
    | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
    | plus hw' ha hb =>
      exact ⟨wmax_hull (hG.2 _ ha (lt_plus_leftY hw')) wα,
        wmax_hull (hG.2 _ hb (lt_plus_rightY hw')) wα⟩
  | plus _ ha hb => exact ⟨ha, hb⟩

theorem WK.plus {n : Nat} (hn : 1 ≤ n) {a b : Tm} (h : WK n (.plus a b)) : WK n a ∧ WK n b := by
  have wx := h.wf
  have wS := WNF.succK hn
  obtain ⟨ha, hb⟩ := hull_plus_inv (WNF.K' hn) h.1
  have hC := h.2.1
  rw [inC_plus, Bool.and_eq_true] at hC
  exact ⟨⟨ha, hC.1, Or.inr (lt_of_lt_of_leY wx.plus.1 wx wS (lt_plus_leftY wx) h.2.2)⟩,
    ⟨hb, hC.2, Or.inr (lt_of_lt_of_leY wx.plus.2.1 wx wS (lt_plus_rightY wx) h.2.2)⟩⟩

theorem WK.psi_arg {n : Nat} {σ κ d : Tm} (h : WK n (.Psi σ κ d))
    (hK : ¬ Lt (.Psi σ κ d) (.K n)) : WK n d ∧ Lt d (succK n) := by
  have hd : Hull (.K n) Wmax d := by
    cases h.1 with
    | mem _ _ hlt => exact absurd hlt hK
    | psi _ _ _ _ hd => exact hd
  rcases inC_psi_iff.mp h.2.1 with h' | ⟨-, -, hdC, hdS⟩
  · exact absurd h' hK
  · exact ⟨⟨hd, hdC, Or.inr hdS⟩, hdS⟩

/-! #### `K_n^+` 未満の項の形 -/

theorem om_lt_succK {n : Nat} (hn : 1 ≤ n) {c : Tm} (hw : WNF (.Om c))
    (h : Lt (.Om c) (succK n)) : Lt (.Om c) (.K n) := by
  have wc := hw.om.1
  have wK := WNF.K' hn
  have wS := succT_WNF wK
  have hc : Lt c (succT (.K n)) := (lt_om_iffY wc wS).mp h
  have hcK : Lt c (.K n) := by
    rcases triY wc wK with h' | e | h'
    · exact h'
    · exact absurd e hw.om_ne_k
    · exact absurd hc (not_lt_of_leY wS wc (succT_leY wK wc h'))
  rw [lt_K_iffY hw hn]
  exact (lt_K_iffY wc hn).mp hcK

theorem K_lt_of_lev {n : Nat} (hn : 1 ≤ n) {x : Tm} (hx : WNF x) (hl : lev x = n + 1)
    (hne : x ≠ .K n) : Lt (.K n) x := by
  rcases triY (WNF.K' hn) hx with h | e | h
  · exact h
  · exact absurd e.symm hne
  · have := (lt_K_iffY hx hn).mp h; omega

theorem xi_le_succK {n m : Nat} (hn : 1 ≤ n) {d : Tm} (hw : WNF (.Xi m d))
    (h : Le (.Xi m d) (succK n)) : Lt (.Xi m d) (.K n) := by
  have wS := WNF.succK hn
  have hl : m ≤ n + 1 := by
    rcases h with e | h
    · cases e
    · have := lev_le_of_lt_gen h; simpa [lev, succK] using this
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · exact (lt_K_iffY hw hn).mpr (by simp only [lev]; omega)
  · exfalso
    subst hl
    have h1 : Lt (.K n) (.Xi (n + 1) d) := K_lt_of_lev hn hw (by simp [lev]) (fun e => by cases e)
    have h2 : Lt (succT (.K n)) (.Xi (n + 1) d) :=
      (lt_plus_prin_iffY (succT_WNF (WNF.K' hn)) rfl).mpr h1
    have h3 : Lt (succK n) (.Xi (n + 1) d) := (lt_om_OFG (Or.inl ⟨n + 1, d, rfl⟩)).mpr h2
    exact not_lt_of_leY hw wS h h3

theorem K_le_succK {n m : Nat} (h : Le (.K m) (succK n)) : m ≤ n := by
  rcases h with e | h
  · cases e
  · have := lev_le_of_lt_gen h; simp [lev, succK] at this; omega

/-- `K_n ≤ Ψ^σ_κ(d) < K_n^+` なら `κ = K_n^+`、`σ = 0` -/
theorem psi_lt_succK {n : Nat} (hn : 1 ≤ n) {σ κ d : Tm} (hw : WNF (.Psi σ κ d))
    (h : Lt (.Psi σ κ d) (succK n)) (hK : ¬ Lt (.Psi σ κ d) (.K n)) :
    κ = succK n ∧ σ = .zero := by
  have wK := WNF.K' hn
  have wS1 := succT_WNF wK
  have hl1 : lev κ ≤ n + 1 := by have := lev_le_of_lt_gen h; simpa [lev, succK] using this
  have hl2 : n + 1 ≤ lev κ := by
    apply Nat.le_of_not_lt
    intro hc
    exact hK ((lt_K_iffY hw hn).mpr (by simp only [lev]; omega))
  rcases hw.shape with ⟨c, rfl, rfl⟩ | hsh
  · obtain ⟨wc, -, hs, -, -, -⟩ := hw.psiOm
    have hcS : Le c (succT (.K n)) := (lt_psi_omY hw wS1).mp h
    have hlc : lev c = n + 1 := by simp only [lev] at hl1 hl2; omega
    have hKc : Lt (.K n) c := by
      rcases triY wK wc with h' | e | h'
      · exact h'
      · subst e; simp [isSucc, summands] at hs
      · have := (lt_K_iffY wc hn).mp h'; omega
    have := le_antisymmY wc wS1 hcS (succT_leY wK wc hKc)
    subst this
    exact ⟨rfl, rfl⟩
  · exfalso
    have hO := IsOF.psi hw (notOm_of_shape hsh)
    have h1 : Lt (.Psi σ κ d) (succT (.K n)) := (lt_OF_omG hO hw wS1).mp h
    rcases (lt_prin_plus_iffY hw rfl wS1).mp h1 with e | h2
    · cases e
    · exact hK h2

/-! #### `WK n` の整礎性 -/

theorem acc_wk_of_wmax {n : Nat} (hn : 1 ≤ n) {x : Tm} (hx : Wmax x) (h : Lt x (succK n)) :
    Acc (Rel (WK n)) x :=
  acc_of_below (fun _ h => h.wf) x (wmax_acc hx) (wmax_wf hx)
    (fun _ hy hyx => wmax_bounded (WNF.K' hn) hy.1 hx (Or.inr hyx) (by rw [nrY_K]; exact h))

theorem acc_wk_of_ltK {n : Nat} (hn : 1 ≤ n) (hG : Good (.K n)) {x : Tm} (hx : WK n x)
    (h : Lt x (.K n)) : Acc (Rel (WK n)) x :=
  acc_wk_of_wmax hn (hG.2 x hx.1 h)
    (lt_transY hx.wf (WNF.K' hn) (WNF.succK hn) h (K_lt_succK hn))

theorem acc_wk_K {n : Nat} (hn : 1 ≤ n) (hG : Good (.K n)) : Acc (Rel (WK n)) (.K n) :=
  Acc.intro _ (fun _ hy => acc_wk_of_ltK hn hG hy.1 hy.2)

theorem acc_wk_plus {n : Nat} (hn : 1 ≤ n) : ∀ v, Acc (Rel (WK n)) v → ∀ u,
    Acc (Rel (WK n)) u → WNF (.plus u v) → Acc (Rel (WK n)) (.plus u v) := by
  intro v hacc
  induction hacc with
  | intro v _ ih =>
    intro u hu hw
    have hup := hw.plus.2.2.1
    refine Acc.intro _ (fun y hyr => ?_)
    obtain ⟨hy, hyl⟩ := hyr
    have wy := hy.wf
    cases y with
    | zero => exact Acc.intro _ (fun z hz => absurd hz.2 (not_lt_zero _))
    | plus y₁ y₂ =>
      by_cases e : y₁ = u
      · subst e
        exact ih y₂ ⟨(hy.plus hn).2, lt_plus_plus_same.mp hyl⟩ y₁ hu wy
      · exact hu.inv ⟨hy, (lt_plus_prin_iffY wy hup).mpr ((lt_plus_plus_neY wy hw e).mp hyl)⟩
    | _ =>
      rcases (lt_prin_plus_iffY wy rfl hw).mp hyl with e | h
      · rw [e]; exact hu
      · exact hu.inv ⟨hy, h⟩

theorem fr_succK_self (n : Nat) : fr (succK n) (succK n) = [] := by
  simp [fr, succK]

/-- `K_n^+` を目標とする崩壊：`d ∈ WK n` が整礎なら `Ψ^0_{K_n^+}(d)` も -/
theorem acc_psiK {n : Nat} (hn : 1 ≤ n) (hG : Good (.K n)) :
    ∀ d, Acc (Rel (WK n)) d → WK n d → Lt d (succK n) → WNF (.Psi .zero (succK n) d) →
      Acc (Rel (WK n)) (.Psi .zero (succK n) d) := by
  have wS := WNF.succK hn
  intro d hacc
  induction hacc with
  | intro d hd' ihd =>
    intro hd hdS hw
    have wd := hd.wf
    have hψS : Lt (.Psi .zero (succK n) d) (succK n) := lt_psi_targetY hw
    refine Acc.intro _ (fun y hyr => ?_)
    obtain ⟨hy, hyl⟩ := hyr
    revert hy hyl
    induction y using size_induction with
    | h y ihy =>
    intro hy hyl
    have wy := hy.wf
    by_cases hyK : Lt y (.K n)
    · exact acc_wk_of_ltK hn hG hy hyK
    have hyS : Lt y (succK n) := lt_transY wy hw wS hyl hψS
    cases y with
    | zero => exact absurd ((lt_K_iffY wy hn).mpr (by simp [lev])) hyK
    | one => exact absurd ((lt_K_iffY wy hn).mpr (by simp [lev]; omega)) hyK
    | K m =>
      have hm := K_le_succK (Or.inr hyS)
      rcases Nat.lt_or_eq_of_le hm with hm | rfl
      · exact absurd ((lt_K_iffY wy hn).mpr (by simp [lev]; omega)) hyK
      · exact acc_wk_K hn hG
    | plus y₁ y₂ =>
      have h12 := hy.plus hn
      have h1 : Lt y₁ (.Psi .zero (succK n) d) := (lt_plus_prin_iffY wy rfl).mp hyl
      have h2 : Lt y₂ (.Psi .zero (succK n) d) :=
        lt_transY wy.plus.2.1 wy hw (lt_plus_rightY wy) hyl
      exact acc_wk_plus hn y₂ (ihy y₂ (by size_omega) h12.2 h2) y₁
        (ihy y₁ (by size_omega) h12.1 h1) wy
    | Om c => exact absurd (om_lt_succK hn wy hyS) hyK
    | Xi m e => exact absurd (xi_le_succK hn wy (Or.inr hyS)) hyK
    | Psi σ κ e =>
      obtain ⟨rfl, rfl⟩ := psi_lt_succK hn wy hyS hyK
      obtain ⟨he, heS⟩ := hy.psi_arg hyK
      have we := he.wf
      rcases (lt_psi_psiY rfl hyl.ne).mp hyl with
        h1 | ⟨-, -, (⟨hed, -, -, -⟩ | ⟨hde, hn'⟩ | ⟨-, -, h0, -⟩ | ⟨h0, -⟩)⟩
      · exact absurd hψS h1
      · exact ihd e ⟨he, hed⟩ he heS wy
      · obtain ⟨w, hwfr, hwn⟩ := wit_c2 hw wy we (le_of_ne_gtY wd we hde) hyS hn'
        rcases hwfr with hwfr | hwfr | hwfr
        · have hwd := fr_leY wS wd hwfr
          have wW : WNF w := wd.of_mem_subs (fr_spec hwfr).1
          rcases le_transY wy wW wd (le_of_not_ltY wW wy hwn) hwd with e' | h'
          · rw [e']; exact Acc.intro d hd'
          · exact hd' _ ⟨hy, h'⟩
        · rw [fr_succK_self] at hwfr; cases hwfr
        · simp [fr] at hwfr
      · exact absurd h0 (Lt.irrefl _)
      · exact absurd h0 (Lt.irrefl _)

/-- `WK n` は整礎 -/
theorem acc_wk {n : Nat} (hn : 1 ≤ n) (hG : Good (.K n)) :
    ∀ x, WK n x → Acc (Rel (WK n)) x := by
  have key : ∀ x, WK n x → Lt x (succK n) → Acc (Rel (WK n)) x := by
    intro x
    induction x using size_induction with
    | h x ih =>
    intro hx hxS
    have wx := hx.wf
    by_cases hxK : Lt x (.K n)
    · exact acc_wk_of_ltK hn hG hx hxK
    cases x with
    | zero => exact absurd ((lt_K_iffY wx hn).mpr (by simp [lev])) hxK
    | one => exact absurd ((lt_K_iffY wx hn).mpr (by simp [lev]; omega)) hxK
    | K m =>
      have hm := K_le_succK (Or.inr hxS)
      rcases Nat.lt_or_eq_of_le hm with hm | rfl
      · exact absurd ((lt_K_iffY wx hn).mpr (by simp [lev]; omega)) hxK
      · exact acc_wk_K hn hG
    | plus a b =>
      have hab := hx.plus hn
      have wS := WNF.succK hn
      exact acc_wk_plus hn b (ih b (by size_omega) hab.2
          (lt_transY wx.plus.2.1 wx wS (lt_plus_rightY wx) hxS)) a
        (ih a (by size_omega) hab.1 (lt_transY wx.plus.1 wx wS (lt_plus_leftY wx) hxS)) wx
    | Om c => exact absurd (om_lt_succK hn wx hxS) hxK
    | Xi m e => exact absurd (xi_le_succK hn wx (Or.inr hxS)) hxK
    | Psi σ κ e =>
      obtain ⟨rfl, rfl⟩ := psi_lt_succK hn wx hxS hxK
      obtain ⟨he, heS⟩ := hx.psi_arg hxK
      exact acc_psiK hn hG e (ih e (by size_omega) he heS) he heS wx
  intro x hx
  rcases hx.2.2 with e | h
  · subst e
    exact Acc.intro _ (fun y hy => key y hy.1 hy.2)
  · exact key x hx h

/-! ### 崩壊の閉包のための補題 -/

theorem WNF.mi {π : Tm} (h : WNF π) : WNF (mi π) := by
  cases π with
  | Om _ => exact WNF.one
  | Xi _ _ => exact h.xi.2.1
  | Psi _ _ _ => exact h.psi.xiF
  | _ => exact WNF.zero

theorem inC_mono_g {x g g' d : Tm} (hx : WNF x) (hg : WNF g) (hg' : WNF g') (hle : Le g g')
    (h : inC x g d = true) : inC x g' d = true :=
  inC_mono x g d g' d h (fun _ _ h => h)
    (fun _ hv hvg => lt_of_lt_of_leY (hx.of_mem_subs hv) hg hg' hvg hle)

theorem succK_mono {j n : Nat} (h : j ≤ n) : Le (succK j) (succK n) := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact Or.inr (lt_of_lev_lt' (by simp [lev, succK]; omega))
  · exact Or.inl rfl

theorem K_le_K {j n : Nat} (h : j ≤ n) : Le (.K j) (.K n) := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact Or.inr (lt_of_lev_lt' (by simp [lev]; omega))
  · exact Or.inl rfl

/-- 列の上で Mahlo 添字は減る：`x` から `Ψ^ζ_ρ(b)` に至る列なら `x = Ψ^{ζ'}_{ρ'}(b')` で `m(ρ') ≤ m(ρ)` -/
theorem Ch.mahlo {x y : Tm} (h : Ch x y) (hx : WNF x) :
    ∀ ζ ρ b, y = .Psi ζ ρ b → ∃ ζ' ρ' b', x = .Psi ζ' ρ' b' ∧ Le (mi ρ') (mi ρ) := by
  induction h with
  | refl => intro ζ ρ b e; exact ⟨ζ, ρ, b, e, Or.inl rfl⟩
  | step h' ih =>
    intro ζ ρ b e
    obtain ⟨ζ', ρ', b', hx', hle⟩ := ih _ _ _ rfl
    subst e
    have w0 := h'.wnf hx
    have wρ0 := w0.psi.piF
    have wx' : WNF (.Psi ζ' ρ' b') := hx' ▸ hx
    exact ⟨ζ', ρ', b', hx', Or.inr (lt_of_le_of_ltY (WNF.mi wx'.psi.piF) wρ0.psi.xiF (WNF.mi wρ0.psi.piF)
      hle wρ0.psi.mlt)⟩

/-- `Ξ_j(d) < π`（`π` は `Ω_c` 以外の目標、階 `j`）、`π ∈ C(a, π)`、`a ≤ d` なら、`π` の前線（`π` について）に
    `Ξ_j(d)` 未満でない元がある -/
theorem wit_xi_tgt (π : Tm) (wπ : WNF π)
    (hsh : (∃ n p, π = .Xi n p) ∨ ∃ ζ κ b, π = .Psi ζ κ b ∧ ζ ≠ .zero) {j : Nat} {d a : Tm}
    (wx : WNF (.Xi j d)) (wa : WNF a) (hlt : Lt (.Xi j d) π) (hl : lev π = j)
    (hC : inC π a π = true) (had : Le a d) : ∃ w, w ∈ fr π π ∧ ¬ Lt w (.Xi j d) := by
  have hT : IsTgt π := hsh.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))
  have hOF : IsOF π := by
    rcases hT.cases wπ with ⟨c, rfl⟩ | h
    · rcases hsh with ⟨_, _, e⟩ | ⟨_, _, _, e, _⟩ <;> cases e
    · exact h
  exact (goodY3 wπ wx wa).wit_xi_tgtS π (mem3_a _ _ _) hOF hT (mem3_b _ _ _) (mem3_c _ _ _) hlt hl
    hC had

/-- `b` を引数とする崩壊が `Wmax` に入る（階 `n` 以下、Mahlo 添字は `WK n`） -/
def CollOK (n : Nat) (b : Tm) : Prop :=
  (∀ j, 1 ≤ j → j ≤ n → WNF (.Xi j b) → Wmax (.Xi j b)) ∧
    (∀ ξ π, WK n ξ → Wmax π → Lt π (.K n) → WNF (.Psi ξ π b) → Wmax (.Psi ξ π b))

/-- 係数についての帰納法で使う性質 -/
def PK (n : Nat) (x : Tm) : Prop :=
  Hull (.K n) Wmax x ∧ (Le x (succK n) → inC x (succK n) (.K n) = true)

/-- `C^{K_n}(Wmax)` の元の前線（`K_n` 以下の `R` について）は `Wmax` に入る -/
theorem fr_hullK {n : Nat} (hn : 1 ≤ n) (hG : Good (.K n)) {x R : Tm}
    (hx : Hull (.K n) Wmax x) (wR : WNF R) (hR : Le R (.K n)) :
    ∀ w, w ∈ fr R x → Wmax w := by
  intro w hw
  rcases fr_hull_wmax (fun m hm _ => fr_wmax wR m hm) x hx w hw with h | h
  · exact h
  · exact hG.2 w h (lt_of_lt_of_leY (hx.wf_of.of_mem_subs (fr_spec hw).1) wR (WNF.K' hn)
      (fr_spec hw).2 hR)

/-- 係数についての帰納法（引数 `a` 未満の引数の崩壊が `Wmax` に入るとき） -/
theorem coeffK {n : Nat} (hn : 1 ≤ n) (hG : Good (.K n)) {a : Tm} (ha : WK n a)
    (MIH : ∀ b, WK n b → Lt b a → CollOK n b) {θ R g : Tm} (wθ : WNF θ) (hθK : Lt θ (.K n))
    (wg : WNF g) (hga : Le g a) (S : Nat)
    (good : ∀ x, Hull θ Wmax x → Lt x θ → x.size < S → Wmax x) :
    ∀ x, Hull θ Wmax x → x.size < S → (∀ w, w ∈ fr R x → Lt w θ) → inC x g R = true →
      PK n x := by
  have wK := WNF.K' hn
  have wS := WNF.succK hn
  have wa := ha.wf
  have hgS : ∀ {d}, WNF d → Lt d g → Lt d (succK n) := fun wd h =>
    lt_of_lt_of_leY wd wg wS h (le_transY wg wa wS hga ha.2.2)
  refine coeff_induction (PK n) S
    (fun x hx hxθ hs => ⟨wmax_hull (good x hx hxθ hs) wK,
      fun _ => inC_of_ltY _ hx.wf_of wK (lt_transY hx.wf_of wθ wK hxθ hθK)⟩)
    ⟨Hull.zero, fun _ => inC_zero _ _⟩ ⟨Hull.one, fun _ => inC_one _ _⟩
    (fun hj => ⟨Hull.K hj, fun _ => inC_K _ _ _⟩) ?_ ?_ ?_ ?_
  · intro a' b' hw h1 h2
    refine ⟨Hull.plus hw h1.1 h2.1, fun hle => ?_⟩
    rw [inC_plus, Bool.and_eq_true]
    exact ⟨h1.2 (Or.inr (lt_of_lt_of_leY hw.plus.1 hw wS (lt_plus_leftY hw) hle)),
      h2.2 (Or.inr (lt_of_lt_of_leY hw.plus.2.1 hw wS (lt_plus_rightY hw) hle))⟩
  · intro a' hw h1
    refine ⟨Hull.om hw h1.1, fun hle => ?_⟩
    rw [inC_om]
    exact h1.2 (Or.inr (lt_of_lt_of_leY hw.om.1 hw wS hw.om.2.2 hle))
  · intro j d hw hdg hd
    have wd := hw.xi.2.1
    have hj := hw.xi.1
    by_cases hjn : j ≤ n
    · have hnode : Lt (.Xi j d) (.K n) := (lt_K_iffY hw hn).mpr hjn
      have hdS : Le d (succK n) :=
        le_transY wd (WNF.succK hj) wS (le_of_ne_gtY wd (WNF.succK hj) hw.xi.2.2.2.1)
          (succK_mono hjn)
      have hW : Wmax (.Xi j d) :=
        (MIH d ⟨hd.1, hd.2 hdS, hdS⟩ (lt_of_lt_of_leY wd wg wa hdg hga)).1 j hj hjn hw
      exact ⟨wmax_hull hW wK, fun _ => inC_of_ltY _ hw wK hnode⟩
    · have hKj : Lt (.K n) (.K j) := lt_of_lev_lt' (by simp [lev]; omega)
      refine ⟨Hull.xi hw hKj hd.1, fun hle => ?_⟩
      have := (lt_K_iffY hw hn).mp (xi_le_succK hn hw hle)
      simp only [lev] at this
      exact absurd this hjn
  · intro σ κ d hw hdg hσ hκ hd
    have hP := hw.psi
    have wd := hP.aF
    have hdS : Lt d (succK n) := hgS wd hdg
    by_cases hnode : Lt (.Psi σ κ d) (.K n)
    · have hσd : Le σ d := le_of_ne_gtY hP.xiF wd hP.le
      have hσS : Le σ (succK n) := Or.inr (lt_of_le_of_ltY hP.xiF wd wS hσd hdS)
      have hκK : Lt κ (.K n) := (lt_K_iffY hP.piF hn).mpr ((lt_K_iffY hw hn).mp hnode)
      have hW : Wmax (.Psi σ κ d) :=
        (MIH d ⟨hd.1, hd.2 (Or.inr hdS), Or.inr hdS⟩ (lt_of_lt_of_leY wd wg wa hdg hga)).2 σ κ
          ⟨hσ.1, hσ.2 hσS, hσS⟩ (hG.2 κ hκ.1 hκK) hκK hw
      exact ⟨wmax_hull hW wK, fun _ => inC_of_ltY _ hw wK hnode⟩
    · have hKκ : Lt (.K n) κ :=
        lt_of_le_of_ltY wK hw hP.piF (le_of_not_ltY hw wK hnode) (lt_psi_targetY hw)
      refine ⟨Hull.psi hw hKκ hσ.1 hκ.1 hd.1, fun hle => ?_⟩
      have hlt : Lt (.Psi σ κ d) (succK n) := by
        rcases hle with e | h
        · cases e
        · exact h
      obtain ⟨rfl, rfl⟩ := psi_lt_succK hn hw hlt hnode
      exact inC_psi_iff.mpr (Or.inr ⟨hκ.2 (Or.inl rfl), inC_zero _ _, hd.2 (Or.inr hdS), hdS⟩)

/-- 列の上の `Good` な崩壊の Mahlo 添字は `WK n` に入る -/
theorem mahlo_wk {n : Nat} (hn : 1 ≤ n) (hG : Good (.K n)) {a : Tm} (ha : WK n a)
    (MIH : ∀ b, WK n b → Lt b a → CollOK n b) {ζ ρ b : Tm} (hγ : Good (.Psi ζ ρ b))
    (hK : Lt (.Psi ζ ρ b) (.K n)) (hma : Le (mi ρ) a) : WK n ζ := by
  have wγ := hγ.1.wf_of
  have hP := wγ.psi
  have wm := WNF.mi hP.piF
  have wS := WNF.succK hn
  have hζH : Hull (.Psi ζ ρ b) Wmax ζ := by
    cases hγ.1 with
    | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
    | psi _ _ hs _ _ => exact hs
  have hPζ := coeffK hn hG ha MIH wγ hK wm hma (ζ.size + 1)
    (fun x hx hxθ _ => hγ.2 x hx hxθ) ζ hζH (Nat.lt_succ_self _) (FWOrder.k2s wγ) hP.mC
  have hζS : Le ζ (succK n) :=
    Or.inr (lt_of_lt_of_leY hP.xiF wm wS hP.mlt (le_transY wm ha.wf wS hma ha.2.2))
  exact ⟨hPζ.1, hPζ.2 hζS, hζS⟩

/-- Mahlo 添字についての帰納法：引数 `a` 未満の引数の崩壊が `Wmax` に入るとき、Mahlo 添字が `a` 以下で
    `WK n` に入る `K_n` 未満の `Good` な `Ψ^ζ_ρ(b)` は `Wmax` に入る -/
theorem mahlo_step {n : Nat} (hn : 1 ≤ n) (hG : Good (.K n)) {a : Tm} (ha : WK n a)
    (MIH : ∀ b, WK n b → Lt b a → CollOK n b) :
    ∀ ζ, Acc (Rel (WK n)) ζ → WK n ζ → Le ζ a → ∀ ρ b, WNF (.Psi ζ ρ b) →
      Lt (.Psi ζ ρ b) (.K n) → Good (.Psi ζ ρ b) → Wmax (.Psi ζ ρ b) := by
  have wK := WNF.K' hn
  intro ζ hacc
  induction hacc with
  | intro ζ _ IH =>
  intro hζ hζa ρ b hw hK hGγ
  refine wmax_of_good_hyp hGγ (hyp_of_good hGγ ?_)
  intro γ' τ' hγ' hγ'γ _ hc hch _ _
  have wγ' := hγ'.1.wf_of
  rcases hc with ⟨m, b', e, -⟩ | ⟨ζ', b', rfl⟩
  · cases e
  obtain ⟨ζ'', ρ'', b'', rfl, hle⟩ := hch.mahlo wγ' _ _ _ rfl
  have hP := wγ'.psi
  have wm := WNF.mi hP.piF
  have hle' : Le (mi ρ'') ζ := hle
  have hζ''ζ : Lt ζ'' ζ := lt_of_lt_of_leY hP.xiF wm hζ.wf hP.mlt hle'
  have hK' : Lt (.Psi ζ'' ρ'' b'') (.K n) := lt_transY wγ' hw wK hγ'γ hK
  have hW := mahlo_wk hn hG ha MIH hγ' hK' (le_transY wm hζ.wf ha.wf hle' hζa)
  exact IH ζ'' ⟨hW, hζ''ζ⟩ hW (le_transY hP.xiF hζ.wf ha.wf (Or.inr hζ''ζ) hζa) ρ'' b'' wγ'
    hK' hγ'

/-! ### `K_n` 未満の崩壊の閉包 -/

/-- `WK n` の元を引数とする階 `n` 以下の崩壊は `Wmax` に入る（引数 `a ∈ WK n` についての帰納法。
    `Ψ^ξ_π(a)` はさらに Mahlo 添字 `ξ ∈ WK n` についての帰納法） -/
theorem coll_wk {n : Nat} (hn : 1 ≤ n) (hG : Good (.K n)) : ∀ a, WK n a → CollOK n a := by
  have wK := WNF.K' hn
  have wS := WNF.succK hn
  intro a ha
  induction acc_wk hn hG a ha with
  | intro a _ MIH0 =>
    have MIH : ∀ b, WK n b → Lt b a → CollOK n b := fun b hb hba => MIH0 b ⟨hb, hba⟩ hb
    have wa := ha.wf
    have hullK : ∀ {η x}, WNF η → Lt η (.K n) → Hull (.K n) Wmax x → Hull η Wmax x :=
      fun wη hηK hx => Hull.lower HW wη wK (Or.inr hηK) hx
    have wkOf : ∀ {x}, PK n x → Le x (succK n) → WK n x := fun h hle => ⟨h.1, h.2 hle, hle⟩
    have leS : ∀ {x}, WNF x → Le x a → Le x (succK n) := fun wx h => le_transY wx wa wS h ha.2.2
    refine ⟨fun j hj hjn hw => ?_, fun ξ0 π hξ0 hπ hπK hw0 => ?_⟩
    · -- `Ξ_j(a)`
      have wKj := WNF.K' hj
      have hXK : Lt (.Xi j a) (.K j) := (lt_K_iffY hw hj).mpr (Nat.le_refl _)
      have hXKn : Lt (.Xi j a) (.K n) := lt_of_lt_of_leY hw wKj wK hXK (K_le_K hjn)
      have hnα := nr_specY _ hw
      have bound : ∀ x w, Hull (.Xi j a) Wmax x → Wmax w → Lt w (.Xi j a) → ¬ Lt w x →
          Wmax x := fun x w hx hW hwlt hn =>
        wmax_bounded hw hx hW (le_of_not_ltY (wmax_wf hW) hx.wf_of hn)
          (lt_transY (wmax_wf hW) hw hnα.1 hwlt hnα.2.2)
      have hGx : Good (.Xi j a) := by
        refine ⟨Hull.xi hw hXK (hullK hw hXKn ha.1), ?_⟩
        intro β1
        induction β1 using size_induction with
        | h β1 LIH =>
          intro hβ hβlt
          have below : ∀ x, WNF x → Lt x β1 → Lt x (.Xi j a) :=
            fun x wx h => lt_transY wx hβ.wf_of hw h hβlt
          cases hβ with
          | zero => exact wmax_zero
          | one => exact wmax_one
          | K hj' => exact hG.2 _ (Hull.K hj') (lt_transY (WNF.K' hj') hw wK hβlt hXKn)
          | mem hX _ _ => exact hX
          | plus hw₁ hb₁ hb₂ =>
            exact wmax_add hw₁
              (LIH _ (by size_omega) hb₁ (below _ hw₁.plus.1 (lt_plus_leftY hw₁)))
              (LIH _ (by size_omega) hb₂ (below _ hw₁.plus.2.1 (lt_plus_rightY hw₁)))
          | om hw₁ hd =>
            exact wmax_om _ (LIH _ (by size_omega) hd (below _ hw₁.om.1 hw₁.om.2.2)) hw₁
          | @xi j' d hw₁ hXKj hd =>
            have hjj : j' = j := by
              have h1 := (lt_K_iffY hw hw₁.xi.1).mp hXKj
              have h2 := lev_le_of_lt_gen hβlt
              simp only [lev] at h1 h2
              omega
            subst hjj
            by_cases hda : d = a
            · subst hda
              exact absurd hβlt (Lt.irrefl _)
            rcases (ff_xiY hw₁ hw hda).mp hβlt with ⟨hdlt, hfr⟩ | ⟨-, w, hwfr, hwn⟩
            · have wd := hw₁.xi.2.1
              have hPd := coeffK hn hG ha MIH hw hXKn wd (Or.inr hdlt) _
                (fun x hx hxθ hs => LIH x hs hx hxθ) d hd (by size_omega) hfr hw₁.xi.2.2.2.2
              exact (MIH d (wkOf hPd (leS wd (Or.inr hdlt))) hdlt).1 j' hj hjn hw₁
            · exact bound _ w (Hull.xi hw₁ hXKj hd)
                (fr_hullK hn hG ha.1 wKj (K_le_K hjn) w hwfr) (FWOrder.k2x hw w hwfr) hwn
          | @psi s κ d hw₁ hσ hs hκ hd =>
            rcases hw₁.shape with ⟨c', rfl, rfl⟩ | -
            · exact absurd hβlt (Lt.asymmY hw hw₁ ((lt_OF_psiOm (Or.inl ⟨j, a, rfl⟩) hw hw₁).mpr
                ((lt_OF_omG (Or.inl ⟨j, a, rfl⟩) hw hw₁.psiOm.1).mp hσ)))
            · have hl : lev κ = j := by
                have h1 := lev_le_of_lt_gen hσ
                have h2 := lev_le_of_lt_gen hβlt
                simp only [lev] at h1 h2
                omega
              obtain ⟨-, w, hwfr, hwn⟩ := wit_psi_xi hw₁ hw hl hβlt hσ
              exact bound _ w (Hull.psi hw₁ hσ hs hκ hd)
                (fr_hullK hn hG ha.1 wKj (K_le_K hjn) w hwfr) (FWOrder.k2x hw w hwfr) hwn
      have h15xi : H15 (.Xi j a) := by
        intro γ' τ' hγ' hγ'γ _ hc hch _ _
        have wγ' := hγ'.1.wf_of
        rcases hc with ⟨m, b', e, -⟩ | ⟨ζ', b', rfl⟩
        · cases e
        obtain ⟨ζ'', ρ'', b'', rfl, hle⟩ := hch.mahlo wγ' _ _ _ rfl
        have hP := wγ'.psi
        have hle' : Le (mi ρ'') a := hle
        have hK' : Lt (.Psi ζ'' ρ'' b'') (.K n) := lt_transY wγ' hw wK hγ'γ hXKn
        have hW := mahlo_wk hn hG ha MIH hγ' hK' hle'
        exact mahlo_step hn hG ha MIH ζ'' (acc_wk hn hG ζ'' hW) hW
          (Or.inr (lt_of_lt_of_leY hP.xiF (WNF.mi hP.piF) wa hP.mlt hle')) ρ'' b'' wγ' hK' hγ'
      exact wmax_of_good_hyp hGx (hyp_of_good hGx h15xi)
    · -- `Ψ^ξ_π(a)`：Mahlo 添字 `ξ` についての帰納法
      have wπ := wmax_wf hπ
      have keyξ : ∀ ξ, Acc (Rel (WK n)) ξ → WK n ξ → WNF (.Psi ξ π a) → Wmax (.Psi ξ π a) := by
        intro ξ haccξ
        induction haccξ with
        | intro ξ _ XIH0 =>
          intro hξ hw
          have XIH : ∀ σ, WK n σ → Lt σ ξ → WNF (.Psi σ π a) → Wmax (.Psi σ π a) :=
            fun σ hσ hσξ => XIH0 σ ⟨hσ, hσξ⟩ hσ
          have wξ := hw.psi.xiF
          have hnα := nr_specY _ hw
          have hγπ := lt_psi_targetY hw
          have hηK : Lt (.Psi ξ π a) (.K n) := lt_transY hw wπ wK hγπ hπK
          have bound : ∀ x w, Hull (.Psi ξ π a) Wmax x → Wmax w → Lt w (.Psi ξ π a) →
              ¬ Lt w x → Wmax x := fun x w hx hW hwlt hn =>
            wmax_bounded hw hx hW (le_of_not_ltY (wmax_wf hW) hx.wf_of hn)
              (lt_transY (wmax_wf hW) hw hnα.1 hwlt hnα.2.2)
          have hπK' : Le π (.K n) := Or.inr hπK
          have hGη : Good (.Psi ξ π a) := by
            refine ⟨Hull.psi hw hγπ (hullK hw hηK hξ.1) (wmax_hull hπ hw)
              (hullK hw hηK ha.1), ?_⟩
            intro β1
            induction β1 using size_induction with
            | h β1 LIH =>
              intro hβ hβlt
              have good : ∀ x, Hull (.Psi ξ π a) Wmax x → Lt x (.Psi ξ π a) →
                  x.size < β1.size → Wmax x := fun x hx hxθ hs => LIH x hs hx hxθ
              have below : ∀ x, WNF x → Lt x β1 → Lt x (.Psi ξ π a) :=
                fun x wx h => lt_transY wx hβ.wf_of hw h hβlt
              have coeffA : ∀ x, Hull (.Psi ξ π a) Wmax x → x.size < β1.size →
                  inC x a (.Psi ξ π a) = true → PK n x := fun x hx hs hC =>
                coeffK hn hG ha MIH hw hηK wa (Or.inl rfl) _ good x hx hs
                  (fun w hw' => (fr_spec hw').2) hC
              cases hβ with
              | zero => exact wmax_zero
              | one => exact wmax_one
              | K hj' => exact hG.2 _ (Hull.K hj') (lt_transY (WNF.K' hj') hw wK hβlt hηK)
              | mem hX _ _ => exact hX
              | plus hw₁ hb₁ hb₂ =>
                exact wmax_add hw₁
                  (LIH _ (by size_omega) hb₁ (below _ hw₁.plus.1 (lt_plus_leftY hw₁)))
                  (LIH _ (by size_omega) hb₂ (below _ hw₁.plus.2.1 (lt_plus_rightY hw₁)))
              | om hw₁ hd =>
                exact wmax_om _ (LIH _ (by size_omega) hd (below _ hw₁.om.1 hw₁.om.2.2)) hw₁
              | @xi j d hw₁ hK hd =>
                rcases hw.shape with ⟨c, rfl, rfl⟩ | hsh
                · exact wmax_bounded hw (Hull.xi hw₁ hK hd) (wmax_om_arg hπ)
                    (Or.inr ((lt_OF_psiOm (Or.inl ⟨j, d, rfl⟩) hw₁ hw).mp hβlt))
                    (lt_transY hw.psiOm.1 hw hnα.1 (FWOrder.cx hw) hnα.2.2)
                · have hl : lev π = j := by
                    have h1 := lev_le_of_lt_gen hβlt
                    have h2 := (lt_K_iffY hw hw₁.xi.1).mp hK
                    simp only [lev] at h1 h2
                    omega
                  have hjn : j ≤ n := by
                    have := (lt_K_iffY wπ hn).mp hπK
                    omega
                  have wd := hw₁.xi.2.1
                  have hn' := (lt_xi_psiY hl).mp hβlt
                  rw [lt_psi_xiY hl] at hn'
                  by_cases hda : Lt d a
                  · have hC : inC d a (.Psi ξ π a) = true := by
                      cases e : inC d a (Tm.Psi ξ π a)
                      · exact absurd (Or.inr ⟨hda, e⟩) hn'
                      · rfl
                    have hPd := coeffA d hd (by size_omega) hC
                    have hdS : Le d (succK n) :=
                      le_transY wd (WNF.succK hw₁.xi.1) wS
                        (le_of_ne_gtY wd (WNF.succK hw₁.xi.1) hw₁.xi.2.2.2.1)
                        (succK_mono hjn)
                    exact (MIH d (wkOf hPd hdS) hda).1 j hw₁.xi.1 hjn hw₁
                  · have hxπ : Lt (.Xi j d) π := by
                      cases e : cmp π (.Xi j d) with
                      | gt => exact lt_of_gtY wπ hw₁ e
                      | _ => exact absurd (Or.inl (by rw [e]; decide)) hn'
                    obtain ⟨w, hwfr, hwn⟩ := wit_xi_tgt π wπ hsh hw₁ wa hxπ hl hw.psi.Cpi
                      (le_of_not_ltY wd wa hda)
                    exact bound _ w (Hull.xi hw₁ hK hd) (fr_wmax wπ π hπ w hwfr)
                      (FWOrder.k2t hw w hwfr) hwn
              | @psi σ κ d hw₁ hσ hσH hκ hd =>
                have wσ := hw₁.psi.xiF
                have wd := hw₁.psi.aF
                have hl : lev κ = lev π := by
                  have h1 := lev_le_of_lt_gen hσ
                  have h2 := lev_le_of_lt_gen hβlt
                  simp only [lev] at h1 h2
                  omega
                rcases (lt_psi_psiY hl hβlt.ne).mp hβlt with
                  h1 | ⟨-, hβπ, (⟨hda, hdC, hσC, hκC⟩ | ⟨had, hnC⟩ | ⟨hda, e, hσξ, hσC⟩ |
                    ⟨hξσ, hnC⟩)⟩
                · exact absurd hσ h1
                · -- (1)
                  have hPd := coeffA d hd (by size_omega) hdC
                  have hPσ := coeffA σ hσH (by size_omega) hσC
                  have hPκ := coeffA κ hκ (by size_omega) hκC
                  have hκK : Lt κ (.K n) := by
                    have := (lt_K_iffY wπ hn).mp hπK
                    exact (lt_K_iffY hw₁.psi.piF hn).mpr (by omega)
                  have hdS := leS wd (Or.inr hda)
                  have hσS : Le σ (succK n) :=
                    le_transY wσ wd wS (le_of_ne_gtY wσ wd hw₁.psi.le) hdS
                  exact (MIH d (wkOf hPd hdS) hda).2 σ κ (wkOf hPσ hσS)
                    (hG.2 κ hPκ.1 hκK) hκK hw₁
                · -- (2)
                  obtain ⟨w, hwfr, hwn⟩ := wit_c2 hw hw₁ wd (le_of_ne_gtY wa wd had) hβπ hnC
                  rcases hwfr with hwfr | hwfr | hwfr
                  · exact bound _ w (Hull.psi hw₁ hσ hσH hκ hd)
                      (fr_hullK hn hG ha.1 wπ hπK' w hwfr) (FWOrder.k2 hw w hwfr) hwn
                  · exact bound _ w (Hull.psi hw₁ hσ hσH hκ hd) (fr_wmax wπ π hπ w hwfr)
                      (FWOrder.k2t hw w hwfr) hwn
                  · exact bound _ w (Hull.psi hw₁ hσ hσH hκ hd)
                      (fr_hullK hn hG hξ.1 wπ hπK' w hwfr) (FWOrder.k2s hw w hwfr) hwn
                · -- (3)
                  have e' := FWOrder.eq wd wa hda
                  subst e' e
                  have hPσ := coeffA σ hσH (by size_omega) hσC
                  have hσS : Le σ (succK n) := leS wσ (le_of_ne_gtY wσ wd hw₁.psi.le)
                  exact XIH σ (wkOf hPσ hσS) hσξ hw₁
                · -- (4)
                  obtain ⟨w, hwfr, hwn⟩ := wit_c4 hw hw₁ wσ hβlt hξσ hnC
                  exact bound _ w (Hull.psi hw₁ hσ hσH hκ hd)
                    (fr_hullK hn hG hξ.1 hw (Or.inr hηK) w hwfr) (fr_spec hwfr).2 hwn
          exact mahlo_step hn hG ha MIH ξ (acc_wk hn hG ξ hξ) hξ
            (le_of_ne_gtY wξ wa hw.psi.le) π a hw hηK hGη
      exact keyξ ξ0 (acc_wk hn hG ξ0 hξ0) hξ0 hw0

/-! ### `K_n` -/

theorem wmax_K : ∀ n, 1 ≤ n → Wmax (.K n) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihn =>
    intro hn
    have wK := WNF.K' hn
    have hG := goodK hn (fun j hj hjn => ihn j hjn hj)
    have hcoll := coll_wk hn hG
    refine wmax_of_good_hyp hG (hyp_of_good hG ?_)
    intro γ τ hγ _ Obs hc hch hτH hfr
    have wγ := hγ.1.wf_of
    rcases hc with ⟨m, b, e, rfl⟩ | ⟨ξ, b, rfl⟩
    · injection e with e
      subst e
      have hγτ := hch.le wγ
      cases hτH with
      | mem hX _ _ => exact Obs _ hX hγτ
      | xi hw _ hb =>
        have hτK : Lt (.Xi n b) (.K n) := (lt_K_iffY hw hn).mpr (Nat.le_refl _)
        have hbK : Hull (.K n) Wmax b :=
          hull_transfer wK wK (Or.inl rfl) (b.size + 1) (fun x hx hxγ _ => hγ.2 x hx hxγ) b hb
            (Nat.lt_succ_self _) (fun w hw' => hfr w (by
              rw [fr]
              simp only [Lt.irrefl, ↓reduceIte]
              exact fr_sub wK hw (Or.inr hτK) hw.xi.2.1 hw' (FWOrder.k2x hw w hw')))
        have wb := hw.xi.2.1
        have hbS : Le b (succK n) := le_of_ne_gtY wb (WNF.succK hn) hw.xi.2.2.2.1
        have hbC : inC b (succK n) (.K n) = true :=
          inC_mono_g wb wb (WNF.succK hn) hbS hw.xi.2.2.2.2
        exact Obs _ ((hcoll b ⟨hbK, hbC, hbS⟩).1 n hn (Nat.le_refl _) hw) hγτ
    · exfalso
      exact not_tgt_of_shape (fun _ e => by cases e) (fun _ _ e => by cases e)
        (fun _ _ _ e => by cases e) (hch.wnf wγ).psi.tgt

/-! ### 主定理 -/

/-- 体系全体の標準形は全て最大区別集合に入る -/
theorem wmax_of_WNF : ∀ t : Tm, WNF t → Wmax t
  | .zero, _ => wmax_zero
  | .one, _ => wmax_one
  | .K _, h => wmax_K _ h.k
  | .plus a b, h => wmax_add h (wmax_of_WNF a h.plus.1) (wmax_of_WNF b h.plus.2.1)
  | .Om a, h => wmax_om a (wmax_of_WNF a h.om.1) h
  | .Xi j a, h => by
    have hj := h.xi.1
    have wa := h.xi.2.1
    have hG := goodK hj (fun i hi _ => wmax_K i hi)
    have hS : Le a (succK j) := le_of_ne_gtY wa (WNF.succK hj) h.xi.2.2.2.1
    exact (coll_wk hj hG a ⟨wmax_hull (wmax_of_WNF a wa) (WNF.K' hj),
      inC_mono_g wa wa (WNF.succK hj) hS h.xi.2.2.2.2, hS⟩).1 j hj (Nat.le_refl _) h
  | .Psi x p a, h => by
    have hP := h.psi
    have hn : 1 ≤ lev x + lev p + lev a + 1 := by omega
    have wK := WNF.K' hn
    have hG := goodK hn (fun i hi _ => wmax_K i hi)
    have wk : ∀ y, WNF y → lev y ≤ lev x + lev p + lev a + 1 → Wmax y →
        WK (lev x + lev p + lev a + 1) y := fun y wy hl hy =>
      have hyK := (lt_K_iffY wy hn).mpr hl
      ⟨wmax_hull hy wK, inC_of_ltY _ wy wK hyK,
        Or.inr (lt_transY wy wK (WNF.succK hn) hyK (K_lt_succK hn))⟩
    exact (coll_wk hn hG a (wk a hP.aF (by omega) (wmax_of_WNF a hP.aF))).2 x p
      (wk x hP.xiF (by omega) (wmax_of_WNF x hP.xiF)) (wmax_of_WNF p hP.piF)
      ((lt_K_iffY hP.piF hn).mpr (by omega)) h

/-- 体系全体の整列性：標準形（`isNF t = true`）全体の上の `<` は整礎。`Classical.choice` も大基数の仮定も
    使わない（公理は `propext`・`Quot.sound` だけ。下の `#guard_msgs` で検査） -/
theorem _root_.RTKA.wellFounded_isNF :
    WellFounded (fun a b : {t : Tm // isNF t = true} => Lt a.1 b.1) := by
  refine ⟨fun ⟨t, ht⟩ => ?_⟩
  induction wmax_acc (wmax_of_WNF t ht) with
  | intro t _ ih => exact ⟨_, fun ⟨u, hu⟩ hlt => ih u ⟨wmax_of_WNF u hu, hlt⟩ hu⟩

end RTKA.W.WFY

/-! `#print axioms` の出力を固定する検査。主定理の依存（`cmp`・`inC`・`isNF`・`instFWOrder` など全て）が
`Classical.choice` を使うようになるとビルドが失敗する。 -/

/-- info: 'RTKA.wellFounded_isNF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms RTKA.wellFounded_isNF
