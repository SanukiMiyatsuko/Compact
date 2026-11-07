import Compact.FS.Floor
import Compact.FS.OmMain

/-! 列の不変量の全体：崩壊 `t = Ψ^0_π(X)` の残りの分岐（`X = 0`・後者の本体）をまとめ、標準形全体の定理 `seqI_all` を示す。 -/

namespace RTKA.Fund

open Tm W

/-! ### 倍数の列 -/

theorem lt_mul_of_le {v p : Tm} (hv : WNF v) (hp : WNF p) (hpp : isPrincipal p = true) (h : Le v p) :
    Lt v (mulNat p 2) :=
  lt_of_le_of_ltY hv hp (wnf_mulNat hp hpp 2) h (mulNat_lt_mulNat hp hpp (n := 1) (m := 2) (by omega))

/-- 倍数の列の不変量 -/
theorem seqI_mul {t p : Tm} (ht : WNF t) (hp : WNF p) (hpp : isPrincipal p = true)
    (htp : isPrincipal t = true) (hlt : Lt p t)
    (hC : ∀ g d, WNF g → WNF d → inC t g d = true → inC p g d = true)
    (hgap : ∀ v, v ∈ subs t → v ≠ t → Lt v t → Lt v (mulNat p 2)) : SeqI t (.mul p 2) := by
  refine seqI_nat rfl ⟨natUB_mul hp hpp htp hlt hC (by omega), fun n v hv hne hl => ?_⟩
  show Lt v (mulNat p (n + 2))
  cases n with
  | zero => exact hgap v hv hne hl
  | succ k =>
    exact lt_transY (ht.of_mem_subs hv) (wnf_mulNat hp hpp 2) (wnf_mulNat hp hpp _) (hgap v hv hne hl)
      (mulNat_lt_mulNat hp hpp (by omega))

/-! ### `X = 0`：`Ψ^0_{Ω_c}(0)` -/

/-- `Ψ^0_{Ω_c}(0)` の列の底 -/
def omBase (c : Tm) : Tm := if c = .one then .one else omHat (pred c)

/-- `omHat e` は `Ω_e` か、`e` 自身（`K_m` か `Ω` の不動点） -/
theorem omHat_cases {e : Tm} (he : WNF e) (he0 : e ≠ .zero) :
    (omHat e = .Om e ∧ WNF (.Om e)) ∨ (omHat e = e ∧ ((∃ m, e = .K m) ∨ IsOF e)) := by
  by_cases h : (isPrincipal e && omegaFixed e) = true
  · have h1 : omHat e = e := by
      unfold omHat
      rw [ite_eq_right he0, ite_eq_left h]
    refine Or.inr ⟨h1, ?_⟩
    simp only [Bool.and_eq_true] at h
    cases hq : e with
    | Xi n a => exact Or.inr (Or.inl ⟨n, a, rfl⟩)
    | K m => exact Or.inl ⟨m, rfl⟩
    | Psi ξ π a =>
      refine Or.inr (Or.inr ⟨ξ, π, a, rfl, hq ▸ he, ?_⟩)
      intro d e'
      subst e'
      have h2 := h.2
      rw [hq] at h2
      have hξ : ξ = .zero := by
        have hP' := (hq ▸ he : WNF (.Psi ξ (.Om d) a)).psi
        have := hP'.mlt
        simp only [mi] at this
        exact lt_oneY hP'.xiF this
      subst hξ
      simp [omegaFixed, isInacc] at h2
    | _ =>
      rw [hq] at h
      simp [isPrincipal, omegaFixed] at h
  · have h1 : omHat e = .Om e := by
      unfold omHat
      rw [ite_eq_right he0, ite_eq_right h]
    have hw := (omHat_wnf he he0).1
    rw [h1] at hw
    exact Or.inl ⟨h1, hw⟩

theorem le_omHat {e : Tm} (he : WNF e) (he0 : e ≠ .zero) : Le e (omHat e) := by
  rcases omHat_cases he he0 with ⟨h1, hw⟩ | ⟨h1, -⟩
  · rw [h1]
    exact Or.inr hw.om.2.2
  · rw [h1]
    exact Or.inl rfl

theorem om_le_omHat {d e : Tm} (hd : WNF (.Om d)) (he : WNF e) (he0 : e ≠ .zero) (hle : Le d e) :
    Le (.Om d) (omHat e) := by
  have hdF := hd.om.1
  rcases omHat_cases he he0 with ⟨h1, -⟩ | ⟨h1, ⟨m, rfl⟩ | hOF⟩
  · rw [h1]
    exact le_om_of_leY hdF he hle
  · rw [h1]
    have hm : 1 ≤ m := he.k
    rcases hle with rfl | h
    · exfalso
      have h2 : Lt (.K m) (.Om (.K m)) := hd.om.2.2
      exact Lt.irrefl _ ((lt_K_omY hm hdF).mp h2)
    · have h2 := (lt_K_iffY hdF hm).mp h
      exact Or.inr ((lt_K_iffY hd hm).mpr (by simpa only [lev] using h2))
  · rw [h1]
    rcases hle with rfl | h
    · exfalso
      have h2 : Lt d (.Om d) := hd.om.2.2
      exact Lt.irrefl _ ((lt_OF_omG hOF he he).mp h2)
    · exact Or.inr ((lt_om_OFG hOF).mpr h)

theorem om_succ_of_tgt {c : Tm} (h : IsTgt (.Om c)) : isSucc c = true := by
  rcases h with ⟨c', e, hs⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, -⟩
  · cases e
    exact hs
  · cases e
  · cases e

theorem pred_ne_zero {c : Tm} (hc : WNF c) (hs : isSucc c = true) (h1 : c ≠ .one) : pred c ≠ .zero := by
  intro e
  apply h1
  rw [← succT_pred hc hs, e]
  rfl

/-- `Ψ^0_{Ω_c}(0)` 未満の主要項は底以下 -/
theorem prin_le_base {c h : Tm} (ht : WNF (.Psi .zero (.Om c) .zero)) (hF : WNF h)
    (hp : isPrincipal h = true) (hl : Lt h (.Psi .zero (.Om c) .zero)) : Le h (omBase c) := by
  have hB : WNF (omBase c) := (mul_base_lt ht).1
  have hBp : isPrincipal (omBase c) = true := (mul_base_lt ht).2.1
  have hP := ht.psi
  have hπ := hP.piF
  have hcF := hπ.om.1
  have hs := om_succ_of_tgt hP.tgt
  have hlΩ : Lt h (.Om c) := lt_transY hF ht hπ hl (lt_psi_targetY ht)
  have key : ∀ z, WNF z → Lt z c → Le z (omBase c) := fun z hz hlt => by
    by_cases h1 : c = .one
    · rw [h1] at hlt
      rw [lt_oneY hz hlt]
      exact zero_le _
    · have hpc := wnf_pred hcF
      have hpc0 := pred_ne_zero hcF hs h1
      have hle : Le z (pred c) := le_of_lt_succT hz hpc (by rw [succT_pred hcF hs]; exact hlt)
      have e : omBase c = omHat (pred c) := ite_eq_right h1
      rw [e]
      exact le_transY hz hpc (omHat_wnf hpc hpc0).1 hle (le_omHat hpc hpc0)
  have keyO : ∀ d, WNF (.Om d) → Lt d c → Le (.Om d) (omBase c) := fun d hd hlt => by
    by_cases h1 : c = .one
    · rw [h1] at hlt
      exact absurd (lt_oneY hd.om.1 hlt) hd.om.2.1
    · have hpc := wnf_pred hcF
      have hpc0 := pred_ne_zero hcF hs h1
      have hle : Le d (pred c) := le_of_lt_succT hd.om.1 hpc (by rw [succT_pred hcF hs]; exact hlt)
      have e : omBase c = omHat (pred c) := ite_eq_right h1
      rw [e]
      exact om_le_omHat hd hpc hpc0 hle
  cases h with
  | zero => cases hp
  | plus a b => cases hp
  | one =>
    by_cases hB1 : omBase c = .one
    · exact Or.inl hB1.symm
    · exact Or.inr (one_lt_of_prin hB hBp hB1)
  | K m => exact key _ hF ((lt_K_omY hF.k hcF).mp hlΩ)
  | Om d => exact keyO d hF ((lt_om_psiY ht).mp hl)
  | Xi m a => exact key _ hF ((lt_OF_psiOm (Or.inl ⟨m, a, rfl⟩) hF ht).mp hl)
  | Psi ξ κ a =>
    by_cases hκ : ∃ d, κ = .Om d
    · obtain ⟨d, rfl⟩ := hκ
      have hQ := hF.psi
      have hξ : ξ = .zero := by
        have := hQ.mlt
        simp only [mi] at this
        exact lt_oneY hQ.xiF this
      subst hξ
      rcases triY hcF hQ.piF.om.1 with h' | h' | h'
      · exact absurd ((lt_om_psiY hF).mpr h') (Lt.asymmY hF hπ hlΩ)
      · subst h'
        by_cases ha : a = .zero
        · subst ha
          exact absurd hl (Lt.irrefl _)
        · have hC : inC (.Psi .zero (.Om c) .zero) a (.Psi .zero (.Om c) a) = true :=
            inC_psi_iff.mpr (Or.inr ⟨inC_tgt_of_k2t hF fun w hw => FWOrder.k2t hF w hw, inC_zero _ _,
              inC_zero _ _, zero_lt ha⟩)
          exact absurd (coll_psiY hF _ ht hC (lt_psi_targetY ht)) (Lt.asymmY hF ht hl)
      · exact Or.inr (lt_of_lt_of_leY hF hQ.piF hB (lt_psi_targetY hF) (keyO d hQ.piF h'))
    · exact key _ hF ((lt_OF_psiOm (IsOF.psi hF fun d e => hκ ⟨d, e⟩) hF ht).mp hl)

/-- `Ω_c` の添字の部分項で `Ψ^0_{Ω_c}(0)` 未満のものは底の 2 倍未満 -/
theorem om0_gap {c v : Tm} (ht : WNF (.Psi .zero (.Om c) .zero)) (hv : v ∈ subs c)
    (hl : Lt v (.Psi .zero (.Om c) .zero)) : Lt v (mulNat (omBase c) 2) := by
  have hB : WNF (omBase c) := (mul_base_lt ht).1
  have hBp : isPrincipal (omBase c) = true := (mul_base_lt ht).2.1
  have hP := ht.psi
  have hcF := hP.piF.om.1
  have hs := om_succ_of_tgt hP.tgt
  have hvF := hcF.of_mem_subs hv
  cases hsv : summands v with
  | nil =>
    rw [eq_zero_of_summands_nil hsv]
    exact lt_mul_of_le WNF.zero hB hBp (zero_le _)
  | cons a r =>
    have ham : a ∈ summands v := by
      rw [hsv]
      exact List.mem_cons_self
    have haN := (nfl_summands hvF).1 a ham
    have hal := lt_of_le_of_ltY haN.1 hvF ht (head_leY hvF hsv) hl
    rcases prin_le_base ht haN.1 haN.2 hal with e | h
    · have has : a ∈ subs v := mem_subs_of_mem_summands ham
      by_cases h1 : c = .one
      · subst h1
        simp only [subs, List.mem_singleton] at hv
        rw [hv]
        exact lt_mul_of_le WNF.one hB hBp (Or.inl rfl)
      have hpc := wnf_pred hcF
      have hpc0 := pred_ne_zero hcF hs h1
      have e1 : omBase c = omHat (pred c) := ite_eq_right h1
      rw [e1] at e ⊢
      rw [e1] at hB hBp
      rcases omHat_cases hpc hpc0 with ⟨h2, -⟩ | ⟨h2, hq⟩
      · exfalso
        rw [h2] at e
        rw [e] at has
        have h3 := node_mem_subs_pred hcF hs rfl (by intro e'; cases e') (subs_trans hv has)
        have h4 := size_le_of_mem_subs h3
        simp only [Tm.size] at h4
        omega
      · rw [h2] at e hB hBp ⊢
        have hsc := succT_pred hcF hs
        obtain ⟨z, hz⟩ : ∃ z, pred c = z := ⟨_, rfl⟩
        rw [hz] at hpc hpc0 e hB hBp hq hsc ⊢
        have hc : c = .plus z .one := by
          rw [← hsc]
          rcases hq with ⟨m, rfl⟩ | ⟨n, b, rfl⟩ | ⟨ξ, π, b, rfl, -, -⟩ <;> rfl
        have hz1 : Lt .one z := one_lt_of_prin hB hBp (by
          rcases hq with ⟨m, rfl⟩ | ⟨n, b, rfl⟩ | ⟨ξ, π, b, rfl, -, -⟩ <;> intro e' <;> cases e')
        subst hc
        simp only [subs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | h3 | h3
        · have h4 := oadd_lt_oadd hB WNF.one hB hz1
          have h5 : WNF (.plus z z) := wnf_mulNat hB hBp 2
          rw [oadd_plus hcF, oadd_plus h5] at h4
          exact h4
        · refine lt_mul_of_le (hB.of_mem_subs h3) hB hBp (Or.inl ?_)
          rw [e] at has
          exact Classical.byContradiction fun hne => by
            have h4 := size_lt_of_mem_subs_ne h3 hne
            have h5 := size_le_of_mem_subs has
            omega
        · rw [h3]
          exact lt_mul_of_le WNF.one hB hBp (Or.inr hz1)
    · exact lt_mul_of_le hvF hB hBp (Or.inr (lt_prin_of_head hsv hBp haN.2 h))

/-- `Ψ^0_{Ω_c}(0)` の列 -/
theorem seqI_om_zero {c : Tm} (ht : WNF (.Psi .zero (.Om c) .zero)) :
    SeqI (.Psi .zero (.Om c) .zero) (.mul (if c = .one then .one else omHat (pred c)) 2) := by
  obtain ⟨hB, hBp, hBt⟩ := mul_base_lt ht
  refine seqI_mul ht hB hBp rfl hBt (fun g d _ hd h => ?_) fun v hv hne hl => ?_
  · by_cases hdt : Lt (.Psi .zero (.Om c) .zero) d
    · exact WFY.inC_of_ltY _ hB hd (lt_transY hB ht hd hBt hdt)
    · obtain ⟨-, hk, -, -⟩ := comp_of_inC ht hd hdt h
      rw [inC_om] at hk
      split
      · exact inC_one _ _
      · exact inC_omHat (inC_pred_of ht.psi.piF.om.1 hk)
  · simp only [subs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
    rcases hv with e | (h | h | h) | h
    · exact absurd e hne
    · rw [h]
      exact lt_mul_of_le WNF.zero hB hBp (zero_le _)
    · rw [h] at hl
      exact absurd hl (Lt.asymmY ht ht.psi.piF (lt_psi_targetY ht))
    · exact om0_gap ht h hl
    · rw [h]
      exact lt_mul_of_le WNF.zero hB hBp (zero_le _)

/-! ### 後者の引数 -/

theorem seed_of_fr {π X p : Tm} (ht : WNF (.Psi .zero π X)) (hp : p ∈ fr π X) : SeedP π X p :=
  ⟨ht.psi.aF.of_mem_subs (fr_spec hp).1, FWOrder.k2 ht p hp,
    fun _ _ hg hd h => inC_seed_fr ht hp hg hd h, fr_node hp⟩

/-- 後者の引数：`Ψ^0_π(pred X)` 以上の主要項は隙間を満たす -/
theorem gp_succ {π X y : Tm} (ht : WNF (.Psi .zero π X)) (hs : isSucc X = true)
    (hp : WNF (.Psi .zero π (pred X))) (hyF : WNF y) (hyp : isPrincipal y = true)
    (hle : Le (.Psi .zero π (pred X)) y) : Gp (.Psi .zero π X) y := by
  intro v hv hne hl
  have hvF := ht.of_mem_subs hv
  have hy0 : y ≠ .zero := fun e => by
    rw [e] at hyp
    cases hyp
  simp only [subs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
  rcases hv with e | (h | h) | h
  · exact absurd e hne
  · rw [h]
    exact zero_lt hy0
  · exact lt_of_lt_of_leY hvF hp hyF
      (lt_of_mem_tgt hp h (lt_transY hvF ht ht.psi.piF hl (lt_psi_targetY ht))) hle
  · exact lt_of_lt_of_leY hvF hp hyF (lt_seed_of_sub ht hs hp h hl) hle

theorem mi_ne_zero {π : Tm} (hπ : WNF π) (h : IsTgt π) : mi π ≠ .zero := by
  rcases h with ⟨c, rfl, -⟩ | ⟨n, q, rfl⟩ | ⟨ζ, κ, b, rfl, hζ⟩
  · intro e
    cases e
  · exact hπ.xi.2.2.1
  · exact hζ

/-- 目標の Mahlo 添字の上限の加数 -/
theorem mi_parts {π X : Tm} (ht : WNF (.Psi .zero π X))
    (hIH : ∀ u, u ∈ subs (.Psi .zero π X) → u ≠ .Psi .zero π X → SeqI u (info u).seq) :
    (∀ u, u ∈ summands (mi π) → u ≠ .one → SeqI u (info u).seq) ∧
      ∀ u, u ∈ summands (mi π) → u ≠ .one → u ∈ subs (.Psi .zero π X) ∧ u.size < π.size := by
  rcases ht.psi.tgt with ⟨c, rfl, -⟩ | ⟨n, q, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩
  · constructor <;>
    · intro u hu h1
      simp only [mi, summands, List.mem_singleton] at hu
      exact absurd hu h1
  · obtain ⟨h1, h2, -⟩ := xi_parts ht hIH (.refl _)
    exact ⟨h1, h2⟩
  · obtain ⟨-, h1, h2⟩ := psi_parts hIH (.refl _)
    exact ⟨h1, h2⟩

/-- 後者の引数の文脈：`τ = π`、`Y = pred X`、Mahlo 添字の上限は `mi π` -/
theorem mctx_succ {π X : Tm} (ht : WNF (.Psi .zero π X)) (hs : isSucc X = true)
    (hval : validR π (pred X) = true) : MCtx π X π (pred X) (mi π) (fun _ _ => False) := by
  have hP := ht.psi
  have hπF := hP.piF
  have hX := hP.aF
  have hYF := wnf_pred hX
  have hτY : ∀ r, argR? π = some r → Lt r (pred X) := fun r hr => by
    unfold validR at hval
    rw [hr] at hval
    exact ltB_iff.mp hval
  obtain ⟨hμF, hμY, hμ1, hμ2, hμC⟩ := mi_facts hπF hP.tgt hYF hτY
  have hsub : ∀ u, u ∈ summands (pred X) → u ∈ summands X := fun u hu => by
    rw [← succT_pred hX hs, summands_succT]
    exact List.mem_append_left _ hu
  exact
    { ht := ht
      hv := by
        show WNF (.Psi .zero π (succT (pred X)))
        rw [succT_pred hX hs]
        exact ht
      hYC := inC_pred_self hX hs hP.Ca
      hτY := hτY
      hle := Or.inl rfl
      hlev := rfl
      hYF := hYF
      hYm := fun u hu => subs_psi_a (mem_subs_of_mem_summands (hsub u hu))
      hμF := hμF
      hμY := hμY
      hμm := Or.inl rfl
      hμ1 := hμ1
      hμ2 := hμ2
      hμσ := fun σ hσ hπσ => inC_mono_d hπF hσ hπσ hμF hμ2
      comp := fun g d h => by
        obtain ⟨hdt, hk, hδ, hXg⟩ := h.comp ht
        have hdπ : Le d π := le_transY h.2.1 ht hπF hdt (Or.inr (lt_psi_targetY ht))
        exact ⟨hdπ, hk, inC_pred_of hX hδ, lt_of_lt_of_leY hYF hX h.1 (pred_lt hX hs) hXg,
          hμC g d (fun h2 => not_lt_of_leY h.2.1 hπF hdπ h2) hk⟩
      hT := fun _ _ h => h.elim
      ltT := fun _ _ h _ => h
      ltI := fun _ hy _ _ => lt_psi_targetY hy }

/-- 最初の近似は `Ψ^0_τ(Y)` 以上 -/
theorem mcanon_ge {π X τ Y μ : Tm} {T : Tm → Tm → Prop} (C : MCtx π X τ Y μ T) (hμ0 : μ ≠ .zero)
    (hSμ : ∀ u, u ∈ summands μ → u ≠ .one → SeqI u (info u).seq)
    (hμs : ∀ u, u ∈ summands μ → u ≠ .one → u ∈ subs (.Psi .zero π X) ∧ u.size < π.size) :
    WNF (mcanon π τ Y μ) ∧ Le (.Psi .zero τ Y) (mcanon π τ Y μ) := by
  have hw0 := C.hw0
  unfold mcanon
  by_cases h1 : μ = .one
  · rw [ite_eq_left h1]
    exact ⟨hw0, Or.inl rfl⟩
  rw [ite_eq_right h1]
  by_cases hs : isSucc μ = true
  · rw [ite_eq_left hs]
    have hμF := C.hμF
    have hy₁ : WNF (.Psi (pred μ) τ Y) :=
      C.nfI (wnf_pred hμF) (pred_lt hμF hs) h1 (inC_pred_of hμF C.hμ1) (inC_pred_of hμF C.hμ2)
    exact ⟨hy₁, Or.inr (psi0_lt_idx hw0 hy₁ (pred_ne_zero hμF hs h1))⟩
  · rw [ite_eq_right hs]
    obtain ⟨pre, R, -, -, -, -, -, o0⟩ := s0_out C hSμ hμs hμ0 hs
    obtain ⟨P₀, z₀, -, hz₀, hfF, -⟩ := o0.form _ o0.mem
    refine ⟨hfF, ?_⟩
    rw [hz₀] at hfF ⊢
    by_cases hz0 : approx pre P₀ z₀ = .zero
    · rw [hz0]
      exact Or.inl rfl
    · exact Or.inr (psi0_lt_idx hw0 hfF hz0)

theorem sums_eq : ∀ t : Tm, (info t).sums = (summands t).map fun s => (s, (info s).seq)
  | .zero | .one | .K _ | .Om _ | .Xi _ _ | .Psi _ _ _ => rfl
  | .plus a b => by
    show (a, (info a).seq) :: (info b).sums = _
    rw [sums_eq b]
    rfl

theorem sums_pred {X : Tm} (hX : WNF X) : (info X).sums.dropLast = (info (pred X)).sums := by
  have e : summands (pred X) = (summands X).dropLast := by
    unfold pred
    exact summands_ofSummands _ fun x hx => nfl_principal (nfl_summands hX) x (List.dropLast_subset _ hx)
  rw [sums_eq X, sums_eq (pred X), e, List.map_dropLast]

/-! ### 崩壊の列 -/

/-- 崩壊 `t = Ψ^0_π(X)` の列の不変量 -/
theorem seqI_psi0 {π X : Tm} (ht : WNF (.Psi .zero π X))
    (hIH : ∀ u, u ∈ subs (.Psi .zero π X) → u ≠ .Psi .zero π X → SeqI u (info u).seq) :
    SeqI (.Psi .zero π X) (cseq π (info π).fam X (info X).sums) := by
  have hP := ht.psi
  have hπF := hP.piF
  have hX := hP.aF
  have hsX : ∀ S, S ∈ subs X → S ≠ .Psi .zero π X := fun S hS => ne_of_size_lt (by
    have := size_le_of_mem_subs hS
    simp only [Tm.size]
    omega)
  have hS : ∀ S, S ∈ summands X → S ≠ .one → SeqI S (info S).seq := fun S hm _ =>
    hIH S (subs_psi_a (mem_subs_of_mem_summands hm)) (hsX S (mem_subs_of_mem_summands hm))
  have hfam : (∀ c, π ≠ .Om c) → ∀ p W, SeedP π X p → Dom (.Psi .zero π X) p →
      WNF (.Psi .zero π W) → Le (.Psi .zero π W) p →
      SeqI (.Psi .zero π X) (famSeq (info π).fam π (some p)) := fun hn p W Sp hD hw hle =>
    fam_rec ht hIH π (.refl _) hn p W Sp hD hw hle
  have hmul : ∀ c, π = .Om c → ∀ p, SeedP π X p →
      (∀ v, v ∈ subs (.Psi .zero π X) → v ≠ .Psi .zero π X → Lt v (.Psi .zero π X) → Lt v (mulNat p 2)) →
      SeqI (.Psi .zero π X) (famSeq (info π).fam π (some p)) := by
    intro c e p Sp hgap
    subst e
    have e' : (info (.Om c)).fam = .om := rfl
    rw [e', famSeq]
    exact seqI_mul ht Sp.hF Sp.prin rfl Sp.hlt Sp.hC hgap
  unfold cseq
  by_cases hX0 : X = .zero
  · rw [ite_eq_left hX0]
    subst hX0
    cases π with
    | Om c => exact seqI_om_zero ht
    | _ => exact True.intro
  rw [ite_eq_right hX0]
  have hd := lastS_dom hX hX0
  by_cases hs : isSucc X = true
  · have hd1 : (lastS (info X).sums).dom = .one := by
      rw [hd]
      exact (dom_eq_one_iff hX).mpr hs
    rw [hd1]
    dsimp only
    by_cases hval : validR π (pred X) = true
    · rw [ite_eq_right (by simp [hval])]
      have C := mctx_succ ht hs hval
      have hμ0 := mi_ne_zero hπF hP.tgt
      obtain ⟨hSμ, hμs⟩ := mi_parts ht hIH
      have hSY : ∀ u, u ∈ summands (pred X) → u ≠ .one → SeqI u (info u).seq := fun u hu h1 =>
        hS u (by
          rw [← succT_pred hX hs, summands_succT]
          exact List.mem_append_left _ hu) h1
      obtain ⟨hmF, hm0⟩ := mcanon_ge C hμ0 hSμ hμs
      rw [sums_pred hX, mOfT_tgt hP.tgt, fam_mdl hP.tgt]
      refine mahlo_spec C (mpar_chain ht hIH (.refl _) hP.tgt) hμ0 hSY hSμ hμs (fun _ e => by cases e) (fun _ e => by cases e)
        (fun y hyF hyp _ hle _ => gp_succ ht hs C.hw0 hyF hyp (le_transY C.hw0 hmF hyF hm0 hle))
        (fun p' Sp hD hle => ?_) (fun _ e => by cases e)
      by_cases hn : ∃ c, π = .Om c
      · obtain ⟨c, e⟩ := hn
        exact hmul c e p' Sp fun v hv hne hl => lt_mul_of_le (ht.of_mem_subs hv) Sp.hF Sp.prin
          (Or.inr (gp_succ ht hs C.hw0 Sp.hF Sp.prin hle v hv hne hl))
      · exact hfam (fun c e => hn ⟨c, e⟩) p' (pred X) Sp hD C.hw0 hle
    · rw [ite_eq_left (Bool.eq_false_iff.mpr hval)]
      cases hr : argR? π with
      | none =>
        unfold validR at hval
        rw [hr] at hval
        exact absurd rfl hval
      | some r =>
        have hrF := wnf_of_argR hπF hr
        have hn : ¬ Lt r (pred X) := fun h' => hval (by
          unfold validR
          rw [hr]
          exact ltB_iff.mpr h')
        have h3 : Le r (pred X) := le_of_lt_succT hrF (wnf_pred hX) (by
          rw [succT_pred hX hs]
          exact arg_lt_of_psi ht hr)
        have h4 : r = pred X := h3.resolve_right hn
        have e' : X = sc r := by
          rw [h4]
          exact (succT_pred hX hs).symm
        subst e'
        cases π with
        | Xi m q =>
          cases hr
          exact floor_xi ht hIH
        | Psi ζ κ γ =>
          cases hr
          exact floor_psi ht hIH
        | _ => cases hr
  · have hd1 : (lastS (info X).sums).dom ≠ .one := by
      rw [hd]
      exact fun h => hs ((dom_eq_one_iff hX).mp h)
    have hlim := seqI_limit (πf := (info π).fam) ht hX0 hs hS fun p W hpm _ hD hw hle hΩ => by
      have Sp := seed_of_fr ht hpm
      by_cases hn : ∃ c, π = .Om c
      · obtain ⟨c, e⟩ := hn
        exact hmul c e p Sp fun v hv hne hl => lt_mul_of_le (ht.of_mem_subs hv) Sp.hF Sp.prin
          (hΩ c e v hv hne hl)
      · exact hfam (fun c e => hn ⟨c, e⟩) p W Sp hD hw hle
    split
    · rename_i h
      exact absurd h hd1
    · exact hlim

/-! ### 全体の定理 -/

theorem seqI_add {a b : Tm} {s : SeqD} (ht : WNF (.plus a b)) (hb : SeqI b s) :
    SeqI (.plus a b) (.add a s) := by
  unfold SeqI at hb ⊢
  have e : (SeqD.add a s).dom = s.dom := rfl
  rw [e]
  cases hd : s.dom with
  | zero => trivial
  | one => trivial
  | omega =>
    rw [hd] at hb
    exact natInv_add ht hb
  | big σ =>
    rw [hd] at hb
    exact ⟨bigInv_add ht hb.1, (fun h => by cases h), hb.2.2⟩

theorem seqI_om {c : Tm} (ht : WNF (.Om c)) (hIH : SeqI c (info c).seq) :
    SeqI (.Om c) (info (.Om c)).seq := by
  by_cases hs : isSucc c = true
  · have e : (info (.Om c)).seq = .reg (.Om c) (base (.Om c)) := by simp [info, hs]
    rw [e]
    exact seqI_big rfl (Or.inl (Or.inl ⟨c, rfl, hs⟩)) (bigInv_om_succ ht hs)
  · have e : (info (.Om c)).seq = .om (info c).seq := by simp [info, hs]
    rw [e]
    unfold SeqI at hIH ⊢
    have e2 : (SeqD.om (info c).seq).dom = (info c).seq.dom := rfl
    rw [e2]
    cases hd : (info c).seq.dom with
    | zero => trivial
    | one => trivial
    | omega =>
      rw [hd] at hIH
      exact natInv_om ht hs hIH
    | big σ =>
      rw [hd] at hIH
      have h := bigInv_om ht hs hIH.1
      exact ⟨h.weak, fun _ => h.2, hIH.2.2⟩

/-- 標準形の項の列の不変量 -/
theorem seqI_all (t : Tm) (ht : WNF t) : SeqI t (info t).seq := by
  induction hn : t.size using Nat.strongRecOn generalizing t with
  | ind n ih =>
    have hIH : ∀ u, u ∈ subs t → u ≠ t → SeqI u (info u).seq := fun u hu hne =>
      ih u.size (hn ▸ size_lt_of_mem_subs_ne hu hne) u (ht.of_mem_subs hu) rfl
    cases t with
    | zero => exact True.intro
    | one => exact True.intro
    | K m => exact seqI_big rfl (Or.inr ⟨m, rfl⟩) (bigInv_K ht.k)
    | plus a b =>
      refine seqI_add ht (hIH b ?_ ?_)
      · exact subs_plus_r (self_mem_subs b)
      · exact ne_of_size_lt (by simp only [Tm.size]; omega)
    | Om c =>
      refine seqI_om ht (hIH c (subs_om (self_mem_subs c)) ?_)
      exact ne_of_size_lt (by simp only [Tm.size]; omega)
    | Xi m q => exact seqI_big rfl (Or.inl (Or.inr (Or.inl ⟨m, q, rfl⟩))) (bigInv_xi ht)
    | Psi ζ π X =>
      by_cases hζ : ζ = .zero
      · subst hζ
        exact seqI_psi0 ht hIH
      · have e : (info (.Psi ζ π X)).seq = .reg (.Psi ζ π X) (base (.Psi ζ π X)) := by simp [info, hζ]
        rw [e]
        exact seqI_big rfl (Or.inl (Or.inr (Or.inr ⟨ζ, π, X, rfl, hζ⟩))) (bigInv_psi ht hζ)

end RTKA.Fund
