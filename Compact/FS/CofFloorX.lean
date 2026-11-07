import Compact.FS.CofFloor

/-! 底の共終性（続き）：`Ξ` の底の種の主張と、底の列の共終性（`floor_cof_psi`・`floor_cof_xi`）。 -/

namespace RTKA.Fund

open Tm W

/-- `Ξ` の底の種の分岐：引数の残りの段の節点は種 `p` 未満 -/
theorem floor_hWx {m : Nat} {q p : Tm} (ht : WNF (.Psi .zero (.Xi m q) (sc q)))
    (hIH : ∀ u, u ∈ subs (.Psi .zero (.Xi m q) (sc q)) → u ≠ .Psi .zero (.Xi m q) (sc q) →
      SeqI u (info u).seq)
    (hs : ¬ isSucc q = true)
    (Sp : SeedP (.Xi m q) (sc q) p) (hpm : p ∈ fr (.Xi m q) (.Xi m q))
    (hmax : ∀ f, f ∈ fr (.Xi m q) (.Xi m q) → Le f p)
    (hlt : Lt (s0X (.Xi m q) m q).first p) :
    ∀ L₁ L₂, summands q = L₁ ++ L₂ → (∀ u, u ∈ L₂ → Le u p) →
      ∀ b, WNF (.Xi m b) → Lt (.Xi m b) (.Psi .zero (.Xi m q) (sc q)) → Lt b q → ¬ Lt b (ofSummands L₁) →
      Le (.Xi m b) p ∨ SubLe (.Psi .zero (.Xi m q) (sc q)) (.Xi m b) := by
  intro L₁ L₂ hsum12 hL₂ b hx hxt hbq hbL
  have hρ := ht.psi.piF
  have hm := hρ.xi.1
  have hqF := hρ.xi.2.1
  have hq0 := hρ.xi.2.2.1
  have hKF : WNF (.K m) := WNF.K' hm
  have hρK : Lt (.Xi m q) (.K m) := (lt_K_iffY hρ hm).mpr (Nat.le_refl _)
  have hc : Chain (.Xi m q) (.Xi m q) := .refl _
  obtain ⟨hS, hqs, hqσ⟩ := xi_parts ht hIH hc
  obtain ⟨pre, R, hsum, hR1, -, -, -, o0⟩ := s0x_out ht hc hS hqs hqσ hq0 hs
  obtain ⟨P₀, x₀, hP₀, hz₀, hfF, hx₀F, hx₀R, hz₀q, -, -, hx₀0, hx₀g⟩ := o0.form _ o0.mem
  have e0 : P₀ = .zero := by
    rcases hP₀ with h | h <;> exact h
  subst e0
  rw [hz₀] at hlt hfF
  have hRm : R ∈ summands q := by
    rw [hsum]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hRp := nfl_principal (nfl_summands hqF) R hRm
  have hR0 : R ≠ .zero := by
    intro e
    rw [e] at hRp
    cases hRp
  have G : XiG m q .zero .one pre [] R :=
    ⟨hρ, hsum, WNF.zero, zero_lt hR0, zero_lt (by intro e; cases e), Or.inr rfl, hR1⟩
  have hRF := G.hRF
  have hN := G.hN
  have hpreF := G.hpreF
  have hpreN := nfl_append_left hN
  have hAF := G.hAF hx₀F
  have hEF := G.hEF hx₀F
  have hpK : Lt p (.K m) := lt_transY Sp.hF hρ hKF (fr_spec hpm).2 hρK
  have hfrpre : ∀ w, w ∈ fr (.K m) (ofSummands pre) → Lt w (.Xi m (xA .one pre .zero x₀)) := fun w hw =>
    FWOrder.k2x hfF w (fr_oadd_of_left hpreF hEF (fun s hd r' hs' e => by
      rw [summands_ofSummands _ (nfl_principal hpreN)] at hs'
      exact head_le_pre hN hEF (G.hER hx₀F hx₀R) s hd r' hs' e) hw)
  have hpR : p ∈ fr (.K m) R := by
    obtain ⟨s, hs', hp'⟩ := (mem_fr_iff hqF).mp (fr_cover_xi hρ hpm)
    rw [hsum] at hs'
    rcases List.mem_append.mp hs' with h2 | h2
    · exfalso
      have h3 : p ∈ fr (.K m) (ofSummands pre) := (mem_fr_iff hpreF).mpr
        ⟨s, by rw [summands_ofSummands _ (nfl_principal hpreN)]; exact h2, hp'⟩
      exact Lt.asymmY Sp.hF hfF (hfrpre p h3) hlt
    · rw [List.mem_singleton.mp h2] at hp'
      exact hp'
  have hpleR : Le p R := fr_leY hKF hRF hpR
  have hpp : p ∈ fr (.K m) p := mem_fr_self (fr_node hpm) hpK
  -- `pre` の加数は `p` より大きい
  have hpnot : ∀ u, u ∈ pre → ¬ Le u p := fun u hu hup => by
    have huF := (hN.1 u (List.mem_append_left _ hu)).1
    have hRu : Le R u := le_of_ne_gtY hRF huF (le_of_nfl_append (rest := []) hN u hu)
    have e1 : u = p := le_antisymmY huF Sp.hF hup (le_transY Sp.hF hRF huF hpleR hRu)
    rw [e1] at hu
    exact Lt.asymmY Sp.hF hfF (hfrpre p ((mem_fr_iff hpreF).mpr
      ⟨p, by rw [summands_ofSummands _ (nfl_principal hpreN)]; exact hu, hpp⟩)) hlt
  have hL₂ne : L₂ ≠ [] := by
    rintro rfl
    rw [List.append_nil] at hsum12
    apply hbL
    rw [← hsum12, ofSummands_summands q hqF]
    exact hbq
  -- `L₁ = pre`、`R = p`
  obtain ⟨hL1, hRe⟩ : L₁ = pre ∧ R = p := by
    have e := hsum12.symm.trans hsum
    rcases List.append_eq_append_iff.mp e with ⟨a', h1', h2'⟩ | ⟨c', h1', h2'⟩
    · have hRL : R ∈ L₂ := by
        rw [h2']
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      have hRp' : R = p := le_antisymmY hRF Sp.hF (hL₂ R hRL) hpleR
      cases a' with
      | nil => exact ⟨by simpa using h1'.symm, hRp'⟩
      | cons u l =>
        exfalso
        have hu1 : u ∈ pre := by
          rw [h1']
          exact List.mem_append_right _ List.mem_cons_self
        have hu2 : u ∈ L₂ := by
          rw [h2']
          exact List.mem_append_left _ List.mem_cons_self
        exact hpnot u hu1 (hL₂ u hu2)
    · cases c' with
      | nil =>
        have h1'' : L₁ = pre := by simpa using h1'
        have h2'' : L₂ = [R] := by simpa using h2'.symm
        exact ⟨h1'', le_antisymmY hRF Sp.hF (hL₂ R (by rw [h2'']; exact List.mem_singleton.mpr rfl)) hpleR⟩
      | cons u l =>
        exfalso
        simp only [List.cons_append, List.cons.injEq] at h2'
        apply hL₂ne
        cases L₂ with
        | nil => rfl
        | cons a l' => simp at h2'
  rw [hL1] at hbL
  have hbF := hx.xi.2.1
  have hqe : q = ofSummands (pre ++ R :: []) := by rw [← hsum, ofSummands_summands q hqF]
  obtain ⟨L', hbs, hL'⟩ := lt_sum_split hN hbF (by rw [← hqe]; exact hbq) hbL
  have hbN := nfl_summands hbF
  rw [hbs] at hbN
  have hL'N : NFL L' := nfl_append_right hbN
  have hRN1 : NFL (R :: []) := nfl_append_right hN
  have hL'lt : Lt (ofSummands L') R := by
    have h1 : Lt (ofSummands L') (ofSummands (R :: [])) := by
      unfold Lt
      rw [cmp_eq, summands_ofSummands _ (nfl_principal hL'N), summands_ofSummands _ (nfl_principal hRN1)]
      exact hL'
    exact h1
  have hL'p : ∀ u, u ∈ L' → Lt u p := fun u hu => by
    rw [← hRe]
    exact lt_of_le_of_ltY (hL'N.1 u hu).1 (wnf_ofSummands hL'N) hRF (le_ofSummands_of_mem hL'N hu) hL'lt
  -- `p` の真の部分項で `ρ` 未満のものは `s0` の 0 番目未満
  have hS' : ∀ v, v ∈ subs p → v ≠ p → Lt v (.Xi m q) → Lt v (.Xi m (xA .one pre .zero x₀)) := by
    intro v hv hne hl
    have hx₀K : Lt x₀ (.K m) := lt_transY hx₀F hRF hKF hx₀R (by rw [hRe]; exact hpK)
    have hyK : Lt (.Xi m (xA .one pre .zero x₀)) (.K m) := (lt_K_iffY hfF hm).mpr (Nat.le_refl _)
    have hAC : inC (xA .one pre .zero x₀) (xA .one pre .zero x₀) (.Xi m (xA .one pre .zero x₀)) = true :=
      inC_of_fr_lt hAF hKF hfF hAF hAF hfF.xi.2.2.2.2 (Or.inr hyK) (Or.inl rfl)
        fun w hw => FWOrder.k2x hfF w hw
    have hxy := coll_xi0 hfF x₀ hx₀F (G.parts hx₀F hx₀R hAC).2.1 hx₀K
    have hG0 : ∀ u, u ∈ subs p → u ≠ p → Lt u p → Lt u (.Xi m (xA .one pre .zero x₀)) :=
      fun u hu hne' hl' => by
        have hu' := hx₀g u (by rw [hRe]; exact hu) (by rw [hRe]; exact hne') (by rw [hRe]; exact hl')
        exact lt_transY (Sp.hF.of_mem_subs hu) hx₀F hfF hu' hxy
    have hvF := Sp.hF.of_mem_subs hv
    have hvK : Lt v (.K m) := lt_transY hvF hρ hKF hl hρK
    have hsv := size_lt_of_mem_subs_ne hv hne
    have hsp := size_le_of_mem_subs (fr_spec hpm).1
    have hsz : v.size < (Tm.Xi m q).size := by omega
    have hmem : R ∈ pre ++ [R] := List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have hsubR : ∀ {u n : Tm}, n ∈ subs v → u ∈ subs n → u ∈ subs R := fun hn hu => by
      rw [hRe]
      exact subs_trans hv (subs_trans hn hu)
    have hneR : ∀ {u n : Tm}, n ∈ subs v → u.size < n.size → u ≠ R := fun hn hu => by
      rw [hRe]
      exact ne_of_size_lt (by
        have := size_le_of_mem_subs hn
        omega)
    refine hull_ltx hρ hfF hsz (fun n hn hnF hny f hf => ?_) (fun s k a hn hlt' => ?_)
      (fun m' b' hn hlt' => ?_) hvF hvK (WFY.inC_of_ltY q hvF hρ hl)
    · have hnp : n ∈ subs p := subs_trans hv hn
      have hnne : n ≠ p := ne_of_size_lt (Nat.lt_of_le_of_lt (size_le_of_mem_subs hn) hsv)
      have h1 : ¬ Lt n p := fun h' => hny (hG0 n hnp hnne h')
      have h2 : Lt p n := (le_of_not_ltY hnF Sp.hF h1).resolve_left (Ne.symm hnne)
      exact lt_of_le_of_ltY (hρ.of_mem_subs (fr_spec hf).1) Sp.hF hnF (hmax f hf) h2
    · exact G.lt_xA hx₀F hx₀R hx₀0 hx₀g hmem (hsubR hn (subs_psi_a (self_mem_subs a)))
        (hneR hn (by simp only [Tm.size]; omega)) hlt'
    · exact G.lt_xA hx₀F hx₀R hx₀0 hx₀g hmem (hsubR hn (subs_xi (self_mem_subs b')))
        (hneR hn (by simp only [Tm.size]; omega)) hlt'
  have hxρ : Lt (.Xi m b) (.Xi m q) := lt_transY hx ht hρ hxt (lt_psi_targetY ht)
  have hsubp : ∀ w, w ∈ subs p → w ≠ p → Lt w p → Lt w (.Xi m (xA .one pre .zero x₀)) :=
    fun w hw hne hwp => hS' w hw hne (lt_transY (Sp.hF.of_mem_subs hw) Sp.hF hρ hwp (fr_spec hpm).2)
  have hbC : ∀ g, inC (ofSummands pre) g p = true → inC b g p = true := fun g hpreC => by
    rw [inC_iff_summands hbF, hbs]
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact (inC_ofSummands pre).mp hpreC u hu
    · exact WFY.inC_of_ltY g (hL'N.1 u hu).1 Sp.hF (hL'p u hu)
  rcases fr_node hpm with ⟨j, φ, ep⟩ | ⟨s₁, π₁, φ, ep⟩
  · subst ep
    have hpj := Sp.hF.xi
    have hφF := hpj.2.1
    have hjm : m = j := by
      have h1 := lev_le_of_lt_gen hlt
      have h2 := (lt_K_iffY Sp.hF hm).mp hpK
      simp only [lev] at h1 h2
      omega
    subst hjm
    have hAφ : xA .one pre .zero x₀ ≠ φ := fun e => by
      rw [e] at hlt
      exact Lt.irrefl _ hlt
    rcases (lt_xi_xi0 hAφ).mp hlt with ⟨hAφ', hAC⟩ | ⟨hφA, hn⟩
    · have hφq : φ ≠ q := fun e => by
        have h' := (fr_spec hpm).2
        rw [e] at h'
        exact Lt.irrefl _ h'
      rcases (lt_xi_xi0 hφq).mp (fr_spec hpm).2 with ⟨hφq', -⟩ | ⟨hqφ, -⟩
      · exfalso
        have hqo : q = oadd (ofSummands pre) R := eq_oadd_of_sum hqF hsum
        rw [hqo] at hφq'
        rcases lt_oadd_cases hN hφF hφq' with h' | ⟨φ', hφ'F, hφ'R, hsφ, e⟩
        · exact Lt.asymmY hAF hφF hAφ' (lt_of_lt_of_leY hφF hpreF hAF h' (le_oadd_left hpreF hEF))
        · have hEφ' : Lt (nsum .one (nsum .zero x₀)) φ' := by
            refine (le_of_not_ltY hφ'F hEF fun h'' => ?_).resolve_left fun e' => ?_
            · rw [e] at hAφ'
              exact Lt.asymmY hAF (wnf_oadd hpreF hφ'F) hAφ' (oadd_lt_oadd hpreF hφ'F hEF h'')
            · rw [e, ← e'] at hAφ'
              exact Lt.irrefl _ hAφ'
          have hx₀E : Le x₀ (nsum .one (nsum .zero x₀)) :=
            le_transY hx₀F (wnf_nsum WNF.zero hx₀F) hEF (le_nsum_right WNF.zero hx₀F)
              (le_nsum_right WNF.one (wnf_nsum WNF.zero hx₀F))
          have hx₀φ' : Lt x₀ φ' := lt_of_le_of_ltY hx₀F hEF hφ'F hx₀E hEφ'
          have hφ'0 : φ' ≠ .zero := fun e' => by
            rw [e'] at hx₀φ'
            exact not_lt_zero _ hx₀φ'
          have hφ's : φ' ∈ subs φ := by
            have := tail_mem_subs hφF hsφ (summands_ne_nil hφ'0)
            rwa [ofSummands_summands φ' hφ'F] at this
          have hφ'ne : φ' ≠ R := by
            rw [hRe]
            exact ne_of_size_lt (by
              have := size_le_of_mem_subs hφ's
              simp only [Tm.size]
              omega)
          exact Lt.asymmY hx₀F hφ'F hx₀φ' (hx₀g φ' (by rw [hRe]; exact subs_xi hφ's) hφ'ne hφ'R)
      · have hbφ : Lt b φ := lt_transY hbF hqF hφF hbq hqφ
        have hpreC := (G.parts hx₀F hx₀R hAC).1
        exact Or.inl (Or.inr ((lt_xi_xi0 hbφ.ne).mpr (Or.inl ⟨hbφ, hbC φ hpreC⟩)))
    · exfalso
      by_cases hall : ∀ w, w ∈ fr (.K m) φ → Lt w (.Xi m (xA .one pre .zero x₀))
      · have hyK : Lt (.Xi m (xA .one pre .zero x₀)) (.K m) := (lt_K_iffY hfF hm).mpr (Nat.le_refl _)
        have hC : inC φ (xA .one pre .zero x₀) (.Xi m (xA .one pre .zero x₀)) = true :=
          inC_of_fr_lt hφF hKF hfF hφF hAF hpj.2.2.2.2 (Or.inr hyK) (Or.inr hφA) hall
        rw [hC] at hn
        cases hn
      · obtain ⟨w, hw, hn'⟩ := exists_of_not_forall_mem _ hall
        have hws : w ∈ subs (.Xi m φ) := subs_xi (fr_spec hw).1
        have hwne : w ≠ .Xi m φ := ne_of_size_lt (by
          have := size_le_of_mem_subs (fr_spec hw).1
          simp only [Tm.size]
          omega)
        exact hn' (hsubp w hws hwne (FWOrder.k2x Sp.hF w hw))
  · subst ep
    have hQ := Sp.hF.psi
    have hφF := hQ.aF
    have hl : lev π₁ = m := by
      have h1 := lev_le_of_lt_gen hlt
      have h2 := (lt_K_iffY Sp.hF hm).mp hpK
      simp only [lev] at h1 h2
      omega
    have hnp : ¬ Lt (.Psi s₁ π₁ φ) (.Xi m (xA .one pre .zero x₀)) := (lt_xi_psiY hl).mp hlt
    rw [lt_psi_xiY hl] at hnp
    have hyπ₁ : Lt (.Xi m (xA .one pre .zero x₀)) π₁ :=
      lt_of_gtY hQ.piF hfF (Classical.byContradiction fun h => hnp (Or.inl h))
    have hπ₁s : π₁ ∈ subs (.Psi s₁ π₁ φ) := subs_psi_p (self_mem_subs π₁)
    have hπ₁ne : π₁ ≠ .Psi s₁ π₁ φ := ne_of_size_lt (by simp only [Tm.size]; omega)
    have hρπ₁ : Lt (.Xi m q) π₁ := by
      rcases le_of_not_ltY hQ.piF hρ (fun h' => Lt.asymmY hfF hQ.piF hyπ₁ (hS' π₁ hπ₁s hπ₁ne h')) with e | h'
      · exfalso
        have h3 := size_le_of_mem_subs (fr_spec hpm).1
        rw [← e] at h3
        simp only [Tm.size] at h3
        omega
      · exact h'
    have hqφ : Lt q φ := by
      rcases (lt_psi_xiY hl).mp (fr_spec hpm).2 with h' | ⟨hqφ, -⟩
      · exact absurd hρπ₁ (not_lt_of_leY hQ.piF hρ (le_of_ne_gtY hQ.piF hρ h'))
      · exact hqφ
    have hAφ : Lt (xA .one pre .zero x₀) φ := lt_transY hAF hqF hφF hz₀q hqφ
    have hAC : inC (xA .one pre .zero x₀) φ (.Psi s₁ π₁ φ) = true := by
      cases e : inC (xA .one pre .zero x₀) φ (.Psi s₁ π₁ φ) with
      | true => rfl
      | false => exact absurd (Or.inr ⟨hAφ, e⟩) hnp
    have hpreC := (G.parts hx₀F hx₀R hAC).1
    have hbC' := hbC φ hpreC
    have hxπ₁ : Lt (.Xi m b) π₁ := lt_transY hx hρ hQ.piF hxρ hρπ₁
    refine Or.inl (Or.inr ((lt_xi_psiY hl).mpr ?_))
    rw [lt_psi_xiY hl]
    rintro (h | ⟨-, h⟩)
    · exact not_lt_of_leY hQ.piF hx (le_of_ne_gtY hQ.piF hx h) hxπ₁
    · rw [hbC'] at h
      cases h

/-! ### 底の列の共終性 -/

/-- 目標 `Ψ^ζ_κ(γ)` の底の共終性 -/
theorem floor_cof_psi {ζ κ γ : Tm} (ht : WNF (.Psi .zero (.Psi ζ κ γ) (sc γ)))
    (hIH : ∀ u, u ∈ subs (.Psi .zero (.Psi ζ κ γ) (sc γ)) → u ≠ .Psi .zero (.Psi ζ κ γ) (sc γ) →
      SeqI u (info u).seq)
    (hIC : ∀ u, u ∈ subs (.Psi .zero (.Psi ζ κ γ) (sc γ)) → u ≠ .Psi .zero (.Psi ζ κ γ) (sc γ) →
      SeqC u (info u).seq) :
    SeqI (.Psi .zero (.Psi ζ κ γ) (sc γ))
        (famSeq (info (.Psi ζ κ γ)).fam (.Psi ζ κ γ) (maxL (frB (.Psi ζ κ γ) (.Psi ζ κ γ)))) →
      SeqC (.Psi .zero (.Psi ζ κ γ) (sc γ))
        (famSeq (info (.Psi ζ κ γ)).fam (.Psi ζ κ γ) (maxL (frB (.Psi ζ κ γ) (.Psi ζ κ γ)))) := by
  have hρ := ht.psi.piF
  have hP := hρ.psi
  have hζ0 : ζ ≠ .zero := by
    rcases ht.psi.tgt with ⟨c, e, -⟩ | ⟨n, p', e⟩ | ⟨ζ', κ', b, e, h⟩
    · cases e
    · cases e
    · cases e
      exact h
  have hc : Chain (.Psi ζ κ γ) (.Psi ζ κ γ) := .refl _
  have C := mctx_chain (X := sc γ) ht hc
  have M := mpar_chain ht hIH (hc.snoc rfl) hP.tgt
  obtain ⟨hSY, hSμ, hμs⟩ := psi_parts hIH hc
  obtain ⟨hSYC, hSμC⟩ := psi_partsC hIC hc
  have e : (info (.Psi ζ κ γ)).fam = .psi ζ (info ζ).sums κ (info κ).fam γ (info γ).sums := rfl
  rw [e, famSeq]
  exact mahlo_cof C M hζ0 hSY hSμ hμs hSYC hSμC (mi_partsC hIC (hc.snoc rfl) hP.tgt)
    (fun p hm => (maxL_frt ht hm).1)
    (fun p hm hs _ _ e' => floor_nefirst ht hIH hζ0 hs p (maxL_frt ht hm).2.1 e')
    (fun u hu => (hc.snoc rfl).fr_mem hρ hu) (floor_lowC ht _) (chain_cls ht hc)
    (fun p hm hs _ hlt => by
      obtain ⟨Sp, hpm, hmax⟩ := maxL_frt ht hm
      exact floor_hW ht hIH hζ0 hs Sp hpm hmax hlt)
    fun p' S' hle' hL' => fam_cof ht hIH hIC κ (hc.snoc rfl) (tgt_not_om hρ hζ0) p' γ S' C.hw0 hle' hL'

/-- 目標 `Ξ_m(q)` の底の共終性 -/
theorem floor_cof_xi {m : Nat} {q : Tm} (ht : WNF (.Psi .zero (.Xi m q) (sc q)))
    (hIH : ∀ u, u ∈ subs (.Psi .zero (.Xi m q) (sc q)) → u ≠ .Psi .zero (.Xi m q) (sc q) →
      SeqI u (info u).seq)
    (hIC : ∀ u, u ∈ subs (.Psi .zero (.Xi m q) (sc q)) → u ≠ .Psi .zero (.Xi m q) (sc q) →
      SeqC u (info u).seq) :
    SeqI (.Psi .zero (.Xi m q) (sc q))
        (famSeq (info (.Xi m q)).fam (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))) →
      SeqC (.Psi .zero (.Xi m q) (sc q))
        (famSeq (info (.Xi m q)).fam (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))) := by
  have hc : Chain (.Xi m q) (.Xi m q) := .refl _
  obtain ⟨hS, hqs, hqσ⟩ := xi_parts ht hIH hc
  have e : (info (.Xi m q)).fam = .xi m q (info q).sums := rfl
  rw [e, famSeq]
  exact vk_cof ht hc hS hqs hqσ (xi_partsC hIC hc) (fun p hm => (maxL_frt ht hm).1)
    (fun p hm hs _ _ e' => floor_nefirstx ht hIH hs p (maxL_frt ht hm).2.1 e') (floor_lowCx ht _)
    (fun p hm hs _ hlt => by
      obtain ⟨Sp, hpm, hmax⟩ := maxL_frt ht hm
      exact floor_hWx ht hIH hs Sp hpm hmax hlt)

end RTKA.Fund
