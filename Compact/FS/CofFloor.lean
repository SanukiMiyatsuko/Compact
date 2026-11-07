import Compact.FS.CofFam

/-! 底 `t = Ψ^0_ρ(r + 1)`（`r` は目標 `ρ` の引数）の共終性。

* 目標が `t` と族の目標の間の節点は隙間：`C(X, t)` の目標は `ρ` 以上で、`ρ` への崩壊は引数が `r` 以下にならない。
* 種の分岐（`s0` の 0 番目が種 `p` 未満）の底版の種の主張：`p` は `ρ` の添字（引数）の最後の加数で、
  `Ψ` なら `p = Ψ^{s₁}_{π₁}(φ)` は `C(φ, p)` の崩壊（`γ < φ`）か同じ引数で添字が `ζ` 以上、`Ξ` なら `q < φ`。
  どちらでも残りの段の節点は `p` 未満。 -/

namespace RTKA.Fund

open Tm W

/-- 隙間：`t` の引数・目標の前線の元以下なら部分項以下 -/
theorem subLe_gap {π X x w : Tm} (ht : WNF (.Psi .zero π X)) (hw : w ∈ fr π X ∨ w ∈ fr π π) (hxw : Le x w) :
    SubLe (.Psi .zero π X) x := by
  rcases hw with hw | hw
  · have h1 := (fr_spec hw).1
    have h2 := size_le_of_mem_subs h1
    exact ⟨w, subs_psi_a h1, ne_of_size_lt (by simp only [Tm.size]; omega), FWOrder.k2 ht w hw, hxw⟩
  · exact subLe_frπ ht hw hxw

/-- 節点は（基準より小さければ）自分の前線の元 -/
theorem mem_fr_self {R p : Tm} (hn : (∃ m a, p = .Xi m a) ∨ ∃ s q a, p = .Psi s q a) (hpR : Lt p R) :
    p ∈ fr R p := by
  rcases hn with ⟨m, a, rfl⟩ | ⟨s, q, a, rfl⟩
  · rw [fr]
    simp [hpR]
  · rw [fr]
    simp [hpR]

/-! ### 下の段 -/

/-- `Ψ` の底の下の段：目標が `t` と `κ` の間の節点は部分項以下 -/
theorem floor_lowC {ζ κ γ : Tm} (ht : WNF (.Psi .zero (.Psi ζ κ γ) (sc γ))) (P : Option Tm) :
    LowC (.Psi .zero (.Psi ζ κ γ) (sc γ)) κ P := by
  intro x hx hxt htk hkκ
  refine Or.inr ?_
  have hρ := ht.psi.piF
  have hγF := hρ.psi.aF
  have hc : Chain (.Psi ζ κ γ) (.Psi ζ κ γ) := .refl _
  rcases rho_cls ht hc hx hxt htk (Or.inr hkκ) with hkρ | hsub | ⟨s, a, rfl, -⟩
  · cases x with
    | Psi s k a =>
      have hP := hx.psi
      rcases below_psi ht hx hxt with h | ⟨w, hw, hle⟩ | ⟨-, haX, -, -, hkC⟩
      · exact absurd h (Lt.asymmY ht hP.piF htk)
      · exact subLe_gap ht hw hle
      · exfalso
        have hρk := tgt_ge ht hP.piF htk hkC
        have e : k = .Psi ζ κ γ := le_antisymmY hP.piF hρ hkρ hρk
        subst e
        have haγ : Le a γ := le_of_lt_succT hP.aF hγF haX
        rcases inC_psi_iff.mp hP.Cpi with h' | ⟨-, -, -, hγa⟩
        · exact Lt.irrefl _ h'
        · exact not_lt_of_leY hP.aF hγF haγ hγa
    | Xi j b =>
      exfalso
      have hKF := WNF.K' hx.xi.1
      have hρK := tgt_ge ht hKF htk (inC_K _ _ _)
      have e := le_antisymmY hKF hρ hkρ hρK
      cases e
    | _ => exact absurd htk (not_lt_zero _)
  · exact hsub
  · exact absurd hkκ (Lt.irrefl _)

/-- `Ξ` の底の下の段：目標が `t` と `K_m` の間の節点は部分項以下 -/
theorem floor_lowCx {m : Nat} {q : Tm} (ht : WNF (.Psi .zero (.Xi m q) (sc q))) (P : Option Tm) :
    LowC (.Psi .zero (.Xi m q) (sc q)) (.K m) P := by
  intro x hx hxt htk hkK
  refine Or.inr ?_
  have hρ := ht.psi.piF
  have hm := hρ.xi.1
  have hqF := hρ.xi.2.1
  have hc : Chain (.Xi m q) (.Xi m q) := .refl _
  cases x with
  | Psi s k a =>
    have hP := hx.psi
    by_cases hkρ : Lt (.Xi m q) k
    · have hl' : lev k = m := by
        have h1 := lev_le_of_lt_gen hxt
        have h2 := lev_le_of_lt_gen hkρ
        simp only [lev] at h1 h2 ⊢
        omega
      have hxρ : Lt (.Psi s k a) (.Xi m q) := lt_transY hx ht hρ hxt (lt_psi_targetY ht)
      obtain ⟨-, w, hw, hn⟩ := wit_psi_xi hx hρ hl' hxρ hkρ
      exact subLe_frπ ht (xi_fr_mem hρ hc hw) (le_of_not_ltY (hqF.of_mem_subs (fr_spec hw).1) hx hn)
    · rcases below_psi ht hx hxt with h | ⟨w, hw, hle⟩ | ⟨-, haX, -, -, hkC⟩
      · exact absurd h (Lt.asymmY ht hP.piF htk)
      · exact subLe_gap ht hw hle
      · exfalso
        have hρk := tgt_ge ht hP.piF htk hkC
        have e : k = .Xi m q := le_antisymmY hP.piF hρ (le_of_not_ltY hρ hP.piF hkρ) hρk
        subst e
        have haq : Le a q := le_of_lt_succT hP.aF hqF haX
        rcases inC_xi_iff.mp hP.Cpi with h' | ⟨-, hqa⟩
        · exact Lt.irrefl _ h'
        · exact not_lt_of_leY hP.aF hqF haq hqa
  | Xi j b =>
    exfalso
    have hj := hx.xi.1
    have hKF := WNF.K' hj
    by_cases hkρ : Lt (.Xi m q) (.K j)
    · have h3 := (lt_K_iffY hKF hm).mp hkK
      have h4 : Lt (.K j) (.Xi m q) := K_lt_xi hρ (by simp only [lev] at h3; exact h3)
      exact Lt.asymmY hKF hρ h4 hkρ
    · have hρK := tgt_ge ht hKF htk (inC_K _ _ _)
      have e := le_antisymmY hKF hρ (le_of_not_ltY hρ hKF hkρ) hρK
      cases e
  | _ => exact absurd htk (not_lt_zero _)

/-! ### `s0` の 0 番目は前線の元と異なる -/

theorem floor_nefirst {ζ κ γ : Tm} (ht : WNF (.Psi .zero (.Psi ζ κ γ) (sc γ)))
    (hIH : ∀ u, u ∈ subs (.Psi .zero (.Psi ζ κ γ) (sc γ)) → u ≠ .Psi .zero (.Psi ζ κ γ) (sc γ) →
      SeqI u (info u).seq)
    (hζ0 : ζ ≠ .zero) (hs : ¬ isSucc ζ = true) :
    ∀ p, p ∈ fr (.Psi ζ κ γ) (.Psi ζ κ γ) → (s0Of (.Psi ζ κ γ) κ γ ζ).first ≠ p := by
  have hρ := ht.psi.piF
  have hP := hρ.psi
  have hζF := hP.xiF
  have hc : Chain (.Psi ζ κ γ) (.Psi ζ κ γ) := .refl _
  have C := mctx_chain (X := sc γ) ht hc
  obtain ⟨-, hSμ, hμs⟩ := psi_parts hIH hc
  obtain ⟨pre, R, hsum, hR1, -, -, -, o0⟩ := s0_out C hSμ hμs hζ0 hs
  obtain ⟨P₀, x₀, hP₀, hz₀, hfF, hx₀F, hyR, hz₀μ, -, -, hx₀0, hx₀g⟩ := o0.form _ o0.mem
  have e0 : P₀ = .zero := by
    rcases hP₀ with h | h <;> exact h
  subst e0
  have hN : NFL (pre ++ R :: []) := hsum ▸ nfl_summands hζF
  have hζe : ζ = ofSummands (pre ++ R :: []) := by rw [← hsum, ofSummands_summands ζ hζF]
  have hI : ∀ s, Tm.Psi s κ γ ∈ subs ζ → Lt s ζ → Lt s (approx pre .zero x₀) := fun s hn hsζ => by
    obtain ⟨S, hSm, hnS⟩ := mem_subs_summand rfl hn
    rw [hsum] at hSm
    have hsne : s ≠ S := by
      refine ne_of_size_lt ?_
      have h3 := size_le_of_mem_subs hnS
      simp only [Tm.size] at h3
      omega
    exact lt_approx_summand hN hx₀F WNF.zero hyR hx₀0 hx₀g hSm
      (subs_trans hnS (subs_psi_s (self_mem_subs s))) hsne (by rw [← hζe]; exact hsζ)
  intro p hp e'
  rw [hz₀] at e'
  subst e'
  have hps := (fr_spec hp).1
  simp only [subs, List.mem_cons, List.mem_append] at hps
  rcases hps with e' | (h | h) | h
  · exact (fr_spec hp).2.ne e'
  · exact Lt.irrefl _ (hI _ h hz₀μ)
  · have h3 := size_le_of_mem_subs h
    simp only [Tm.size] at h3
    omega
  · have h3 := size_le_of_mem_subs h
    simp only [Tm.size] at h3
    omega

theorem floor_nefirstx {m : Nat} {q : Tm} (ht : WNF (.Psi .zero (.Xi m q) (sc q)))
    (hIH : ∀ u, u ∈ subs (.Psi .zero (.Xi m q) (sc q)) → u ≠ .Psi .zero (.Xi m q) (sc q) →
      SeqI u (info u).seq)
    (hs : ¬ isSucc q = true) :
    ∀ p, p ∈ fr (.Xi m q) (.Xi m q) → (s0X (.Xi m q) m q).first ≠ p := by
  have hρ := ht.psi.piF
  have hqF := hρ.xi.2.1
  have hq0 := hρ.xi.2.2.1
  have hc : Chain (.Xi m q) (.Xi m q) := .refl _
  obtain ⟨hS, hqs, hqσ⟩ := xi_parts ht hIH hc
  obtain ⟨pre, R, hsum, hR1, -, -, -, o0⟩ := s0x_out ht hc hS hqs hqσ hq0 hs
  obtain ⟨P₀, x₀, hP₀, hz₀, hfF, hx₀F, hx₀R, hz₀q, -, -, hx₀0, hx₀g⟩ := o0.form _ o0.mem
  have e0 : P₀ = .zero := by
    rcases hP₀ with h | h <;> exact h
  subst e0
  have hRm : R ∈ summands q := by
    rw [hsum]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hRp := nfl_principal (nfl_summands hqF) R hRm
  have hR0 : R ≠ .zero := by
    intro e'
    rw [e'] at hRp
    cases hRp
  have G : XiG m q .zero .one pre [] R :=
    ⟨hρ, hsum, WNF.zero, zero_lt hR0, zero_lt (by intro e'; cases e'), Or.inr rfl, hR1⟩
  have hA : ∀ {n a : Tm}, n ∈ subs q → isPrincipal n = true → a ∈ subs n → a.size < n.size → Lt a q →
      Lt a (xA .one pre .zero x₀) := fun hn hnp ha hsz hlt => by
    obtain ⟨S, hSm, hnS⟩ := mem_subs_summand hnp hn
    rw [hsum] at hSm
    exact G.lt_xA hx₀F hx₀R hx₀0 hx₀g hSm (subs_trans hnS ha)
      (ne_of_size_lt (Nat.lt_of_lt_of_le hsz (size_le_of_mem_subs hnS))) hlt
  have hc1x : ∀ m' b, Tm.Xi m' b ∈ subs q → Lt b q → Lt b (xA .one pre .zero x₀) := fun m' b hn hlt =>
    hA hn rfl (subs_xi (self_mem_subs b)) (by simp only [Tm.size]; omega) hlt
  intro p hp e'
  rw [hz₀] at e'
  subst e'
  have hps := (fr_spec hp).1
  simp only [subs, List.mem_cons] at hps
  rcases hps with e' | h
  · exact (fr_spec hp).2.ne e'
  · exact Lt.irrefl _ (hc1x _ _ h hz₀q)

/-! ### 底版の種の主張 -/

/-- `Ψ` の底の種の分岐：添字の残りの段の節点は種 `p` 未満 -/
theorem floor_hW {ζ κ γ p : Tm} (ht : WNF (.Psi .zero (.Psi ζ κ γ) (sc γ)))
    (hIH : ∀ u, u ∈ subs (.Psi .zero (.Psi ζ κ γ) (sc γ)) → u ≠ .Psi .zero (.Psi ζ κ γ) (sc γ) →
      SeqI u (info u).seq)
    (hζ0 : ζ ≠ .zero) (hs : ¬ isSucc ζ = true)
    (Sp : SeedP (.Psi ζ κ γ) (sc γ) p) (hpm : p ∈ fr (.Psi ζ κ γ) (.Psi ζ κ γ))
    (hmax : ∀ f, f ∈ fr (.Psi ζ κ γ) (.Psi ζ κ γ) → Le f p)
    (hlt : Lt (s0Of (.Psi ζ κ γ) κ γ ζ).first p) :
    ∀ L₁ L₂, summands ζ = L₁ ++ L₂ → (∀ u, u ∈ L₂ → Le u p) →
      ∀ z, WNF (.Psi z κ γ) → Lt (.Psi z κ γ) (.Psi .zero (.Psi ζ κ γ) (sc γ)) → Lt z ζ →
      ¬ Lt z (ofSummands L₁) →
      Le (.Psi z κ γ) p ∨ SubLe (.Psi .zero (.Psi ζ κ γ) (sc γ)) (.Psi z κ γ) := by
  intro L₁ L₂ hsum12 hL₂ z hx hxt hzζ hzL
  have hρ := ht.psi.piF
  have hP := hρ.psi
  have hκF := hP.piF
  have hγF := hP.aF
  have hζF := hP.xiF
  have hρκ : Lt (.Psi ζ κ γ) κ := lt_psi_targetY hρ
  have hc : Chain (.Psi ζ κ γ) (.Psi ζ κ γ) := .refl _
  have C := mctx_chain (X := sc γ) ht hc
  obtain ⟨-, hSμ, hμs⟩ := psi_parts hIH hc
  obtain ⟨pre, R, hsum, hR1, -, -, -, o0⟩ := s0_out C hSμ hμs hζ0 hs
  obtain ⟨P₀, x₀, hP₀, hz₀, hfF, hx₀F, hyR, -, -, -, hx₀0, hx₀g⟩ := o0.form _ o0.mem
  have e0 : P₀ = .zero := by
    rcases hP₀ with h | h <;> exact h
  subst e0
  rw [hz₀] at hlt hfF
  have hN : NFL (pre ++ R :: []) := hsum ▸ nfl_summands hζF
  have hζe : ζ = ofSummands (pre ++ R :: []) := by rw [← hsum, ofSummands_summands ζ hζF]
  have hRN := hN.1 R (List.mem_append_right _ List.mem_cons_self)
  have hRF := hRN.1
  have hpreN := nfl_append_left hN
  have hpreF := wnf_ofSummands hpreN
  have hz₀F := hfF.psi.xiF
  have hpκ : Lt p κ := lt_transY Sp.hF hρ hκF (fr_spec hpm).2 hρκ
  have hfrpre : ∀ w, w ∈ fr κ (ofSummands pre) → Lt w (.Psi (approx pre .zero x₀) κ γ) := fun w hw =>
    FWOrder.k2s hfF w (fr_oadd_of_left hpreF (wnf_nsum hx₀F WNF.zero) (fun s hd r' hs' e => by
      rw [summands_ofSummands _ (nfl_principal hpreN)] at hs'
      exact head_le_pre hN (wnf_nsum hx₀F WNF.zero) hyR s hd r' hs' e) hw)
  have hpR : p ∈ fr κ R := by
    rcases fr_cover hρ hpm with h | h | h
    · obtain ⟨s, hs', hp'⟩ := (mem_fr_iff hζF).mp h
      rw [hsum] at hs'
      rcases List.mem_append.mp hs' with h2 | h2
      · exfalso
        have h3 : p ∈ fr κ (ofSummands pre) := (mem_fr_iff hpreF).mpr
          ⟨s, by rw [summands_ofSummands _ (nfl_principal hpreN)]; exact h2, hp'⟩
        exact Lt.asymmY Sp.hF hfF (hfrpre p h3) hlt
      · rw [List.mem_singleton.mp h2] at hp'
        exact hp'
    · exact absurd (FWOrder.k2t hfF p h) (Lt.asymmY hfF Sp.hF hlt)
    · exact absurd (FWOrder.k2 hfF p h) (Lt.asymmY hfF Sp.hF hlt)
  have hpleR : Le p R := fr_leY hκF hRF hpR
  have hpp : p ∈ fr κ p := mem_fr_self (fr_node hpm) hpκ
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
    apply hzL
    rw [← hsum12, ofSummands_summands ζ hζF]
    exact hzζ
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
  rw [hL1] at hzL
  have hzF := hx.psi.xiF
  obtain ⟨L', hzs, hL'⟩ := lt_sum_split hN hzF (by rw [← hζe]; exact hzζ) hzL
  have hzN := nfl_summands hzF
  rw [hzs] at hzN
  have hL'N : NFL L' := nfl_append_right hzN
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
  have hS' : ∀ v, v ∈ subs p → v ≠ p → Lt v (.Psi ζ κ γ) → Lt v (.Psi (approx pre .zero x₀) κ γ) := by
    intro v hv hne hl
    have hx₀R : Lt x₀ R :=
      lt_of_le_of_ltY hx₀F (wnf_nsum hx₀F WNF.zero) hRF (le_nsum_left hx₀F WNF.zero) hyR
    have hx₀κ : Lt x₀ κ := lt_transY hx₀F hRF hκF hx₀R (by rw [hRe]; exact hpκ)
    have hzC := inC_of_fr_lt hz₀F hκF hfF hγF hγF hfF.psi.Cxi (Or.inr (lt_psi_targetY hfF)) (Or.inl rfl)
      fun w hw => FWOrder.k2s hfF w hw
    have hxC := (inC_approx_parts hN hx₀F WNF.zero hyR hzC).2.1
    have hxy := coll_psiY hfF x₀ hx₀F hxC hx₀κ
    have hG0 : ∀ u, u ∈ subs p → u ≠ p → Lt u p → Lt u (.Psi (approx pre .zero x₀) κ γ) :=
      fun u hu hne' hl' => by
        have hu' := hx₀g u (by rw [hRe]; exact hu) (by rw [hRe]; exact hne') (by rw [hRe]; exact hl')
        exact lt_transY (Sp.hF.of_mem_subs hu) hx₀F hfF hu' hxy
    have hvF := Sp.hF.of_mem_subs hv
    have hvκ : Lt v κ := lt_transY hvF hρ hκF hl hρκ
    have hsv := size_lt_of_mem_subs_ne hv hne
    have hsp := size_le_of_mem_subs (fr_spec hpm).1
    have hsz : v.size < (Tm.Psi ζ κ γ).size := by omega
    refine hull_lt hρ hfF (Or.inl rfl) hsz (fun n hn hnF hny f hf => ?_) (fun _ _ _ _ h' => h')
      (fun _ _ _ h' => h') (fun s hs hsζ hC => ?_) hvF hvκ (WFY.inC_of_ltY γ hvF hρ hl)
    · have hnp : n ∈ subs p := subs_trans hv hn
      have hnne : n ≠ p := ne_of_size_lt (Nat.lt_of_le_of_lt (size_le_of_mem_subs hn) hsv)
      have h1 : ¬ Lt n p := fun h' => hny (hG0 n hnp hnne h')
      have h2 : Lt p n := (le_of_not_ltY hnF Sp.hF h1).resolve_left (Ne.symm hnne)
      exact lt_of_le_of_ltY (hρ.of_mem_subs (fr_spec hf).1) Sp.hF hnF (hmax f hf) h2
    · have hs1 : s ∈ subs R := by
        rw [hRe]
        exact subs_trans hv (subs_trans hs (subs_psi_s (self_mem_subs s)))
      have hsne : s ≠ R := by
        rw [hRe]
        refine ne_of_size_lt ?_
        have h3 := size_le_of_mem_subs hs
        simp only [Tm.size] at h3
        omega
      have hmem : R ∈ pre ++ [R] := List.mem_append_right _ (List.mem_singleton.mpr rfl)
      exact lt_same_arg (hvF.of_mem_subs hs) hfF
        (lt_approx_summand hN hx₀F WNF.zero hyR hx₀0 hx₀g hmem hs1 hsne (by rw [← hζe]; exact hsζ)) hC
  have hxρ : Lt (.Psi z κ γ) (.Psi ζ κ γ) := lt_transY hx ht hρ hxt (lt_psi_targetY ht)
  have hsubp : ∀ w, w ∈ subs p → w ≠ p → Lt w p → Lt w (.Psi (approx pre .zero x₀) κ γ) :=
    fun w hw hne hwp => hS' w hw hne (lt_transY (Sp.hF.of_mem_subs hw) Sp.hF hρ hwp (fr_spec hpm).2)
  have hzC : ∀ g, inC (ofSummands pre) g p = true → inC z g p = true := fun g hpreC => by
    rw [inC_iff_summands hzF, hzs]
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact (inC_ofSummands pre).mp hpreC u hu
    · exact WFY.inC_of_ltY g (hL'N.1 u hu).1 Sp.hF (hL'p u hu)
  rcases fr_node hpm with ⟨m', φ, ep⟩ | ⟨s₁, π₁, φ, ep⟩
  · exfalso
    subst ep
    have hlev1 := lev_le_of_lt_gen hlt
    have hlev2 := lev_le_of_lt_gen hpκ
    simp only [lev] at hlev1 hlev2
    have hl : lev κ = m' := by omega
    obtain ⟨-, w, hw, hn⟩ := wit_psi_xi hfF Sp.hF hl hlt hpκ
    have hws : w ∈ subs (.Xi m' φ) := subs_xi (fr_spec hw).1
    have hwne : w ≠ .Xi m' φ := ne_of_size_lt (by
      have := size_le_of_mem_subs (fr_spec hw).1
      simp only [Tm.size]
      omega)
    exact hn (hsubp w hws hwne (FWOrder.k2x Sp.hF w hw))
  · subst ep
    have hQ := Sp.hF.psi
    have hφF := hQ.aF
    have hs₁F := hQ.xiF
    have hlev1 := lev_le_of_lt_gen hlt
    have hlev2 := lev_le_of_lt_gen hpκ
    simp only [lev] at hlev1 hlev2
    have hl : lev κ = lev π₁ := by omega
    rcases (lt_psi_psiY hl hlt.ne).mp hlt with h | ⟨-, hyπ₁, hcs⟩
    · exact absurd hpκ h
    have hπ₁s : π₁ ∈ subs (.Psi s₁ π₁ φ) := subs_psi_p (self_mem_subs π₁)
    have hπ₁ne : π₁ ≠ .Psi s₁ π₁ φ := ne_of_size_lt (by simp only [Tm.size]; omega)
    have hρπ₁ : Le (.Psi ζ κ γ) π₁ := le_of_not_ltY hQ.piF hρ fun h' =>
      Lt.asymmY hfF hQ.piF hyπ₁ (hS' π₁ hπ₁s hπ₁ne h')
    have hxπ₁ : Lt (.Psi z κ γ) π₁ := lt_of_lt_of_leY hx hρ hQ.piF hxρ hρπ₁
    rcases hcs with ⟨hγφ, hγC, hz₀C, hκC⟩ | ⟨hle, hn⟩ | ⟨heq, hκπ, hzs₁, hz₀C⟩ | ⟨hs₁z, hn⟩
    · -- c1：`x ∈ C(φ, p)`
      have hpreC := (inC_approx_parts hN hx₀F WNF.zero hyR hz₀C).1
      have hxC : inC (.Psi z κ γ) φ (.Psi s₁ π₁ φ) = true :=
        inC_psi_iff.mpr (Or.inr ⟨hκC, hzC φ hpreC, hγC, hγφ⟩)
      exact Or.inl (Or.inr (coll_psiY Sp.hF _ hx hxC hxπ₁))
    · -- c2：証人は `p` の真の部分項
      exfalso
      obtain ⟨w, hw, hn'⟩ := wit_c2 Sp.hF hfF hγF (le_of_ne_gtY hφF hγF hle) hyπ₁ hn
      have hws : w ∈ subs (.Psi s₁ π₁ φ) ∧ Lt w (.Psi s₁ π₁ φ) := by
        rcases hw with hw | hw | hw
        · exact ⟨subs_psi_a (fr_spec hw).1, FWOrder.k2 Sp.hF w hw⟩
        · exact ⟨subs_psi_p (fr_spec hw).1, FWOrder.k2t Sp.hF w hw⟩
        · exact ⟨subs_psi_s (fr_spec hw).1, FWOrder.k2s Sp.hF w hw⟩
      exact hn' (hsubp w hws.1 hws.2.ne hws.2)
    · -- c3：同じ引数・同じ目標
      have e1 : φ = γ := (FWOrder.eq hγF hφF heq).symm
      by_cases hs₁ζ : Lt s₁ ζ
      · exfalso
        have hAF := wnf_oadd hpreF hx₀F
        have hzs' : Lt (oadd (ofSummands pre) x₀) s₁ := by
          rw [← approx_zero_eq hx₀F]
          exact hzs₁
        have hs₁lt : Lt s₁ (oadd (ofSummands pre) R) := by
          rw [← eq_oadd_of_sum hζF hsum]
          exact hs₁ζ
        rcases lt_oadd_cases hN hs₁F hs₁lt with h' | ⟨φ', hφ'F, hφ'R, hsφ, e⟩
        · exact Lt.asymmY hs₁F hAF (lt_of_lt_of_leY hs₁F hpreF hAF h' (le_oadd_left hpreF hx₀F)) hzs'
        · have hx₀φ' : Lt x₀ φ' := by
            refine (le_of_not_ltY hφ'F hx₀F fun h'' => ?_).resolve_left fun e' => ?_
            · rw [e] at hzs'
              exact Lt.asymmY hAF (wnf_oadd hpreF hφ'F) hzs' (oadd_lt_oadd hpreF hφ'F hx₀F h'')
            · rw [e, ← e'] at hzs'
              exact Lt.irrefl _ hzs'
          have hφ'0 : φ' ≠ .zero := fun e' => by
            rw [e'] at hx₀φ'
            exact not_lt_zero _ hx₀φ'
          have hφ's : φ' ∈ subs s₁ := by
            have := tail_mem_subs hs₁F hsφ (summands_ne_nil hφ'0)
            rwa [ofSummands_summands φ' hφ'F] at this
          have hφ'ne : φ' ≠ R := by
            rw [hRe]
            exact ne_of_size_lt (by
              have := size_le_of_mem_subs hφ's
              simp only [Tm.size]
              omega)
          exact Lt.asymmY hx₀F hφ'F hx₀φ' (hx₀g φ' (by rw [hRe]; exact subs_psi_s hφ's) hφ'ne hφ'R)
      · have hzs₁' : Lt z s₁ := lt_of_lt_of_leY hzF hζF hs₁F hzζ (le_of_not_ltY hs₁F hζF hs₁ζ)
        have hpreC := (inC_approx_parts hN hx₀F WNF.zero hyR hz₀C).1
        have hy' : WNF (.Psi s₁ κ γ) := by
          rw [← hκπ, ← e1]
          exact Sp.hF
        have hpe : Tm.Psi s₁ π₁ φ = .Psi s₁ κ γ := by rw [hκπ, e1]
        have hzC' : inC z γ (.Psi s₁ κ γ) = true := by
          rw [← hpe, ← e1]
          exact hzC φ hpreC
        rw [hpe]
        exact Or.inl (Or.inr (lt_same_arg hx hy' hzs₁' hzC'))
    · -- c4：証人は `p` の添字の前線の元
      exfalso
      obtain ⟨w, hw, hn'⟩ := wit_c4 Sp.hF hfF hz₀F hlt hs₁z hn
      have hws : w ∈ subs (.Psi s₁ π₁ φ) := subs_psi_s (fr_spec hw).1
      have hwne : w ≠ .Psi s₁ π₁ φ := ne_of_size_lt (by
        have := size_le_of_mem_subs (fr_spec hw).1
        simp only [Tm.size]
        omega)
      exact hn' (hsubp w hws hwne (fr_spec hw).2)

end RTKA.Fund
