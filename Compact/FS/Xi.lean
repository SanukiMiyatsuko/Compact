import Compact.FS.Spec

/-! `Ξ_m(x)` の族の閉包：`t = Ψ^0_π(X)`、鎖の上に `Ξ_m(q)` があるとき、列の項は `Ξ_m(pre ⊕ (c # (P # x)))`（`c` は `0` か `1`）。
`mahloVK` の仕様（`vk_spec`）。 -/

namespace RTKA.Fund

open Tm W


/-- `Ξ_m` の族の列の出力 -/
structure XiOut (π X : Tm) (m : Nat) (q P c : Tm) (pre : List Tm) (R : Tm) (s : SeqD) : Prop where
  mem : InSeq s s.first
  form : ∀ y, InSeq s y → ∃ P' x, (P' = P ∨ P' = .zero) ∧ y = .Xi m (xA c pre P' x) ∧ WNF y ∧ WNF x ∧
    Lt x R ∧ Lt (xA c pre P' x) q ∧ Le s.first y ∧ (P ≠ .zero → Lt P y) ∧
    (x = .zero → ∀ v, v ∈ subs R → v = R) ∧ ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v x
  ltπ : Lt s.first π
  ubF : ∀ g d, WNF g → WNF d → Lt .zero g → (∀ v, v ∈ subs q → Lt v π → inC v g d = true → Lt v d) →
    inC q g d = true → Lt q g → inC P g d = true → inC s.first g d = true
  inv : (∀ y, InSeq s y → Gp (.Psi .zero π X) y) → SeqI (.Psi .zero π X) s

/-- 鎖の上の `Ξ_m(q)` の成分 -/
theorem xi_comp {π X q g d : Tm} {n : Nat} (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Xi n q))
    (h : Ad π X g d) : inC q g d = true ∧ Lt q g := by
  obtain ⟨h1, h2⟩ := h.tgt ht hc
  rcases inC_xi_iff.mp h1 with h' | h'
  · exact absurd h' h2
  · exact h'

/-- `Ξ_m` の族の `ω` 型の列 -/
theorem xi_nat_out {π X q P c : Tm} {m : Nat} {pre rest : List Tm} {R : Tm} {x : Nat → Tm} {s : SeqD}
    (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Xi m q)) (G : XiG m q P c pre rest R)
    (hc0 : c = .zero → P ≠ .zero)
    (I : Inner P .zero pre R x) (he : ∀ n, s.nat n = .Xi m (xA c pre P (x n))) (hdt : s.dom = .omega)
    (hPπ : Lt P π) (hPA : ∀ g d, Ad π X g d → inC P g d = true)
    (hPfr : P ≠ .zero → P ∈ fr (.K m) P) : XiOut π X m q P c pre R s := by
  have hπF := ht.psi.piF
  have hx := I.hx
  have hρ := G.ht
  have hKF := G.hKF
  have hπρ : Le π (.Xi m q) := hc.le hπF
  have hA0 : ∀ n, approx pre P (oadd .zero (x n)) = approx pre P (x n) := fun n => by
    rw [zero_oadd (hx n)]
  have hPK' : ∀ {g : Tm}, inC P g (.K m) = true := WFY.inC_of_ltY _ G.hPF hKF G.hPK
  have hPρ : inC P q (.Xi m q) = true :=
    WFY.inC_of_ltY _ G.hPF hρ (lt_of_lt_of_leY G.hPF hπF hρ hPπ hπρ)
  have hA0F : ∀ n, WNF (approx pre P (x n)) := fun n => wnf_oadd G.hpreF (wnf_nsum (hx n) G.hPF)
  have hCK : ∀ n, inC (x n) (xA c pre P (x n)) (.K m) = true := fun n =>
    G.hCx (hx n) (I.hxR n) (I.zero n) (I.gap n) fun hR hp =>
      I.ub _ _ n (hA0F n) hKF hR hp (inC_zero _ _) hPK' (Or.inr (by rw [hA0]))
  have hnf : ∀ n, WNF (.Xi m (xA c pre P (x n))) := fun n =>
    G.nf (G.hA_ne hc0 (hx n)) (hx n) (I.hxR n) (hCK n)
  have hA0lt : ∀ n, Lt (approx pre P (x n)) (xA c pre P (x (n + 1))) := fun n =>
    lt_of_le_of_ltY (hA0F n) (G.hAF (hx n)) (G.hAF (hx (n + 1))) (G.hA0le (hx n))
      (G.hAmono (hx n) (hx (n + 1)) (I.mono n))
  have hm : ∀ n, Lt (.Xi m (xA c pre P (x n))) (.Xi m (xA c pre P (x (n + 1)))) := fun n =>
    G.lt2 (hx n) (hx (n + 1)) (I.hxR (n + 1)) (I.mono n) (hnf (n + 1)) fun h hp hP =>
      I.ub2 _ _ n (G.hAF (hx (n + 1))) (hnf (n + 1)) h hp (inC_zero _ _) hP (by rw [hA0]; exact hA0lt n)
  have hρlt : ∀ n, Lt (.Xi m (xA c pre P (x n))) (.Xi m q) := fun n =>
    G.ltρ (hx n) (I.hxR n) (I.ub q _ n G.hqF hρ (G.qparts G.hqρ).1 (G.qparts G.hqρ).2 (inC_zero _ _) hPρ
      (Or.inl G.hTq)) hPρ
  have L : NatL (.Xi m q) s := by
    refine ⟨fun n => ?_, fun n => ?_, fun g d n hg hd h => ?_⟩
    · rw [he n, he (n + 1)]
      exact ⟨hnf n, hρlt n, hm n⟩
    · rw [he n]
      intro e
      cases e
    · rw [he (n + 1)] at h
      rw [he n]
      exact G.ub2 (hx n) (hx (n + 1)) (I.hxR (n + 1)) (I.mono n) (hnf n) (hnf (n + 1)) (hm n) hd hg
        (fun h' hp hP hlt => I.ub2 g d n hg hd h' hp (inC_zero _ _) hP (by rw [hA0]; exact hlt)) h
  have hz : ∀ g d n, WNF g → WNF d → inC q g d = true → Le q g → inC P g d = true →
      inC (xA c pre P (x n)) g d = true := fun g d n hg hd hqC hqg hP =>
    G.inC_A (hx n) (G.qparts hqC).2 (I.ub g d n hg hd (G.qparts hqC).1 (G.qparts hqC).2 (inC_zero _ _) hP
      (Or.inl (le_transY G.hTF G.hqF hg G.hTq hqg))) hP
  have hyC : ∀ g d n, WNF g → WNF d → inC q g d = true → Lt q g → inC P g d = true →
      inC (.Xi m (xA c pre P (x n))) g d = true := fun g d n hg hd h1 h2 hP =>
    inC_xi_iff.mpr (Or.inr ⟨hz g d n hg hd h1 (Or.inr h2) hP,
      lt_transY (G.hAF (hx n)) G.hqF hg (G.hAlt (hx n) (I.hxR n) G.hqF G.hTq) h2⟩)
  have hlt : ∀ n, Lt (s.nat n) π := fun n => by
    rw [he n]
    refine hc.lt_base hπF (hnf n) (hρlt n) fun g d hg hd hle hn hC => ?_
    rcases inC_xi_iff.mp hC with h' | ⟨h1, h2⟩
    · exact absurd h' hn
    · exact hyC g d n hg hd h1 h2 (WFY.inC_of_ltY _ G.hPF hd (lt_of_lt_of_leY G.hPF hπF hd hPπ hle))
  refine ⟨Or.inl ⟨hdt, 0, first_of_nat hdt⟩, ?_, by rw [first_of_nat hdt]; exact hlt 0,
    fun g d hg hd _ _ h1 h2 hP => ?_, fun hG => ?_⟩
  · rintro y (⟨-, n, rfl⟩ | ⟨σ, η, hd, -⟩)
    · refine ⟨P, x n, Or.inl rfl, he n, (L.good n).1, hx n, I.hxR n, G.hAlt (hx n) (I.hxR n) G.hqF G.hTq, ?_,
        fun h0 => ?_, I.zero n, I.gap n⟩
      · rw [first_of_nat hdt]
        exact le_of_mono (y := s.nat) (fun k => (L.good k).1) (fun k => (L.good k).2.2) n
      · rw [he n]
        exact G.seed_lt (hx n) (hnf n) (hPfr h0)
    · rw [hdt] at hd
      cases hd
  · rw [first_of_nat hdt, he 0]
    exact hyC g d 0 hg hd h1 h2 hP
  · refine seqI_nat hdt (natInv_lift ht L hlt (fun g d n h => ?_) fun n => hG _ (Or.inl ⟨hdt, n, rfl⟩))
    obtain ⟨h1, h2⟩ := xi_comp ht hc h
    rw [he n]
    exact hyC g d n h.1 h.2.1 h1 h2 (hPA g d h)

/-- `Ξ_m` の族の、共終数が `ceil` 未満の列 -/
theorem xi_big_out {π X q P c σ : Tm} {m : Nat} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Xi m q)) (G : XiG m q P c pre rest R)
    (hc0 : c = .zero → P ≠ .zero)
    (hB : BigInv R σ r) (hreg : RegTerm σ) (hd : r.dom = .big σ) (hσπ : Lt σ π)
    (hRs : R ∈ subs (.Psi .zero π X))
    (hPπ : Lt P π) (hPA : ∀ g d, Ad π X g d → inC P g d = true)
    (hPfr : P ≠ .zero → P ∈ fr (.K m) P) : XiOut π X m q P c pre R (.app π (.xi m) pre R r P c) := by
  have hπF := ht.psi.piF
  have hρ := G.ht
  have hKF := G.hKF
  have hπρ : Le π (.Xi m q) := hc.le hπF
  have hU := hB.1
  have hσF := hU.hσF
  have hσ0 : Lt .zero σ := zero_lt hreg.ne_zero
  have hσρ : Lt σ (.Xi m q) := lt_of_lt_of_leY hσF hπF hρ hσπ hπρ
  have hσK : Lt σ (.K m) := lt_transY hσF hρ hKF hσρ G.hρK
  have hd' := app_dom_big_lt (P := P) (c := c) (g := .xi m) (pre := pre) (R := R) hd (ltB_iff.mpr hσπ)
  have hxF : ∀ η, WNF η → Lt η σ → WNF (r.big η) := fun η hη hησ => (hU.good.1 η hη hησ).1
  have hxR : ∀ η, WNF η → Lt η σ → Lt (r.big η) R := fun η hη hησ => (hU.good.1 η hη hησ).2
  have he : ∀ η, (SeqD.app π (.xi m) pre R r P c).big η = .Xi m (xA c pre P (r.big η)) := fun _ => rfl
  have hPK' : ∀ {g : Tm}, inC P g (.K m) = true := WFY.inC_of_ltY _ G.hPF hKF G.hPK
  have hPρ : inC P q (.Xi m q) = true :=
    WFY.inC_of_ltY _ G.hPF hρ (lt_of_lt_of_leY G.hPF hπF hρ hPπ hπρ)
  have hCK : ∀ η, WNF η → Lt η σ → inC (r.big η) (xA c pre P (r.big η)) (.K m) = true := fun η hη hησ =>
    G.hCx (hxF η hη hησ) (hxR η hη hησ) (hU.pos η hη hησ) (hB.2 η hη hησ) fun hR _ => by
      by_cases h0 : r.big η = .zero
      · rw [h0]
        exact inC_zero _ _
      · exact hU.ub _ _ η (wnf_oadd G.hpreF (wnf_nsum (hxF η hη hησ) G.hPF)) hKF hη hησ
          (approx_pos G.hpreF (hxF η hη hησ) G.hPF h0) (Or.inl (Or.inr hσK)) hR
          (WFY.inC_of_ltY _ hη hKF (lt_transY hη hσF hKF hησ hσK))
  have hnf : ∀ η, WNF η → Lt η σ → WNF (.Xi m (xA c pre P (r.big η))) := fun η hη hησ =>
    G.nf (G.hA_ne hc0 (hxF η hη hησ)) (hxF η hη hησ) (hxR η hη hησ) (hCK η hη hησ)
  have hρlt : ∀ η, WNF η → Lt η σ → Lt (.Xi m (xA c pre P (r.big η))) (.Xi m q) := fun η hη hησ =>
    G.ltρ (hxF η hη hησ) (hxR η hη hησ)
      (hU.ub q _ η G.hqF hρ hη hησ (lt_of_lt_of_leY WNF.zero G.hRF G.hqF (zero_lt G.hR0) (by
        have := le_ofSummands_of_mem (nfl_summands G.hqF) G.hRm
        rwa [ofSummands_summands q G.hqF] at this)) (Or.inl (Or.inr hσρ)) (G.qparts G.hqρ).1
        (WFY.inC_of_ltY _ hη hρ (lt_transY hη hσF hρ hησ hσρ))) hPρ
  have hA0lt : ∀ {η₁ η₂ : Tm}, WNF η₁ → WNF η₂ → Lt η₁ η₂ → Lt η₂ σ →
      Lt (approx pre P (r.big η₁)) (xA c pre P (r.big η₂)) := fun {η₁ η₂} h₁ h₂ hlt hησ => by
    have h₁σ := lt_transY h₁ h₂ hσF hlt hησ
    exact lt_of_le_of_ltY (wnf_oadd G.hpreF (wnf_nsum (hxF η₁ h₁ h₁σ) G.hPF)) (G.hAF (hxF η₁ h₁ h₁σ))
      (G.hAF (hxF η₂ h₂ hησ)) (G.hA0le (hxF η₁ h₁ h₁σ))
      (G.hAmono (hxF η₁ h₁ h₁σ) (hxF η₂ h₂ hησ) (hU.good.2 η₁ η₂ h₁ h₂ hlt hησ))
  have hR0pos : Lt .zero q := lt_of_lt_of_leY WNF.zero G.hRF G.hqF (zero_lt G.hR0) (by
    have := le_ofSummands_of_mem (nfl_summands G.hqF) G.hRm
    rwa [ofSummands_summands q G.hqF] at this)
  have hm0' : ∀ η, WNF η → Lt .zero η → Lt η σ →
      Lt (.Xi m (xA c pre P (r.big .zero))) (.Xi m (xA c pre P (r.big η))) := fun η hη h0 hησ =>
    G.lt2 (hxF _ WNF.zero hσ0) (hxF η hη hησ) (hxR η hη hησ) (hU.good.2 _ η WNF.zero hη h0 hησ)
      (hnf η hη hησ) fun h _ _ =>
        hU.ub2 _ _ .zero η (G.hAF (hxF η hη hησ)) (hnf η hη hησ) WNF.zero hη h0 hησ h (inC_zero _ _)
  have hfirst : (SeqD.app π (.xi m) pre R r P c).first = .Xi m (xA c pre P (r.big .zero)) := by
    unfold SeqD.first
    rw [hd']
    rfl
  have hz : ∀ g d η, WNF g → WNF d → WNF η → Lt η σ → Lt .zero g → BigOK σ g d → inC q g d = true →
      inC P g d = true → inC η g d = true → inC (xA c pre P (r.big η)) g d = true :=
    fun g d η hg hd hη hησ h0 hok hqC hP hηC =>
      G.inC_A (hxF η hη hησ) (G.qparts hqC).2 (hU.ub g d η hg hd hη hησ h0 hok (G.qparts hqC).1 hηC) hP
  have hyC : ∀ g d η, WNF g → WNF d → WNF η → Lt η σ → Lt .zero g → BigOK σ g d → inC q g d = true →
      Lt q g → inC P g d = true → inC η g d = true → inC (.Xi m (xA c pre P (r.big η))) g d = true :=
    fun g d η hg hd hη hησ h0 hok hqC hqg hP hηC =>
      inC_xi_iff.mpr (Or.inr ⟨hz g d η hg hd hη hησ h0 hok hqC hP hηC,
        lt_transY (G.hAF (hxF η hη hησ)) G.hqF hg (G.hAlt (hxF η hη hησ) (hxR η hη hησ) G.hqF G.hTq) hqg⟩)
  have hlt : ∀ η, WNF η → Lt η σ → Lt (.Xi m (xA c pre P (r.big η))) π := fun η hη hησ => by
    refine hc.lt_base hπF (hnf η hη hησ) (hρlt η hη hησ) fun g d hg hd hle hn hC => ?_
    rcases inC_xi_iff.mp hC with h' | ⟨h1, h2⟩
    · exact absurd h' hn
    · have hσd := lt_of_lt_of_leY hσF hπF hd hσπ hle
      exact hyC g d η hg hd hη hησ (lt_transY WNF.zero G.hqF hg hR0pos h2) (Or.inl (Or.inr hσd)) h1 h2
        (WFY.inC_of_ltY _ G.hPF hd (lt_of_lt_of_leY G.hPF hπF hd hPπ hle))
        (WFY.inC_of_ltY _ hη hd (lt_transY hη hσF hd hησ hσd))
  refine ⟨Or.inr ⟨σ, .zero, hd', WNF.zero, hσ0, first_of_big hd'⟩, ?_,
    by rw [hfirst]; exact hlt _ WNF.zero hσ0, fun g d hg hd2 h0 hsub h1 h2 hP => ?_, fun hG => ?_⟩
  · rintro y (⟨hdt, -⟩ | ⟨σ', η, hd2, hη, hησ, rfl⟩)
    · rw [hd'] at hdt
      cases hdt
    · rw [hd'] at hd2
      cases hd2
      refine ⟨P, r.big η, Or.inl rfl, rfl, hnf η hη hησ, hxF η hη hησ, hxR η hη hησ,
        G.hAlt (hxF η hη hησ) (hxR η hη hησ) G.hqF G.hTq, ?_, fun h0 => ?_, hU.pos η hη hησ, hB.2 η hη hησ⟩
      · rw [hfirst]
        by_cases h0 : η = .zero
        · rw [h0]
          exact Or.inl rfl
        · exact Or.inr (hm0' η hη (zero_lt h0) hησ)
      · exact G.seed_lt (hxF η hη hησ) (hnf η hη hησ) (hPfr h0)
  · rw [hfirst]
    have hσq : σ ∈ subs q := subs_trans (mem_subs_of_mem_summands G.hRm) hU.hσs
    exact hyC g d .zero hg hd2 WNF.zero hσ0 h0
      (Or.inl (Or.inr (hsub σ hσq hσπ (hU.hσC g d hg hd2 (G.qparts h1).1)))) h1 h2 hP (inC_zero _ _)
  · have hRt : inC R X (.Psi .zero π X) = true := (G.qparts (xi_comp ht hc (Ad.self ht)).1).1
    have hσt : Lt σ (.Psi .zero π X) := coll_psiY ht σ hσF (hU.hσC X _ ht.psi.aF ht hRt) hσπ
    have hσs : σ ∈ subs (.Psi .zero π X) := subs_trans hRs hU.hσs
    have hσy : ∀ η, WNF η → Lt η σ → Lt σ (.Xi m (xA c pre P (r.big η))) := fun η hη hησ =>
      hG _ (Or.inr ⟨σ, η, hd', hη, hησ, rfl⟩) σ hσs hσt.ne hσt
    have hmono : ∀ η₁ η₂, WNF η₁ → WNF η₂ → Lt η₁ η₂ → Lt η₂ σ →
        Lt (.Xi m (xA c pre P (r.big η₁))) (.Xi m (xA c pre P (r.big η₂))) := by
      intro η₁ η₂ h₁ h₂ hlt' hησ
      have h₁σ := lt_transY h₁ h₂ hσF hlt' hησ
      exact G.lt2 (hxF η₁ h₁ h₁σ) (hxF η₂ h₂ hησ) (hxR η₂ h₂ hησ) (hU.good.2 η₁ η₂ h₁ h₂ hlt' hησ)
        (hnf η₂ h₂ hησ) fun h _ _ =>
          hU.ub2 _ _ η₁ η₂ (G.hAF (hxF η₂ h₂ hησ)) (hnf η₂ h₂ hησ) h₁ h₂ hlt' hησ h
            (WFY.inC_of_ltY _ h₁ (hnf η₂ h₂ hησ) (lt_transY h₁ hσF (hnf η₂ h₂ hησ) h₁σ (hσy η₂ h₂ hησ)))
    have hX0 : Lt .zero X :=
      lt_transY WNF.zero G.hqF ht.psi.aF hR0pos (xi_comp ht hc (Ad.self ht)).2
    refine seqI_big hd' hreg (bigInv_lift ht hX0 hσF hσt hσs (fun g d h => ?_) hnf hlt
      (fun g d η h hη hησ h0 hok hηC => ?_) hmono (fun η hη hησ e => ?_)
      (fun g d η₁ η₂ hg hd2 h₁ h₂ hlt' hησ h hηC => ?_) (fun g d η hd2 hη hησ h => ?_)
      (fun η hη hησ _ => ?_) (fun m' e _ η hη hησ => ?_) (fun m' e _ η hη hησ => ?_)
      (fun η hη hησ => hG _ (Or.inr ⟨σ, η, hd', hη, hησ, rfl⟩)))
    · exact hU.hσC g d h.1 h.2.1 (G.qparts (xi_comp ht hc h).1).1
    · obtain ⟨h1, h2⟩ := xi_comp ht hc h
      exact hyC g d η h.1 h.2.1 hη hησ h0 hok h1 h2 (hPA g d h) hηC
    · cases e
    · have h₁σ := lt_transY h₁ h₂ hσF hlt' hησ
      exact G.ub2 (hxF η₁ h₁ h₁σ) (hxF η₂ h₂ hησ) (hxR η₂ h₂ hησ) (hU.good.2 η₁ η₂ h₁ h₂ hlt' hησ)
        (hnf η₁ h₁ h₁σ) (hnf η₂ h₂ hησ) (hmono η₁ η₂ h₁ h₂ hlt' hησ) hd2 hg
        (fun h' _ _ _ => hU.ub2 g d η₁ η₂ hg hd2 h₁ h₂ hlt' hησ h' hηC) h
    · have hy := hnf η hη hησ
      rcases inC_xi_iff.mp h with h' | ⟨hz', -⟩
      · exact WFY.inC_of_ltY _ hη hd2 (lt_transY hη hσF hd2 hησ (lt_transY hσF hy hd2 (hσy η hη hησ) h'))
      · exact hU.lo g d η hd2 hη hησ (G.parts (hxF η hη hησ) (hxR η hη hησ) hz').2.1
    · show ¬ isSucc (.Xi m (xA c pre P (r.big η))) = true
      rw [isSucc_principal rfl]
      simp
    · have h1 : lev (.K m') ≤ lev π := lev_le_of_lt_gen (e ▸ hσπ)
      have h2 : lev π = m := hc.lev_eq
      have h3 : lev (.K m') = m' + 1 := rfl
      have h4 : lev (.Xi m (xA c pre P (r.big η))) = m := rfl
      exact Or.inr (K_lt_of_lev (y := .Xi m (xA c pre P (r.big η))) (hnf η hη hησ) rfl rfl (by omega))
    · have h1 : lev (.K m') ≤ lev π := lev_le_of_lt_gen (e ▸ hσπ)
      have h2 : lev π = m := hc.lev_eq
      have h3 : lev (.K m') = m' + 1 := rfl
      have h4 : lev (.Xi m (xA c pre P (r.big η))) = m := rfl
      have hm' : 1 ≤ m' := (e ▸ hσF : WNF (.K m')).k
      exact Or.inr (succK_lt_of_OF (y := .Xi m (xA c pre P (r.big η))) hm' (Or.inl ⟨m, _, rfl⟩)
        (hnf η hη hησ) (K_lt_of_lev (hnf η hη hησ) rfl rfl (by omega)))

/-- 節点 -/
def NodeT (x : Tm) : Prop := (∃ m a, x = .Xi m a) ∨ ∃ s q a, x = .Psi s q a

theorem NodeT.not_inC {x : Tm} (h : NodeT x) : inC x .zero .zero = false := by
  cases hC : inC x .zero .zero with
  | false => rfl
  | true =>
    exfalso
    rcases h with ⟨m, a, rfl⟩ | ⟨s, q, a, rfl⟩
    · rcases inC_xi_iff.mp hC with h' | ⟨-, h'⟩
      · exact not_lt_zero _ h'
      · exact not_lt_zero _ h'
    · rcases inC_psi_iff.mp hC with h' | ⟨-, -, -, h'⟩
      · exact not_lt_zero _ h'
      · exact not_lt_zero _ h'

/-- 節点の添字の項は `0` でない -/
theorem big_ne_of_node {R σ γ : Tm} {r : SeqD} (hU : BigUB R σ r) (hγ : WNF γ) (hγσ : Lt γ σ)
    (hn : NodeT γ) : r.big γ ≠ .zero := by
  intro e
  have h1 : inC (r.big γ) .zero .zero = true := by
    rw [e]
    exact inC_zero _ _
  have h2 := hU.lo _ _ _ WNF.zero hγ hγσ h1
  rw [hn.not_inC] at h2
  cases h2

/-- 値の帰還の塔 -/
def xiT (m : Nat) (c : Tm) (pre : List Tm) (r : SeqD) (P : Tm) : Nat → Tm
  | 0 => P
  | k + 1 => .Xi m (xA c pre .zero (r.big (xiT m c pre r P k)))
/-- `K_m` の対角化（`Ξ_m` の族）の値の帰還の塔：塔の各段は標準形で `Ξ_m(q)` 未満、列の項は塔の段 -/
theorem xi_K_data {π X q P c : Tm} {m : Nat} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Xi m q)) (G : XiG m q .zero c pre rest R)
    (hc0 : c = .zero → P ≠ .zero) (hd : r.dom = .big (.K m)) (hlt : ltB (.K m) π = false)
    (hB : BigInv R (.K m) r) (hPF : WNF P) (hPπ : Lt P π) (hPn : P = .zero ∨ NodeT P) :
    (∀ k, WNF (xiT m c pre r P k) ∧ Lt (xiT m c pre r P k) (.Xi m q) ∧
      (c = .zero → xiT m c pre r P k ≠ .zero) ∧ (xiT m c pre r P k = .zero ∨ NodeT (xiT m c pre r P k))) ∧
    ∀ n, (SeqD.app π (.xi m) pre R r P c).nat n = xiT m c pre r P (n + 1) := by
  have hπF := ht.psi.piF
  have hρ := G.ht
  have hKF := G.hKF
  have hm := G.hm
  have hρK := G.hρK
  have hU := hB.1
  have hπρ : Le π (.Xi m q) := hc.le hπF
  have hP0 : Lt P (.Xi m q) := lt_of_lt_of_leY hPF hπF hρ hPπ hπρ
  have hq0 : Lt .zero q := lt_of_lt_of_leY WNF.zero G.hRF G.hqF (zero_lt G.hR0) (by
    have := le_ofSummands_of_mem (nfl_summands G.hqF) G.hRm
    rwa [ofSummands_summands q G.hqF] at this)
  -- 1 段
  have hstep : ∀ {γ : Tm}, WNF γ → Lt γ (.Xi m q) → (c = .zero → γ ≠ .zero) → (γ = .zero ∨ NodeT γ) →
      WNF (.Xi m (xA c pre .zero (r.big γ))) := by
    intro γ hγ hγρ h1 h2
    have hγK := lt_transY hγ hρ hKF hγρ hρK
    have hx := (hU.good.1 γ hγ hγK).1
    have hxR := (hU.good.1 γ hγ hγK).2
    have hne : xA c pre .zero (r.big γ) ≠ .zero := by
      rcases G.hc with rfl | rfl
      · have hx0 : r.big γ ≠ .zero := by
          rcases h2 with e | hn
          · exact absurd e (h1 rfl)
          · exact big_ne_of_node hU hγ hγK hn
        intro e
        have h3 := G.hxA hx
        rw [e] at h3
        rcases h3 with h3 | h3
        · exact hx0 h3
        · exact not_lt_zero _ h3
      · intro e
        have h3 : Le (nsum .one (nsum .zero (r.big γ))) (xA .one pre .zero (r.big γ)) :=
          le_oadd_right G.hpreF (G.hEF hx)
        have h4 := le_nsum_left WNF.one (G.hyF hx)
        rw [e] at h3
        have h5 : nsum .one (nsum .zero (r.big γ)) = .zero := by
          rcases h3 with h3 | h3
          · exact h3
          · exact absurd h3 (not_lt_zero _)
        rw [h5] at h4
        rcases h4 with h4 | h4
        · cases h4
        · exact not_lt_zero _ h4
    refine G.nf hne hx hxR (G.hCx hx hxR (hU.pos γ hγ hγK) (hB.2 γ hγ hγK) fun hR _ => ?_)
    by_cases hx0 : r.big γ = .zero
    · rw [hx0]
      exact inC_zero _ _
    · exact hU.ub _ _ γ (wnf_oadd G.hpreF (wnf_nsum hx WNF.zero)) hKF hγ hγK
        (approx_pos G.hpreF hx WNF.zero hx0) (bigOK_none rfl) hR (WFY.inC_of_ltY _ hγ hKF hγK)
  have htow : ∀ k, WNF (xiT m c pre r P k) ∧ Lt (xiT m c pre r P k) (.Xi m q) ∧
      (c = .zero → xiT m c pre r P k ≠ .zero) ∧ (xiT m c pre r P k = .zero ∨ NodeT (xiT m c pre r P k)) := by
    intro k
    induction k with
    | zero => exact ⟨hPF, hP0, hc0, hPn⟩
    | succ k ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      have hy := hstep h1 h2 h3 h4
      have hγK := lt_transY h1 hρ hKF h2 hρK
      have hx := (hU.good.1 _ h1 hγK).1
      have hxR := (hU.good.1 _ h1 hγK).2
      refine ⟨hy, G.ltρ hx hxR (hU.ub q _ _ G.hqF hρ h1 hγK hq0 (bigOK_none rfl) (G.qparts G.hqρ).1
        (WFY.inC_of_ltY _ h1 hρ h2)) (inC_zero _ _), fun _ e => ?_, Or.inr (Or.inl ⟨m, _, rfl⟩)⟩
      cases e
  have hγK : ∀ k, Lt (xiT m c pre r P k) (.K m) := fun k =>
    lt_transY (htow k).1 hρ hKF (htow k).2.1 hρK
  have hxF : ∀ k, WNF (r.big (xiT m c pre r P k)) := fun k => (hU.good.1 _ (htow k).1 (hγK k)).1
  have hxR : ∀ k, Lt (r.big (xiT m c pre r P k)) R := fun k => (hU.good.1 _ (htow k).1 (hγK k)).2
  have hy : ∀ k, WNF (xiT m c pre r P (k + 1)) := fun k => (htow (k + 1)).1
  -- 定義との対応
  have hgam : ∀ n, gam π (.K m) (.xi m) pre R r c P n = xiT m c pre r P n := by
    intro n
    induction n with
    | zero => simp only [gam, canonK, outsideMode, Bool.false_eq_true, ↓reduceIte, xiT]
    | succ k ih =>
      have hA : argOf π (.K m) (.xi m) pre R r c P (gam π (.K m) (.xi m) pre R r c P k) =
          xA c pre .zero (r.big (xiT m c pre r P k)) := by
        rw [ih]
        simp only [argOf, canonK, outsideMode, seedOut, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
        rfl
      have hAF := G.hAF (hxF k)
      have hne : xA c pre .zero (r.big (xiT m c pre r P k)) ≠ .zero := (hy k).xi.2.2.1
      have hle : leB (xA c pre .zero (r.big (xiT m c pre r P k))) (succK m) = true :=
        leB_iff.mpr (hy k).xi.2.2.2.1
      simp only [gam, canonK, outsideMode, Bool.false_eq_true, ↓reduceIte]
      rw [hA, col_K_le hne hle]
      have hself : ltB (.Xi m (xA c pre .zero (r.big (xiT m c pre r P k))))
          ((Gen.xi m).ap (xA c pre .zero (r.big (xiT m c pre r P k)))) = false := ltB_self _
      rw [hself]
      rfl
  have he : ∀ n, (SeqD.app π (.xi m) pre R r P c).nat n = xiT m c pre r P (n + 1) := fun n => by
    have hA : argOf π (.K m) (.xi m) pre R r c P (gam π (.K m) (.xi m) pre R r c P n) =
        xA c pre .zero (r.big (xiT m c pre r P n)) := by
      rw [hgam n]
      simp only [argOf, canonK, outsideMode, seedOut, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
      rfl
    rw [app_nat_big hd hlt, hA]
    rfl
  exact ⟨htow, he⟩


/-- `K_m` の対角化（`Ξ_m` の族）：添字は値の帰還 -/
theorem xi_K_out {π X q P c : Tm} {m : Nat} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Xi m q)) (G : XiG m q .zero c pre rest R)
    (hc0 : c = .zero → P ≠ .zero) (hd : r.dom = .big (.K m)) (hlt : ltB (.K m) π = false)
    (hB : BigInv R (.K m) r) (hPF : WNF P) (hPπ : Lt P π)
    (hPA : ∀ g d, Ad π X g d → inC P g d = true) (hPn : P = .zero ∨ NodeT P) :
    XiOut π X m q P c pre R (.app π (.xi m) pre R r P c) := by
  have hπF := ht.psi.piF
  have hρ := G.ht
  have hKF := G.hKF
  have hm := G.hm
  have hρK := G.hρK
  have hU := hB.1
  have hπρ : Le π (.Xi m q) := hc.le hπF
  have hP0 : Lt P (.Xi m q) := lt_of_lt_of_leY hPF hπF hρ hPπ hπρ
  have hq0 : Lt .zero q := lt_of_lt_of_leY WNF.zero G.hRF G.hqF (zero_lt G.hR0) (by
    have := le_ofSummands_of_mem (nfl_summands G.hqF) G.hRm
    rwa [ofSummands_summands q G.hqF] at this)
  obtain ⟨htow, he⟩ := xi_K_data ht hc G hc0 hd hlt hB hPF hPπ hPn
  have hγK : ∀ k, Lt (xiT m c pre r P k) (.K m) := fun k =>
    lt_transY (htow k).1 hρ hKF (htow k).2.1 hρK
  have hxF : ∀ k, WNF (r.big (xiT m c pre r P k)) := fun k => (hU.good.1 _ (htow k).1 (hγK k)).1
  have hxR : ∀ k, Lt (r.big (xiT m c pre r P k)) R := fun k => (hU.good.1 _ (htow k).1 (hγK k)).2
  have hy : ∀ k, WNF (xiT m c pre r P (k + 1)) := fun k => (htow (k + 1)).1
  have hmono : ∀ k, Lt (xiT m c pre r P k) (xiT m c pre r P (k + 1)) := fun k => by
    have hy' := hy k
    have hy'' : WNF (.Xi m (xA c pre .zero (r.big (xiT m c pre r P k)))) := hy'
    have hK' : Lt (.Xi m (xA c pre .zero (r.big (xiT m c pre r P k)))) (.K m) :=
      (lt_K_iffY hy'' hm).mpr (Nat.le_refl _)
    have hA := G.hAF (hxF k)
    have hC : inC (r.big (xiT m c pre r P k)) (xA c pre .zero (r.big (xiT m c pre r P k)))
        (.Xi m (xA c pre .zero (r.big (xiT m c pre r P k)))) = true := by
      have hCK : inC (xA c pre .zero (r.big (xiT m c pre r P k)))
          (xA c pre .zero (r.big (xiT m c pre r P k)))
          (.Xi m (xA c pre .zero (r.big (xiT m c pre r P k)))) = true :=
        inC_of_fr_lt hA hKF hy'' hA hA hy''.xi.2.2.2.2 (Or.inr hK') (Or.inl rfl)
          fun w hw => FWOrder.k2x hy'' w hw
      exact (G.parts (hxF k) (hxR k) hCK).2.1
    exact coll_xi0 hy'' _ (htow k).1 (hU.lo _ _ _ hy'' (htow k).1 (hγK k) hC) (hγK k)
  have hclo : ∀ g d k, WNF g → WNF d → inC q g d = true → Lt q g → inC P g d = true →
      inC (xiT m c pre r P k) g d = true := by
    intro g d k hg hd h1 h2 h3
    induction k with
    | zero => exact h3
    | succ k ih =>
      have h0 : Lt .zero g := lt_transY WNF.zero G.hqF hg hq0 h2
      have hxC := hU.ub g d _ hg hd (htow k).1 (hγK k) h0 (bigOK_none rfl) (G.qparts h1).1 ih
      exact inC_xi_iff.mpr (Or.inr ⟨G.inC_A (hxF k) (G.qparts h1).2 hxC (inC_zero _ _),
        lt_transY (G.hAF (hxF k)) G.hqF hg (G.hAlt (hxF k) (hxR k) G.hqF G.hTq) h2⟩)
  have hdt := app_dom_big_ge (P := P) (c := c) (g := .xi m) (pre := pre) (R := R) hd hlt
  have L : NatL (.Xi m q) (.app π (.xi m) pre R r P c) := by
    refine ⟨fun n => ?_, fun n => ?_, fun g d n hg hd' h => ?_⟩
    · rw [he n, he (n + 1)]
      exact ⟨hy n, (htow (n + 1)).2.1, hmono (n + 1)⟩
    · rw [he n]
      intro e
      cases e
    · rw [he (n + 1)] at h
      rw [he n]
      rcases inC_xi_iff.mp h with h' | ⟨h', -⟩
      · exact WFY.inC_of_ltY _ (hy n) hd' (lt_transY (hy n) (hy (n + 1)) hd' (hmono (n + 1)) h')
      · exact hU.lo g d _ hd' (hy n) (hγK (n + 1)) (G.parts (hxF (n + 1)) (hxR (n + 1)) h').2.1
  have hlt' : ∀ n, Lt ((SeqD.app π (.xi m) pre R r P c).nat n) π := fun n => by
    rw [he n]
    refine hc.lt_base hπF (hy n) (htow (n + 1)).2.1 fun g d hg hd' hle hn hC => ?_
    rcases inC_xi_iff.mp hC with h' | ⟨h1, h2⟩
    · exact absurd h' hn
    · exact hclo g d (n + 1) hg hd' h1 h2 (WFY.inC_of_ltY _ hPF hd' (lt_of_lt_of_leY hPF hπF hd' hPπ hle))
  have hP1 : Lt P (xiT m c pre r P 1) := hmono 0
  refine ⟨Or.inl ⟨hdt, 0, first_of_nat hdt⟩, ?_, by rw [first_of_nat hdt]; exact hlt' 0,
    fun g d hg hd' _ _ h1 h2 hP => ?_, fun hG => ?_⟩
  · rintro y (⟨-, n, rfl⟩ | ⟨σ, η, hd2, -⟩)
    · have hle := le_of_mono (y := (SeqD.app π (.xi m) pre R r P c).nat) (fun k => (L.good k).1)
        (fun k => (L.good k).2.2) n
      refine ⟨.zero, r.big (xiT m c pre r P n), Or.inr rfl, he n, (L.good n).1, hxF n, hxR n,
        G.hAlt (hxF n) (hxR n) G.hqF G.hTq, ?_, fun _ => ?_, hU.pos _ (htow n).1 (hγK n),
        hB.2 _ (htow n).1 (hγK n)⟩
      · rw [first_of_nat hdt]
        exact hle
      · refine lt_of_lt_of_leY hPF (L.good 0).1 (L.good n).1 ?_ hle
        rw [he 0]
        exact hP1
    · rw [hdt] at hd2
      cases hd2
  · rw [first_of_nat hdt, he 0]
    exact hclo g d 1 hg hd' h1 h2 hP
  · refine seqI_nat hdt (natInv_lift ht L hlt' (fun g d n h => ?_) fun n => hG _ (Or.inl ⟨hdt, n, rfl⟩))
    obtain ⟨h1, h2⟩ := xi_comp ht hc h
    rw [he n]
    exact hclo g d (n + 1) h.1 h.2.1 h1 h2 (hPA g d h)

/-- 加数の共終数による場合分け -/
theorem xi_app {π X q P c : Tm} {m : Nat} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Xi m q)) (G : XiG m q P c pre rest R)
    (hc0 : c = .zero → P ≠ .zero)
    (hRI : SeqI R r) (h0 : r.dom ≠ .zero) (h1 : r.dom ≠ .one) (hRs : R ∈ subs (.Psi .zero π X))
    (hRsz : R.size < π.size) (hPs : ¬ isSucc P = true)
    (hPπ : Lt P π) (hPA : ∀ g d, Ad π X g d → inC P g d = true)
    (hPfr : P ≠ .zero → P ∈ fr (.K m) P)
    (hqσ : ∀ σ, WNF σ → Le π σ → inC q q σ = true)
    (hPn : P = .zero ∨ NodeT P) :
    XiOut π X m q P c pre R (.app π (.xi m) pre R r P c) := by
  unfold SeqI at hRI
  have hπF := ht.psi.piF
  cases hd : r.dom with
  | zero => exact absurd hd h0
  | one => exact absurd hd h1
  | omega =>
    rw [hd] at hRI
    have hdom : ∀ σ, r.dom ≠ .big σ := fun σ e => by
      rw [hd] at e
      cases e
    exact xi_nat_out ht hc G hc0 (inner_nat hRI) (fun n => by rw [app_nat_of_not_big hdom n]; rfl)
      (app_dom_nat hdom) hPπ hPA hPfr
  | big σ =>
    rw [hd] at hRI
    obtain ⟨hBW, hBS, hreg⟩ := hRI
    have hB : BigInv R σ r := ⟨hBW.1, hBS G.hRp⟩
    have hσF := hB.1.hσF
    by_cases hσπ : Lt σ π
    · exact xi_big_out ht hc G hc0 hB hreg hd hσπ hRs hPπ hPA hPfr
    have hlt' : ltB σ π = false := by
      cases e : ltB σ π with
      | false => rfl
      | true => exact absurd (ltB_iff.mp e) hσπ
    rcases hreg with hσt | ⟨m', rfl⟩
    · have hne : σ ≠ π := fun e => by
        have h2 := size_le_of_mem_subs hB.1.hσs
        rw [e] at h2
        omega
      have hπσ : Le π σ := le_of_not_ltY hσF hπF hσπ
      have hqπ := hqσ π hπF (Or.inl rfl)
      have hσC := hB.1.hσC q π G.hqF hπF (G.qparts hqπ).1
      have htσ : WNF (.Psi .zero σ q) :=
        wnf_psi0 hσF hσt G.hqF (hqσ σ hσF hπσ) fun q' hq => (arg_of_inC hq hσC hσπ).2
      have hR0 : Lt .zero R := zero_lt G.hR0
      have H : DiagHyp .zero σ q .zero .zero pre rest R r :=
        { ht := htσ, hsum := G.hsum, hRU := hB.1, hRG := hB.2, hGF := WNF.zero
          hGσ := zero_lt hσt.ne_zero, hGs := by simp [isSucc, summands], hQF := WNF.zero, hQR := hR0
          hQσ := zero_lt hσt.ne_zero
          hI := IdxHyp.zero htσ, hξ := zero_le _ }
      refine xi_nat_out ht hc G hc0 (H.inner_out (c := .zero) WNF.zero G.hPF hPs (fun _ _ _ _ _ => inC_zero _ _))
        (fun n => ?_) (app_dom_big_ge hd hlt') hPπ hPA hPfr
      rw [app_nat_outG H (by simpa [Gen.tgt?] using hne) rfl hd hlt']
      rfl
    · have hm := G.hm
      have hm' : 1 ≤ m' := hB.1.hσF.k
      have e : m' = m := by
        have h3 : Lt π (.K m') := by
          rcases triY hπF (WNF.K' hm') with h' | h' | h'
          · exact h'
          · exact absurd h' (IsTgt.ne_K ht.psi.tgt m')
          · exact absurd h' hσπ
        have h4 : lev π ≤ m' := (lt_K_iffY hπF hm').mp h3
        have h5 : lev π = m := hc.lev_eq
        have h6 : Le (.K m') R := hB.1.hσle
        have h7 : Le R q := by
          have := le_ofSummands_of_mem (nfl_summands G.hqF) G.hRm
          rwa [ofSummands_summands q G.hqF] at this
        have h8 : Le (.K m') (succK m) :=
          le_transY (WNF.K' hm') G.hqF (WNF.succK hm) (le_transY (WNF.K' hm') G.hRF G.hqF h6 h7)
            (le_of_ne_gtY G.hqF (WNF.succK hm) G.ht.xi.2.2.2.1)
        have h9 : lev (Tm.K m') ≤ lev (succK m) := by
          rcases h8 with e' | e'
          · exact Nat.le_of_eq (congrArg lev e')
          · exact lev_le_of_lt_gen e'
        have h10 : lev (Tm.K m') = m' + 1 := rfl
        have h11 : lev (succK m) = m + 1 := rfl
        omega
      subst e
      have G0 : XiG m' q .zero c pre rest R :=
        ⟨G.ht, G.hsum, WNF.zero, zero_lt G.hR0, zero_lt (by intro e; cases e), G.hc, G.hR1⟩
      exact xi_K_out ht hc G0 hc0 hd hlt' hB G.hPF hPπ hPA hPn

/-- Ω の塔の列 -/
theorem tower_spec {π X G : Tm} (ht : WNF (.Psi .zero π X)) (hπ : ∀ c, π ≠ .Om c) (hGF : WNF G)
    (hGt : Lt G (.Psi .zero π X))
    (hC : ∀ g d, WNF g → WNF d → inC (.Psi .zero π X) g d = true → inC G g d = true)
    (hG : ∀ n, Gp (.Psi .zero π X) (tower G (n + 1))) : SeqI (.Psi .zero π X) (.tower G) := by
  have hgood := natGood_tower ht (IsOF.psi ht hπ) hGF hGt
  have hub : ∀ g d k, inC G g d = true → inC (tower G k) g d = true := by
    intro g d k h
    induction k with
    | zero => exact h
    | succ k ih =>
      show inC (.Om (succT (tower G k))) g d = true
      rw [inC_om]
      exact inC_succT ih
  refine seqI_nat rfl ⟨⟨hgood, fun n e => ?_, fun g d n hg hd h => hub g d (n + 1) (hC g d hg hd h),
    fun g d n hg hd h => ?_⟩, fun n v hv hne hl => hG n v hv hne hl⟩
  · cases e
  · have h' : inC (.Om (succT (tower G (n + 1)))) g d = true := h
    rw [inC_om] at h'
    exact inC_of_succT h'

/-- 列 `s0` -/
def s0X (π : Tm) (m : Nat) (q : Tm) : SeqD :=
  .app π (.xi m) (preT (info q).sums) (lastT (info q).sums) (lastS (info q).sums) .zero .one

/-- 最初の近似（隙間の下限） -/
def xcanon (π : Tm) (m : Nat) (q : Tm) : Tm :=
  if q = .one then floorLev m else if isSucc q then .Xi m (pred q) else (s0X π m q).first

theorem mkApp_xi {ceil : Tm} {m : Nat} {pre : List Tm} {R : Tm} {r : SeqD} {P c : Tm}
    (hP : P = .zero ∨ ltB P R = true) :
    mkApp ceil (.xi m) pre R r P c = some (.app ceil (.xi m) pre R r P c) := by
  unfold mkApp
  rcases hP with rfl | hP
  · simp [Gen.tgt?]
  · simp [hP, Gen.tgt?]

/-- 鎖の上の `Ξ_m(z)` は種 -/
theorem seedX {π X q z : Tm} {m : Nat} (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Xi m q))
    (hy : WNF (.Xi m z)) (hρ : Lt (.Xi m z) (.Xi m q)) (hzq : Lt z q)
    (hC : ∀ g d, inC q g d = true → inC z g d = true) : SeedP π X (.Xi m z) := by
  have hπF := ht.psi.piF
  have hq := (hc.wnf hπF).xi.2.1
  have hz := hy.xi.2.1
  have hyC : ∀ g d, WNF g → inC q g d = true → Lt q g → inC (.Xi m z) g d = true := fun g d hg h1 h2 =>
    inC_xi_iff.mpr (Or.inr ⟨hC g d h1, lt_transY hz hq hg hzq h2⟩)
  have hlt : Lt (.Xi m z) π := hc.lt_base hπF hy hρ fun g d hg hd _ hn h => by
    rcases inC_xi_iff.mp h with h' | ⟨h1, h2⟩
    · exact absurd h' hn
    · exact hyC g d hg h1 h2
  have hX := ht.psi.aF
  obtain ⟨h1, h2⟩ := xi_comp ht hc (Ad.self ht)
  have hltt : Lt (.Xi m z) (.Psi .zero π X) := coll_psiY ht _ hy (hyC X _ hX h1 h2) hlt
  refine ⟨hy, hltt, fun g d hg hd h => ?_, Or.inl ⟨m, z, rfl⟩⟩
  by_cases hdt : Lt (.Psi .zero π X) d
  · exact WFY.inC_of_ltY _ hy hd (lt_transY hy ht hd hltt hdt)
  · obtain ⟨h1', h2'⟩ := xi_comp ht hc (⟨hg, hd, Or.inl ⟨h, hdt⟩⟩ : Ad π X g d)
    exact hyC g d hg h1' h2'

theorem chain_not_om {π : Tm} {m : Nat} {q : Tm} (hc : Chain π (.Xi m q)) : ∀ c, π ≠ .Om c := by
  intro c e
  subst e
  cases hc

/-- 階の下端は `t` 未満 -/
theorem floorLev_lt {π X : Tm} (ht : WNF (.Psi .zero π X)) (hl : lev π = m) (hm : 1 ≤ m) :
    WNF (floorLev m) ∧ Lt (floorLev m) (.Psi .zero π X) ∧ ∀ g d, inC (floorLev m) g d = true := by
  unfold floorLev
  by_cases h : m ≤ 1
  · rw [ite_eq_left h]
    exact ⟨WNF.zero, zero_lt (by intro e; cases e), fun _ _ => inC_zero _ _⟩
  · rw [ite_eq_right h]
    refine ⟨WNF.K' (by omega), bot_ltY rfl (by simp only [lev]; omega) rfl rfl ht, fun _ _ => inC_K _ _ _⟩

/-- `Ξ` の族の近似の列の出力 -/
theorem vk_out {π X q : Tm} {m : Nat} (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Xi m q))
    (hS : ∀ u, u ∈ summands q → u ≠ .one → SeqI u (info u).seq)
    (hqs : ∀ u, u ∈ summands q → u ≠ .one → u ∈ subs (.Psi .zero π X) ∧ u.size < π.size)
    (hqσ : ∀ σ, WNF σ → Le π σ → inC q q σ = true)
    (P' c : Tm) (pre rest : List Tm) (R : Tm) (hsum : summands q = pre ++ R :: rest) (hR1 : R ≠ .one)
    (hPR : Lt P' R) (hSP : P' ≠ .zero → SeedP π X P') (hPF : WNF P') (hc' : c = .zero ∨ c = .one)
    (hc0 : c = .zero → P' ≠ .zero) :
    XiOut π X m q P' c pre R (.app π (.xi m) pre R (info R).seq P' c) := by
  have hπF := ht.psi.piF
  have hρ : WNF (.Xi m q) := hc.wnf hπF
  have hm : 1 ≤ m := hρ.xi.1
  have hqF := hρ.xi.2.1
  have hKF : WNF (.K m) := WNF.K' hm
  have hρK : Lt (.Xi m q) (.K m) := (lt_K_iffY hρ hm).mpr (Nat.le_refl _)
  have hπK : Le π (.K m) := Or.inr (lt_of_le_of_ltY hπF hρ hKF (hc.le hπF) hρK)
  have hpK : ∀ {p : Tm}, SeedP π X p → Lt p (.K m) := fun Sp =>
    lt_of_lt_of_leY Sp.hF hπF hKF (Sp.hπ ht) hπK
  have hRm : R ∈ summands q := by
    rw [hsum]
    exact List.mem_append_right _ List.mem_cons_self
  have hRF := hqF.of_mem_subs (mem_subs_of_mem_summands hRm)
  have hRp := nfl_principal (nfl_summands hqF) R hRm
  obtain ⟨h0, h1⟩ := dom_ne_of_principal hRF hRp hR1
  have hP0 : P' = .zero ∨ P' ≠ .zero := by
    by_cases h : P' = .zero
    · exact Or.inl h
    · exact Or.inr h
  have hPK : Lt P' (.K m) := by
    rcases hP0 with rfl | h
    · exact zero_lt (by intro e; cases e)
    · exact hpK (hSP h)
  have hPπ : Lt P' π := by
    rcases hP0 with rfl | h
    · exact zero_lt ht.psi.tgt.ne_zero
    · exact (hSP h).hπ ht
  have hPs : ¬ isSucc P' = true := by
    rcases hP0 with rfl | h
    · simp [isSucc, summands]
    · exact (hSP h).ns
  have G : XiG m q P' c pre rest R := ⟨hρ, hsum, hPF, hPR, hPK, hc', hR1⟩
  exact xi_app ht hc G hc0 (hS R hRm hR1) h0 h1 (hqs R hRm hR1).1 (hqs R hRm hR1).2 hPs hPπ
    (fun g d h => by
      rcases hP0 with rfl | h'
      · exact inC_zero _ _
      · exact (hSP h').ad h)
    (fun h => (hSP h).self_fr (hpK (hSP h))) hqσ (by
      rcases hP0 with rfl | h'
      · exact Or.inl rfl
      · exact Or.inr (hSP h').hn)

/-- 塔の列 -/
theorem tower_seq {π X G : Tm} (ht : WNF (.Psi .zero π X)) (hnot : ∀ c, π ≠ .Om c) (hGF : WNF G)
    (hGt : Lt G (.Psi .zero π X))
    (hC : ∀ g d, WNF g → WNF d → inC (.Psi .zero π X) g d = true → inC G g d = true)
    (hgp : ∀ y, WNF y → isPrincipal y = true → y ≠ .one → Lt G y → Gp (.Psi .zero π X) y) :
    SeqI (.Psi .zero π X) (.tower G) :=
  tower_spec ht hnot hGF hGt hC fun n => hgp _ (wnf_tower hGF _) rfl (fun e => by
    have e' : tower G (n + 1) = .Om (sc (tower G n)) := rfl
    rw [e'] at e
    cases e) (by
    induction n with
    | zero => exact tower_mono hGF 0
    | succ k ih => exact lt_transY hGF (wnf_tower hGF _) (wnf_tower hGF _) ih (tower_mono hGF (k + 1)))

/-- `mahloVK` の種の分岐（`q` が極限で、種が素の 0 番目を越えるとき） -/
def vTail (π : Tm) (m : Nat) (q p : Tm) : SeqD :=
  match splitGtD p (info q).sums with
  | some (pre, R, r) =>
    match mkApp π (.xi m) pre R r p .zero with
    | some s => s
    | none => .tower p
  | none => .tower p

/-- 種が `t` の部分項を支配するときの種の分岐 -/
theorem vk_tail_dom {π X q p : Tm} {m : Nat} (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Xi m q))
    (hS : ∀ u, u ∈ summands q → u ≠ .one → SeqI u (info u).seq)
    (hqs : ∀ u, u ∈ summands q → u ≠ .one → u ∈ subs (.Psi .zero π X) ∧ u.size < π.size)
    (hqσ : ∀ σ, WNF σ → Le π σ → inC q q σ = true) (Sp : SeedP π X p)
    (hD : Dom (.Psi .zero π X) p) : SeqI (.Psi .zero π X) (vTail π m q p) := by
  have hnot := chain_not_om hc
  have hne0 : p ≠ .zero := by
    rcases Sp.hn with ⟨m', a, e'⟩ | ⟨s, q'', a, e'⟩ <;> rw [e'] <;> simp
  have hins : SeqI (.Psi .zero π X) (.tower p) :=
    tower_seq ht hnot Sp.hF Sp.hlt Sp.hC fun y hyF hyp _ hlt v hv hne hl => hD v hv hne hl y hyF hyp hlt
  unfold vTail
  cases hsp : splitGtD p (info q).sums with
  | none => exact hins
  | some q' =>
    obtain ⟨pre₂, R₂, r₂⟩ := q'
    obtain ⟨L, rest, hys, hL, hpR₂, -, -⟩ := splitGtD_spec hsp
    have hpR : Lt p R₂ := ltB_iff.mp hpR₂
    have hsum₂ : summands q = pre₂ ++ R₂ :: rest.map Prod.fst := by
      rw [← info_sums_fst, hys, List.map_append, hL, List.map_cons]
    have hrc : r₂ = (info R₂).seq := by
      have hm' : (R₂, r₂) ∈ (info q).sums := by
        rw [hys]
        simp
      exact coh_sums q (R₂, r₂) hm'
    subst hrc
    have hR₂1 : R₂ ≠ .one := by
      intro e
      rw [e] at hpR
      have e0 := lt_oneY Sp.hF hpR
      exact hne0 e0
    dsimp only
    rw [mkApp_xi (Or.inr hpR₂)]
    simp only
    have o := vk_out ht hc hS hqs hqσ p .zero pre₂ _ R₂ hsum₂ hR₂1 hpR (fun _ => Sp) Sp.hF (Or.inl rfl)
      fun _ => hne0
    refine o.inv fun y hy => ?_
    obtain ⟨P', x, -, rfl, hyF, -, -, -, -, hPy, -, -⟩ := o.form y hy
    exact fun v hv hne hl => hD v hv hne hl _ hyF rfl (hPy hne0)

/-- `mahloVK` の仕様 -/
theorem vk_spec {π X q : Tm} {m : Nat} {P : Option Tm} (ht : WNF (.Psi .zero π X))
    (hc : Chain π (.Xi m q))
    (hS : ∀ u, u ∈ summands q → u ≠ .one → SeqI u (info u).seq)
    (hqs : ∀ u, u ∈ summands q → u ≠ .one → u ∈ subs (.Psi .zero π X) ∧ u.size < π.size)
    (hqσ : ∀ σ, WNF σ → Le π σ → inC q q σ = true)
    (hP : ∀ p, P = some p → SeedP π X p)
    (hne : ∀ p, P = some p → ¬ isSucc q = true → q ≠ .one →
      XiOut π X m q .zero .one (preT (info q).sums) (lastT (info q).sums) (s0X π m q) →
      (s0X π m q).first ≠ p)
    (hG : ∀ y, WNF y → isPrincipal y = true → y ≠ .one → (∀ p, P = some p → Lt p y) →
      Le (xcanon π m q) y → (q = .one ∨ isSucc q = true ∨ ∀ p, P = some p → ¬ Lt (xcanon π m q) p) →
      Gp (.Psi .zero π X) y)
    (hTail : ∀ p, P = some p → ¬ isSucc q = true → q ≠ .one → Lt (s0X π m q).first p →
      SeqI (.Psi .zero π X) (vTail π m q p)) :
    SeqI (.Psi .zero π X) (mahloVK m q (info q).sums π P) := by
  have hπF := ht.psi.piF
  have hρ : WNF (.Xi m q) := hc.wnf hπF
  have hm : 1 ≤ m := hρ.xi.1
  have hqF := hρ.xi.2.1
  have hq0 : q ≠ .zero := hρ.xi.2.2.1
  have hqC := hρ.xi.2.2.2.2
  have hnot := chain_not_om hc
  have hKF : WNF (.K m) := WNF.K' hm
  have hρK : Lt (.Xi m q) (.K m) := (lt_K_iffY hρ hm).mpr (Nat.le_refl _)
  have hqρ : inC q q (.Xi m q) = true :=
    inC_of_fr_lt hqF hKF hρ hqF hqF hqC (Or.inr hρK) (Or.inl rfl) fun w hw => FWOrder.k2x hρ w hw
  have hone : ∀ {G y : Tm}, WNF G → ((∃ m a, G = .Xi m a) ∨ ∃ s q a, G = .Psi s q a) → Lt G y → y ≠ .one :=
    fun hGF hn hlt e => by
      rw [e] at hlt
      have e0 := lt_oneY hGF hlt
      rcases hn with ⟨m', a, e'⟩ | ⟨s, q', a, e'⟩ <;> rw [e0] at e' <;> cases e'
  have hT : ∀ G, WNF G → Lt G (.Psi .zero π X) →
      (∀ g d, WNF g → WNF d → inC (.Psi .zero π X) g d = true → inC G g d = true) →
      (∀ y, WNF y → isPrincipal y = true → y ≠ .one → Lt G y → Gp (.Psi .zero π X) y) →
      SeqI (.Psi .zero π X) (.tower G) := fun G hGF hGt hC hgp => tower_seq ht hnot hGF hGt hC hgp
  have hout := vk_out ht hc hS hqs hqσ
  unfold mahloVK
  by_cases h1 : q = .one
  · rw [ite_eq_left h1]
    have hc' : xcanon π m q = floorLev m := by
      unfold xcanon
      rw [ite_eq_left h1]
    obtain ⟨hfF, hft, hfC⟩ := floorLev_lt ht (hc.lev_eq.trans rfl) hm
    -- 始点
    have hG0 : WNF (maxO P (floorLev m)) ∧ Lt (maxO P (floorLev m)) (.Psi .zero π X) ∧
        (∀ g d, WNF g → WNF d → inC (.Psi .zero π X) g d = true → inC (maxO P (floorLev m)) g d = true) ∧
        Le (floorLev m) (maxO P (floorLev m)) ∧ ∀ p, P = some p → Le p (maxO P (floorLev m)) := by
      cases P with
      | none => exact ⟨hfF, hft, fun g d _ _ _ => hfC g d, Or.inl rfl, fun p e => by cases e⟩
      | some p =>
        have Sp := hP p rfl
        unfold maxO
        by_cases h : ltB p (floorLev m) = true
        · simp only [h, ↓reduceIte]
          refine ⟨hfF, hft, fun g d _ _ _ => hfC g d, Or.inl rfl, fun p' e => ?_⟩
          cases e
          exact Or.inr (ltB_iff.mp h)
        · simp only [h, ↓reduceIte]
          refine ⟨Sp.hF, Sp.hlt, Sp.hC, ?_, fun p' e => ?_⟩
          · exact le_of_not_ltY Sp.hF hfF fun h' => h (ltB_iff.mpr h')
          · cases e
            exact Or.inl rfl
    obtain ⟨g1, g2, g3, g4, g5⟩ := hG0
    refine hT _ g1 g2 g3 fun y hyF hyp hy1 hlt => hG y hyF hyp hy1
      (fun p e => lt_of_le_of_ltY (hP p e).hF g1 hyF (g5 p e) hlt) ?_ (Or.inl h1)
    rw [hc']
    exact Or.inr (lt_of_le_of_ltY hfF g1 hyF g4 hlt)
  rw [ite_eq_right h1]
  by_cases hs : isSucc q = true
  · rw [ite_eq_left hs]
    have hc' : xcanon π m q = .Xi m (pred q) := by
      unfold xcanon
      rw [ite_eq_right h1, ite_eq_left hs]
    have hpq : Lt (pred q) q := pred_lt hqF hs
    have hpF := wnf_pred hqF
    have hpne : pred q ≠ .zero := by
      intro e
      apply h1
      rw [← succT_pred hqF hs, e]
      rfl
    have hy₁ : WNF (.Xi m (pred q)) := wnf_xi_mk hm hpF hpne
      (ne_gt_of_le (le_transY hpF hqF (WNF.succK hm) (Or.inr hpq) (le_of_ne_gtY hqF (WNF.succK hm) hρ.xi.2.2.2.1)))
      (inC_pred_self hqF hs hqC)
    have Sx : SeedP π X (.Xi m (pred q)) := seedX ht hc hy₁
      ((lt_xi_xi0 hpq.ne).mpr (Or.inl ⟨hpq, inC_pred_of hqF hqρ⟩)) hpq fun g d h => inC_pred_of hqF h
    obtain ⟨S1, S2, S3⟩ := maxO_seed Sx hP
    have hgap : ∀ y, WNF y → isPrincipal y = true → Lt (maxO P (.Xi m (pred q))) y →
        Gp (.Psi .zero π X) y := fun y hyF hyp hlt =>
      hG y hyF hyp (hone S1.hF S1.hn hlt) (fun p e => lt_of_le_of_ltY (hP p e).hF S1.hF hyF (S3 p e) hlt)
        (by rw [hc']; exact Or.inr (lt_of_le_of_ltY hy₁ S1.hF hyF S2 hlt)) (Or.inr (Or.inl hs))
    have hins := hT _ S1.hF S1.hlt S1.hC fun y hyF hyp _ hlt => hgap y hyF hyp hlt
    cases hsp : splitPosD π (info q).sums.dropLast with
    | none => exact hins
    | some q' =>
      obtain ⟨pre, R, r⟩ := q'
      obtain ⟨⟨rest, hsum⟩, rfl, hπR⟩ := split_pos hs hsp
      have hRm : R ∈ summands q := by
        rw [hsum]
        exact List.mem_append_right _ List.mem_cons_self
      have hRF := hqF.of_mem_subs (mem_subs_of_mem_summands hRm)
      have hπR' : Le π R := le_of_ne_gtY hπF hRF (leB_iff.mp hπR)
      have hpR : Lt (maxO P (.Xi m (pred q))) R := lt_of_lt_of_leY S1.hF hπF hRF (S1.hπ ht) hπR'
      have hR1 : R ≠ .one := by
        intro e
        rw [e] at hpR
        have e0 := lt_oneY S1.hF hpR
        rcases S1.hn with ⟨m', a, e'⟩ | ⟨s, q'', a, e'⟩ <;> rw [e0] at e' <;> cases e'
      have hne0 : maxO P (.Xi m (pred q)) ≠ .zero := by
        rcases S1.hn with ⟨m', a, e'⟩ | ⟨s, q'', a, e'⟩ <;> rw [e'] <;> simp
      dsimp only
      rw [mkApp_xi (Or.inr (ltB_iff.mpr hpR))]
      simp only
      have o := hout _ .zero pre rest R hsum hR1 hpR (fun _ => S1) S1.hF (Or.inl rfl) fun _ => hne0
      refine o.inv fun y hy => ?_
      obtain ⟨P', x, -, rfl, hyF, -, -, -, -, hPy, -, -⟩ := o.form y hy
      exact hgap _ hyF rfl (hPy hne0)
  · rw [ite_eq_right hs]
    have hc' : xcanon π m q = (s0X π m q).first := by
      unfold xcanon
      rw [ite_eq_right h1, ite_eq_right hs]
    have hsum := summands_pre_last hq0
    have hlast : lastS (info q).sums = (info (lastT (info q).sums)).seq := lastS_coh (coh_sums q)
    obtain ⟨pre, hpr⟩ : ∃ pre, pre = preT (info q).sums := ⟨_, rfl⟩
    obtain ⟨R, hR⟩ : ∃ R, R = lastT (info q).sums := ⟨_, rfl⟩
    rw [← hpr, ← hR] at hsum
    rw [← hR] at hlast
    have hRm : R ∈ summands q := by
      rw [hsum]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have hR1 : R ≠ .one := by
      intro e
      apply hs
      show (summands q).getLast? == some one
      rw [hsum, e]
      simp
    have hRp := nfl_principal (nfl_summands hqF) R hRm
    have hR0 : R ≠ .zero := by
      intro e
      rw [e] at hRp
      cases hRp
    have hs0 : s0X π m q = .app π (.xi m) pre R (info R).seq .zero .one := by
      unfold s0X
      rw [← hpr, ← hR, hlast]
    have o0 := hout .zero .one pre [] R hsum hR1 (zero_lt hR0) (fun h => absurd rfl h) WNF.zero (Or.inr rfl)
      (fun e => by cases e)
    rw [← hs0] at o0
    obtain ⟨P₀, x₀, -, -, hfF, -, -, -, -, -, -, -⟩ := o0.form _ o0.mem
    have hne' : ∀ p, P = some p → (s0X π m q).first ≠ p := fun p e =>
      hne p e hs h1 (by rw [← hpr, ← hR]; exact o0)
    dsimp only
    rw [← hpr, ← hR, hlast, ← hs0]
    cases P with
    | none =>
      refine o0.inv fun y hy => ?_
      obtain ⟨P', x, -, rfl, hyF, -, -, -, hle, -, -, -⟩ := o0.form y hy
      exact hG _ hyF rfl (fun e => by cases e) (fun p e => by cases e) (by rw [hc']; exact hle)
        (Or.inr (Or.inr fun p e => by cases e))
    | some p =>
      have Sp := hP p rfl
      simp only
      by_cases h2 : ltB p (s0X π m q).first = true
      · rw [ite_eq_left h2]
        refine o0.inv fun y hy => ?_
        obtain ⟨P', x, -, rfl, hyF, -, -, -, hle, -, -, -⟩ := o0.form y hy
        exact hG _ hyF rfl (fun e => by cases e) (fun p' e => by
          cases e
          exact lt_of_lt_of_leY Sp.hF hfF hyF (ltB_iff.mp h2) hle) (by rw [hc']; exact hle)
          (Or.inr (Or.inr fun p' e => by
            cases e
            rw [hc']
            exact Lt.asymmY Sp.hF hfF (ltB_iff.mp h2)))
      · rw [ite_eq_right h2, ite_eq_right (hne' p rfl)]
        have hlt : Lt (s0X π m q).first p := by
          rcases triY hfF Sp.hF with h | h | h
          · exact h
          · exact absurd h (hne' p rfl)
          · exact absurd (ltB_iff.mpr h) h2
        exact hTail p rfl hs h1 hlt

end RTKA.Fund
