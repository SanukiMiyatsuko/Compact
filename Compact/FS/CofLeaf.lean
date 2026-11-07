import Compact.FS.CofIdx

/-! 族の閉包の葉の共終性：`mkApp` の出力（ψ・Mahlo 型、目標 `τ ≥ π`）と `idx_app` の出力（添字の閉包）。

段の節点の分類（`a` が `T` 以上の節点など）と下の段は仮定に残す。 -/

namespace RTKA.Fund

open Tm W

/-- 目標 `τ` の段の `mkApp` の出力の列の共終性：引数が `T = pre ⊕ R` 以上の節点は `hN`、下の段は `hlow` -/
theorem cof_app_lvl {π X ξ τ X' P : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r s : SeqD}
    (hg : GenPsi g ξ τ) (hv : WNF (.Psi .zero τ X')) (hsum : summands X' = pre ++ R :: rest)
    (S : SeedHyp τ X' P R) (hR1 : R ≠ .one) (hx0 : WNF r.first) (hx0R : Lt r.first R)
    (h : mkApp π g pre R r P .zero = some s) (hI : IdxHyp ξ τ X') (hξ : Le ξ (ofSummands pre))
    (hRI : SeqI R r) (hRC : SeqC R r) (h0 : r.dom ≠ .zero) (h1 : r.dom ≠ .one)
    (hRp : isPrincipal R = true) (hσlow : ∀ σ, r.dom = .big σ → Lt σ τ → Lt σ π)
    (hπK : ∀ m, 1 ≤ m → ¬ Lt (.K m) π → Lt τ (.K m)) (hRne : ∀ m, r.dom = .big (.K m) → R ≠ succK m)
    (ht : WNF (.Psi .zero π X)) (hπτ : Le π τ) (hτfr : ∀ u, u ∈ fr τ τ → u ∈ fr π π)
    (pk : Pack ξ τ X' P pre rest R π r s) (hsI : SeqI (.Psi .zero π X) s)
    (hlow : ∀ x y, InSeq s y → WNF x → Lt x (.Psi .zero π X) →
      (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w y) →
      Lt (.Psi .zero π X) (tgtN x) → Lt (tgtN x) τ → Le π (tgtN x) → Lt x y)
    (hN : ∀ x y, InSeq s y → WNF x → Lt x (.Psi .zero π X) →
      (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w y) →
      ∀ s' a, x = .Psi s' τ a → Lt a X → ¬ Lt a (oadd (ofSummands pre) R) → Lt x y) :
    SeqC (.Psi .zero π X) s := by
  have hP := hv.psi
  have hτF := hP.piF
  have hτt := hP.tgt
  have hπF := ht.psi.piF
  have htτ : Lt (.Psi .zero π X) τ := lt_of_lt_of_leY ht hπF hτF (lt_psi_targetY ht) hπτ
  have hN' : NFL (pre ++ [R]) := by
    have h' : NFL (pre ++ R :: rest) := hsum ▸ nfl_summands hP.aF
    rw [show pre ++ R :: rest = (pre ++ [R]) ++ rest by simp] at h'
    exact nfl_append_left h'
  have hxτ : ∀ {x : Tm}, WNF x → Lt x (.Psi .zero π X) → Lt x τ := fun hx hxt =>
    lt_transY hx ht hτF hxt htτ
  have hparF : ∀ {x y : Tm}, WNF x → Lt x (.Psi .zero π X) →
      (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w y) → ∀ w, w ∈ parF x → Lt w y := fun hx hxt hpar w hw =>
    hpar w (parF_sub_parL hw)
      (lt_transY (hx.of_mem_subs (parL_sub (parF_sub_parL hw)).1) hx ht (parF_lt hx hw) hxt)
  unfold SeqC
  cases hd : s.dom with
  | zero => trivial
  | one => trivial
  | omega =>
    have hNI : NatInv (.Psi .zero π X) s := by
      unfold SeqI at hsI
      rwa [hd] at hsI
    have hyF : ∀ n, WNF (s.nat n) := fun n => (hNI.1.good n).1
    have hm : ∀ n, Lt (s.nat n) (s.nat (n + 1)) := fun n => (hNI.1.good n).2.2
    have hnb : ∀ σ, r.dom = .big σ → ¬ Lt σ π := fun σ hd' hlt => by
      rw [mkApp_dom_big h hd' hlt] at hd
      cases hd
    have hS := arg_mkApp hg hv hsum S hR1 hx0 hx0R h hI hξ hRI hRC h0 h1 hRp hnb hσlow hπK hRne ht htτ
      fun n => (hNI.1.good n).2.1
    refine leaf_natG ht hτt hπτ hτfr hNI (fun n => ?_) (fun x N hx hxt hpar htk hkτ hπk =>
      ⟨N, hlow x _ (Or.inl ⟨hd, N, rfl⟩) hx hxt hpar htk hkτ hπk⟩) fun x N hx hxt hpar z a e haX haC hafr => ?_
    · obtain ⟨P', x, -, e, -⟩ := pk.form (Or.inl ⟨hd, n, rfl⟩)
      exact ⟨ξ, _, e⟩
    · subst e
      by_cases haT : Lt a (oadd (ofSummands pre) R)
      · obtain ⟨n, B, hNn, hB, haB⟩ := hS a N (wnf_of_argR hx rfl) haT haC hafr
        have hy := hyF n
        refine ⟨n, ?_⟩
        rw [hB] at hy ⊢
        refine (Clo.psi hy).lt hx (hxτ hx hxt) (fun w hw => ?_) fun a' e' => by
          cases e'
          exact haB
        rw [← hB]
        exact lt_of_lt_of_leY (hx.of_mem_subs (parL_sub (parF_sub_parL hw)).1) (hyF N) (hyF n)
          (hparF hx hxt hpar w hw) (mono_le hyF hm hNn)
      · exact ⟨N, hN _ _ (Or.inl ⟨hd, N, rfl⟩) hx hxt hpar z a rfl haX haT⟩
  | big σ =>
    have hsI' := hsI
    unfold SeqI at hsI'
    rw [hd] at hsI'
    obtain ⟨⟨hU, -⟩, hG, -⟩ := hsI'
    rcases pk with ⟨-, hd'⟩ | ⟨σ', D⟩
    · rw [hd] at hd'
      cases hd'
    obtain ⟨g', c, hg', rfl, adj, -⟩ := D.ex
    have hσσ : σ' = σ := by
      have := app_dom_big_lt (P := P) (c := c) (g := g') (pre := pre) (R := R) (τ := π) D.hd (ltB_iff.mpr D.hσc)
      rw [this] at hd
      cases hd
      rfl
    subst hσσ
    have hS := argB_app (ceil := π) (P := P) hg' hN' adj.hF S.hPF D.hd D.hB.1 hRC
    have hYF : ∀ β, WNF β → Lt β σ' → WNF ((SeqD.app π g' pre R r P c).big β) := fun β hβ hβσ =>
      (hU.good.1 β hβ hβσ).1
    refine leaf_bigG ht hτt hπτ hτfr hU.hσF hU (hG rfl) (fun β _ _ => ⟨ξ, _, app_big_eq hg'⟩)
      (fun x β hx hxt hβ hβσ _ _ hpar htk hkτ hπk => hlow x _ (Or.inr ⟨σ', β, hd, hβ, hβσ, rfl⟩) hx hxt hpar
        htk hkτ hπk) fun x β hx hxt hβ hβσ hCl hfr hpar hσx z a e haX => ?_
    subst e
    by_cases haT : Lt a (oadd (ofSummands pre) R)
    · have haF := hx.psi.aF
      obtain ⟨B, hB, haB⟩ := hS a β haF haT hβ hβσ hCl fun f hf => hfr f (fr_arg hU.hσF hx hσx rfl hf)
      have hy := hYF β hβ hβσ
      rw [hB] at hy ⊢
      refine (Clo.psi hy).lt hx (hxτ hx hxt) (fun w hw => ?_) fun a' e' => by
        cases e'
        exact haB
      have := hparF hx hxt hpar w hw
      rwa [hB] at this
    · exact hN _ _ (Or.inr ⟨σ', β, hd, hβ, hβσ, rfl⟩) hx hxt hpar z a rfl haX haT

/-- 添字の閉包の葉（`idx_app` の出力）の共終性 -/
theorem cof_idx_app {π X τ Y μ P : Tm} {T : Tm → Tm → Prop} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (C : MCtx π X τ Y μ T) (G : IdxG τ Y μ P pre rest R) (hRI : SeqI R r) (hRC : SeqC R r)
    (h0 : r.dom ≠ .zero) (h1 : r.dom ≠ .one) (hRp : isPrincipal R = true) (hRs : R ∈ subs (.Psi .zero π X))
    (hRsz : R.size < π.size) (hPs : ¬ isSucc P = true) (hPπ : Lt P π)
    (hPA : ∀ g d, Ad π X g d → inC P g d = true) (hPfr : P ≠ .zero → P ∈ fr τ P)
    (hτΩ : ∀ c, τ ≠ .Om c) (hτfr : ∀ u, u ∈ fr τ τ → u ∈ fr π π)
    (hsI : SeqI (.Psi .zero π X) (.app π (.idx τ Y) pre R r P .zero))
    (hlow : ∀ x y, InSeq (.app π (.idx τ Y) pre R r P .zero) y → WNF x → Lt x (.Psi .zero π X) →
      (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w y) →
      Lt (.Psi .zero π X) (tgtN x) → Lt (tgtN x) τ → Le π (tgtN x) → Lt x y)
    (hcls : ∀ x y, InSeq (.app π (.idx τ Y) pre R r P .zero) y → WNF x → Lt x (.Psi .zero π X) →
      (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w y) →
      ∀ z a, x = .Psi z τ a → Lt a X → Lt a Y ∨ (a = Y ∧ Lt z (oadd (ofSummands pre) R)) ∨ Lt x y) :
    SeqC (.Psi .zero π X) (.app π (.idx τ Y) pre R r P .zero) := by
  have o := idx_app C G hRI h0 h1 hRp hRs hRsz hPs hPπ hPA hPfr
  have hπF := C.hπF
  have hN' : NFL (pre ++ [R]) := by
    have h := G.hN
    rw [show pre ++ R :: rest = (pre ++ [R]) ++ rest by simp] at h
    exact nfl_append_left h
  have hpreF := G.hpreF
  refine cof_idx C.ht G.hτF G.hτt C.hle hτfr hsI (fun y hy => by
    obtain ⟨P', x, -, e, -⟩ := o.form y hy
    exact ⟨_, e⟩) (fun hd => ?_) (fun σ hd => ?_) hlow hcls
  · -- `ω` 型：加数の共終数で分ける
    have hRI' := hRI
    unfold SeqI at hRI'
    cases hr : r.dom with
    | zero => exact absurd hr h0
    | one => exact absurd hr h1
    | omega =>
      rw [hr] at hRI'
      exact idxS_nat hN' G.hPF hr (fun n => (hRI'.1.good n).1) (fun n => (hRI'.1.good n).2.2) hRC
    | big σ =>
      rw [hr] at hRI'
      obtain ⟨hBW, hBS, hreg⟩ := hRI'
      have hB : BigInv R σ r := ⟨hBW.1, hBS hRp⟩
      have hσF := hB.1.hσF
      have hσπ : ¬ Lt σ π := fun h' => by
        rw [app_dom_big_lt hr (ltB_iff.mpr h')] at hd
        cases hd
      have hlt' : ltB σ π = false := by
        cases e : ltB σ π with
        | false => rfl
        | true => exact absurd (ltB_iff.mp e) hσπ
      rcases hreg with hσt | ⟨m, rfl⟩
      · have hne : σ ≠ π := fun e => by
          have h2 := size_le_of_mem_subs hB.1.hσs
          rw [e] at h2
          omega
        have hπσ : Le π σ := le_of_not_ltY hσF hπF hσπ
        have hμπ := C.hμσ π hπF (Or.inl rfl)
        have hσC := hB.1.hσC μ π G.hμF hπF (G.parts hμπ).1
        have htσ : WNF (.Psi .zero σ μ) :=
          wnf_psi0 hσF hσt G.hμF (C.hμσ σ hσF hπσ) fun q hq => (arg_of_inC hq hσC hσπ).2
        have hR0 : Lt .zero R := lt_of_le_of_ltY WNF.zero G.hPF G.hRF (zero_le _) G.hPR
        have H : DiagHyp .zero σ μ .zero .zero pre rest R r :=
          { ht := htσ, hsum := G.hsum, hRU := hB.1, hRG := hB.2, hGF := WNF.zero
            hGσ := zero_lt hσt.ne_zero, hGs := by simp [isSucc, summands], hQF := WNF.zero, hQR := hR0
            hQσ := zero_lt hσt.ne_zero
            hI := IdxHyp.zero htσ, hξ := zero_le _ }
        -- `σ ≥ π` なら `σ ≥ τ`
        have hτσ : Le τ σ := le_of_not_ltY hσF G.hτF fun hστ => hσπ (C.ltT σ hσF hστ fun g d hT => by
          obtain ⟨hg, hd2, -, -, -, -, -, h5⟩ := C.hT g d hT
          exact hB.1.hσC g d hg hd2 (G.parts h5).1)
        exact idxS_out G H hr hlt' hne hRC hτΩ hτσ fun m e => IsTgt.ne_K hσt m e
      · exact idxS_K C G hr hlt' hB hPπ hRC hτΩ
  · -- 共終数が `π` 未満
    have hr : r.dom = .big σ ∧ Lt σ π := by
      cases hr : r.dom with
      | big σ' =>
        by_cases h' : Lt σ' π
        · rw [app_dom_big_lt hr (ltB_iff.mpr h')] at hd
          cases hd
          exact ⟨rfl, h'⟩
        · have hlt' : ltB σ' π = false := by
            cases e : ltB σ' π with
            | false => rfl
            | true => exact absurd (ltB_iff.mp e) h'
          rw [app_dom_big_ge hr hlt'] at hd
          cases hd
      | _ =>
        rw [app_dom_nat (fun σ' e => by rw [hr] at e; cases e)] at hd
        cases hd
    obtain ⟨hr, -⟩ := hr
    have hRI' := hRI
    unfold SeqI at hRI'
    rw [hr] at hRI'
    have hU := hRI'.1.1
    have hRC' : ∀ x β, WNF x → Lt x R → WNF β → Lt β σ → Cl σ β → (∀ f, f ∈ fr σ x → Lt f β) →
        Lt x (r.big β) := by
      have := hRC
      unfold SeqC at this
      rwa [hr] at this
    intro z β hz hzT hβ hβσ hCl hfr
    obtain ⟨z', hz', hz'R, hsub, hle⟩ := lt_oadd_split hN' hz hzT
    have hxF := (hU.good.1 β hβ hβσ).1
    have h1' : Lt z' (r.big β) := hRC' z' β hz' hz'R hβ hβσ hCl fun f hf => by
      obtain ⟨u, hu, hfu⟩ := (mem_fr_iff hz').mp hf
      exact hfr f ((mem_fr_iff hz).mpr ⟨u, hsub u hu, hfu⟩)
    refine ⟨approx pre P (r.big β), ?_, ?_⟩
    · show (Gen.idx τ Y).ap (combine (.idx τ Y) pre .zero P (r.big β)) = _
      rw [combine_idx hxF G.hPF]
      rfl
    · exact lt_of_lt_of_leY hz (wnf_oadd hpreF hxF) (wnf_oadd hpreF (wnf_nsum hxF G.hPF))
        (lt_of_le_of_ltY hz (wnf_oadd hpreF hz') (wnf_oadd hpreF hxF) hle (oadd_lt_oadd hpreF hz' hxF h1'))
        (le_approx0 hpreF G.hPF hxF)

end RTKA.Fund
