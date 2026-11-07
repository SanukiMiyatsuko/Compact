import Compact.FS.CofLvl

/-! 共終数が大きい葉と、種の主張。

* `leaf_big`・`argB_app`：共終数 `σ < ceil` の列。`a < pre ⊕ R` は `R` の共終性で `a < pre ⊕ R[β]`。
* `seed_lt`（種の主張）：`X` の最後の加数が種 `p`（`X` の最大の前線の元で `y₀ < p`）なら、`p = Ψ^{s₁}_{π₁}(φ)` で
  `t < π₁`、`X ≤ φ`、`π ∈ C(φ, p)`。したがって `π` への崩壊で引数が `X` 未満、成分の前線が `p` 未満のものは `p` 未満（c1）。
  `p = Ξ_m(φ)` は `wit_psi_xi` と `sub_lt_first` で起こらない。 -/

namespace RTKA.Fund

open Tm W

/-- 共終数が大きい崩壊の列の共終性 -/
theorem leaf_big {π X ξ τ T σ : Tm} {s : SeqD} (ht : WNF (.Psi .zero π X)) (hτt : IsTgt τ) (hπτ : Le π τ)
    (hτfr : ∀ u, u ∈ fr τ τ → u ∈ fr π π) (hσF : WNF σ)
    (hU : BigUB (.Psi .zero π X) σ s) (hG : BigGap (.Psi .zero π X) σ s)
    (hform : ∀ β, WNF β → Lt β σ → ∃ A, s.big β = .Psi ξ τ A)
    (hS : ∀ a β, WNF a → Lt a T → WNF β → Lt β σ → Cl σ β → (∀ f, f ∈ fr σ a → Lt f β) →
      ∃ A, s.big β = .Psi ξ τ A ∧ Lt a A)
    (hlow : ∀ x β, WNF x → Lt x (.Psi .zero π X) → WNF β → Lt β σ → Cl σ β →
      (∀ f, f ∈ fr σ x → Lt f β) → (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w (s.big β)) →
      Lt (.Psi .zero π X) (tgtN x) → Lt (tgtN x) τ → Le π (tgtN x) → Lt x (s.big β))
    (hN : ∀ x β, WNF x → Lt x (.Psi .zero π X) → WNF β → Lt β σ → Cl σ β →
      (∀ f, f ∈ fr σ x → Lt f β) → (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w (s.big β)) →
      ∀ s' a, x = .Psi s' τ a → Lt a X → ¬ Lt a T → Lt x (s.big β)) :
    ∀ x β, WNF x → Lt x (.Psi .zero π X) → WNF β → Lt β σ → Cl σ β → (∀ f, f ∈ fr σ x → Lt f β) →
      Lt x (s.big β) := by
  have hYF : ∀ β, WNF β → Lt β σ → WNF (s.big β) := fun β hβ hβσ => (hU.good.1 β hβ hβσ).1
  refine cof_big hσF (fun β hβ hβσ hCl => Cl.le_big hCl hU hβ hβσ) hYF
    fun x β hx hxt hβ hβσ hCl hfr hσx hpar => ?_
  obtain ⟨A, hA⟩ := hform β hβ hβσ
  rcases leaf_one ht hτt hπτ hτfr (hYF β hβ hβσ) hA (fun v hv hne hl => hG β hβ hβσ v hv hne hl) hx hxt
    hpar with h | ⟨a, harg, haX, -, -, htk, hπk, hkτ | ⟨s', rfl⟩⟩
  · exact h
  · exact hlow x β hx hxt hβ hβσ hCl hfr hpar htk hkτ hπk
  · have haF := wnf_of_argR hx harg
    by_cases haT : Lt a T
    · obtain ⟨B, hB, haB⟩ := hS a β haF haT hβ hβσ hCl fun f hf => hfr f (fr_arg hσF hx hσx harg hf)
      have hyn := hYF β hβ hβσ
      rw [hB] at hyn ⊢
      have hτF := hyn.psi.piF
      exact (Clo.psi hyn).lt hx
        (lt_transY hx ht hτF hxt (lt_of_lt_of_leY ht ht.psi.piF hτF (lt_psi_targetY ht) hπτ))
        (fun w hw => by
          have hwt := lt_transY (hx.of_mem_subs (parL_sub (parF_sub_parL hw)).1) hx ht (parF_lt hx hw) hxt
          have h1 := hpar w (parF_sub_parL hw) hwt
          rwa [hB] at h1)
        fun a' e => by
          cases harg
          cases e
          exact haB
    · exact hN _ β hx hxt hβ hβσ hCl hfr hpar s' a rfl haX haT

/-- 共終数が目標未満の加数の列の引数の共終性 -/
theorem argB_app {ξ τ P c ceil σ : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ τ) (hN : NFL (pre ++ [R])) (hc : WNF c) (hP : WNF P) (hd : r.dom = .big σ)
    (hU : BigUB R σ r) (hRC : SeqC R r) :
    ∀ a β, WNF a → Lt a (oadd (ofSummands pre) R) → WNF β → Lt β σ → Cl σ β →
      (∀ f, f ∈ fr σ a → Lt f β) → ∃ A, (SeqD.app ceil g pre R r P c).big β = .Psi ξ τ A ∧ Lt a A := by
  have hpreF := wnf_ofSummands (nfl_append_left hN)
  have hRC' : ∀ x β, WNF x → Lt x R → WNF β → Lt β σ → Cl σ β → (∀ f, f ∈ fr σ x → Lt f β) →
      Lt x (r.big β) := by
    have := hRC
    unfold SeqC at this
    rwa [hd] at this
  intro a β ha haT hβ hβσ hCl hfr
  obtain ⟨a', ha', ha'R, hsub, hle⟩ := lt_oadd_split hN ha haT
  have hxF := (hU.good.1 β hβ hβσ).1
  have h1 : Lt a' (r.big β) := hRC' a' β ha' ha'R hβ hβσ hCl fun f hf => by
    obtain ⟨u, hu, hfu⟩ := (mem_fr_iff ha').mp hf
    exact hfr f ((mem_fr_iff ha).mpr ⟨u, hsub u hu, hfu⟩)
  refine ⟨_, app_big_eq hg, ?_⟩
  exact lt_of_lt_of_leY ha (wnf_oadd hpreF hxF) (wnf_oadd hpreF (wnf_nsum (wnf_oadd hc hxF) hP))
    (lt_of_le_of_ltY ha (wnf_oadd hpreF ha') (wnf_oadd hpreF hxF) hle (oadd_lt_oadd hpreF ha' hxF h1))
    (le_approx hpreF hc hP hxF)

/-! ### 種の主張 -/

/-- `X = pre ⊕ R`（加数の並びが `pre ++ [R]`） -/
theorem eq_oadd_of_sum {X R : Tm} {pre : List Tm} (hX : WNF X) (hsum : summands X = pre ++ [R]) :
    X = oadd (ofSummands pre) R := by
  have hN : NFL (pre ++ [R]) := hsum ▸ nfl_summands hX
  have hRN := hN.1 R (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  have hpreN := nfl_append_left hN
  have hge : ∀ s h r, s ∈ pre → summands R = h :: r → leB h s = true := fun s h r hs e => by
    rw [summands_principal hRN.2] at e
    simp only [List.cons.injEq] at e
    rw [← e.1, leB_iff]
    exact le_of_nfl_append (rest := []) hN s hs
  have hs : summands (oadd (ofSummands pre) R) = pre ++ [R] := by
    rw [summands_oadd_pre hpreN hRN.1 hge, summands_principal hRN.2]
  rw [← ofSummands_summands X hX, hsum, ← hs, ofSummands_summands _ (wnf_oadd (wnf_ofSummands hpreN) hRN.1)]

/-- 種の主張：最後の加数が種 `p` のとき、`π` への崩壊で引数が `X` 未満、成分の前線が `p` 未満のものは `p` 未満 -/
theorem seed_lt {π X p x₀ s a : Tm} {pre : List Tm} (H : Approx1 .zero π X .zero pre [] p x₀)
    (hx0 : x₀ = .zero → ∀ v, v ∈ subs p → v = p)
    (hG : ∀ v, v ∈ subs p → v ≠ p → Lt v p → Lt v x₀)
    (hlt : Lt (.Psi .zero π (approx pre .zero x₀)) p) (hpm : p ∈ fr π X)
    (hfr : ∀ f, f ∈ fr π X → Le f p)
    (hx : WNF (.Psi s π a)) (hxt : Lt (.Psi s π a) (.Psi .zero π X)) (haX : Lt a X)
    (hF : ∀ w, w ∈ parF (.Psi s π a) → Lt w p) :
    Lt (.Psi s π a) p := by
  have ht := H.ht
  have hπF := H.hπF
  have hX := H.hX
  have hpF := H.hRF
  have hy₀ := H.hnf
  have hBF := H.hAF
  have hpπ : Lt p π := (fr_spec hpm).2
  have hpt : Lt p (.Psi .zero π X) := FWOrder.k2 ht p hpm
  have hsubp : ∀ v, v ∈ subs p → v ≠ p → Lt v p → Lt v (.Psi .zero π (approx pre .zero x₀)) :=
    fun v hv hne hvp => sub_lt_first H hx0 hG hlt hpπ hpt hfr hv hne
      (lt_transY (hpF.of_mem_subs hv) hpF ht hvp hpt)
  have hlev1 := lev_le_of_lt_gen hlt
  have hlev2 := lev_le_of_lt_gen hpπ
  have hP := hx.psi
  rcases fr_node hpm with ⟨m, φ, rfl⟩ | ⟨s₁, π₁, φ, rfl⟩
  · exfalso
    simp only [lev] at hlev1 hlev2
    have hl : lev π = m := by omega
    obtain ⟨-, w, hw, hn⟩ := wit_psi_xi hy₀ hpF hl hlt hpπ
    have hws : w ∈ subs (.Xi m φ) := subs_xi (fr_spec hw).1
    have hwne : w ≠ .Xi m φ := ne_of_size_lt (by
      have := size_le_of_mem_subs (fr_spec hw).1
      simp only [Tm.size]
      omega)
    exact hn (hsubp w hws hwne (FWOrder.k2x hpF w hw))
  have hQ := hpF.psi
  simp only [lev] at hlev1 hlev2
  have hl : lev π = lev π₁ := by omega
  have hφF := hQ.aF
  rcases (lt_psi_psiY hl hlt.ne).mp hlt with h | ⟨-, hyπ₁, h1 | h2 | h3 | h4⟩
  · exact absurd hpπ h
  · obtain ⟨hBφ, -, -, hπC⟩ := h1
    -- `t < π₁`
    have hπ₁s : π₁ ∈ subs (.Psi s₁ π₁ φ) := subs_psi_p (self_mem_subs π₁)
    have hπ₁ne : π₁ ≠ .Psi s₁ π₁ φ := ne_of_size_lt (by simp only [Tm.size]; omega)
    have htπ₁ : Lt (.Psi .zero π X) π₁ := by
      rcases triY ht hQ.piF with h' | h' | h'
      · exact h'
      · exfalso
        have h7 : π₁.size < (Tm.Psi s₁ π₁ φ).size := by simp only [Tm.size]; omega
        have h8 := size_le_of_mem_subs (fr_spec hpm).1
        have h9 : X.size < (Tm.Psi .zero π X).size := by simp only [Tm.size]; omega
        rw [h'] at h9
        omega
      · exact absurd (sub_lt_first H hx0 hG hlt hpπ hpt hfr hπ₁s hπ₁ne h') (Lt.asymmY hy₀ hQ.piF hyπ₁)
    -- `X ≤ φ`
    have hXφ : Le X φ := by
      refine le_of_not_ltY hφF hX fun hφX => ?_
      have hsum : summands X = pre ++ [.Psi s₁ π₁ φ] := H.hsum
      have hN : NFL (pre ++ [.Psi s₁ π₁ φ]) := hsum ▸ nfl_summands hX
      rw [eq_oadd_of_sum hX hsum] at hφX
      have hpreF := H.hpreF
      have hx₀F := H.hx
      have hB : approx pre .zero x₀ = oadd (ofSummands pre) x₀ := approx_zero_eq hx₀F
      rw [hB] at hBφ hBF
      rcases lt_oadd_cases hN hφF hφX with h' | ⟨φ', hφ'F, hφ'p, hsφ, e⟩
      · exact Lt.asymmY hBF hφF hBφ (lt_of_lt_of_leY hφF hpreF hBF h' (le_oadd_left hpreF hx₀F))
      · have hx₀φ' : Lt x₀ φ' := by
          refine (le_of_not_ltY hφ'F hx₀F fun h'' => ?_).resolve_left fun e' => ?_
          · rw [e] at hBφ
            exact Lt.asymmY hBF (wnf_oadd hpreF hφ'F) hBφ (oadd_lt_oadd hpreF hφ'F hx₀F h'')
          · rw [e, e'] at hBφ
            exact Lt.irrefl _ hBφ
        have hφ'0 : φ' ≠ .zero := fun e' => by
          rw [e'] at hx₀φ'
          exact not_lt_zero _ hx₀φ'
        have hφ's : φ' ∈ subs φ := by
          have := tail_mem_subs hφF hsφ (summands_ne_nil hφ'0)
          rwa [ofSummands_summands φ' hφ'F] at this
        have hφ'ne : φ' ≠ .Psi s₁ π₁ φ := ne_of_size_lt (by
          have := size_le_of_mem_subs hφ's
          simp only [Tm.size]
          omega)
        exact Lt.asymmY hx₀F hφ'F hx₀φ' (hG φ' (subs_psi_a hφ's) hφ'ne hφ'p)
    -- 結論（c1）
    have haφ : Lt a φ := lt_of_lt_of_leY hP.aF hX hφF haX hXφ
    have hxπ₁ : Lt (.Psi s π a) π₁ := lt_transY hx ht hQ.piF hxt htπ₁
    have haC : inC a φ (.Psi s₁ π₁ φ) = true :=
      inC_of_fr_lt hP.aF hπF hpF hP.aF hφF hP.Ca (Or.inr hpπ) (Or.inr haφ) fun w hw =>
        hF w (by simp [parF, hw])
    have hsC : inC s φ (.Psi s₁ π₁ φ) = true :=
      inC_of_fr_lt hP.xiF hπF hpF hP.aF hφF hP.Cxi (Or.inr hpπ) (Or.inr haφ) fun w hw =>
        hF w (by simp [parF, hw])
    have hne : Tm.Psi s π a ≠ .Psi s₁ π₁ φ := fun e => by
      cases e
      exact Lt.irrefl _ haφ
    exact (lt_psi_psiY hl hne).mpr (Or.inr ⟨hpπ, hxπ₁, Or.inl ⟨haφ, haC, hsC, hπC⟩⟩)
  · exfalso
    obtain ⟨hle, hn⟩ := h2
    obtain ⟨w, hw, hn'⟩ := wit_c2 hpF hy₀ hBF (le_of_ne_gtY hφF hBF hle) hyπ₁ hn
    have hws : w ∈ subs (.Psi s₁ π₁ φ) ∧ Lt w (.Psi s₁ π₁ φ) := by
      rcases hw with hw | hw | hw
      · exact ⟨subs_psi_a (fr_spec hw).1, FWOrder.k2 hpF w hw⟩
      · exact ⟨subs_psi_p (fr_spec hw).1, FWOrder.k2t hpF w hw⟩
      · exact ⟨subs_psi_s (fr_spec hw).1, FWOrder.k2s hpF w hw⟩
    exact hn' (hsubp w hws.1 hws.2.ne hws.2)
  · exfalso
    obtain ⟨heq, -, -, -⟩ := h3
    have e : approx pre .zero x₀ = φ := FWOrder.eq hBF hφF heq
    have hx₀F := H.hx
    by_cases hx₀0 : x₀ = .zero
    · have h5 := congrArg Tm.size (hx0 hx₀0 φ (subs_psi_a (self_mem_subs φ)))
      simp only [Tm.size] at h5
      omega
    · have hpreN := H.hpreN
      have hx₀R := H.hxR
      have hge : ∀ s h r, s ∈ pre → summands x₀ = h :: r → leB h s = true :=
        fun s' h r hs he => head_le_pre (rest := []) H.hN hx₀F hx₀R s' h r hs he
      have hsφ : summands φ = pre ++ summands x₀ := by
        rw [← e, approx_zero_eq hx₀F, summands_oadd_pre hpreN hx₀F hge]
      have hx₀s : x₀ ∈ subs φ := by
        have := tail_mem_subs hφF hsφ (summands_ne_nil hx₀0)
        rwa [ofSummands_summands x₀ hx₀F] at this
      have hx₀ne : x₀ ≠ .Psi s₁ π₁ φ := ne_of_size_lt (by
        have := size_le_of_mem_subs hx₀s
        simp only [Tm.size]
        omega)
      exact Lt.irrefl _ (hG x₀ (subs_psi_a hx₀s) hx₀ne hx₀R)
  · exact absurd h4.1 (not_lt_zero _)

end RTKA.Fund
