import Compact.FS.CofZ

/-! 添字の閉包 `Ψ^{pre ⊕ (R[n] # P)}_τ(Y)` の列の、添字の共終性（`IdxS`）。

* `ω` 型の加数：`R` の共終性。
* `K_m` 型（値の帰還の塔 `idxT`）：`β = y_N` は `K_m` で閉じた点。添字の `K_m` についての前線は、`τ` 未満なら `x` の成分の前線、
  `τ` 以上なら補題 Z で起こらない。
* 外に足す型（`σ ≥ π`、`σ ≠ K`）：補題 Z・W で `σ = K_L⁺`、`m(τ) ≤ T`。塔は `τ` を越えるので、添字は `C(m(τ), γ_1)` に入り、
  `Tow.hull` で前線が塔の中。 -/

namespace RTKA.Fund

open Tm W

/-- `τ` への崩壊は `K_{lev τ}` で閉じた点 -/
theorem Cl_K_psi {ξ τ A : Tm} (hy : WNF (.Psi ξ τ A)) (hτΩ : ∀ c, τ ≠ .Om c) :
    Cl (.K (lev τ)) (.Psi ξ τ A) := by
  have hOF : IsOF (.Psi ξ τ A) := IsOF.psi hy hτΩ
  have hyp : isPrincipal (Tm.Psi ξ τ A) = true := rfl
  have hL : 1 ≤ lev τ := lev_posY hy.psi.piF (IsTgt.ne_zero hy.psi.tgt)
  refine ⟨fun d hd => ?_, fun x hx hxK hfr => ?_⟩
  · cases e : inC (.Psi ξ τ A) .zero d with
    | false => rfl
    | true =>
      rcases inC_psi_iff.mp e with h | ⟨-, -, -, h⟩
      · exact absurd h hd
      · exact absurd h (not_lt_zero _)
  · induction hn : x.size using Nat.strongRecOn generalizing x with
    | ind n ih =>
      cases x with
      | zero => exact zero_lt (by intro e; cases e)
      | one => exact one_lt_of_prin hy rfl (by intro e; cases e)
      | K j =>
        have hj := (lt_K_iffY hx hL).mp hxK
        simp only [lev] at hj
        exact K_lt_of_lev hy hyp rfl (by simp only [lev]; omega)
      | plus a b =>
        obtain ⟨ha, hb, -, -⟩ := hx.plus
        refine (lt_plus_prin_iffY hx hyp).mpr (ih a.size (by rw [← hn]; simp only [Tm.size]; omega) a ha
          (lt_transY ha hx (WNF.K' hL) (lt_plus_leftY hx) hxK) (fun f hf => hfr f ?_) rfl)
        rw [fr, List.mem_append]
        exact Or.inl hf
      | Om e =>
        have heF := hx.om.1
        refine (lt_om_OFG hOF).mpr (ih e.size (by rw [← hn]; simp only [Tm.size]; omega) e heF
          (lt_transY heF hx (WNF.K' hL) hx.om.2.2 hxK) (fun f hf => hfr f ?_) rfl)
        rw [fr]
        exact hf
      | Xi j b =>
        refine hfr _ ?_
        rw [fr]
        simp [hxK]
      | Psi s k a =>
        refine hfr _ ?_
        rw [fr]
        simp [hxK]

/-- `pre ⊕ x ≤ pre ⊕ (x # P)` -/
theorem le_approx0 {pre : List Tm} {P x : Tm} (hpreF : WNF (ofSummands pre)) (hP : WNF P) (hx : WNF x) :
    Le (oadd (ofSummands pre) x) (approx pre P x) := by
  have h := le_approx hpreF WNF.zero hP hx
  rwa [zero_oadd hx] at h

/-- 添字の閉包の列の添字の共終性 -/
def IdxS (t T τ Y : Tm) (s : SeqD) : Prop :=
  ∀ z N, WNF (.Psi z τ Y) → Lt (.Psi z τ Y) t → Lt z T →
    (∀ w, w ∈ parF (.Psi z τ Y) → Lt w (s.nat N)) →
    ∃ n ξ, N ≤ n ∧ s.nat n = .Psi ξ τ Y ∧ Lt z ξ

/-- `ω` 型の加数 -/
theorem idxS_nat {t τ Y P ceil : Tm} {pre : List Tm} {R : Tm} {r : SeqD} (hN : NFL (pre ++ [R])) (hP : WNF P)
    (hd : r.dom = .omega) (hF : ∀ n, WNF (r.nat n)) (hmo : ∀ n, Lt (r.nat n) (r.nat (n + 1)))
    (hRC : SeqC R r) : IdxS t (oadd (ofSummands pre) R) τ Y (.app ceil (.idx τ Y) pre R r P .zero) := by
  have hpreF := wnf_ofSummands (nfl_append_left hN)
  have hRC' : ∀ x, WNF x → Lt x R → ∃ n, Lt x (r.nat n) := by
    have := hRC
    unfold SeqC at this
    rwa [hd] at this
  have hdom : ∀ σ, r.dom ≠ .big σ := fun σ e => by
    rw [hd] at e
    cases e
  intro z N hz _ hzT _
  have hzF := hz.psi.xiF
  obtain ⟨z', hz', hz'R, -, hle⟩ := lt_oadd_split hN hzF hzT
  obtain ⟨n₀, hn₀⟩ := hRC' z' hz' hz'R
  have hn : Lt z' (r.nat (max n₀ N)) :=
    lt_of_lt_of_leY hz' (hF n₀) (hF _) hn₀ (mono_le hF hmo (Nat.le_max_left _ _))
  refine ⟨max n₀ N, approx pre P (r.nat (max n₀ N)), Nat.le_max_right _ _, ?_, ?_⟩
  · rw [app_nat_of_not_big hdom, combine_idx (hF _) hP]
    rfl
  · exact lt_of_lt_of_leY hzF (wnf_oadd hpreF (hF _)) (wnf_oadd hpreF (wnf_nsum (hF _) hP))
      (lt_of_le_of_ltY hzF (wnf_oadd hpreF hz') (wnf_oadd hpreF (hF _)) hle (oadd_lt_oadd hpreF hz' (hF _) hn))
      (le_approx0 hpreF hP (hF _))

/-- 値の帰還の塔（`idx_K_out` の前半） -/
theorem idx_K_data {π X τ Y μ P : Tm} {T : Tm → Tm → Prop} {pre rest : List Tm} {R : Tm} {r : SeqD} {m : Nat}
    (C : MCtx π X τ Y μ T) (G : IdxG τ Y μ P pre rest R) (hd : r.dom = .big (.K m))
    (hlt : ltB (.K m) π = false) (hB : BigInv R (.K m) r) (hPπ : Lt P π) :
    lev τ = m ∧ (∀ k, WNF (idxT τ Y pre r P k) ∧ Lt (idxT τ Y pre r P k) π) ∧
      ∀ n, (SeqD.app π (.idx τ Y) pre R r P .zero).nat n = idxT τ Y pre r P (n + 1) := by
  have hU := hB.1
  have hτF := G.hτF
  have hπF := C.hπF
  have hτt := G.hτt
  have hPF := G.hPF
  have hmF := WFY.WNF.mi hτF
  have hm : 1 ≤ m := hU.hσF.k
  have hKF : WNF (.K m) := WNF.K' hm
  have hnl : ¬ Lt (.K m) π := fun h => by
    rw [ltB_iff.mpr h] at hlt
    cases hlt
  have hτK : Lt τ (.K m) := C.τK m hm hnl
  have hπK : Le π (.K m) := Or.inr (lt_of_le_of_ltY hπF hτF hKF C.hle hτK)
  have hRμ : Le R μ := by
    have := le_ofSummands_of_mem (nfl_summands G.hμF) G.hRm
    rwa [ofSummands_summands μ G.hμF] at this
  have hKμ : Le (.K m) μ := le_transY hKF G.hRF G.hμF hU.hσle hRμ
  have hKY : Le (.K m) Y := le_transY hKF G.hμF G.hYF hKμ G.hμY
  have hlτ : 1 ≤ lev τ := lev_posY hτF (IsTgt.ne_zero hτt)
  have hμS : Le μ (succK (lev τ)) :=
    le_transY G.hμF hmF (WNF.succK hlτ) G.hμm (mi_le_succK τ hτF hτt)
  have hl : lev τ = m := by
    have h1 : lev τ ≤ m := (lt_K_iffY hτF hm).mp hτK
    have h2 : lev (Tm.K m) ≤ lev (succK (lev τ)) := by
      rcases le_transY hKF G.hμF (WNF.succK hlτ) hKμ hμS with e | e
      · exact Nat.le_of_eq (congrArg lev e)
      · exact lev_le_of_lt_gen e
    have h3 : lev (Tm.K m) = m + 1 := rfl
    have h4 : lev (succK (lev τ)) = lev τ + 1 := rfl
    omega
  have hKS : Le μ (succK m) := by
    rw [← hl]
    exact hμS
  have hR0 : Lt .zero R := lt_of_le_of_ltY WNF.zero hPF G.hRF (zero_le _) G.hPR
  have hτ0 : Lt .zero τ := lt_of_le_of_ltY WNF.zero hPF hτF (zero_le _) G.hPτ
  have hK0 : Lt .zero (.K m) := lt_transY WNF.zero hτF hKF hτ0 hτK
  have h1K : Lt .one (.K m) := (lt_K_iffY WNF.one hm).mpr hm
  have G0 : IdxG τ Y μ .zero pre rest R :=
    ⟨G.hv, G.hYF, G.hYC, G.hτY, G.hμF, G.hsum, G.hμY, G.hμm, G.hμ1, G.hμ2, WNF.zero, hR0, hτ0⟩
  have hμpos : Lt .zero μ := lt_of_lt_of_leY WNF.zero hKF G.hμF hK0 hKμ
  have hμ0 : μ ≠ .zero := fun e => by
    rw [e] at hμpos
    exact not_lt_zero _ hμpos
  have hμξ : WNF (.Xi m μ) := wnf_xi_mk hm G.hμF hμ0 (ne_gt_of_le hKS) (C.hμσ _ hKF hπK)
  have hR1 : R ≠ .one := fun e => by
    have h := hU.hσle
    rw [e] at h
    exact not_lt_of_leY hKF WNF.one h h1K
  have X0 : XiG m μ .zero .zero pre rest R := ⟨hμξ, G.hsum, WNF.zero, hR0, hK0, Or.inl rfl, hR1⟩
  have hY0 : Lt .zero Y := lt_of_lt_of_leY WNF.zero hKF G.hYF hK0 hKY
  have hm0 : Lt .zero (mi τ) := lt_of_lt_of_leY WNF.zero G.hμF hmF hμpos G.hμm
  have h1Y : Lt .one Y := lt_of_lt_of_leY WNF.one hKF G.hYF h1K hKY
  have h1m : Lt .one (mi τ) :=
    lt_of_lt_of_leY WNF.one hKF hmF h1K (le_transY hKF G.hμF hmF hKμ G.hμm)
  have hγτ : ∀ {γ : Tm}, WNF γ → Lt γ π → Lt γ τ := fun hγ h => lt_of_lt_of_leY hγ hπF hτF h C.hle
  have hγK : ∀ {γ : Tm}, WNF γ → Lt γ π → Lt γ (.K m) := fun hγ h =>
    lt_transY hγ hτF hKF (hγτ hγ h) hτK
  have hxF : ∀ {γ : Tm}, WNF γ → Lt γ π → WNF (r.big γ) := fun hγ h =>
    (hU.good.1 _ hγ (hγK hγ h)).1
  have hxR : ∀ {γ : Tm}, WNF γ → Lt γ π → Lt (r.big γ) R := fun hγ h =>
    (hU.good.1 _ hγ (hγK hγ h)).2
  have h1 : ∀ {γ : Tm}, WNF γ → Lt γ π → inC (r.big γ) Y τ = true := fun hγ h =>
    hU.ub Y τ _ G.hYF hτF hγ (hγK hγ h) hY0 (bigOK_none rfl) (G.parts G.hμ1).1
      (WFY.inC_of_ltY _ hγ hτF (hγτ hγ h))
  have h2 : ∀ {γ : Tm}, WNF γ → Lt γ π → inC (r.big γ) (mi τ) τ = true := fun hγ h =>
    hU.ub _ τ _ hmF hτF hγ (hγK hγ h) hm0 (bigOK_none rfl) (G.parts G.hμ2).1
      (WFY.inC_of_ltY _ hγ hτF (hγτ hγ h))
  have hy : ∀ {γ : Tm}, WNF γ → Lt γ π → WNF (.Psi (approx pre .zero (r.big γ)) τ Y) := fun hγ h =>
    G0.nf (hxF hγ h) (hxR hγ h) (h1 hγ h) (h2 hγ h)
  have hAμ : ∀ {γ : Tm}, WNF γ → Lt γ π → Lt (approx pre .zero (r.big γ)) μ := fun hγ h =>
    G0.hAlt (hxF hγ h) (hxR hγ h) G.hμF G.hTμ
  have hAC : ∀ {γ : Tm}, WNF γ → Lt γ π →
      inC (approx pre .zero (r.big γ)) Y (.Psi (approx pre .zero (r.big γ)) τ Y) = true := fun hγ h => by
    have hy' := hy hγ h
    have hP' := hy'.psi
    exact inC_of_fr_lt hP'.xiF hτF hy' G.hYF G.hYF hP'.Cxi (Or.inr (lt_psi_targetY hy')) (Or.inl rfl)
      fun w hw => FWOrder.k2s hy' w hw
  have hlt1 : ∀ {γ : Tm}, WNF γ → Lt γ π → Lt (.Psi (approx pre .zero (r.big γ)) τ Y) π := fun hγ h =>
    C.ltI _ (hy hγ h) (hAμ hγ h) fun g d hT => by
      obtain ⟨hg, hd2, hπd, -, -, -, h4, h5⟩ := C.hT g d hT
      exact G0.inC_A (hxF hγ h) (G.parts h5).2 (hU.ub g d _ hg hd2 hγ (hγK hγ h)
        (lt_of_lt_of_leY WNF.zero G.hYF hg hY0 h4) (bigOK_none rfl) (G.parts h5).1
        (WFY.inC_of_ltY _ hγ hd2 (lt_of_lt_of_leY hγ hπF hd2 h hπd))) (inC_zero _ _)
  have hcl : ∀ {γ : Tm} (k : Nat), WNF γ → Lt γ π →
      Lt (col (.K m) (approx pre .zero (r.big γ)) k) (.Psi (approx pre .zero (r.big γ)) τ Y) := by
    intro γ k hγ h
    have hy' := hy hγ h
    by_cases hA0 : approx pre .zero (r.big γ) = .zero
    · rw [hA0] at hy' ⊢
      rw [col_K_zero]
      exact coll_psiY hy' _ (wnf_xi_one hm) (inC_xi_iff.mpr (Or.inr ⟨inC_one _ _, h1Y⟩))
        (xi_lt_tgt (wnf_xi_one hm) τ hτF hτt hl h1m (inC_one _ _))
    · have hx := hxF hγ h
      have hxR' := hxR hγ h
      have hA : xA .zero pre .zero (r.big γ) = approx pre .zero (r.big γ) :=
        combine_idx (κ := .zero) (γ := .zero) hx WNF.zero
      have hC : inC (r.big γ) (xA .zero pre .zero (r.big γ)) (.K m) = true := by
        refine X0.hCx hx hxR' (hU.pos _ hγ (hγK hγ h)) (hB.2 _ hγ (hγK hγ h)) fun hR _ => ?_
        by_cases hx0 : r.big γ = .zero
        · rw [hx0]
          exact inC_zero _ _
        · exact hU.ub _ _ _ (wnf_oadd G.hpreF (wnf_nsum hx WNF.zero)) hKF hγ (hγK hγ h)
            (approx_pos G.hpreF hx WNF.zero hx0) (bigOK_none rfl) hR
            (WFY.inC_of_ltY _ hγ hKF (hγK hγ h))
      have hX : WNF (.Xi m (approx pre .zero (r.big γ))) := by
        have := X0.nf (by rw [hA]; exact hA0) hx hxR' hC
        rwa [hA] at this
      have hle : leB (approx pre .zero (r.big γ)) (succK m) = true :=
        leB_iff.mpr (ne_gt_of_le (Or.inr (lt_of_lt_of_leY (G0.hAF hx) G.hμF (WNF.succK hm)
          (hAμ hγ h) hKS)))
      rw [col_K_le hA0 hle]
      exact coll_psiY hy' _ hX (inC_xi_iff.mpr (Or.inr ⟨hAC hγ h, G0.hAlt hx hxR' G.hYF G.hTY⟩))
        (xi_lt_tgt hX τ hτF hτt hl (G0.hAlt hx hxR' hmF G.hTm)
          (G0.inC_A hx (G.parts G.hμ2).2 (h2 hγ h) (inC_zero _ _)))
  have htow : ∀ k, WNF (idxT τ Y pre r P k) ∧ Lt (idxT τ Y pre r P k) π := by
    intro k
    induction k with
    | zero => exact ⟨hPF, hPπ⟩
    | succ k ih => exact ⟨hy ih.1 ih.2, hlt1 ih.1 ih.2⟩
  have hA' : ∀ {γ : Tm}, WNF γ → Lt γ π →
      argOf π (.K m) (.idx τ Y) pre R r .zero P γ = approx pre .zero (r.big γ) := fun hγ h => by
    simp only [argOf, canonK, outsideMode, seedOut, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
    exact combine_idx (hxF hγ h) WNF.zero
  have hgam : ∀ n, gam π (.K m) (.idx τ Y) pre R r .zero P n = idxT τ Y pre r P n := by
    intro n
    induction n with
    | zero => simp only [gam, canonK, outsideMode, Bool.false_eq_true, ↓reduceIte, idxT]
    | succ k ih =>
      have hw := htow k
      have h3 : ltB (col (.K m) (approx pre .zero (r.big (idxT τ Y pre r P k))) k)
          ((Gen.idx τ Y).ap (approx pre .zero (r.big (idxT τ Y pre r P k)))) = true :=
        ltB_iff.mpr (hcl k hw.1 hw.2)
      have h4 : ltB ((Gen.idx τ Y).ap (approx pre .zero (r.big (idxT τ Y pre r P k)))) (.K m) = true :=
        ltB_iff.mpr (lt_transY (hy hw.1 hw.2) hτF hKF (lt_psi_targetY (hy hw.1 hw.2)) hτK)
      simp only [gam, canonK, outsideMode, Bool.false_eq_true, ↓reduceIte]
      rw [ih, hA' hw.1 hw.2, h3, h4]
      rfl
  refine ⟨hl, htow, fun n => ?_⟩
  rw [app_nat_big hd hlt, hgam n, hA' (htow n).1 (htow n).2]
  rfl

/-- `K_m` 型の加数（値の帰還の塔） -/
theorem idxS_K {π X τ Y μ P t : Tm} {T : Tm → Tm → Prop} {pre rest : List Tm} {R : Tm} {r : SeqD} {m : Nat}
    (C : MCtx π X τ Y μ T) (G : IdxG τ Y μ P pre rest R) (hd : r.dom = .big (.K m))
    (hlt : ltB (.K m) π = false) (hB : BigInv R (.K m) r) (hPπ : Lt P π) (hRC : SeqC R r)
    (hτΩ : ∀ c, τ ≠ .Om c) : IdxS t (oadd (ofSummands pre) R) τ Y (.app π (.idx τ Y) pre R r P .zero) := by
  obtain ⟨hl, htow, he⟩ := idx_K_data C G hd hlt hB hPπ
  have hτF := G.hτF
  have hπF := C.hπF
  have hm : 1 ≤ m := hB.1.hσF.k
  have hKF : WNF (.K m) := WNF.K' hm
  have hτK : Lt τ (.K m) := (lt_K_iffY hτF hm).mpr (Nat.le_of_eq hl)
  have hN : NFL (pre ++ [R]) := by
    have h := G.hN
    rw [show pre ++ R :: rest = (pre ++ [R]) ++ rest by simp] at h
    exact nfl_append_left h
  have hpreF := G.hpreF
  have hRC' : ∀ x β, WNF x → Lt x R → WNF β → Lt β (.K m) → Cl (.K m) β →
      (∀ f, f ∈ fr (.K m) x → Lt f β) → Lt x (r.big β) := by
    have := hRC
    unfold SeqC at this
    rwa [hd] at this
  intro z N hz _ hzT hpar
  have hP := hz.psi
  have hzF := hP.xiF
  obtain ⟨z', hz', hz'R, hsub, hle⟩ := lt_oadd_split hN hzF hzT
  -- `β = y_N`
  obtain ⟨hβF, hβπ⟩ := htow (N + 1)
  have hβτ : Lt (idxT τ Y pre r P (N + 1)) τ := lt_of_lt_of_leY hβF hπF hτF hβπ C.hle
  have hβK : Lt (idxT τ Y pre r P (N + 1)) (.K m) := lt_transY hβF hτF hKF hβτ hτK
  have hβCl : Cl (.K m) (idxT τ Y pre r P (N + 1)) := by
    have e : idxT τ Y pre r P (N + 1) = .Psi (approx pre .zero (r.big (idxT τ Y pre r P N))) τ Y := rfl
    have h := Cl_K_psi (by rw [← e]; exact hβF) hτΩ
    rw [hl] at h
    rw [e]
    exact h
  have hfr : ∀ f, f ∈ fr (.K m) z' → Lt f (idxT τ Y pre r P (N + 1)) := by
    intro f hf
    have hfz : f ∈ fr (.K m) z := by
      obtain ⟨u, hu, hfu⟩ := (mem_fr_iff hz').mp hf
      exact (mem_fr_iff hzF).mpr ⟨u, hsub u hu, hfu⟩
    have hfF := hzF.of_mem_subs (fr_spec hfz).1
    by_cases hfτ : Lt f τ
    · have h1 : f ∈ fr τ z := fr_of_fr hKF hτF (Or.inr hτK) hzF hfz hfτ
      have h2 := hpar f (by simp [parF, h1])
      rwa [he N] at h2
    · exfalso
      have hfC : inC f (mi τ) τ = true := fr_of_inC z (fun w _ hn hwτ => hn (lt_transY
        (hzF.of_mem_subs (by assumption)) hτF hKF hwτ hτK)) hP.mC f hfz
      have := not_lt_K_of_inC_mi hτF G.hτt hτΩ f hfF hfC (le_of_not_ltY hfF hτF hfτ)
      rw [hl] at this
      exact this (fr_spec hfz).2
  have h1 := hRC' z' _ hz' hz'R hβF hβK hβCl hfr
  have hxF : WNF (r.big (idxT τ Y pre r P (N + 1))) := (hB.1.good.1 _ hβF hβK).1
  refine ⟨N + 1, _, by omega, by rw [he (N + 1)]; rfl, ?_⟩
  rw [approx_zero_eq hxF]
  exact lt_of_le_of_ltY hzF (wnf_oadd hpreF hz') (wnf_oadd hpreF hxF) hle (oadd_lt_oadd hpreF hz' hxF h1)


/-- 外に足す型の加数（`τ ≤ σ`、`σ` は `K` でない）：`σ = K_L⁺` で、添字の前線は塔の中 -/
theorem idxS_out {π τ Y μ P σ t : Tm} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (G : IdxG τ Y μ P pre rest R) (H : DiagHyp .zero σ μ .zero .zero pre rest R r)
    (hd : r.dom = .big σ) (hlt : ltB σ π = false) (hne : σ ≠ π) (hRC : SeqC R r)
    (hτΩ : ∀ c, τ ≠ .Om c) (hτσ : Le τ σ) (hσK : ∀ m, σ ≠ .K m) :
    IdxS t (oadd (ofSummands pre) R) τ Y (.app π (.idx τ Y) pre R r P .zero) := by
  have Tw := H.tow hd hRC
  have hτF := G.hτF
  have hσF := H.hσF
  have hσt := H.ht.psi.tgt
  have hmF := WFY.WNF.mi hτF
  have hL : 1 ≤ lev τ := lev_posY hτF (IsTgt.ne_zero G.hτt)
  have hKF := WNF.K' hL
  have hTF := Tw.hTF
  have hRμ : Le R μ := by
    have := le_ofSummands_of_mem (nfl_summands G.hμF) G.hRm
    rwa [ofSummands_summands μ G.hμF] at this
  -- `σ ∈ C(m(τ), τ)`、補題 Z・W
  have hσC : inC σ (mi τ) τ = true := H.hRU.hσC _ _ hmF hτF (G.parts G.hμ2).1
  have hKσ : Lt (.K (lev τ)) σ := by
    rcases le_of_not_ltY hσF hKF (not_lt_K_of_inC_mi hτF G.hτt hτΩ σ hσF hσC hτσ) with e | h
    · exact absurd e.symm (hσK _)
    · exact h
  have hσR : Le σ R := H.hRU.hσle
  have hσμ : Le σ μ := le_transY hσF H.hRF G.hμF hσR hRμ
  have hμS : Le μ (succK (lev τ)) :=
    le_transY G.hμF hmF (WNF.succK hL) G.hμm (mi_le_succK τ hτF G.hτt)
  have hσe : σ = succK (lev τ) := tgt_eq_succK hσF hσt hL hKσ (le_transY hσF G.hμF (WNF.succK hL) hσμ hμS)
  have hmT : Le (mi τ) (oadd (ofSummands pre) R) := by
    refine le_transY hmF hσF hTF (by rw [hσe]; exact mi_le_succK τ hτF G.hτt) ?_
    exact le_transY hσF H.hRF hTF hσR (le_oadd_right H.hpreF H.hRF)
  -- 塔は `τ` を越える
  have hγF : ∀ n, WNF (gamT .zero σ pre r .zero .zero (n + 1)) := Tw.hγF
  have hKγ : Lt (.K (lev τ)) (gamT .zero σ pre r .zero .zero (1 + 1)) :=
    (Tw.hC 0).coll _ hKF (inC_K _ _ _) hKσ
  have hτγ : Le τ (gamT .zero σ pre r .zero .zero (1 + 1)) :=
    Or.inr (lt_transY hτF hKF (hγF 1) ((lt_K_iffY hτF hL).mpr (Nat.le_refl _)) hKγ)
  have hAF : ∀ n, WNF (oadd (ofSummands pre) (r.big (gamT .zero σ pre r .zero .zero (n + 1)))) :=
    fun n => (Tw.hC n).hA
  have hxTF : ∀ k, WNF (xT .zero σ pre r .zero .zero k) := fun k => by
    cases k with
    | zero => exact wnf_nsum (H.hRU.good.1 .zero WNF.zero (zero_lt (IsTgt.ne_zero hσt))).1 WNF.zero
    | succ k => exact (H.tower (k + 1)).2.2.hx
  have he : ∀ k, (SeqD.app π (.idx τ Y) pre R r P .zero).nat k =
      .Psi (approx pre P (xT .zero σ pre r .zero .zero k)) τ Y := fun k => by
    rw [app_nat_outG H (by simpa [Gen.tgt?] using hne) rfl hd hlt k, combine_idx (hxTF k) G.hPF]
    rfl
  intro z N hz _ hzT _
  have hP := hz.psi
  have hzF := hP.xiF
  have hz1 : inC z (mi τ) (gamT .zero σ pre r .zero .zero (1 + 1)) = true :=
    inC_mono_d hτF (hγF 1) hτγ hzF hP.mC
  obtain ⟨n, hn⟩ := Tw.harg z hzF hzT fun f hf => Tw.hull (N := 1) hmF hmT f
    (hzF.of_mem_subs (fr_spec hf).1)
    (fr_of_inC z (fun w hw hn' h' => hn' (lt_transY (hzF.of_mem_subs hw) (hγF 1) hσF h' (Tw.hlt 1))) hz1 f hf)
    (fr_spec hf).2
  have hn' := lt_of_lt_of_leY hzF (hAF n) (hAF _) hn (mono_le' hAF Tw.hAm (Nat.le_max_left n N))
  have hxF : WNF (r.big (gamT .zero σ pre r .zero .zero (max n N + 1))) := (H.tower (max n N + 1)).2.2.hx
  refine ⟨max n N + 1, _, by omega, he _, ?_⟩
  exact lt_of_lt_of_leY hzF (hAF _) (wnf_oadd H.hpreF (wnf_nsum hxF G.hPF)) hn' (le_approx0 H.hpreF G.hPF hxF)

/-! ### 添字の閉包の葉 -/

/-- 添字の閉包の列の共終性：段の節点は `a < Y`（崩壊の性質）、`a = Y` で添字が `T` 未満（`IdxS`）、その他は仮定 -/
theorem cof_idx {π X τ Y T : Tm} {s : SeqD} (ht : WNF (.Psi .zero π X)) (hτF : WNF τ) (hτt : IsTgt τ) (hπτ : Le π τ)
    (hτfr : ∀ u, u ∈ fr τ τ → u ∈ fr π π) (hsI : SeqI (.Psi .zero π X) s)
    (hform : ∀ y, InSeq s y → ∃ ξ, y = .Psi ξ τ Y)
    (hS : s.dom = .omega → IdxS (.Psi .zero π X) T τ Y s)
    (hB : ∀ σ, s.dom = .big σ → ∀ z β, WNF z → Lt z T → WNF β → Lt β σ → Cl σ β →
      (∀ f, f ∈ fr σ z → Lt f β) → ∃ ξ, s.big β = .Psi ξ τ Y ∧ Lt z ξ)
    (hlow : ∀ x y, InSeq s y → WNF x → Lt x (.Psi .zero π X) →
      (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w y) →
      Lt (.Psi .zero π X) (tgtN x) → Lt (tgtN x) τ → Le π (tgtN x) → Lt x y)
    (hcls : ∀ x y, InSeq s y → WNF x → Lt x (.Psi .zero π X) →
      (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w y) →
      ∀ z a, x = .Psi z τ a → Lt a X → Lt a Y ∨ (a = Y ∧ Lt z T) ∨ Lt x y) :
    SeqC (.Psi .zero π X) s := by
  have hπF := ht.psi.piF
  have hxτ : ∀ {x : Tm}, WNF x → Lt x (.Psi .zero π X) → Lt x τ := fun hx hxt =>
    lt_transY hx ht hτF hxt (lt_of_lt_of_leY ht hπF hτF (lt_psi_targetY ht) hπτ)
  have hparF : ∀ {x y : Tm}, WNF x → Lt x (.Psi .zero π X) →
      (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w y) → ∀ w, w ∈ parF x → Lt w y := fun hx hxt hpar w hw =>
    hpar w (parF_sub_parL hw)
      (lt_transY (hx.of_mem_subs (parL_sub (parF_sub_parL hw)).1) hx ht (parF_lt hx hw) hxt)
  -- `a = Y` で添字 `z < ξ` なら `x < Ψ^ξ_τ(Y)`
  have hc3 : ∀ {z ξ : Tm}, WNF (.Psi z τ Y) → WNF (.Psi ξ τ Y) → Lt z ξ →
      (∀ w, w ∈ parF (.Psi z τ Y) → Lt w (.Psi ξ τ Y)) → Lt (.Psi z τ Y) (.Psi ξ τ Y) := fun hx hy hzξ hF => by
    have hP := hx.psi
    exact lt_same_arg hx hy hzξ (inC_of_fr_lt hP.xiF hτF hy hP.aF hP.aF hP.Cxi (Or.inr (lt_psi_targetY hy))
      (Or.inl rfl) fun w hw => hF w (by simp [parF, hw]))
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
    refine leaf_natG ht hτt hπτ hτfr hNI (fun n => ?_) (fun x N hx hxt hpar htk hkτ hπk => ⟨N, hlow x _
      (Or.inl ⟨hd, N, rfl⟩) hx hxt hpar htk hkτ hπk⟩) fun x N hx hxt hpar z a e haX _ _ => ?_
    · obtain ⟨ξ, e⟩ := hform _ (Or.inl ⟨hd, n, rfl⟩)
      exact ⟨ξ, Y, e⟩
    · subst e
      rcases hcls _ (s.nat N) (Or.inl ⟨hd, N, rfl⟩) hx hxt hpar z a rfl haX with haY | ⟨rfl, hzT⟩ | h
      · obtain ⟨ξ, e⟩ := hform _ (Or.inl ⟨hd, N, rfl⟩)
        have hy := hyF N
        refine ⟨N, ?_⟩
        rw [e] at hy ⊢
        exact (Clo.psi hy).lt hx (hxτ hx hxt) (fun w hw => by
          have := hparF hx hxt hpar w hw
          rwa [e] at this) fun a' e' => by
            cases e'
            exact haY
      · obtain ⟨n, ξ, hNn, hξ, hzξ⟩ := hS hd z N hx hxt hzT (hparF hx hxt hpar)
        have hy := hyF n
        refine ⟨n, ?_⟩
        rw [hξ] at hy ⊢
        refine hc3 hx hy hzξ fun w hw => ?_
        rw [← hξ]
        exact lt_of_lt_of_leY (hx.of_mem_subs (parL_sub (parF_sub_parL hw)).1) (hyF N) (hyF n)
          (hparF hx hxt hpar w hw) (mono_le hyF hm hNn)
      · exact ⟨N, h⟩
  | big σ =>
    have hsI' := hsI
    unfold SeqI at hsI'
    rw [hd] at hsI'
    obtain ⟨⟨hU, -⟩, hG, -⟩ := hsI'
    have hσF := hU.hσF
    have hYF : ∀ β, WNF β → Lt β σ → WNF (s.big β) := fun β hβ hβσ => (hU.good.1 β hβ hβσ).1
    refine leaf_bigG ht hτt hπτ hτfr hσF hU (hG rfl) (fun β hβ hβσ => ?_)
      (fun x β hx hxt hβ hβσ _ _ hpar htk hkτ hπk => hlow x _ (Or.inr ⟨σ, β, hd, hβ, hβσ, rfl⟩) hx hxt hpar
        htk hkτ hπk) fun x β hx hxt hβ hβσ hCl hfr hpar hσx z a e haX => ?_
    · obtain ⟨ξ, e⟩ := hform _ (Or.inr ⟨σ, β, hd, hβ, hβσ, rfl⟩)
      exact ⟨ξ, Y, e⟩
    · subst e
      rcases hcls _ (s.big β) (Or.inr ⟨σ, β, hd, hβ, hβσ, rfl⟩) hx hxt hpar z a rfl haX with
        haY | ⟨rfl, hzT⟩ | h
      · obtain ⟨ξ, e⟩ := hform _ (Or.inr ⟨σ, β, hd, hβ, hβσ, rfl⟩)
        have hy := hYF β hβ hβσ
        rw [e] at hy ⊢
        exact (Clo.psi hy).lt hx (hxτ hx hxt) (fun w hw => by
          have := hparF hx hxt hpar w hw
          rwa [e] at this) fun a' e' => by
            cases e'
            exact haY
      · have hzF := hx.psi.xiF
        obtain ⟨ξ, hξ, hzξ⟩ := hB σ hd z β hzF hzT hβ hβσ hCl fun f hf => hfr f (by
          have h2 : ¬ Lt (.Psi z τ a) σ := not_lt_of_leY hσF hx hσx
          rw [fr]
          simp only [h2, ↓reduceIte, List.mem_append]
          exact Or.inl (Or.inl hf))
        have hy := hYF β hβ hβσ
        rw [hξ] at hy ⊢
        exact hc3 hx hy hzξ fun w hw => by
          have := hparF hx hxt hpar w hw
          rwa [hξ] at this
      · exact h

end RTKA.Fund
