import Compact.FS.LadPlainOm

/-! 種つきの近似の列（目標 `Ω_c`、最後の加数は ω 型）の下界の道具。

`t[n] = Ψ^0(H ⊕ (R[n] # P))`（`P` は種）。`A_n = B_n # P`（`B_n = H ⊕ R[n]`）は一般に `D(W[0])` に入らないので、
`B_n ∈ D(V)` と `P` が `V` の前線以下であることから閉包に入れる（`le_psi_om_seed`）。 -/

namespace RTKA.Fund

open Tm W

/-- 種つきの閉包の下界（目標 `Ω_c`）：`B ∈ D(V)`、`B # P ≤ V`、`P` は `V` のある前線以下なら
    `Ψ^0(B # P) ≤ Ψ^0(V)`（`V` の後者を一つずつ外し、極限では閉包の移し替え） -/
theorem le_psi_om_seed {c B P : Tm} (hy : WNF (.Psi .zero (.Om c) (nsum B P))) (hBF : WNF B) (hPF : WNF P)
    (V : NF) : WNF (.Psi .zero (.Om c) V.1) → DescT B V.1 → Le (nsum B P) V.1 →
      (∃ f, f ∈ fr (.Om c) V.1 ∧ Le P f) →
      Le (.Psi .zero (.Om c) (nsum B P)) (.Psi .zero (.Om c) V.1) := by
  refine WellFounded.induction (C := fun V : NF => WNF (.Psi .zero (.Om c) V.1) → DescT B V.1 →
    Le (nsum B P) V.1 → (∃ f, f ∈ fr (.Om c) V.1 ∧ Le P f) →
    Le (.Psi .zero (.Om c) (nsum B P)) (.Psi .zero (.Om c) V.1)) wellFounded_isNF V ?_
  intro V ih hq hD hle hfr
  have hAF := wnf_nsum hBF hPF
  rcases hle with e | hlt
  · rw [e]
    exact Or.inl rfl
  have hBV : B ≠ V.1 := fun e => by
    rw [← e] at hlt
    exact not_lt_of_leY hBF hAF (le_nsum_left hBF hPF) hlt
  by_cases hs : isSucc V.1 = true
  · have hpF := wnf_pred V.2
    have hq' := wnf_psi_om_pred hq hs
    have hD' : DescT B (pred V.1) := by
      have := hD.of_ne hBV
      rwa [fund_eq, (dom_eq_one_iff V.2).mpr hs] at this
    have hle' : Le (nsum B P) (pred V.1) :=
      le_of_lt_succT hAF hpF (by rw [succT_pred V.2 hs]; exact hlt)
    have hfr' : ∃ f, f ∈ fr (.Om c) (pred V.1) ∧ Le P f := by
      obtain ⟨f, hf, hPf⟩ := hfr
      refine ⟨f, ?_, hPf⟩
      rw [← fr_succT (.Om c) (pred V.1), succT_pred V.2 hs]
      exact hf
    have h1 := ih ⟨pred V.1, hpF⟩ (pred_lt V.2 hs) hq' hD' hle' hfr'
    exact le_transY hy hq' hq h1 (Or.inr (psi_pred_lt hq' hq hs))
  · have hV0 : Lt .zero V.1 := lt_of_le_of_ltY WNF.zero hAF V.2 (zero_le _) hlt
    have hBC : inC B V.1 (.Psi .zero (.Om c) V.1) = true :=
      inC_of_descT V.2 hq hV0 hD V.2 (fun u σ hu _ _ hdu => bigOK_of_ns (seqI_dom_big hu hdu).1.hσF V.2 hs)
        (inC_arg_psi hq)
    obtain ⟨f, hf, hPf⟩ := hfr
    have hVF : WNF V.1 := V.2
    have hfF := hVF.of_mem_subs (fr_spec hf).1
    have hPq : Lt P (.Psi .zero (.Om c) V.1) := lt_of_le_of_ltY hPF hfF hq hPf (FWOrder.k2 hq f hf)
    have hPC : inC P V.1 (.Psi .zero (.Om c) V.1) = true := WFY.inC_of_ltY _ hPF hq hPq
    exact le_psi_of_inC hy hq (Or.inr hlt) (inC_nsum hBF hPF hBC hPC)

/-- 種つきの近似の引数 `H ⊕ (x # P)` の閉包の所属 -/
theorem inC_seedArg {H : List Tm} {x P g d : Tm} (hH : NFL H) (hx : WNF x) (hP : WNF P)
    (h1 : inC (ofSummands H) g d = true) (h2 : inC x g d = true) (h3 : inC P g d = true) :
    inC (oadd (ofSummands H) (nsum x P)) g d = true :=
  inC_oadd (wnf_ofSummands hH) (wnf_nsum hx hP) h1 (inC_nsum hx hP h2 h3)

/-- 種つきの列：`H ⊕ R ≤ W < X`（`X` の加数は `H ++ R :: L'`）なら、全ての近似 `Ψ^0(H ⊕ (R[m] # P))` は `w` 未満 -/
theorem seed_lt_w_of_ge {c W : Tm} {H : List Tm} {R P : Tm} {L' : List Tm}
    (hw : WNF (.Psi .zero (.Om c) W)) (hN : NFL (H ++ R :: L')) (hdR : dom R = .omega)
    (hPw : Lt P (.Psi .zero (.Om c) W)) (hPF : WNF P) (hPR : Lt P R)
    (hWX : Lt W (ofSummands (H ++ R :: L')))
    (hge : Le (oadd (ofSummands H) R) W) (m : Nat)
    (hym : WNF (.Psi .zero (.Om c) (oadd (ofSummands H) (nsum ((info R).seq.nat m) P)))) :
    Lt (.Psi .zero (.Om c) (oadd (ofSummands H) (nsum ((info R).seq.nat m) P))) (.Psi .zero (.Om c) W) := by
  have hWF := hw.psi.aF
  have hHN : NFL H := nfl_append_left hN
  have hRN := hN.1 R (List.mem_append_right _ List.mem_cons_self)
  have hHR : NFL (H ++ [R]) := by
    have : NFL ((H ++ [R]) ++ L') := by simpa using hN
    exact nfl_append_left this
  -- `W` の加数は `H ++ [R]` で始まる
  have hsHR : summands (oadd (ofSummands H) R) = H ++ [R] := by
    rw [← eq_oadd_last (wnf_ofSummands hHR) (summands_ofSummands _ (nfl_principal hHR))]
    exact summands_ofSummands _ (nfl_principal hHR)
  have hc1 : cmpList ((H ++ [R]) ++ []) (summands W) ≠ .gt := by
    rw [List.append_nil, ← hsHR, ← cmp_eq]
    exact ne_gt_of_le hge
  have hc2 : cmpList (summands W) ((H ++ [R]) ++ L') = .lt := by
    have := hWX
    unfold Lt at this
    rw [cmp_eq, summands_ofSummands _ (nfl_principal hN)] at this
    simpa using this
  obtain ⟨V', hV'⟩ := prefix_of_between (by simpa using hHR) (nfl_summands hWF) hc1 hc2
  have hWC := inC_arg_psi hw
  have hRC : inC R W (.Psi .zero (.Om c) W) = true :=
    inC_of_mem_summands hWF hWC (by rw [hV']; simp)
  have hHC : inC (ofSummands H) W (.Psi .zero (.Om c) W) = true := by
    rw [inC_ofSummands]
    intro s hs
    exact inC_of_mem_summands hWF hWC (by rw [hV']; simp [hs])
  have hU := (seqI_dom_nat hRN.1 hdR).1
  have hxF := (hU.good m).1
  have hxR := (hU.good m).2.1
  have hxC := hU.ub _ _ m hWF hw hRC
  have hPC : inC P W (.Psi .zero (.Om c) W) = true := WFY.inC_of_ltY _ hPF hw hPw
  have hAC := inC_seedArg hHN hxF hPF hHC hxC hPC
  have hAW : Lt (oadd (ofSummands H) (nsum ((info R).seq.nat m) P)) W :=
    lt_of_lt_of_leY hym.psi.aF (wnf_oadd (wnf_ofSummands hHN) hRN.1) hWF
      (oadd_lt_oadd (wnf_ofSummands hHN) (wnf_nsum hxF hPF) hRN.1 (nsum_lt_prin hxF hPF hRN.2 hxR hPR)) hge
  exact coll_psiY hw _ hym (inC_psi_iff.mpr (Or.inr ⟨inC_tgt_of_k2t hw fun u hu => FWOrder.k2t hw u hu,
    inC_zero _ _, hAC, hAW⟩)) (lt_psi_targetY hym)

end RTKA.Fund
