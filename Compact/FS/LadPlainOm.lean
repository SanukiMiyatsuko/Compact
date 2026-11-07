import Compact.FS.LadZOm

/-! 目標が `Ω_c` の崩壊の区間の下界の主定理と、素の近似の列（一つずらしたものを含む）の下界。

* `le_psi_om_of_descT`：`A ∈ D(V)` なら `Ψ^0_{Ω_c}(A) ≤ Ψ^0_{Ω_c}(V)`（`V` の後者を一つずつ外し、極限では閉包の移し替え）。
* `lbi_om_of_desc`：`y = Ψ^0_{Ω_c}(A)`、`y' < Ω_c`。区間 `(y, y']` の崩壊 `w = Ψ^0(W)` で前線が全て `y` 未満のものに
  `A ∈ D(W[0])` があれば `LBI y y'`。和は先頭の加数、主要項は帯の分類で崩壊、前線が `y` 以上なら z 側の補題で終わる。 -/

namespace RTKA.Fund

open Tm W

/-- 目標が `Ω_c`：`A ∈ D(V)` なら `Ψ^0(A) ≤ Ψ^0(V)` -/
theorem le_psi_om_of_descT {c A : Tm} (hy : WNF (.Psi .zero (.Om c) A)) (V : NF) :
    WNF (.Psi .zero (.Om c) V.1) → DescT A V.1 → Le (.Psi .zero (.Om c) A) (.Psi .zero (.Om c) V.1) := by
  refine WellFounded.induction (C := fun V : NF => WNF (.Psi .zero (.Om c) V.1) → DescT A V.1 →
    Le (.Psi .zero (.Om c) A) (.Psi .zero (.Om c) V.1)) wellFounded_isNF V ?_
  intro V ih hq hD
  by_cases hAV : A = V.1
  · rw [hAV]
    exact Or.inl rfl
  by_cases hs : isSucc V.1 = true
  · have hpF := wnf_pred V.2
    have hq' := wnf_psi_om_pred hq hs
    have hD' : DescT A (pred V.1) := by
      have := hD.of_ne hAV
      rwa [fund_eq, (dom_eq_one_iff V.2).mpr hs] at this
    have h1 := ih ⟨pred V.1, hpF⟩ (pred_lt V.2 hs) hq' hD'
    exact le_transY hy hq' hq h1 (Or.inr (psi_pred_lt hq' hq hs))
  · exact le_psi_of_descT_ns hy hq V.2 hD (Or.inl rfl) (inC_arg_psi hq) hs

/-- 主要項 `y` が和 `a + b` 未満なら `y ≤ a` -/
theorem le_head_of_lt_plus {y a b : Tm} (hy : WNF y) (hyp : isPrincipal y = true) (hP : WNF (.plus a b))
    (h : Lt y (.plus a b)) : Le y a := by
  obtain ⟨ha, hb, hap, hb0⟩ := hP.plus
  refine le_of_not_ltY ha hy fun hay => ?_
  have hsb := summands_le_head_plus hP
  have hb' : Lt b y := lt_transY hb (wnf_mulNat ha hap _) hy (lt_mulNat_of_le hb hap hsb)
    (mulNat_lt_prin hap hyp hay _)
  have hlt : Lt (.plus a b) y := by
    rw [← oadd_prin_eq hap hb hb0 hsb]
    exact oadd_lt_prin ha hb hyp hay hb'
  exact Lt.asymmY hy hP h hlt

/-- 目標が `Ω_c` の崩壊の区間の下界の骨組み：区間の崩壊 `w = Ψ^0(W)` で前線が全て `y` 未満のものについて
    `y ≤ w[0]` なら `LBI y y'` -/
theorem lbi_om_of_zle {c A y' : Tm} (hy : WNF (.Psi .zero (.Om c) A)) (hy' : WNF y')
    (hy'π : Lt y' (.Om c))
    (hZ : ∀ W, WNF (.Psi .zero (.Om c) W) → Lt (.Psi .zero (.Om c) A) (.Psi .zero (.Om c) W) →
      Le (.Psi .zero (.Om c) W) y' → (∀ f, f ∈ fr (.Om c) W → Lt f (.Psi .zero (.Om c) A)) →
      Le (.Psi .zero (.Om c) A) (fund (.Psi .zero (.Om c) W) .zero)) :
    LBI (.Psi .zero (.Om c) A) y' := by
  intro w hw h1 h2
  have hπ := hy.psi.piF
  have hcs : isSucc c = true := (WNF.psiOm hy).2.2.1
  have hwπ : Lt w (.Om c) := lt_of_le_of_ltY hw hy' hπ h2 hy'π
  have hw0F := fund_wnf hw WNF.zero
  by_cases hwp : isPrincipal w = true
  · obtain ⟨W, rfl⟩ := band_om_prin hπ hcs hw hwp
      (lt_transY (omBase_wnf hπ hcs).1 hy hw (omBase_lt_psi hy) h1) hwπ
    have hW0 : W ≠ .zero := by
      rintro rfl
      exact not_lt_of_leY hw hy (le_psi_of_inC hw hy (zero_le A) (inC_zero _ _)) h1
    obtain ⟨hfr, -⟩ := zside_om hw hW0
    by_cases hex : ∃ f, f ∈ fr (.Om c) W ∧ Le (.Psi .zero (.Om c) A) f
    · obtain ⟨f, hf, hyf⟩ := hex
      have hfF := hw.psi.aF.of_mem_subs (fr_spec hf).1
      exact le_transY hy hfF hw0F hyf (hfr f hf)
    · have hfr' : ∀ f, f ∈ fr (.Om c) W → Lt f (.Psi .zero (.Om c) A) := fun f hf => by
        have hfF := hw.psi.aF.of_mem_subs (fr_spec hf).1
        refine Classical.byContradiction fun hn => hex ⟨f, hf, le_of_not_ltY hfF hy hn⟩
      exact hZ W hw h1 h2 hfr'
  · cases w with
    | plus a b =>
      have hya := le_head_of_lt_plus hy rfl hw h1
      have hb0F := fund_wnf hw.plus.2.1 WNF.zero
      rw [fund_plus hw .zero] at hw0F ⊢
      exact le_transY hy hw.plus.1 hw0F hya (le_oadd_left hw.plus.1 hb0F)
    | zero => exact absurd h1 (not_lt_zero _)
    | _ => exact absurd rfl hwp

/-- z 側の閉包の下界：`A ∈ D(W[0])` なら `Ψ^0(A) ≤ w[0]`（`w = Ψ^0_{Ω_c}(W)`、`W ≠ 0`） -/
theorem le_fund_of_desc {c A W : Tm} (hy : WNF (.Psi .zero (.Om c) A)) (hw : WNF (.Psi .zero (.Om c) W))
    (hW0 : W ≠ .zero) (hD : DescT A (fund W .zero)) :
    Le (.Psi .zero (.Om c) A) (fund (.Psi .zero (.Om c) W) .zero) := by
  obtain ⟨-, V, hqF, hqw, hle, hC, hVd⟩ := zside_om hw hW0
  have hW0F := fund_wnf hw.psi.aF WNF.zero
  have hw0F := fund_wnf hw WNF.zero
  have hyq : Le (.Psi .zero (.Om c) A) (.Psi .zero (.Om c) V) := by
    rcases hVd with e | hVs
    · subst e
      exact le_psi_om_of_descT hy ⟨_, hW0F⟩ hqF hD
    · exact le_psi_of_descT_ns hy hqF hW0F hD hle hC hVs
  exact le_transY hy hqF hw0F hyq hqw

/-- 目標が `Ω_c` の崩壊の区間の下界の主定理：区間の崩壊で前線が `y` 未満のものに `A ∈ D(W[0])` があれば `LBI y y'` -/
theorem lbi_om_of_desc {c A y' : Tm} (hy : WNF (.Psi .zero (.Om c) A)) (hy' : WNF y')
    (hy'π : Lt y' (.Om c))
    (hD : ∀ W, WNF (.Psi .zero (.Om c) W) → Lt (.Psi .zero (.Om c) A) (.Psi .zero (.Om c) W) →
      Le (.Psi .zero (.Om c) W) y' → (∀ f, f ∈ fr (.Om c) W → Lt f (.Psi .zero (.Om c) A)) →
      DescT A (fund W .zero)) :
    LBI (.Psi .zero (.Om c) A) y' :=
  lbi_om_of_zle hy hy' hy'π fun W hw h1 h2 hfr => by
    have hW0 : W ≠ .zero := by
      rintro rfl
      exact not_lt_of_leY hw hy (le_psi_of_inC hw hy (zero_le A) (inC_zero _ _)) h1
    exact le_fund_of_desc hy hw hW0 (hD W hw h1 h2 hfr)

/-! ### 和の分解と降下列の写し（接頭辞 `pre`） -/

/-- `pre ⊕ y ≤ W < pre ⊕ R`（`y < R`）なら `W = pre ⊕ W'`、`y ≤ W' < R` -/
theorem between_pre {pre : List Tm} {R y W : Tm} (hN : NFL (pre ++ [R])) (hy : WNF y) (hyR : Lt y R)
    (hW : WNF W) (h1 : Le (oadd (ofSummands pre) y) W) (h2 : Lt W (oadd (ofSummands pre) R)) :
    ∃ W', WNF W' ∧ Le y W' ∧ Lt W' R ∧ W = oadd (ofSummands pre) W' ∧
      ∀ s, s ∈ pre → ∀ u, u ∈ summands W' → Le u s := by
  have hpre := nfl_append_left hN
  have hRN := hN.1 R (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  have hsy := summands_oadd_pre hpre hy (head_le_pre (rest := []) hN hy hyR)
  have hsR : summands (oadd (ofSummands pre) R) = pre ++ [R] := by
    rw [summands_oadd_pre hpre hRN.1 (fun s h r hs e => by
      rw [summands_principal hRN.2] at e
      simp only [List.cons.injEq] at e
      rw [← e.1]
      exact le_leB (le_of_ne_gtY hRN.1 (hpre.1 s hs).1 (le_of_nfl_append (rest := []) hN s hs))),
      summands_principal hRN.2]
  have hAN : NFL (pre ++ summands y) := hsy ▸ nfl_summands (wnf_oadd (wnf_ofSummands hpre) hy)
  have hc1 : cmpList (pre ++ summands y) (summands W) ≠ .gt := by
    rw [← hsy, ← cmp_eq]
    exact ne_gt_of_le h1
  have hc2 : cmpList (summands W) (pre ++ [R]) = .lt := by
    rw [← hsR, ← cmp_eq]
    exact h2
  obtain ⟨V', hV'⟩ := prefix_of_between hAN (nfl_summands hW) hc1 hc2
  have hWN : NFL (pre ++ V') := hV' ▸ nfl_summands hW
  have hV'N := nfl_append_right hWN
  have hW'F := wnf_ofSummands hV'N
  have hsW' : summands (ofSummands V') = V' := summands_ofSummands _ (nfl_principal hV'N)
  have hge : ∀ s, s ∈ pre → ∀ u, u ∈ summands (ofSummands V') → Le u s := fun s hs u hu => by
    rw [hsW'] at hu
    have hsF := (hWN.1 s (List.mem_append_left _ hs)).1
    have huF := (hWN.1 u (List.mem_append_right _ hu)).1
    obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hu
    have h' : NFL (pre ++ L1 ++ u :: L2) := by simpa [List.append_assoc] using hWN
    exact le_of_ne_gtY huF hsF (le_of_nfl_append h' s (List.mem_append_left _ hs))
  have hWe : W = oadd (ofSummands pre) (ofSummands V') := by
    rw [← ofSummands_summands W hW, ← ofSummands_summands (oadd (ofSummands pre) (ofSummands V'))
      (wnf_oadd (wnf_ofSummands hpre) hW'F), summands_oadd_le hpre hW'F hge, hsW', ← hV',
      ofSummands_summands W hW]
  refine ⟨ofSummands V', hW'F, ?_, ?_, hWe, hge⟩
  · refine le_of_ne_gtY hy hW'F ?_
    rw [cmp_eq, hsW']
    rw [hV', cmpList_append_same] at hc1
    exact hc1
  · unfold Lt
    rw [cmp_eq, hsW', summands_principal hRN.2]
    rw [hV', cmpList_append_same] at hc2
    exact hc2

/-- 接頭辞の結合：`pre ⊕ (M ⊕ y) = (pre ++ M) ⊕ y` -/
theorem oadd_assoc_pre {pre M : List Tm} {y : Tm} (hN : NFL (pre ++ M)) (hy : WNF y)
    (hge : ∀ s, s ∈ pre ++ M → ∀ u, u ∈ summands y → Le u s) :
    oadd (ofSummands pre) (oadd (ofSummands M) y) = oadd (ofSummands (pre ++ M)) y := by
  have hpre := nfl_append_left hN
  have hM := nfl_append_right hN
  have hZF := wnf_oadd (wnf_ofSummands hM) hy
  have hZs : summands (oadd (ofSummands M) y) = M ++ summands y :=
    summands_oadd_le hM hy fun s hs u hu => hge s (List.mem_append_right _ hs) u hu
  have hgeZ : ∀ s, s ∈ pre → ∀ u, u ∈ summands (oadd (ofSummands M) y) → Le u s := by
    intro s hs u hu
    rw [hZs] at hu
    rcases List.mem_append.mp hu with hu | hu
    · obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hu
      have h' : NFL (pre ++ L1 ++ u :: L2) := by simpa [List.append_assoc] using hN
      exact le_of_ne_gtY (hM.1 u (by simp)).1 (hpre.1 s hs).1 (le_of_nfl_append h' s (List.mem_append_left _ hs))
    · exact hge s (List.mem_append_left _ hs) u hu
  rw [← ofSummands_summands (oadd (ofSummands pre) (oadd (ofSummands M) y)) (wnf_oadd (wnf_ofSummands hpre) hZF),
    ← ofSummands_summands (oadd (ofSummands (pre ++ M)) y) (wnf_oadd (wnf_ofSummands hN) hy),
    summands_oadd_le hpre hZF hgeZ, hZs, summands_oadd_le hN hy hge, List.append_assoc]

/-- 降下列の元は標準形 -/
theorem DescT.wnf {x y : Tm} (h : DescT x y) (hy : WNF y) : WNF x := by
  induction h with
  | refl => exact hy
  | step _ ih => exact ih (fund_wnf hy WNF.zero)

/-- 加数が全て `s` 以下の項以下の項の加数も `s` 以下 -/
theorem summands_le_of_le' {s y z : Tm} (hs : WNF s) (hsp : isPrincipal s = true) (hy : WNF y) (hz : WNF z)
    (hsy : ∀ u, u ∈ summands y → Le u s) (hzy : Le z y) : ∀ u, u ∈ summands z → Le u s :=
  summands_le_of_le hs hsp hy hz hsy hzy

/-- 接頭辞の 0 番目：`(pre ⊕ W')[0] = pre ⊕ W'[0]` -/
theorem fund_oadd_pre {pre : List Tm} {W' : Tm} (hpre : NFL pre) (hW' : WNF W') (hW'0 : W' ≠ .zero)
    (hge : ∀ s, s ∈ pre → ∀ u, u ∈ summands W' → Le u s) :
    fund (oadd (ofSummands pre) W') .zero = oadd (ofSummands pre) (fund W' .zero) := by
  have hsum := summands_pre_last hW'0
  generalize preT (info W').sums = M at hsum
  generalize lastT (info W').sums = L at hsum
  have hWs : summands (oadd (ofSummands pre) W') = (pre ++ M) ++ [L] := by
    rw [summands_oadd_le hpre hW' hge, hsum, List.append_assoc]
  have hAF := wnf_oadd (wnf_ofSummands hpre) hW'
  have hN : NFL ((pre ++ M) ++ [L]) := hWs ▸ nfl_summands hAF
  have hLF : WNF L := (hN.1 L (by simp)).1
  have hLp : isPrincipal L = true := (hN.1 L (by simp)).2
  have hy := fund_wnf hLF WNF.zero
  have hyL := fund_zero_le hLF
  rw [fund_of_summands_last (pre ++ M) hAF hWs, fund_of_summands_last M hW' hsum]
  refine (oadd_assoc_pre (nfl_append_left hN) hy fun s hs u hu => ?_).symm
  have hsF := ((nfl_append_left hN).1 s hs).1
  have hLs : Le L s := le_of_ne_gtY hLF hsF (le_of_nfl_append (rest := []) hN s hs)
  have huF := ((nfl_summands hy).1 u hu).1
  exact le_transY huF hy hsF (summand_le hy hu) (le_transY hy hLF hsF hyL hLs)

/-- 降下列の写し（接頭辞）：`x ∈ D(y)` で `y` の加数が `pre` の加数以下なら `pre ⊕ x ∈ D(pre ⊕ y)` -/
theorem desc_oadd_pre : ∀ {pre : List Tm}, NFL pre → ∀ {x y : Tm}, DescT x y → WNF y →
    (∀ s, s ∈ pre → ∀ u, u ∈ summands y → Le u s) →
    DescT (oadd (ofSummands pre) x) (oadd (ofSummands pre) y)
  | [], _, x, y, h, hy, _ => by
    rw [show ofSummands [] = Tm.zero from rfl, zero_oadd hy, zero_oadd (h.wnf hy)]
    exact h
  | a :: pre, hN, x, y, h, hy, hge => by
    have haN := hN.1 a List.mem_cons_self
    have hpreN := nfl_tail hN
    have hxF := h.wnf hy
    have hxy := DescT.le hxF hy h
    have hgex : ∀ s, s ∈ a :: pre → ∀ u, u ∈ summands x → Le u s := fun s hs u hu =>
      summands_le_of_le (hN.1 s hs).1 (hN.1 s hs).2 hy hxF (hge s hs) hxy u hu
    have ih := desc_oadd_pre hpreN h hy fun s hs u hu => hge s (List.mem_cons_of_mem _ hs) u hu
    have hZF := wnf_oadd (wnf_ofSummands hpreN) hy
    have hsZ : ∀ u, u ∈ summands (oadd (ofSummands pre) y) → Le u a := by
      intro u hu
      rw [summands_oadd_le hpreN hy fun s hs u hu => hge s (List.mem_cons_of_mem _ hs) u hu] at hu
      rcases List.mem_append.mp hu with hu | hu
      · exact le_head_mem hN (List.mem_cons_of_mem _ hu)
      · exact hge a List.mem_cons_self u hu
    have h2 := desc_oadd haN.1 haN.2 ih hZF hsZ
    have e1 := oadd_assoc_pre (pre := [a]) (M := pre) (y := x) (by simpa using hN) hxF (by simpa using hgex)
    have e2 := oadd_assoc_pre (pre := [a]) (M := pre) (y := y) (by simpa using hN) hy (by simpa using hge)
    rw [show ofSummands [a] = a from rfl] at e1 e2
    rw [show a :: pre = [a] ++ pre from rfl, ← e1, ← e2]
    exact h2

/-- 加数が `pre ++ [R]` の項は `pre ⊕ R` -/
theorem eq_oadd_last {X : Tm} {pre : List Tm} {R : Tm} (hX : WNF X) (hsum : summands X = pre ++ [R]) :
    X = oadd (ofSummands pre) R := by
  have hN : NFL (pre ++ [R]) := hsum ▸ nfl_summands hX
  have hpre := nfl_append_left hN
  have hRN := hN.1 R (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  have hge : ∀ s, s ∈ pre → ∀ u, u ∈ summands R → Le u s := fun s hs u hu => by
    rw [summands_principal hRN.2, List.mem_singleton] at hu
    subst hu
    exact le_of_ne_gtY hRN.1 (hpre.1 s hs).1 (le_of_nfl_append (rest := []) hN s hs)
  rw [← ofSummands_summands X hX, ← ofSummands_summands (oadd (ofSummands pre) R)
    (wnf_oadd (wnf_ofSummands hpre) hRN.1), summands_oadd_le hpre hRN.1 hge, summands_principal hRN.2, hsum]

/-! ### 素の近似の列（ω 型の最後の加数） -/

/-- 素の近似の列の列の側：`A = pre ⊕ R[m]`、区間の崩壊 `w = Ψ^0(W)`（`w < t`）で前線が `y` 未満なら `A ∈ D(W[0])` -/
theorem tside_plain_om {c X : Tm} (ht : WNF (.Psi .zero (.Om c) X)) {pre : List Tm} {R : Tm}
    (hsum : summands X = pre ++ [R]) (hdR : dom R = .omega)
    (hLR : ∀ m, LBI ((info R).seq.nat m) ((info R).seq.nat (m + 1))) (m : Nat)
    (hy : WNF (.Psi .zero (.Om c) (oadd (ofSummands pre) ((info R).seq.nat m))))
    (hgap : ∀ f, f ∈ fr (.Om c) X → Lt f (.Psi .zero (.Om c) (oadd (ofSummands pre) ((info R).seq.nat m))))
    {W : Tm} (hw : WNF (.Psi .zero (.Om c) W))
    (h1 : Lt (.Psi .zero (.Om c) (oadd (ofSummands pre) ((info R).seq.nat m))) (.Psi .zero (.Om c) W))
    (h2 : Lt (.Psi .zero (.Om c) W) (.Psi .zero (.Om c) X))
    (hfr : ∀ f, f ∈ fr (.Om c) W → Lt f (.Psi .zero (.Om c) (oadd (ofSummands pre) ((info R).seq.nat m)))) :
    DescT (oadd (ofSummands pre) ((info R).seq.nat m)) (fund W .zero) := by
  have hXF := ht.psi.aF
  have hWF := hw.psi.aF
  have hN : NFL (pre ++ [R]) := hsum ▸ nfl_summands hXF
  have hpreN := nfl_append_left hN
  have hRN := hN.1 R (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  have hU := (seqI_dom_nat hRN.1 hdR).1
  have hxF := (hU.good m).1
  have hxR := (hU.good m).2.1
  have hAF := hy.psi.aF
  have hXe := eq_oadd_last hXF hsum
  -- `A < W < X`
  have hAW : Lt (oadd (ofSummands pre) ((info R).seq.nat m)) W := by
    rcases triY hAF hWF with h | h | h
    · exact h
    · rw [h] at h1; exact absurd h1 (Lt.irrefl _)
    · exact absurd (psi_lt_psi_of_arg hw hy h hfr) (Lt.asymmY hy hw h1)
  have hWX : Lt W X := by
    rcases triY hWF hXF with h | h | h
    · exact h
    · rw [h] at h2; exact absurd h2 (Lt.irrefl _)
    · exact absurd (psi_lt_psi_of_arg ht hw h fun f hf => lt_transY (hXF.of_mem_subs (fr_spec hf).1) hy hw
        (hgap f hf) h1) (Lt.asymmY hw ht h2)
  rw [hXe] at hWX
  obtain ⟨W', hW'F, hxW', hW'R, hWe, hge⟩ := between_pre hN hxF hxR hWF (Or.inr hAW) hWX
  have hxW : Lt ((info R).seq.nat m) W' := by
    rcases hxW' with e | h
    · rw [hWe, ← e] at hAW; exact absurd hAW (Lt.irrefl _)
    · exact h
  -- `R` の下界の鎖と共終性から `R[m] ∈ D(W')`
  have hC := seqC_all R hRN.1
  unfold SeqC at hC
  rw [show (info R).seq.dom = dom R from rfl, hdR] at hC
  obtain ⟨M, hM⟩ := hC W' hW'F hW'R
  have hmM : m < M := by
    rcases Nat.lt_or_ge m M with h | h
    · exact h
    · exact absurd (lt_transY hxF hW'F hxF hxW (lt_of_lt_of_leY hW'F (hU.good M).1 hxF hM
        (nat_mono_le hRN.1 hdR h))) (Lt.irrefl _)
  obtain ⟨j, rfl⟩ : ∃ j, M = m + j + 1 := ⟨M - m - 1, by omega⟩
  have hL : LBI ((info R).seq.nat m) W' := fun z hz hz1 hz2 =>
    lbi_chain hRN.1 hdR hLR hz j m hz1 (Or.inr (lt_of_le_of_ltY hz hW'F (hU.good _).1 hz2 hM))
  have hD := descT_of_LBI ⟨W', hW'F⟩ (Or.inr hxW) hL
  have hD' := hD.of_ne (fun e => by rw [e] at hxW; exact Lt.irrefl _ hxW)
  have hW'0 : W' ≠ .zero := ne_zero_of_lt hxW
  rw [hWe, fund_oadd_pre hpreN hW'F hW'0 hge]
  have hf0 := fund_wnf hW'F WNF.zero
  exact desc_oadd_pre hpreN hD' hf0 fun s hs u hu =>
    summands_le_of_le (hpreN.1 s hs).1 (hpreN.1 s hs).2 hW'F hf0 (hge s hs) (fund_zero_le hW'F) u hu

/-- 素の近似の列（`t[n] = Ψ^0(pre ⊕ R[n+j])`）の隣り合う項の区間の下界 -/
theorem lbi_plain_om {c X : Tm} (ht : WNF (.Psi .zero (.Om c) X)) {pre : List Tm} {R : Tm}
    (hsum : summands X = pre ++ [R]) (hdR : dom R = .omega)
    (hLR : ∀ m, LBI ((info R).seq.nat m) ((info R).seq.nat (m + 1))) (j : Nat)
    (hd : dom (.Psi .zero (.Om c) X) = .omega)
    (hs : ∀ n, (info (.Psi .zero (.Om c) X)).seq.nat n =
      .Psi .zero (.Om c) (oadd (ofSummands pre) ((info R).seq.nat (n + j)))) (n : Nat) :
    LBI ((info (.Psi .zero (.Om c) X)).seq.nat n) ((info (.Psi .zero (.Om c) X)).seq.nat (n + 1)) := by
  have hI := seqI_dom_nat ht hd
  have hG := hI.1.good
  have hy : WNF (.Psi .zero (.Om c) (oadd (ofSummands pre) ((info R).seq.nat (n + j)))) := hs n ▸ (hG n).1
  have hy'F := (hG (n + 1)).1
  have hy't := (hG (n + 1)).2.1
  have hπ := ht.psi.piF
  rw [hs n]
  refine lbi_om_of_desc hy hy'F (lt_transY hy'F ht hπ hy't (lt_psi_targetY ht)) fun W hw h1 h2 hfr => ?_
  refine tside_plain_om ht hsum hdR hLR (n + j) hy (fun f hf => ?_) hw h1
    (lt_of_le_of_ltY hw hy'F ht h2 hy't) hfr
  have hfs : f ∈ subs (.Psi .zero (.Om c) X) := subs_psi_a (fr_spec hf).1
  have hft : Lt f (.Psi .zero (.Om c) X) := FWOrder.k2 ht f hf
  have hne : f ≠ .Psi .zero (.Om c) X := fun e => by rw [e] at hft; exact Lt.irrefl _ hft
  have := hI.2 n f hfs hne hft
  rwa [hs n] at this

end RTKA.Fund
