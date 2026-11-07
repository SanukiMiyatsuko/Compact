import Compact.FS.LadSeedOm

/-! 目標が `Ω_c` の崩壊の列の振り分け（細かい形）。

`cs (Ω_c) X` は、種の倍数（`lbi_mulNat`）、素の近似・一つずらし（最後の加数が ω 型なら `lbi_plain_om`、
big 型で共終数が `Ω_c` 未満なら列は big 型で自明、`Ω_c` 以上なら対角化）、種つきの近似のどれか。
対角化と種つきの場合は仮定 `DiagCaseOm`・`SeedCaseOm` として受け取る。 -/

namespace RTKA.Fund

open Tm W

/-- 目標が `Ω_c` の素の近似の列の記述 -/
def plainOm (c X : Tm) : SeqD :=
  (mkApp (.Om c) (.psi0 (.Om c)) (preT (info X).sums) (lastT (info X).sums) (lastS (info X).sums) .zero .zero).getD .none

/-- 種つきの近似の列の場合の仮定 -/
def SeedCaseOm : Prop :=
  ∀ c X Y H R L P k, WNF (.Psi .zero (.Om c) X) →
    ((isSucc X = true ∧ Y = pred X ∧ P = .Psi .zero (.Om c) (pred X)) ∨
      (¬ isSucc X = true ∧ Y = X ∧ maxL (frB (.Om c) X) = some P ∧
        Lt (plainOm c X).first P)) →
    summands Y = H ++ R :: L → Lt P R → (∀ s, s ∈ L → Le s P) →
    cs (.Om c) X = .app (.Om c) (.psi0 (.Om c)) H R (info R).seq P k →
    (∀ u, u ∈ subs (.Psi .zero (.Om c) X) → u ≠ .Psi .zero (.Om c) X → LadL (info u).seq) →
    LadL (cs (.Om c) X)

/-- 対角化（素の近似・ずらし、最後の加数の共終数が `Ω_c` 以上）の場合の仮定 -/
def DiagCaseOm : Prop :=
  ∀ c X pre R σ r k, WNF (.Psi .zero (.Om c) X) → ¬ isSucc X = true → summands X = pre ++ [R] →
    dom R = .big σ → ltB σ (.Om c) = false →
    (r = (info R).seq ∨ r = .shift (info R).seq) →
    cs (.Om c) X = .app (.Om c) (.psi0 (.Om c)) pre R r .zero k →
    (∀ u, u ∈ subs (.Psi .zero (.Om c) X) → u ≠ .Psi .zero (.Om c) X → LadL (info u).seq) →
    LadL (cs (.Om c) X)

/-- 列の記述が ω 型でなければ `LadL` は自明 -/
theorem ladL_of_not_omega {s : SeqD} (h : s.dom ≠ .omega) : LadL s :=
  ladL_of_nat fun hd => absurd hd h

/-- 素の近似・ずらし（最後の加数 `R`）の場合 -/
theorem ladL_plain_case (hD : DiagCaseOm) {c X : Tm} (ht : WNF (.Psi .zero (.Om c) X)) (hs : ¬ isSucc X = true)
    {pre : List Tm} {R : Tm} (hsum : summands X = pre ++ [R]) (j : Nat) (hj : j ≤ 1)
    (he : cs (.Om c) X = .app (.Om c) (.psi0 (.Om c)) pre R (if j = 0 then (info R).seq else .shift (info R).seq)
      .zero (kAdj (.Om c) (.Om c) (.psi0 (.Om c)) pre R (info R).seq))
    (hIH : ∀ u, u ∈ subs (.Psi .zero (.Om c) X) → u ≠ .Psi .zero (.Om c) X → LadL (info u).seq) :
    LadL (cs (.Om c) X) := by
  have hXF := ht.psi.aF
  have hN : NFL (pre ++ [R]) := hsum ▸ nfl_summands hXF
  have hRN := hN.1 R (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  have hRm : R ∈ summands X := by rw [hsum]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hR1 : R ≠ .one := by
    intro e
    apply hs
    show (summands X).getLast? == some one
    rw [hsum, e]
    simp
  obtain ⟨hd0, hd1⟩ := dom_ne_of_principal hRN.1 hRN.2 hR1
  have hRs : R ∈ subs (.Psi .zero (.Om c) X) := subs_psi_a (mem_subs_of_mem_summands hRm)
  have hRne : R ≠ .Psi .zero (.Om c) X := ne_of_size_lt (by
    have := size_le_of_mem_subs (mem_subs_of_mem_summands hRm)
    simp only [Tm.size]; omega)
  have hLR := hIH R hRs hRne
  cases hdR : dom R with
  | zero => exact absurd hdR hd0
  | one => exact absurd hdR hd1
  | omega =>
    have hnb : ∀ σ, (info R).seq.dom ≠ .big σ := fun σ e => by
      rw [show (info R).seq.dom = dom R from rfl, hdR] at e; cases e
    have hk : kAdj (.Om c) (.Om c) (.psi0 (.Om c)) pre R (info R).seq = .zero := kAdj_nat hnb
    rw [hk] at he
    refine ladL_of_nat fun hdt n => ?_
    have hdt' : dom (.Psi .zero (.Om c) X) = .omega := hdt
    have hs' : ∀ n, (info (.Psi .zero (.Om c) X)).seq.nat n =
        .Psi .zero (.Om c) (oadd (ofSummands pre) ((info R).seq.nat (n + j))) := by
      intro n
      show (cs (.Om c) X).nat n = _
      rw [he]
      have hnb' : ∀ σ, (if j = 0 then (info R).seq else SeqD.shift (info R).seq).dom ≠ .big σ := by
        intro σ
        split
        · exact hnb σ
        · exact hnb σ
      rw [app_nat_of_not_big hnb' n]
      have hxF := ((seqI_dom_nat hRN.1 hdR).1.good (n + j)).1
      have e1 : (if j = 0 then (info R).seq else SeqD.shift (info R).seq).nat n = (info R).seq.nat (n + j) := by
        split
        · rename_i h; subst h; rfl
        · rename_i h
          have : j = 1 := by omega
          subst this
          rfl
      rw [e1]
      show Tm.Psi .zero (.Om c) (oadd (ofSummands pre) (nsum (oadd .zero _) .zero)) = _
      rw [zero_oadd hxF, nsum_zero _ hxF]
    exact lbi_plain_om ht hsum hdR (hLR.nat hdR) j hdt' hs' n
  | big σ =>
    cases hl : ltB σ (.Om c) with
    | true =>
      refine ladL_of_not_omega ?_
      rw [he]
      have hd' : (if j = 0 then (info R).seq else SeqD.shift (info R).seq).dom = .big σ := by
        split <;> exact hdR
      rw [app_dom_big_lt hd' hl]
      intro e; cases e
    | false =>
      refine hD c X pre R σ _ _ ht hs hsum hdR hl ?_ he hIH
      split
      · exact Or.inl rfl
      · exact Or.inr rfl

/-- 後者の項の加数の前の部分 -/
theorem summands_pred_sums {X : Tm} (hX : WNF X) :
    summands (pred X) = ((info X).sums.dropLast).map Prod.fst := by
  unfold pred
  rw [summands_ofSummands _ (fun s hs => nfl_principal (nfl_summands hX) s (List.dropLast_subset _ hs)),
    ← info_sums_fst X, List.map_dropLast]

/-- `splitGtD` の残りの加数は閾値以下 -/
theorem splitGtD_rest_le {th : Tm} {ys : DL} {pre : List Tm} {R : Tm} {r : SeqD}
    (h : splitGtD th ys = some (pre, R, r)) {L : List Tm} (hN : NFL (pre ++ R :: L))
    (hys : ys.map Prod.fst = pre ++ R :: L) (hth : WNF th) : ∀ s, s ∈ L → Le s th := by
  obtain ⟨L', rest, hys', hL', -, -, hrest⟩ := splitGtD_spec h
  have hLe : L = rest.map Prod.fst := by
    rw [hys', List.map_append, List.map_cons, hL'] at hys
    simpa using hys.symm
  intro s hs
  cases hr : rest with
  | nil => rw [hLe, hr] at hs; cases hs
  | cons q tl =>
    have h1 := hrest q tl hr
    have hL1 : L = q.1 :: tl.map Prod.fst := by rw [hLe, hr]; rfl
    have hNL : NFL L := nfl_append_right (L := pre ++ [R]) (by simpa using hN)
    rw [hL1] at hNL hs
    have hq1F := (hNL.1 q.1 List.mem_cons_self).1
    have hq1 : Le q.1 th := le_of_not_ltY hth hq1F fun h' => by rw [ltB_iff.mpr h'] at h1; cases h1
    exact le_transY ((hNL.1 s hs).1) hq1F hth (le_head_mem hNL hs) hq1

/-- 目標が `Ω_c` の崩壊の下界（種つき・対角化を仮定して） -/
theorem ladL_psi_om_disp (hD : DiagCaseOm) (hS : SeedCaseOm) {c X : Tm} (ht : WNF (.Psi .zero (.Om c) X))
    (hIH : ∀ u, u ∈ subs (.Psi .zero (.Om c) X) → u ≠ .Psi .zero (.Om c) X → LadL (info u).seq) :
    LadL (info (.Psi .zero (.Om c) X)).seq := by
  rw [info_seq_psi0]
  have hπ := ht.psi.piF
  have hcs : isSucc c = true := (WNF.psiOm ht).2.2.1
  have hXF := ht.psi.aF
  by_cases hX0 : X = .zero
  · subst hX0
    rw [cs_om_zero]
    exact ladL_mul (omBase_wnf hπ hcs).1 (omBase_wnf hπ hcs).2 2
  by_cases hs : isSucc X = true
  · -- 後者の引数：種 `Ψ^0(X - 1)` の挿入
    have hq := wnf_psi_om_pred ht hs
    have hq0 : Tm.Psi .zero (.Om c) (pred X) ≠ .zero := fun e => by cases e
    have e0 := cs_om_succ ht hs
    unfold insertAtM at e0
    cases hsp : splitGtD (.Psi .zero (.Om c) (pred X)) (info X).sums.dropLast with
    | none =>
      rw [hsp] at e0
      rw [e0]
      show LadL (famSeq .om (.Om c) (some _))
      unfold famSeq
      exact ladL_mul hq rfl 2
    | some q =>
      obtain ⟨H, R, r⟩ := q
      rw [hsp] at e0
      dsimp only at e0
      rw [idxOK_om hq hq0, Bool.and_false] at e0
      simp only [Bool.false_eq_true, ↓reduceIte] at e0
      obtain ⟨L', rest, hys', hL', hR, -, -⟩ := splitGtD_spec hsp
      have hcoh := coh_sums X
      have hne : (info X).sums ≠ [] := sums_ne_nil hX0
      have hsumsplit : (info X).sums = (info X).sums.dropLast ++ [(info X).sums.getLast hne] :=
        (List.dropLast_concat_getLast hne).symm
      have hr : r = (info R).seq := by
        apply hcoh (R, r)
        rw [hsumsplit, hys']
        simp
      subst hr
      have hsumY : summands (pred X) = H ++ R :: rest.map Prod.fst := by
        rw [summands_pred_sums hXF, hys', ← hL']
        simp
      have hNY : NFL (H ++ R :: rest.map Prod.fst) := hsumY ▸ nfl_summands (wnf_pred hXF)
      have hqR : Lt (.Psi .zero (.Om c) (pred X)) R := ltB_iff.mp hR
      rw [mkApp_noArg (by rfl) (Or.inr hR)] at e0
      refine hS c X (pred X) H R (rest.map Prod.fst) _ _ ht (Or.inl ⟨hs, rfl, rfl⟩) hsumY hqR
        (splitGtD_rest_le hsp hNY (by rw [hys', ← hL']; simp) hq) e0 hIH
  · -- 極限の引数
    have hlim : cs (.Om c) X = limitSeq (.Om c) .om (.Om c) X (info X).sums none := by
      unfold cs cseq
      rw [ite_eq_right hX0]
      have hd := lastS_dom hXF hX0
      split
      · rename_i h
        rw [hd] at h
        exact absurd ((dom_eq_one_iff hXF).mp h) hs
      · rfl
    have hsum := summands_pre_last hX0 (X := X)
    have hr : lastS (info X).sums = (info (lastT (info X).sums)).seq := lastS_coh (coh_sums X)
    have hplain : plainOm c X = .app (.Om c) (.psi0 (.Om c)) (preT (info X).sums) (lastT (info X).sums)
        (if (0 : Nat) = 0 then (info (lastT (info X).sums)).seq else .shift (info (lastT (info X).sums)).seq)
        .zero (kAdj (.Om c) (.Om c) (.psi0 (.Om c)) (preT (info X).sums) (lastT (info X).sums)
          (info (lastT (info X).sums)).seq) := by
      unfold plainOm
      rw [mkApp_om_plain, Option.getD_some, hr]
      rfl
    have e0 := hlim
    unfold limitSeq at e0
    dsimp only at e0
    have hmo : ∀ q : Option Tm, maxOpt none q = q := fun q => by cases q <;> rfl
    rw [hmo] at e0
    change cs (.Om c) X = (match maxL (frB (.Om c) X) with
      | none => plainOm c X
      | some p =>
        if ltB p (plainOm c X).first = true then plainOm c X
        else if (plainOm c X).first = p then
          (mkApp (.Om c) (.psi0 (.Om c)) (preT (info X).sums) (lastT (info X).sums)
            (.shift (lastS (info X).sums)) .zero .zero).getD .none
        else insertAtL (.Om c) .om (.Om c) p (info X).sums) at e0
    cases hm : maxL (frB (.Om c) X) with
    | none =>
      rw [hm] at e0
      dsimp only at e0
      rw [hplain] at e0
      exact ladL_plain_case hD ht hs hsum 0 (Nat.zero_le _) e0 hIH
    | some p =>
      rw [hm] at e0
      dsimp only at e0
      have hpm : p ∈ fr (.Om c) X := by
        have := maxL_mem hm
        rwa [frB_eq_fr] at this
      have hpF : WNF p := hXF.of_mem_subs (fr_spec hpm).1
      have hpp : isPrincipal p = true := by
        rcases fr_node hpm with ⟨m, a, rfl⟩ | ⟨s', q, a, rfl⟩ <;> rfl
      have hp0 : p ≠ .zero := fun e => by rw [e] at hpp; cases hpp
      by_cases h1 : ltB p (plainOm c X).first = true
      · rw [ite_eq_left h1, hplain] at e0
        exact ladL_plain_case hD ht hs hsum 0 (Nat.zero_le _) e0 hIH
      rw [ite_eq_right h1] at e0
      by_cases h2 : (plainOm c X).first = p
      · rw [ite_eq_left h2] at e0
        rw [mkApp_om_plain, Option.getD_some, hr, kAdj_shift] at e0
        exact ladL_plain_case hD ht hs hsum 1 (Nat.le_refl _) e0 hIH
      rw [ite_eq_right h2] at e0
      -- 種 `p` の挿入
      have hfirst : Lt (plainOm c X).first p := by
        obtain ⟨hfw, -⟩ := plain_first_wnf ht hX0 hs (mkApp_om_plain _ _ _ _ _)
        have hfw' : WNF (plainOm c X).first := by unfold plainOm; rw [mkApp_om_plain]; exact hfw
        rcases le_of_not_ltY hpF hfw' (fun h => h1 (ltB_iff.mpr h)) with e | h
        · exact absurd e h2
        · exact h
      unfold insertAtL at e0
      cases hsp : splitGtD p (info X).sums with
      | none =>
        rw [hsp] at e0
        rw [e0]
        show LadL (famSeq .om (.Om c) (some p))
        unfold famSeq
        exact ladL_mul hpF hpp 2
      | some q =>
        obtain ⟨H, R, r⟩ := q
        rw [hsp] at e0
        dsimp only at e0
        rw [idxOK_om hpF hp0, Bool.and_false] at e0
        simp only [Bool.false_eq_true, ↓reduceIte] at e0
        obtain ⟨L', rest, hys', hL', hR, -, -⟩ := splitGtD_spec hsp
        have hr' : r = (info R).seq := by
          apply coh_sums X (R, r)
          rw [hys']
          simp
        subst hr'
        have hsumX : summands X = H ++ R :: rest.map Prod.fst := by
          rw [← info_sums_fst X, hys', ← hL']
          simp
        have hNX : NFL (H ++ R :: rest.map Prod.fst) := hsumX ▸ nfl_summands hXF
        rw [mkApp_noArg (by rfl) (Or.inr hR)] at e0
        exact hS c X X H R (rest.map Prod.fst) p _ ht (Or.inr ⟨hs, rfl, hm, hfirst⟩) hsumX (ltB_iff.mp hR)
          (splitGtD_rest_le hsp hNX (by rw [info_sums_fst X]; exact hsumX) hpF) e0 hIH

end RTKA.Fund
