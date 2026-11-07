import Compact.FS.LadTr

/-! `Ψ^0_π` の近似の列の 0 番目の形と、目標が `Ω_c` の崩壊 `w = Ψ^0_{Ω_c}(W)` の 0 番目の下界（z 側）。

* `first_app_psi0`：`app τ (psi0 π) pre R r P k` の 0 番目は `Ψ^0_π(pre ⊕ ((k ⊕ x) # P))`。`x` は `R` の列の
  0 番目（ω 型・big 型で `σ < τ`）か、対角化の添字 `γ₀` での値（`γ₀` は `0`・`kStart`・`sStart`）。
* `x` は `R[0]` 以上で、`x ∈ C(g, d)` なら `R[0] ∈ C(g, d)`（`BigUB.ub2`）。
* `zside_om`：`W ≠ 0` なら、`W` の前線は `w[0]` 以下で、標準形の `q = Ψ^0_{Ω_c}(V) ≤ w[0]` が
  `W[0] ≤ V`・`W[0] ∈ C(V, q)` を満たすものがある（後者の `W` は `V = W - 1`、極限は素の近似の 0 番目）。 -/

namespace RTKA.Fund

open Tm W

/-! ### 近似の列の 0 番目 -/

/-- ψ 型の生成では、K への対角化は正準な塔か種を外に足す型のどちらか -/
theorem canonK_or_out_K {τ : Tm} {m : Nat} {π : Tm} {pre : List Tm} {R : Tm} :
    canonK (.K m) (.psi0 π) pre R = true ∨ outsideMode τ (.K m) (.psi0 π) pre R = true := by
  unfold canonK outsideMode
  cases kOld m pre R <;> simp

/-- 対角化の近似の引数は、ψ 型の生成では種を必ず含む -/
theorem argOf_psi0 (τ σ π : Tm) (pre : List Tm) (R : Tm) (r : SeqD) (k P : Tm) :
    argOf τ σ (.psi0 π) pre R r k P (gam τ σ (.psi0 π) pre R r k P 0) =
      combine (.psi0 π) pre k P (r.big (gam τ σ (.psi0 π) pre R r k P 0)) := by
  unfold argOf
  by_cases h1 : canonK σ (.psi0 π) pre R = true
  · rw [ite_eq_left h1]
  · rw [ite_eq_right h1]
    by_cases h2 : outsideMode τ σ (.psi0 π) pre R = true
    · rw [ite_eq_left h2]
    · rw [ite_eq_right h2]
      have hg : gam τ σ (.psi0 π) pre R r k P 0 = .zero := by
        unfold gam
        rw [ite_eq_right h1, ite_eq_right h2]
        cases σ with
        | K m => exact (canonK_or_out_K (τ := τ) (m := m) (π := π) (pre := pre) (R := R)).elim (fun h => absurd h h1) (fun h => absurd h h2)
        | _ => rfl
      rw [hg]
      rfl

/-- `app τ (psi0 π) pre R r P k` の 0 番目 -/
theorem first_app_psi0 (τ π : Tm) (pre : List Tm) (R : Tm) (r : SeqD) (P k : Tm) :
    ∃ x, (SeqD.app τ (.psi0 π) pre R r P k).first = .Psi .zero π (combine (.psi0 π) pre k P x) ∧
      (((∀ σ, r.dom ≠ .big σ) ∧ x = r.nat 0) ∨
        ∃ σ, r.dom = .big σ ∧ x = r.big (if ltB σ τ = true then .zero else gam τ σ (.psi0 π) pre R r k P 0)) := by
  unfold SeqD.first
  cases hd : r.dom with
  | big σ =>
    by_cases hl : ltB σ τ = true
    · have e : (SeqD.app τ (.psi0 π) pre R r P k).dom = .big σ := by simp [SeqD.dom, hd, hl]
      rw [e]
      exact ⟨r.big .zero, rfl, Or.inr ⟨σ, rfl, by rw [ite_eq_left hl]⟩⟩
    · have e : (SeqD.app τ (.psi0 π) pre R r P k).dom = .omega := by simp [SeqD.dom, hd, hl]
      rw [e]
      refine ⟨r.big (gam τ σ (.psi0 π) pre R r k P 0), ?_, Or.inr ⟨σ, rfl, by rw [ite_eq_right hl]⟩⟩
      show SeqD.nat (.app τ (.psi0 π) pre R r P k) 0 = _
      simp only [SeqD.nat, hd, ite_eq_right hl]
      rw [argOf_psi0]
      rfl
  | zero =>
    have e : (SeqD.app τ (.psi0 π) pre R r P k).dom = .omega := by simp [SeqD.dom, hd]
    rw [e]
    refine ⟨r.nat 0, ?_, Or.inl ⟨fun σ h => (by cases h), rfl⟩⟩
    show SeqD.nat (.app τ (.psi0 π) pre R r P k) 0 = _
    simp only [SeqD.nat, hd]
    rfl
  | one =>
    have e : (SeqD.app τ (.psi0 π) pre R r P k).dom = .omega := by simp [SeqD.dom, hd]
    rw [e]
    refine ⟨r.nat 0, ?_, Or.inl ⟨fun σ h => (by cases h), rfl⟩⟩
    show SeqD.nat (.app τ (.psi0 π) pre R r P k) 0 = _
    simp only [SeqD.nat, hd]
    rfl
  | omega =>
    have e : (SeqD.app τ (.psi0 π) pre R r P k).dom = .omega := by simp [SeqD.dom, hd]
    rw [e]
    refine ⟨r.nat 0, ?_, Or.inl ⟨fun σ h => (by cases h), rfl⟩⟩
    show SeqD.nat (.app τ (.psi0 π) pre R r P k) 0 = _
    simp only [SeqD.nat, hd]
    rfl

/-- 対角化の添字の始点は `σ` 未満の標準形 -/
theorem gam0_spec {τ σ π : Tm} {pre : List Tm} {R : Tm} {r : SeqD} {k P : Tm} (hσ : WNF σ) (hσ0 : σ ≠ .zero)
    (hk : WNF k) (hP : WNF P) :
    WNF (gam τ σ (.psi0 π) pre R r k P 0) ∧ Lt (gam τ σ (.psi0 π) pre R r k P 0) σ := by
  unfold gam
  by_cases h1 : canonK σ (.psi0 π) pre R = true
  · rw [ite_eq_left h1]
    cases σ with
    | K m =>
      obtain ⟨h2, h3, -⟩ := start_spec (m := m) hσ.k hk hP
      exact ⟨h2, h3⟩
    | _ => simp [canonK] at h1
  · rw [ite_eq_right h1]
    by_cases h2 : outsideMode τ σ (.psi0 π) pre R = true
    · rw [ite_eq_left h2]
      cases σ with
      | K m => exact ⟨WNF.zero, zero_lt hσ0⟩
      | _ =>
        simp only [seedOut, ↓reduceIte]
        obtain ⟨h3, h4, -⟩ := sStart_spec hσ hσ0 hk hP
        exact ⟨h3, h4⟩
    · rw [ite_eq_right h2]
      cases σ with
      | K m => exact (canonK_or_out_K (τ := τ) (m := m) (π := π) (pre := pre) (R := R)).elim (fun h => absurd h h1) (fun h => absurd h h2)
      | _ => exact ⟨WNF.zero, zero_lt hσ0⟩

/-- 近似の 0 番目の `x` は `R[0]` 以上で、`x` の閉包の所属は `R[0]` に移る -/
theorem first_x_spec {τ π : Tm} {pre : List Tm} {R : Tm} {k P x : Tm} (hR : WNF R)
    (hd0 : dom R ≠ .zero) (hd1 : dom R ≠ .one) (hk : WNF k) (hP : WNF P)
    (hx : ((∀ σ, (info R).seq.dom ≠ .big σ) ∧ x = (info R).seq.nat 0) ∨
      ∃ σ, (info R).seq.dom = .big σ ∧
        x = (info R).seq.big (if ltB σ τ = true then .zero else gam τ σ (.psi0 π) pre R (info R).seq k P 0)) :
    WNF x ∧ Le (fund R .zero) x ∧
      ∀ g d, WNF g → WNF d → inC x g d = true → inC (fund R .zero) g d = true := by
  rw [fund_zero_first hd0 hd1]
  rcases hx with ⟨hnb, rfl⟩ | ⟨σ, hd, rfl⟩
  · have hdo : dom R = .omega := by
      cases h : dom R with
      | zero => exact absurd h hd0
      | one => exact absurd h hd1
      | omega => rfl
      | big σ => exact absurd h (hnb σ)
    rw [first_of_nat hdo]
    exact ⟨((seqI_dom_nat hR hdo).1.good 0).1, Or.inl rfl, fun _ _ _ _ h => h⟩
  · rw [first_of_big hd]
    obtain ⟨hU, hreg⟩ := seqI_dom_big hR hd
    have hσF := hU.hσF
    have hσ0 := hreg.ne_zero
    have hz := hU.good.1 .zero WNF.zero (zero_lt hσ0)
    by_cases hl : ltB σ τ = true
    · rw [ite_eq_left hl]
      exact ⟨hz.1, Or.inl rfl, fun _ _ _ _ h => h⟩
    · rw [ite_eq_right hl]
      obtain ⟨hγ, hγσ⟩ := gam0_spec (τ := τ) (π := π) (pre := pre) (R := R) (r := (info R).seq) hσF hσ0 hk hP
      generalize gam τ σ (.psi0 π) pre R (info R).seq k P 0 = γ at hγ hγσ
      by_cases hγ0 : γ = .zero
      · subst hγ0
        exact ⟨hz.1, Or.inl rfl, fun _ _ _ _ h => h⟩
      · have h0γ : Lt .zero γ := zero_lt hγ0
        exact ⟨(hU.good.1 γ hγ hγσ).1, Or.inr (hU.good.2 .zero γ WNF.zero hγ h0γ hγσ),
          fun g d hg hd h => hU.ub2 g d .zero γ hg hd WNF.zero hγ h0γ hγσ h (inC_zero _ _)⟩

/-! ### 和の 0 番目 -/

/-- `pre ⊕ y` の加数（`y` の加数が `pre` の各加数以下） -/
theorem summands_oadd_le {pre : List Tm} {y : Tm} (hpre : NFL pre) (hy : WNF y)
    (hge : ∀ s, s ∈ pre → ∀ u, u ∈ summands y → Le u s) :
    summands (oadd (ofSummands pre) y) = pre ++ summands y :=
  summands_oadd_pre hpre hy fun s h r hs e => le_leB (hge s hs h (by rw [e]; exact List.mem_cons_self))

/-- 項の加数は項以下 -/
theorem summand_le {y u : Tm} (hy : WNF y) (hu : u ∈ summands y) : Le u y := by
  have := le_ofSummands_of_mem (nfl_summands hy) hu
  rwa [ofSummands_summands y hy] at this

/-- 加数が `pre ++ [R]` の項の 0 番目は `pre ⊕ R[0]` -/
theorem fund_of_summands_last : ∀ (pre : List Tm) {W R : Tm}, WNF W → summands W = pre ++ [R] →
    fund W .zero = oadd (ofSummands pre) (fund R .zero)
  | [], W, R, hW, hs => by
    have hWR : W = R := by
      have := ofSummands_summands W hW
      rw [hs] at this
      exact this.symm
    subst hWR
    exact (zero_oadd (fund_wnf hW WNF.zero)).symm
  | x :: pre, W, R, hW, hs => by
    cases W with
    | plus a b =>
      rw [summands_plus] at hs
      simp only [List.cons_append, List.cons.injEq] at hs
      obtain ⟨e, hsb⟩ := hs
      subst e
      obtain ⟨ha, hb, -, -⟩ := hW.plus
      rw [fund_plus hW, fund_of_summands_last pre hb hsb]
      have hN' : NFL ((a :: pre) ++ [R]) := by
        have := nfl_summands hW
        rw [summands_plus, hsb] at this
        simpa using this
      have hNpre : NFL (a :: pre) := nfl_append_left hN'
      have hpreN : NFL pre := nfl_append_left (by have := nfl_summands hb; rwa [hsb] at this)
      have hRF : WNF R := (hN'.1 R (by simp)).1
      have hy := fund_wnf hRF WNF.zero
      have hyR := fund_zero_le hRF
      have hge : ∀ s, s ∈ a :: pre → ∀ u, u ∈ summands (fund R .zero) → Le u s := by
        intro s hs u hu
        have hsF := (hNpre.1 s hs).1
        have hsR : Le R s := le_of_ne_gtY hRF hsF (le_of_nfl_append (rest := []) hN' s hs)
        have huF := ((nfl_summands hy).1 u hu).1
        exact le_transY huF hy hsF (summand_le hy hu) (le_transY hy hRF hsF hyR hsR)
      have hZF : WNF (oadd (ofSummands pre) (fund R .zero)) := wnf_oadd (wnf_ofSummands hpreN) hy
      have hZs : summands (oadd (ofSummands pre) (fund R .zero)) = pre ++ summands (fund R .zero) :=
        summands_oadd_le hpreN hy fun s hs u hu => hge s (List.mem_cons_of_mem _ hs) u hu
      have hL : summands (oadd a (oadd (ofSummands pre) (fund R .zero))) =
          a :: (pre ++ summands (fund R .zero)) := by
        have h2 := summands_oadd_le (pre := [a]) (y := oadd (ofSummands pre) (fund R .zero))
          (nfl_append_left (l := [a]) (m := pre) (by simpa using hNpre)) hZF (fun s hs u hu => by
            rw [List.mem_singleton] at hs
            subst hs
            rw [hZs] at hu
            rcases List.mem_append.mp hu with hu | hu
            · exact le_head_mem hNpre (List.mem_cons_of_mem _ hu)
            · exact hge s List.mem_cons_self u hu)
        rw [show ofSummands [a] = a from rfl] at h2
        rw [h2, hZs]
        rfl
      have hR' : summands (oadd (ofSummands (a :: pre)) (fund R .zero)) =
          a :: (pre ++ summands (fund R .zero)) := by
        rw [summands_oadd_le hNpre hy hge]
        rfl
      have h1 := ofSummands_summands _ (wnf_oadd ha hZF)
      have h2 := ofSummands_summands _ (wnf_oadd (wnf_ofSummands hNpre) hy)
      rw [hL] at h1
      rw [hR'] at h2
      rw [← h1, ← h2]
    | _ => simp [summands] at hs

/-! ### 種は近似の列の 0 番目未満 -/

/-- 種 `p` は `app τ (psi0 π) pre R r p k` の 0 番目未満 -/
theorem seed_lt_app_first {τ π p k : Tm} {pre : List Tm} {R : Tm}
    (hf : WNF (SeqD.app τ (.psi0 π) pre R (info R).seq p k).first)
    (hpre : WNF (ofSummands pre)) (hR : WNF R) (hd0 : dom R ≠ .zero) (hd1 : dom R ≠ .one)
    (hk : WNF k) (hp : WNF p) (hpfr : p ∈ fr π p) :
    Lt p (SeqD.app τ (.psi0 π) pre R (info R).seq p k).first := by
  obtain ⟨x, hx, hxd⟩ := first_app_psi0 τ π pre R (info R).seq p k
  obtain ⟨hxF, -, -⟩ := first_x_spec hR hd0 hd1 hk hp hxd
  rw [hx] at hf ⊢
  exact FWOrder.k2 hf p (fr_combine_psi0_of_P hpre hk hp hxF hpfr)

/-! ### 目標が `Ω_c`：`w = Ψ^0_{Ω_c}(W)` の 0 番目 -/

/-- `Ψ^0_{Ω_c}(W)`（`W ≠ 0`）の共終数は `0`・後者でない -/
theorem dom_psi0_ne {π W : Tm} (hw : WNF (.Psi .zero π W)) :
    dom (.Psi .zero π W) ≠ .zero ∧ dom (.Psi .zero π W) ≠ .one := by
  have hcsI := cseq_isC π (info π).fam W (info W).sums
  exact ⟨fun e => cs_ne_none hw (SeqD.eq_none_of_dom hcsI e), SeqD.dom_ne_one hcsI⟩

/-- 崩壊の 0 番目は列の記述の 0 番目 -/
theorem fund_psi0_first {π W : Tm} (hw : WNF (.Psi .zero π W)) :
    fund (.Psi .zero π W) .zero = (cs π W).first :=
  fund_zero_first (dom_psi0_ne hw).1 (dom_psi0_ne hw).2

/-- 解析の加数の並びの切り出し：`splitGtD` の結果は `X` の加数の接頭辞と、その記述 -/
theorem splitGtD_sums {th X : Tm} {ys : DL} (hX : WNF X) (hys : ∃ zs, (info X).sums = ys ++ zs)
    {pre : List Tm} {R : Tm} {r : SeqD} (h : splitGtD th ys = some (pre, R, r)) :
    r = (info R).seq ∧ (∃ rest, summands X = pre ++ R :: rest) ∧ Lt th R := by
  obtain ⟨L, rest, hys', hL, hR, -, -⟩ := splitGtD_spec h
  obtain ⟨zs, hzs⟩ := hys
  have hcoh := coh_sums X
  rw [hzs, hys'] at hcoh
  refine ⟨hcoh (R, r) (by simp), ⟨rest.map Prod.fst ++ zs.map Prod.fst, ?_⟩, ltB_iff.mp hR⟩
  rw [← info_sums_fst X, hzs, hys', ← hL]
  simp

/-- 後者の引数：種 `Ψ^0_{Ω_c}(W - 1)` は `w[0]` 未満 -/
theorem zside_om_succ {c W : Tm} (hw : WNF (.Psi .zero (.Om c) W)) (hs : isSucc W = true) :
    Lt (.Psi .zero (.Om c) (pred W)) (fund (.Psi .zero (.Om c) W) .zero) := by
  have hWF := hw.psi.aF
  have hπ := hw.psi.piF
  have hq := wnf_psi_om_pred hw hs
  have hf := fund_wnf hw WNF.zero
  rw [fund_psi0_first hw] at hf ⊢
  rw [cs_om_succ hw hs] at hf ⊢
  have hq0 : Tm.Psi .zero (.Om c) (pred W) ≠ .zero := fun e => by cases e
  unfold insertAtM at hf ⊢
  cases hsp : splitGtD (.Psi .zero (.Om c) (pred W)) (info W).sums.dropLast with
  | none =>
    dsimp only
    show Lt _ (famSeq .om (.Om c) (some _)).first
    unfold famSeq
    show Lt _ (mulNat _ (0 + 2))
    exact lt_plus_leftY (wnf_mulNat hq rfl 2)
  | some q =>
    obtain ⟨pre, R, r⟩ := q
    rw [hsp] at hf
    dsimp only at hf ⊢
    rw [idxOK_om hq hq0, Bool.and_false] at hf ⊢
    simp only [Bool.false_eq_true, ↓reduceIte] at hf ⊢
    obtain ⟨hr, ⟨rest, hsum⟩, hqR⟩ := splitGtD_sums hWF
      (by
        have hne : (info W).sums ≠ [] := sums_ne_nil (fun e => by rw [e] at hs; simp [isSucc, summands] at hs)
        exact ⟨[(info W).sums.getLast hne], (List.dropLast_concat_getLast hne).symm⟩) hsp
    subst hr
    have hNs : NFL (pre ++ R :: rest) := hsum ▸ nfl_summands hWF
    have hRN := hNs.1 R (List.mem_append_right _ List.mem_cons_self)
    have hpre := wnf_ofSummands (nfl_append_left hNs)
    have hR1 : R ≠ .one := fun e => by
      rw [e] at hqR
      exact hq0 (lt_oneY hq hqR)
    obtain ⟨hd0, hd1⟩ := dom_ne_of_principal hRN.1 hRN.2 hR1
    have hR0 : R ≠ .zero := fun e => by rw [e] at hRN; cases hRN.2
    have hk := (kAdj_spec (ceil := .Om c) (g := .psi0 (.Om c)) (pre := pre) (r := (info R).seq) hπ hR0 hRN.1
      fun σ hd => ⟨(seqI_dom_big hRN.1 hd).1.hσF, (seqI_dom_big hRN.1 hd).1.hσle⟩).hF
    rw [mkApp_noArg (by rfl) (Or.inr (ltB_iff.mpr hqR))] at hf ⊢
    exact seed_lt_app_first hf hpre hRN.1 hd0 hd1 hk hq
      (mem_fr_self (Or.inr ⟨_, _, _, rfl⟩) (lt_psi_targetY hq))

/-- `ω` 型の加数には調整はない -/
theorem kAdj_nat {τ ceil : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD} (hd : ∀ σ, r.dom ≠ .big σ) :
    kAdj τ ceil g pre R r = .zero := by
  unfold kAdj
  cases h : r.dom with
  | big σ => exact absurd h (hd σ)
  | _ => rfl

/-- 調整は列の記述の共終数だけで決まる（一つずらしても同じ） -/
theorem kAdj_shift {τ ceil : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD} :
    kAdj τ ceil g pre R (.shift r) = kAdj τ ceil g pre R r := rfl

/-- 目標が `Ω_c` で種 `p` を挿入した列の 0 番目は `p` より大きい -/
theorem seed_lt_insertAtL {c p : Tm} {W : Tm} (hw : WNF (.Psi .zero (.Om c) W))
    (hp : WNF p) (hp0 : p ≠ .zero) (hpfr : p ∈ fr (.Om c) p)
    (hf : WNF (insertAtL (.Om c) .om (.Om c) p (info W).sums).first) :
    Lt p (insertAtL (.Om c) .om (.Om c) p (info W).sums).first := by
  have hWF := hw.psi.aF
  have hπ := hw.psi.piF
  have hpp : isPrincipal p = true := by
    rcases fr_node hpfr with ⟨m, a, rfl⟩ | ⟨s, q, a, rfl⟩ <;> rfl
  unfold insertAtL at hf ⊢
  cases hsp : splitGtD p (info W).sums with
  | none =>
    dsimp only
    show Lt _ (famSeq .om (.Om c) (some _)).first
    unfold famSeq
    show Lt _ (mulNat _ (0 + 2))
    exact lt_plus_leftY (wnf_mulNat hp hpp 2)
  | some q =>
    obtain ⟨pre, R, r⟩ := q
    rw [hsp] at hf
    dsimp only at hf ⊢
    rw [idxOK_om hp hp0, Bool.and_false] at hf ⊢
    simp only [Bool.false_eq_true, ↓reduceIte] at hf ⊢
    obtain ⟨hr, ⟨rest, hsum⟩, hpR⟩ := splitGtD_sums hWF ⟨[], by simp⟩ hsp
    subst hr
    have hNs : NFL (pre ++ R :: rest) := hsum ▸ nfl_summands hWF
    have hRN := hNs.1 R (List.mem_append_right _ List.mem_cons_self)
    have hpre := wnf_ofSummands (nfl_append_left hNs)
    have hR1 : R ≠ .one := fun e => by
      rw [e] at hpR
      exact hp0 (lt_oneY hp hpR)
    obtain ⟨hd0, hd1⟩ := dom_ne_of_principal hRN.1 hRN.2 hR1
    have hR0 : R ≠ .zero := fun e => by rw [e] at hRN; cases hRN.2
    have hk := (kAdj_spec (ceil := .Om c) (g := .psi0 (.Om c)) (pre := pre) (r := (info R).seq) hπ hR0 hRN.1
      fun σ hd => ⟨(seqI_dom_big hRN.1 hd).1.hσF, (seqI_dom_big hRN.1 hd).1.hσle⟩).hF
    rw [mkApp_noArg (by rfl) (Or.inr (ltB_iff.mpr hpR))] at hf ⊢
    exact seed_lt_app_first hf hpre hRN.1 hd0 hd1 hk hp hpfr

/-! ### 始点・調整は節点か `0`（後者でない） -/

/-- `0` か節点 -/
def NodeOrZero (x : Tm) : Prop := x = .zero ∨ (∃ m a, x = .Xi m a) ∨ ∃ s p a, x = .Psi s p a

theorem NodeOrZero.ns {x : Tm} (h : NodeOrZero x) : ¬ isSucc x = true := by
  rcases h with rfl | ⟨m, a, rfl⟩ | ⟨s, p, a, rfl⟩
  · simp [isSucc, summands]
  · rw [isSucc_principal rfl]; simp
  · rw [isSucc_principal rfl]; simp

theorem maxCl_node {cl : Tm → Bool} {ub G : Tm} : ∀ {e : Tm}, maxCl cl ub e = some G →
    (∃ m a, G = .Xi m a) ∨ ∃ s p a, G = .Psi s p a
  | .zero, h | .one, h | .K _, h => by simp [maxCl] at h
  | .plus a b, h => by
    rcases maxOpt_cases h with h | h
    · exact maxCl_node h
    · exact maxCl_node h
  | .Om a, h => maxCl_node (e := a) h
  | .Xi m' a, h => by
    rcases maxOpt_cases h with h | h
    · split at h
      · simp only [Option.some.injEq] at h
        exact Or.inl ⟨m', a, h.symm⟩
      · cases h
    · exact maxCl_node h
  | .Psi s p a, h => by
    rcases maxOpt_cases h with h | h
    · split at h
      · simp only [Option.some.injEq] at h
        exact Or.inr ⟨s, p, a, h.symm⟩
      · cases h
    · rcases maxOpt_cases h with h | h
      · exact maxCl_node h
      · rcases maxOpt_cases h with h | h
        · exact maxCl_node h
        · exact maxCl_node h

theorem getD_node {o : Option Tm} (h : ∀ G, o = some G → (∃ m a, G = .Xi m a) ∨ ∃ s p a, G = .Psi s p a) :
    NodeOrZero (o.getD .zero) := by
  cases e : o with
  | none => exact Or.inl rfl
  | some G => exact Or.inr (h G e)

theorem foldr_maxOpt_node : ∀ {l : List (Option Tm)}, (∀ o, o ∈ l → ∀ G, o = some G →
    (∃ m a, G = .Xi m a) ∨ ∃ s p a, G = .Psi s p a) → ∀ G, l.foldr maxOpt none = some G →
    (∃ m a, G = .Xi m a) ∨ ∃ s p a, G = .Psi s p a
  | [], _, G, h => by simp at h
  | o :: l, hl, G, h => by
    rcases maxOpt_cases h with h | h
    · exact hl o List.mem_cons_self G h
    · exact foldr_maxOpt_node (fun o' ho' => hl o' (List.mem_cons_of_mem _ ho')) G h

theorem frCl_node (cl : Tm → Bool) (τ : Tm) : NodeOrZero (frCl cl τ) := by
  unfold frCl
  refine getD_node fun G hG => foldr_maxOpt_node (fun o ho G' hG' => ?_) G hG
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp ho
  exact maxCl_node hG'

theorem kStart_node (m : Nat) (c P : Tm) : NodeOrZero (kStart m c P) := by
  unfold kStart
  refine getD_node fun G hG => ?_
  rcases maxOpt_cases hG with h | h <;> exact maxCl_node h

theorem kAdj_node (τ ceil : Tm) (g : Gen) (pre : List Tm) (R : Tm) (r : SeqD) :
    NodeOrZero (kAdj τ ceil g pre R r) := by
  unfold kAdj
  split
  · split
    · exact frCl_node _ _
    · exact Or.inl rfl
  · split
    · exact frCl_node _ _
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- 対角化の添字の始点は後者でない -/
theorem gam0_ns {τ σ π : Tm} {pre : List Tm} {R : Tm} {r : SeqD} {k P : Tm} (hσ : WNF σ) (hσ0 : σ ≠ .zero)
    (hk : WNF k) (hP : WNF P) : ¬ isSucc (gam τ σ (.psi0 π) pre R r k P 0) = true := by
  unfold gam
  by_cases h1 : canonK σ (.psi0 π) pre R = true
  · rw [ite_eq_left h1]
    cases σ with
    | K m => exact (kStart_node m k P).ns
    | _ => simp [canonK] at h1
  · rw [ite_eq_right h1]
    by_cases h2 : outsideMode τ σ (.psi0 π) pre R = true
    · rw [ite_eq_left h2]
      cases σ with
      | K m => simp [isSucc, summands]
      | _ =>
        simp only [seedOut, ↓reduceIte]
        exact (sStart_spec hσ hσ0 hk hP).2.2.1
    · rw [ite_eq_right h2]
      cases σ with
      | K m =>
        exact ((canonK_or_out_K (τ := τ) (m := m) (π := π) (pre := pre) (R := R)).elim (fun h => absurd h h1) (fun h => absurd h h2))
      | _ => simp [seedOut, isSucc, summands]

/-- 極限の引数：前線は `w[0]` 以下で、素の近似の 0 番目 `q = Ψ^0(V)` は `w[0]` 以下、`W[0] ≤ V`、`W[0] ∈ C(V, q)` -/
theorem zside_om_lim {c W : Tm} (hw : WNF (.Psi .zero (.Om c) W)) (hW0 : W ≠ .zero) (hs : ¬ isSucc W = true) :
    (∀ f, f ∈ fr (.Om c) W → Le f (fund (.Psi .zero (.Om c) W) .zero)) ∧
    ∃ V, WNF (.Psi .zero (.Om c) V) ∧ Le (.Psi .zero (.Om c) V) (fund (.Psi .zero (.Om c) W) .zero) ∧
      Le (fund W .zero) V ∧ inC (fund W .zero) V (.Psi .zero (.Om c) V) = true ∧
      (V = fund W .zero ∨ ¬ isSucc V = true) := by
  have hWF := hw.psi.aF
  have hπ := hw.psi.piF
  obtain ⟨pre, hpre_def⟩ : ∃ pre, pre = preT (info W).sums := ⟨_, rfl⟩
  obtain ⟨R, hR_def⟩ : ∃ R, R = lastT (info W).sums := ⟨_, rfl⟩
  have hr : lastS (info W).sums = (info R).seq := by rw [hR_def]; exact lastS_coh (coh_sums W)
  have hsum : summands W = pre ++ [R] := by rw [hpre_def, hR_def]; exact summands_pre_last hW0
  have hNs : NFL (pre ++ R :: []) := hsum ▸ nfl_summands hWF
  have hRN := hNs.1 R (List.mem_append_right _ List.mem_cons_self)
  have hpreN := nfl_append_left hNs
  have hpreF := wnf_ofSummands hpreN
  have hR1 : R ≠ .one := by
    intro e
    apply hs
    show (summands W).getLast? == some one
    rw [hsum, e]
    simp
  obtain ⟨hd0, hd1⟩ := dom_ne_of_principal hRN.1 hRN.2 hR1
  have hR0 : R ≠ .zero := fun e => by rw [e] at hRN; cases hRN.2
  have hk0 := kAdj_spec (ceil := .Om c) (g := .psi0 (.Om c)) (pre := pre) (r := (info R).seq) hπ hR0 hRN.1
    fun σ hd => ⟨(seqI_dom_big hRN.1 hd).1.hσF, (seqI_dom_big hRN.1 hd).1.hσle⟩
  generalize hk0e : kAdj (.Om c) (.Om c) (.psi0 (.Om c)) pre R (info R).seq = k0 at hk0
  -- 素の近似の 0 番目
  obtain ⟨x, hx, hxd⟩ := first_app_psi0 (.Om c) (.Om c) pre R (info R).seq .zero k0
  obtain ⟨hxF, hRx, hxC⟩ := first_x_spec hRN.1 hd0 hd1 hk0.hF WNF.zero hxd
  have hplain : (mkApp (.Om c) (.psi0 (.Om c)) (preT (info W).sums) (lastT (info W).sums)
      (lastS (info W).sums) .zero .zero).getD .none = .app (.Om c) (.psi0 (.Om c)) pre R (info R).seq .zero k0 := by
    rw [hr, ← hpre_def, ← hR_def, mkApp_om_plain, hk0e]
    rfl
  have hqF : WNF (.Psi .zero (.Om c) (combine (.psi0 (.Om c)) pre k0 .zero x)) := by
    obtain ⟨hfw, -⟩ := plain_first_wnf hw hW0 hs (mkApp_om_plain _ _ _ _ _)
    have e : (SeqD.app (.Om c) (.psi0 (.Om c)) (preT (info W).sums) (lastT (info W).sums)
        (lastS (info W).sums) .zero (kAdj (.Om c) (.Om c) (.psi0 (.Om c)) (preT (info W).sums)
          (lastT (info W).sums) (lastS (info W).sums))) = .app (.Om c) (.psi0 (.Om c)) pre R (info R).seq .zero k0 := by
      rw [hr, ← hpre_def, ← hR_def, hk0e]
    rw [e, hx] at hfw
    exact hfw
  have hkx : WNF (oadd k0 x) := wnf_oadd hk0.hF hxF
  have hVe : combine (.psi0 (.Om c)) pre k0 .zero x = oadd (ofSummands pre) (oadd k0 x) := by
    show oadd (ofSummands pre) (nsum (oadd k0 x) .zero) = _
    rw [nsum_zero _ hkx]
  -- `x < R`
  have hxR : Lt x R := by
    rcases hxd with ⟨hnb, rfl⟩ | ⟨σ, hd, rfl⟩
    · have hdo : dom R = .omega := by
        cases h : dom R with
        | zero => exact absurd h hd0
        | one => exact absurd h hd1
        | omega => rfl
        | big σ => exact absurd h (hnb σ)
      exact ((seqI_dom_nat hRN.1 hdo).1.good 0).2.1
    · obtain ⟨hU, hreg⟩ := seqI_dom_big hRN.1 hd
      split
      · exact (hU.good.1 .zero WNF.zero (zero_lt hreg.ne_zero)).2
      · obtain ⟨hγ, hγσ⟩ := gam0_spec (τ := .Om c) (π := .Om c) (pre := pre) (R := R) (r := (info R).seq)
          hU.hσF hreg.ne_zero hk0.hF WNF.zero
        exact (hU.good.1 _ hγ hγσ).2
  have hkxR : Lt (oadd k0 x) R := oadd_lt_prin hk0.hF hxF hRN.2 hk0.hR hxR
  have hW0e := fund_of_summands_last pre hWF hsum
  have hfRF := fund_wnf hRN.1 WNF.zero
  -- `W[0] ≤ V` と `W[0] ∈ C(V, q)`
  have hle : Le (fund W .zero) (combine (.psi0 (.Om c)) pre k0 .zero x) := by
    rw [hW0e, hVe]
    exact oadd_le_oadd hpreF hfRF hkx (le_transY hfRF hxF hkx hRx (le_oadd_right hk0.hF hxF))
  have hC : inC (fund W .zero) (combine (.psi0 (.Om c)) pre k0 .zero x)
      (.Psi .zero (.Om c) (combine (.psi0 (.Om c)) pre k0 .zero x)) = true := by
    have hV := inC_arg_psi hqF
    have hV' : inC (oadd (ofSummands pre) (oadd k0 x)) (combine (.psi0 (.Om c)) pre k0 .zero x)
        (.Psi .zero (.Om c) (combine (.psi0 (.Om c)) pre k0 .zero x)) = true := by
      rw [← hVe]; exact hV
    obtain ⟨h1, h2⟩ := inC_oadd_parts hNs hkx hkxR hV'
    have h3 : inC x _ _ = true := (inC_iff_summands hxF).mpr fun s hs => by
      refine inC_of_mem_summands hkx h2 ?_
      cases hsx : summands x with
      | nil => rw [hsx] at hs; cases hs
      | cons h t =>
        rw [summands_oadd hsx (nfl_principal (nfl_summands hk0.hF)) (nfl_principal (nfl_summands hxF))]
        exact List.mem_append_right _ (hsx ▸ hs)
    rw [hW0e]
    exact inC_oadd hpreF hfRF h1 (hxC _ _ hqF.psi.aF hqF h3)
  -- `V` は `W[0]` そのものか、後者でない
  have hVd : combine (.psi0 (.Om c)) pre k0 .zero x = fund W .zero ∨
      ¬ isSucc (combine (.psi0 (.Om c)) pre k0 .zero x) = true := by
    rw [hVe]
    rcases hxd with ⟨hnb, hxe⟩ | ⟨σ, hd, hxe⟩
    · left
      have hk00 : k0 = .zero := by rw [← hk0e]; exact kAdj_nat hnb
      have hdo : (info R).seq.dom = .omega := by
        cases h : (info R).seq.dom with
        | zero => exact absurd h hd0
        | one => exact absurd h hd1
        | omega => rfl
        | big σ => exact absurd h (hnb σ)
      rw [hk00, zero_oadd hxF, hW0e, hxe, fund_zero_first hd0 hd1, first_of_nat hdo]
    · by_cases hl : ltB σ (.Om c) = true
      · left
        have hk00 : k0 = .zero := by
          rw [← hk0e]
          unfold kAdj
          rw [hd]
          cases σ <;> simp [hl]
        rw [ite_eq_left hl] at hxe
        rw [hk00, zero_oadd hxF, hW0e, hxe, fund_zero_first hd0 hd1, first_of_big hd]
      · rw [ite_eq_right hl] at hxe
        obtain ⟨hU, hreg⟩ := seqI_dom_big hRN.1 hd
        have hγns := gam0_ns (τ := .Om c) (π := .Om c) (pre := pre) (R := R) (r := (info R).seq)
          hU.hσF hreg.ne_zero hk0.hF WNF.zero
        obtain ⟨hγ, hγσ⟩ := gam0_spec (τ := .Om c) (π := .Om c) (pre := pre) (R := R) (r := (info R).seq)
          hU.hσF hreg.ne_zero hk0.hF WNF.zero
        have hxns : ¬ isSucc x = true := by rw [hxe]; exact hU.ns hRN.2 _ hγ hγσ hγns
        have hk0n : NodeOrZero k0 := hk0e ▸ kAdj_node _ _ _ _ _ _
        by_cases hx0 : x = .zero
        · by_cases hk00 : k0 = .zero
          · left
            have hR00 : fund R .zero = .zero := by
              rcases hRx with e | h
              · rw [e, hx0]
              · rw [hx0] at h
                exact absurd h (not_lt_zero _)
            rw [hk00, hx0, hW0e, hR00]
            rfl
          · right
            rw [hx0, oadd_zero]
            exact not_succ_oadd hpreF hk0.hF hk00 hk0n.ns
        · right
          have hkx0 : oadd k0 x ≠ .zero := fun e => by
            have h1 := le_oadd_right hk0.hF hxF
            rw [e] at h1
            rcases h1 with h1 | h1
            · exact hx0 h1
            · exact not_lt_zero _ h1
          exact not_succ_oadd hpreF hkx hkx0 (not_succ_oadd hk0.hF hxF hx0 hxns)
  suffices key : (∀ f, f ∈ fr (.Om c) W → Le f (fund (.Psi .zero (.Om c) W) .zero)) ∧
      Le (.Psi .zero (.Om c) (combine (.psi0 (.Om c)) pre k0 .zero x)) (fund (.Psi .zero (.Om c) W) .zero) from
    ⟨key.1, _, hqF, key.2, hle, hC, hVd⟩
  have hlim : cs (.Om c) W = limitSeq (.Om c) .om (.Om c) W (info W).sums none := by
    unfold cs cseq
    rw [ite_eq_right hW0]
    have hd := lastS_dom hWF hW0
    split
    · rename_i h
      rw [hd] at h
      exact absurd ((dom_eq_one_iff hWF).mp h) hs
    · rfl
  have hfrW : ∀ f, f ∈ frB (.Om c) W → WNF f := fun f hf => by
    rw [frB_eq_fr] at hf
    exact hWF.of_mem_subs (fr_spec hf).1
  have hf := fund_wnf hw WNF.zero
  rw [fund_psi0_first hw, hlim] at hf ⊢
  unfold limitSeq at hf ⊢
  dsimp only at hf ⊢
  rw [hplain] at hf ⊢
  have hmo : ∀ q : Option Tm, maxOpt none q = q := fun q => by cases q <;> rfl
  rw [hmo] at hf ⊢
  cases hm : maxL (frB (.Om c) W) with
  | none =>
    dsimp only
    rw [hx]
    refine ⟨fun f hf' => ?_, Or.inl rfl⟩
    rw [← frB_eq_fr, maxL_none hm] at hf'
    cases hf'
  | some p =>
    rw [hm] at hf
    dsimp only at hf ⊢
    have hpm : p ∈ fr (.Om c) W := by
      have := maxL_mem hm
      rwa [frB_eq_fr] at this
    have hpF : WNF p := hWF.of_mem_subs (fr_spec hpm).1
    have hfp : ∀ f, f ∈ fr (.Om c) W → Le f p := fun f hf' =>
      le_maxL hfrW hm (by rw [frB_eq_fr]; exact hf')
    by_cases h1 : ltB p (SeqD.app (.Om c) (.psi0 (.Om c)) pre R (info R).seq .zero k0).first = true
    · -- 素の近似：種は 0 番目未満
      rw [ite_eq_left h1]
      rw [hx]
      have hpq : Lt p (.Psi .zero (.Om c) (combine (.psi0 (.Om c)) pre k0 .zero x)) := by
        rw [hx] at h1
        exact ltB_iff.mp h1
      exact ⟨fun f hf' => le_transY (hWF.of_mem_subs (fr_spec hf').1) hpF hqF (hfp f hf')
        (Or.inr hpq), Or.inl rfl⟩
    rw [ite_eq_right h1] at hf ⊢
    by_cases h2 : (SeqD.app (.Om c) (.psi0 (.Om c)) pre R (info R).seq .zero k0).first = p
    · -- 一つずらした素の近似
      rw [ite_eq_left h2] at hf ⊢
      rw [hr, ← hpre_def, ← hR_def, mkApp_om_plain, Option.getD_some, kAdj_shift, hk0e] at hf ⊢
      obtain ⟨x', hx', hxd'⟩ := first_app_psi0 (.Om c) (.Om c) pre R (.shift (info R).seq) .zero k0
      rw [hx'] at hf ⊢
      have hqle : Le (.Psi .zero (.Om c) (combine (.psi0 (.Om c)) pre k0 .zero x))
          (.Psi .zero (.Om c) (combine (.psi0 (.Om c)) pre k0 .zero x')) := by
        rcases hxd' with ⟨hnb', hx'e⟩ | ⟨σ, hd', hx'e⟩
        · have hnb : ∀ σ, (info R).seq.dom ≠ .big σ := fun σ e => hnb' σ e
          have hxe : x = (info R).seq.nat 0 := by
            rcases hxd with ⟨-, h⟩ | ⟨σ, hd, -⟩
            · exact h
            · exact absurd hd (hnb σ)
          have hk00 : k0 = .zero := by rw [← hk0e]; exact kAdj_nat hnb
          have hdo : dom R = .omega := by
            cases h : dom R with
            | zero => exact absurd h hd0
            | one => exact absurd h hd1
            | omega => rfl
            | big σ => exact absurd h (hnb σ)
          have hU := (seqI_dom_nat hRN.1 hdo).1
          have hx'e' : x' = (info R).seq.nat 1 := hx'e
          subst hxe hx'e' hk00
          have h0F := (hU.good 0).1
          have h1F := (hU.good 1).1
          have h1R : Lt ((info R).seq.nat 1) R := (hU.good 1).2.1
          have hV0 : combine (.psi0 (.Om c)) pre .zero .zero ((info R).seq.nat 0) =
              oadd (ofSummands pre) ((info R).seq.nat 0) := by
            show oadd (ofSummands pre) (nsum (oadd .zero _) .zero) = _
            rw [zero_oadd h0F, nsum_zero _ h0F]
          have hV1 : combine (.psi0 (.Om c)) pre .zero .zero ((info R).seq.nat 1) =
              oadd (ofSummands pre) ((info R).seq.nat 1) := by
            show oadd (ofSummands pre) (nsum (oadd .zero _) .zero) = _
            rw [zero_oadd h1F, nsum_zero _ h1F]
          refine le_psi_of_inC hqF hf ?_ ?_
          · rw [hV0, hV1]
            exact Or.inr (oadd_lt_oadd hpreF h0F h1F (hU.good 0).2.2)
          · have hC1 := inC_arg_psi hf
            have hC1' : inC (oadd (ofSummands pre) ((info R).seq.nat 1))
                (combine (.psi0 (.Om c)) pre .zero .zero ((info R).seq.nat 1))
                (.Psi .zero (.Om c) (combine (.psi0 (.Om c)) pre .zero .zero ((info R).seq.nat 1))) = true := by
              rw [← hV1]; exact hC1
            obtain ⟨h1, h2⟩ := inC_oadd_parts hNs h1F h1R hC1'
            rw [hV0]
            exact inC_oadd hpreF h0F h1 (hU.ub2 _ _ 0 hf.psi.aF hf h2)
        · have hd : (info R).seq.dom = .big σ := hd'
          have hxe : x = x' := by
            rcases hxd with ⟨hnb, -⟩ | ⟨σ', hd2, h⟩
            · exact absurd hd (hnb σ)
            · rw [hd] at hd2
              cases hd2
              rw [h, hx'e]
              rfl
          rw [hxe]
          exact Or.inl rfl
      refine ⟨fun f hf' => ?_, hqle⟩
      have hpq : p = .Psi .zero (.Om c) (combine (.psi0 (.Om c)) pre k0 .zero x) := by rw [← h2, hx]
      exact le_transY (hWF.of_mem_subs (fr_spec hf').1) hqF hf (hpq ▸ hfp f hf') hqle
    · -- 種の挿入
      rw [ite_eq_right h2] at hf ⊢
      have hp0 : p ≠ .zero := fun e => by
        rcases fr_node hpm with ⟨m, a, e'⟩ | ⟨s, q, a, e'⟩ <;> rw [e'] at e <;> cases e
      have hpfr : p ∈ fr (.Om c) p := mem_fr_self (fr_node hpm) (fr_spec hpm).2
      have hlt := seed_lt_insertAtL hw hpF hp0 hpfr hf
      have hqp : Lt (.Psi .zero (.Om c) (combine (.psi0 (.Om c)) pre k0 .zero x)) p := by
        rw [hx] at h1 h2
        rcases le_of_not_ltY hpF hqF (fun h => h1 (ltB_iff.mpr h)) with e | h
        · exact absurd e h2
        · exact h
      exact ⟨fun f hf' => le_transY (hWF.of_mem_subs (fr_spec hf').1) hpF hf (hfp f hf') (Or.inr hlt),
        Or.inr (lt_transY hqF hpF hf hqp hlt)⟩

/-- z 側：`w = Ψ^0_{Ω_c}(W)`（`W ≠ 0`）の前線は `w[0]` 以下で、標準形の `q = Ψ^0_{Ω_c}(V) ≤ w[0]` で
    `W[0] ≤ V`・`W[0] ∈ C(V, q)` を満たすものがある -/
theorem zside_om {c W : Tm} (hw : WNF (.Psi .zero (.Om c) W)) (hW0 : W ≠ .zero) :
    (∀ f, f ∈ fr (.Om c) W → Le f (fund (.Psi .zero (.Om c) W) .zero)) ∧
    ∃ V, WNF (.Psi .zero (.Om c) V) ∧ Le (.Psi .zero (.Om c) V) (fund (.Psi .zero (.Om c) W) .zero) ∧
      Le (fund W .zero) V ∧ inC (fund W .zero) V (.Psi .zero (.Om c) V) = true ∧
      (V = fund W .zero ∨ ¬ isSucc V = true) := by
  by_cases hs : isSucc W = true
  · have hWF := hw.psi.aF
    have hq := wnf_psi_om_pred hw hs
    have hlt := zside_om_succ hw hs
    have hf := fund_wnf hw WNF.zero
    have hfW : fund W .zero = pred W := by
      rw [fund_eq, (dom_eq_one_iff hWF).mpr hs]
    refine ⟨fun f hfr => ?_, pred W, hq, Or.inr hlt, by rw [hfW]; exact Or.inl rfl,
      by rw [hfW]; exact inC_arg_psi hq, Or.inl hfW.symm⟩
    have hfr' : f ∈ fr (.Om c) (pred W) := by
      rw [← fr_succT (.Om c) (pred W), succT_pred hWF hs]
      exact hfr
    exact Or.inr (lt_transY (hWF.of_mem_subs (fr_spec hfr).1) hq hf (FWOrder.k2 hq f hfr') hlt)
  · exact zside_om_lim hw hW0 hs

/-! ### 帯の分類（全ての主要項） -/

/-- `Ω_c` の底と `Ω_c` の間の主要項は `Ψ^0_{Ω_c}` の崩壊 -/
theorem band_om_prin {c w : Tm} (hc : WNF (.Om c)) (hs : isSucc c = true) (hw : WNF w)
    (hwp : isPrincipal w = true) (h1 : Lt (omBase c) w) (h2 : Lt w (.Om c)) :
    ∃ V, w = .Psi .zero (.Om c) V := by
  have hcF := hc.om.1
  have hpF := wnf_pred hcF
  have hce : succT (pred c) = c := succT_pred hcF hs
  have hBF := (omBase_wnf hc hs).1
  cases w with
  | zero => cases hwp
  | plus a b => cases hwp
  | one =>
    exfalso
    by_cases hc1 : c = .one
    · have hB : omBase c = .one := by unfold omBase; rw [ite_eq_left hc1]
      rw [hB] at h1
      exact Lt.irrefl _ h1
    · have hpd0 : pred c ≠ .zero := pred_ne_zero hcF hs hc1
      have hB : omBase c = omHat (pred c) := by unfold omBase; rw [ite_eq_right hc1]
      rw [hB] at h1 hBF
      have h3 : Le .one (pred c) := by
        rcases triY WNF.one hpF with h | h | h
        · exact Or.inr h
        · exact Or.inl h
        · exact absurd (lt_oneY hpF h) hpd0
      exact not_lt_of_leY WNF.one hBF (le_transY WNF.one hpF hBF h3 (le_omHat hpF hpd0)) h1
  | K m =>
    exfalso
    have hm := hw.k
    have h3 : Lt (.K m) c := (lt_K_omY hm hcF).mp h2
    have h4 : Le (.K m) (pred c) := le_of_lt_succT hw hpF (by rw [hce]; exact h3)
    by_cases hc1 : c = .one
    · rw [hc1] at h3
      exact absurd (lt_oneY hw h3) (by intro e; cases e)
    have hpd0 : pred c ≠ .zero := pred_ne_zero hcF hs hc1
    have hB : omBase c = omHat (pred c) := by unfold omBase; rw [ite_eq_right hc1]
    rw [hB] at h1 hBF
    exact not_lt_of_leY hw hBF (le_transY hw hpF hBF h4 (le_omHat hpF hpd0)) h1
  | Om e =>
    exfalso
    have heF := hw.om.1
    have h3 : Lt e c := (lt_om_iffY heF hcF).mp h2
    have h4 : Le e (pred c) := le_of_lt_succT heF hpF (by rw [hce]; exact h3)
    by_cases hc1 : c = .one
    · rw [hc1] at h3
      exact hw.om.2.1 (lt_oneY heF h3)
    have hpd0 : pred c ≠ .zero := pred_ne_zero hcF hs hc1
    have hB : omBase c = omHat (pred c) := by unfold omBase; rw [ite_eq_right hc1]
    rw [hB] at h1 hBF
    exact not_lt_of_leY hw hBF (om_le_omHat hw hpF hpd0 h4) h1
  | Xi m a => exact band_om hc hs hw (Or.inl ⟨m, a, rfl⟩) h1 h2
  | Psi s p a => exact band_om hc hs hw (Or.inr ⟨s, p, a, rfl⟩) h1 h2


end RTKA.Fund
