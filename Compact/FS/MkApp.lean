import Compact.FS.OmInv

/-! `mkApp`（有効性の調整つきの `app` の組み立て）の仕様。

`Ψ^ξ_π` への近似 `A = pre ⊕ ((c + x) # P)` について：

* `π` に引数の下限 `q` がなければ、または `pre` が `q` の接頭辞でなければ、調整なし（`q < pre`）。
* `q = pre ⊕ rt` のとき：`R ≤ rt` なら塞がる（`none`）。そうでなければ、調整なしで有効なら調整なし、K の対角化の特別な場合は
  一つずらす、それ以外は `rt` の先頭部分か `rt + 1`（`adjC`）。

調整 `c` はどの場合も `R` 未満で、`π` の成分（`AdjHyp`）。 -/

namespace RTKA.Fund

open Tm W

/-- `q` が `pre` で始まらず `q < pre ++ M` なら `q < pre` -/
theorem cmpList_lt_of_not_prefix : ∀ {pre L M : List Tm}, NFL pre → NFL L →
    cmpList L (pre ++ M) = .lt →
    ¬ (pre.length ≤ L.length ∧ L.take pre.length = pre) → cmpList L pre = .lt
  | [], L, M, _, _, _, hn => absurd ⟨Nat.zero_le _, by simp⟩ hn
  | a :: p, [], M, _, _, _, _ => cmpList_nil_cons _ _
  | a :: p, b :: T, M, hp, hL, h, hn => by
    have ha := hp.1 a List.mem_cons_self
    have hb := hL.1 b List.mem_cons_self
    rw [List.cons_append] at h
    cases e : cmpP b a with
    | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]
    | gt =>
      rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e] at h
      cases h
    | eq =>
      have hab := eq_of_cmpP_eqY hb.1 ha.1 hb.2 ha.2 e
      subst hab
      rw [cmpList_cons_cons_eq _ _ e] at h ⊢
      refine cmpList_lt_of_not_prefix (nfl_tail hp) (nfl_tail hL) h fun h' => hn ?_
      refine ⟨by simp only [List.length_cons]; omega, ?_⟩
      simp only [List.length_cons, List.take_succ_cons, h'.2]

/-- 下限が `pre` で始まらなければ `pre` 未満 -/
theorem lt_pre_of_tail_none {π X q : Tm} {pre rest : List Tm} {R : Tm} (hπ : WNF π)
    (hq : argR? π = some q) (hnone : tailRaw (argR? π) pre = none) (hX : WNF X)
    (hsum : summands X = pre ++ R :: rest) (hlt : Lt q X) : Lt q (ofSummands pre) := by
  have hqF := wnf_of_argR hπ hq
  have hN : NFL (pre ++ R :: rest) := hsum ▸ nfl_summands hX
  have hp := nfl_append_left hN
  have hn : ¬ (pre.length ≤ (summands q).length ∧ (summands q).take pre.length = pre) := by
    intro h
    rw [hq] at hnone
    simp only [tailRaw] at hnone
    rw [ite_eq_left h] at hnone
    cases hnone
  have h1 : cmpList (summands q) (pre ++ R :: rest) = .lt := by
    have := hlt
    unfold Lt at this
    rwa [cmp_eq, hsum] at this
  unfold Lt
  rw [cmp_eq, summands_ofSummands _ (nfl_principal hp)]
  exact cmpList_lt_of_not_prefix hp (nfl_summands hqF) h1 hn

/-- 下限が `pre` で始まるとき -/
theorem tailRaw_some {π rt : Tm} {pre : List Tm} (hπ : WNF π)
    (h : tailRaw (argR? π) pre = some rt) :
    ∃ q, argR? π = some q ∧ summands q = pre ++ summands rt ∧ WNF rt := by
  cases hq : argR? π with
  | none =>
    rw [hq] at h
    cases h
  | some q =>
    rw [hq] at h
    simp only [tailRaw] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      have hN := nfl_summands (wnf_of_argR hπ hq)
      have e : summands q = pre ++ (summands q).drop pre.length := by
        have := List.take_append_drop pre.length (summands q)
        rw [hc.2] at this
        exact this.symm
      have hdrop : NFL ((summands q).drop pre.length) := by
        have h2 : NFL (pre ++ (summands q).drop pre.length) := by
          rw [← e]
          exact hN
        exact nfl_append_right h2
      refine ⟨q, rfl, ?_, ?_⟩
      · rw [← h, summands_ofSummands _ (nfl_principal hdrop)]
        exact e
      · rw [← h]
        exact wnf_ofSummands hdrop
    · cases h

/-- `adjC` の値 -/
theorem adjC_spec (τ : Tm) (approx : Tm → Tm) (rt : Tm) :
    (∃ k, adjC τ approx rt = ofSummands ((summands rt).take k) ∧
        validR τ (approx (adjC τ approx rt)) = true) ∨ adjC τ approx rt = sc rt := by
  unfold adjC
  cases e : ((List.range ((summands rt).length + 1)).map
      (fun k => ofSummands ((summands rt).take k))).find? (fun c => validR τ (approx c)) with
  | none => exact Or.inr rfl
  | some c =>
    left
    have h1 := List.find?_some e
    obtain ⟨k, -, hk⟩ := List.mem_map.mp (List.mem_of_find?_eq_some e)
    exact ⟨k, hk.symm, h1⟩

theorem ofSummands_take_le {L : List Tm} (hL : NFL L) (k : Nat) :
    NFL (L.take k) ∧ Le (ofSummands (L.take k)) (ofSummands L) := by
  have e : L.take k ++ L.drop k = L := List.take_append_drop k L
  have hT : NFL (L.take k) := by
    have h2 : NFL (L.take k ++ L.drop k) := by
      rw [e]
      exact hL
    exact nfl_append_left h2
  refine ⟨hT, ?_⟩
  have hLF := wnf_ofSummands hL
  apply le_of_ne_gtY (wnf_ofSummands hT) hLF
  rw [cmp_eq, summands_ofSummands _ (nfl_principal hT), summands_ofSummands _ (nfl_principal hL)]
  generalize L.drop k = D at e
  generalize L.take k = T at e
  subst e
  have h3 := cmpList_append_same T [] D
  rw [List.append_nil] at h3
  rw [h3]
  cases D with
  | nil => rw [cmpList_nil_nil]; decide
  | cons _ _ => rw [cmpList_nil_cons]; decide

theorem validR_lt {σ δ q : Tm} (h : validR σ δ = true) (hq : argR? σ = some q) : Lt q δ := by
  unfold validR at h
  rw [hq] at h
  exact ltB_iff.mp h

/-- 下限 `q = pre ⊕ rt` は、`rt < y < R` の近似 `pre ⊕ y` 未満 -/
theorem lt_oadd_of_tail {q rt y R : Tm} {pre rest : List Tm} (hN : NFL (pre ++ R :: rest))
    (hs : summands q = pre ++ summands rt) (hy : WNF y) (hyR : Lt y R) (hlt : Lt rt y) :
    Lt q (oadd (ofSummands pre) y) := by
  unfold Lt
  rw [cmp_eq, hs, summands_oadd_pre (nfl_append_left hN) hy (head_le_pre hN hy hyR),
    cmpList_append_same]
  have := hlt
  unfold Lt at this
  rwa [cmp_eq] at this

/-- `ψ`・Mahlo 型の生成の `mkApp` の仕様 -/
theorem mkApp_psi {ξ π X P ceil : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r s : SeqD}
    (hg : GenPsi g ξ π) (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (S : SeedHyp π X P R) (hR1 : R ≠ .one) (hx0 : WNF (r.first))
    (hx0R : Lt (r.first) R) (hk : AdjHyp π R (kAdj π ceil g pre R r))
    (h : mkApp ceil g pre R r P .zero = some s) :
    ∃ c, AdjHyp π R c ∧
      (kAdj π ceil g pre R r = .zero → validR π (combine g pre .zero P r.first) = true → c = .zero) ∧
      (c = kAdj π ceil g pre R r ∨ ∃ d, WNF d ∧ c = oadd d (kAdj π ceil g pre R r)) ∧
      ((s = .app ceil g pre R r P c ∧
          ∀ q, argR? π = some q → Lt q (approx pre P (oadd c (r.first)))) ∨
        (s = .shift (.app ceil g pre R r P c) ∧ canonSecondValid π ceil g pre R r P c = true)) := by
  have hπF := ht.psi.piF
  have hX := ht.psi.aF
  have hN : NFL (pre ++ R :: rest) := hsum ▸ nfl_summands hX
  have hRN := hN.1 R (List.mem_append_right _ List.mem_cons_self)
  have hpreF := wnf_ofSummands (nfl_append_left hN)
  have hR0 : R ≠ .zero := fun e => by
    have h1 := hRN.2
    rw [e] at h1
    cases h1
  have hPlt : ltB P R = true := ltB_iff.mpr S.hPR
  have hA : ∀ c, WNF c → WNF (approx pre P (oadd c (r.first))) := fun c hc =>
    wnf_oadd hpreF (wnf_nsum (wnf_oadd hc hx0) S.hPF)
  unfold mkApp at h
  rw [hg.tgt] at h
  dsimp only at h
  rw [ite_eq_right (by simp [hPlt])] at h
  generalize hkd : kAdj π ceil g pre R r = k at h hk
  have hk0 : k = .zero → k = .zero := id
  cases htl : tailRaw (argR? π) pre with
  | none =>
    rw [htl] at h
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨k, hk, fun hn _ => hk0 hn, Or.inl rfl, Or.inl ⟨rfl, fun q hq => ?_⟩⟩
    have h1 := lt_pre_of_tail_none hπF hq htl hX hsum (arg_lt_of_psi ht hq)
    exact lt_of_lt_of_leY (wnf_of_argR hπF hq) hpreF (hA _ hk.hF) h1
      (le_oadd_left hpreF (wnf_nsum (wnf_oadd hk.hF hx0) S.hPF))
  | some rt =>
    rw [htl] at h
    dsimp only at h
    obtain ⟨q, hq, hsq, hrtF⟩ := tailRaw_some hπF htl
    by_cases hle : leB R rt = true
    · rw [ite_eq_left hle] at h
      cases h
    rw [ite_eq_right hle] at h
    have hrtR : Lt rt R := by
      apply lt_of_gtY hRN.1 hrtF
      rw [leB_iff] at hle
      simpa using hle
    by_cases hv0 : validR π (combine g pre k P (r.first)) = true
    · rw [ite_eq_left hv0] at h
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨k, hk, fun hn _ => hk0 hn, Or.inl rfl, Or.inl ⟨rfl, fun q' hq' => ?_⟩⟩
      rw [← hg.comb]
      exact validR_lt hv0 hq'
    rw [ite_eq_right hv0] at h
    by_cases hs2 : canonSecondValid π ceil g pre R r P k = true
    · rw [ite_eq_left hs2] at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨k, hk, fun hn _ => hk0 hn, Or.inl rfl, Or.inr ⟨rfl, hs2⟩⟩
    rw [ite_eq_right hs2] at h
    simp only [Option.some.injEq] at h
    subst h
    have hqC : ∀ g' d, WNF d → Le d π → inC π g' d = true → ∀ u, u ∈ summands rt → inC u g' d = true :=
      fun g' d hd hle' hC u hu =>
        inC_of_mem_summands (wnf_of_argR hπF hq) (arg_of_inC hq hC (not_lt_of_leY hd hπF hle')).1
          (by rw [hsq]; exact List.mem_append_right _ hu)
    have hrtN := nfl_summands hrtF
    have hkn : k = .zero → validR π (combine g pre .zero P (r.first)) = true → False :=
      fun hn e => hv0 (by rw [hk0 hn]; exact e)
    rcases adjC_spec π (fun c => combine g pre (oadd c k) P (r.first)) rt with ⟨j, hj, hv⟩ | hj
    · obtain ⟨hT, hle'⟩ := ofSummands_take_le hrtN j
      rw [ofSummands_summands rt hrtF] at hle'
      generalize adjC π (fun c => combine g pre (oadd c k) P (r.first)) rt = c at hj hv
      have hcF : WNF c := by
        rw [hj]
        exact wnf_ofSummands hT
      refine ⟨oadd c k, ⟨wnf_oadd hcF hk.hF, ?_, fun g' d hd hdπ hC => ?_⟩, fun hn e => absurd e (hkn hn),
        Or.inr ⟨c, hcF, rfl⟩, Or.inl ⟨rfl, fun q' hq' => ?_⟩⟩
      · refine oadd_lt_prin hcF hk.hF hRN.2 ?_ hk.hR
        rw [hj]
        exact lt_of_le_of_ltY (wnf_ofSummands hT) hrtF hRN.1 hle' hrtR
      · refine inC_oadd hcF hk.hF ?_ (hk.hU g' d hd hdπ hC)
        rw [hj, inC_ofSummands]
        intro u hu
        exact hqC g' d hd hdπ hC u (List.mem_of_mem_take hu)
      · have := validR_lt hv hq'
        rwa [hg.comb] at this
    · generalize adjC π (fun c => combine g pre (oadd c k) P (r.first)) rt = c at hj
      subst hj
      have hsF : WNF (sc rt) := succT_WNF hrtF
      have hRns : ¬ isSucc R = true := by
        rw [isSucc_principal hRN.2]
        simpa using hR1
      have hsR : Lt (sc rt) R := succT_lt_of_not_succ hrtF hRN.1 hRns hrtR
      have hcF := wnf_oadd hsF hk.hF
      have hcR : Lt (oadd (sc rt) k) R := oadd_lt_prin hsF hk.hF hRN.2 hsR hk.hR
      refine ⟨oadd (sc rt) k, ⟨hcF, hcR, fun g' d hd hdπ hC => ?_⟩, fun hn e => absurd e (hkn hn),
        Or.inr ⟨sc rt, hsF, rfl⟩, Or.inl ⟨rfl, fun q' hq' => ?_⟩⟩
      · exact inC_oadd hsF hk.hF (inC_succT ((inC_iff_summands hrtF).mpr (hqC g' d hd hdπ hC)))
          (hk.hU g' d hd hdπ hC)
      · rw [hq] at hq'
        simp only [Option.some.injEq] at hq'
        subst hq'
        have hxF := wnf_oadd hcF hx0
        have hyF := wnf_nsum hxF S.hPF
        have hxR : Lt (oadd (oadd (sc rt) k) (r.first)) R := oadd_lt_prin hcF hx0 hRN.2 hcR hx0R
        have hyR := nsum_lt_prin hxF S.hPF hRN.2 hxR S.hPR
        have h1 : Lt rt (sc rt) := lt_succT rt
        have h2 : Le (sc rt) (nsum (oadd (oadd (sc rt) k) (r.first)) P) :=
          le_transY hsF hcF hyF (le_oadd_left hsF hk.hF)
            (le_transY hcF hxF hyF (le_oadd_left hcF hx0) (le_nsum_left hxF S.hPF))
        exact lt_oadd_of_tail hN hsq hyF hyR (lt_of_lt_of_leY hrtF hsF hyF h1 h2)

end RTKA.Fund
