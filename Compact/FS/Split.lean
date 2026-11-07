import Compact.FS.App

/-! 種より大きい最後の加数での分割（`splitGtD`）と、前の部分 `pre` を共有する近似。

`X` の加数が `pre ++ R :: rest` のとき、近似 `A = pre ⊕ y`（`0 < y < R`）について：

* `A < X`（`oadd_pre_lt`）。
* 大きさの議論（`lt_pre_of_subs`）：`pre` の加数 `s` の部分項 `v` で `v < X` なら `v < A`。`A ≤ v < X` なら
  `v` の加数は `pre` で始まり `s` を部分項に持つので、`s` の真の部分項にはなれない。したがって
  `pre ∈ C(X, d)` から `pre ∈ C(A, d)`（`inC_pre`）。
* 上界 `ub`（`t ∈ C(g, d)` なら `t[n] ∈ C(g, d)`）・梯子の上界 `ub2`・隙間 `gap`（`t` の真の部分項で `t` 未満のものは
  `t[n]` 以下）が `R` にあれば、近似の崩壊 `Ψ^0_π(pre ⊕ (R[n] # P))` は標準形・減少・単調で、同じ上界を持つ
  （`ApproxHyp`、`app_inv`）。 -/

namespace RTKA.Fund

open Tm W

/-! ### 分割の仕様 -/

theorem mem_takeWhile_imp' {α : Type} {p : α → Bool} : ∀ {l : List α} {a : α},
    a ∈ l.takeWhile p → p a = true
  | [], _, h => by simp at h
  | x :: xs, a, h => by
    simp only [List.takeWhile] at h
    split at h
    · rename_i hx
      rcases List.mem_cons.mp h with rfl | h
      · exact hx
      · exact mem_takeWhile_imp' h
    · simp at h

theorem head_dropWhile_not' {α : Type} {p : α → Bool} : ∀ {l : List α} {d : α} {rest : List α},
    l.dropWhile p = d :: rest → p d = false
  | [], _, _, h => by cases h
  | x :: xs, d, rest, h => by
    rw [List.dropWhile_cons] at h
    split at h
    · exact head_dropWhile_not' h
    · rename_i hx
      simp only [List.cons.injEq] at h
      rw [← h.1]
      simpa using hx

theorem splitGtD_spec {th : Tm} {ys : DL} {pre : List Tm} {R : Tm} {r : SeqD}
    (h : splitGtD th ys = some (pre, R, r)) :
    ∃ L rest, ys = L ++ (R, r) :: rest ∧ L.map Prod.fst = pre ∧ ltB th R = true ∧
      (∀ q, q ∈ L → ltB th q.1 = true) ∧ ∀ q tl, rest = q :: tl → ltB th q.1 = false := by
  unfold splitGtD at h
  generalize hT : ys.takeWhile (fun s => ltB th s.1) = T at h
  cases e : T.getLast? with
  | none => rw [e] at h; cases h
  | some q =>
    rw [e] at h
    obtain ⟨R', r'⟩ := q
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, rfl, rfl⟩ := h
    obtain ⟨L, rfl⟩ := List.getLast?_eq_some_iff.mp e
    refine ⟨L, ys.dropWhile (fun s => ltB th s.1), ?_, ?_, ?_, ?_, ?_⟩
    · have := List.takeWhile_append_dropWhile (p := fun s => ltB th s.1) (l := ys)
      rw [hT, List.append_assoc] at this
      exact this.symm
    · rw [← h1, List.dropLast_concat]
    · have : (R', r') ∈ ys.takeWhile (fun s => ltB th s.1) := by rw [hT]; simp
      exact mem_takeWhile_imp' (p := fun s : Tm × SeqD => ltB th s.1) this
    · intro q hq
      have : q ∈ ys.takeWhile (fun s => ltB th s.1) := by rw [hT]; exact List.mem_append_left _ hq
      exact mem_takeWhile_imp' (p := fun s : Tm × SeqD => ltB th s.1) this
    · intro q tl e
      exact head_dropWhile_not' (p := fun s : Tm × SeqD => ltB th s.1) e

theorem splitGtD_none_head {th : Tm} {q : Tm × SeqD} {ys : DL} (h : splitGtD th (q :: ys) = none) :
    ltB th q.1 = false := by
  cases e : ltB th q.1 with
  | false => rfl
  | true =>
    exfalso
    unfold splitGtD at h
    rw [List.takeWhile_cons_of_pos (by simpa using e)] at h
    cases hg : (q :: ys.takeWhile (fun s => ltB th s.1)).getLast? with
    | none => simp at hg
    | some a =>
      rw [hg] at h
      cases h

/-- 後者の引数の加数（`1` を除く）での分割 -/
theorem split_succ {X p : Tm} {pre : List Tm} {R : Tm} {r : SeqD} (hs : isSucc X = true)
    (h : splitGtD p (info X).sums.dropLast = some (pre, R, r)) :
    (∃ rest, summands X = pre ++ R :: rest) ∧ r = (info R).seq ∧ Lt p R := by
  obtain ⟨L, rest, hys, hL, hR, -⟩ := splitGtD_spec h
  refine ⟨?_, ?_, ltB_iff.mp hR⟩
  · have e1 : (info X).sums.dropLast.map Prod.fst = (summands X).dropLast := by
      rw [List.map_dropLast, info_sums_fst]
    rw [hys, List.map_append, hL, List.map_cons] at e1
    refine ⟨rest.map Prod.fst ++ [one], ?_⟩
    rw [summands_eq_dropLast_one hs, ← e1]
    simp
  · have hm : (R, r) ∈ (info X).sums := by
      apply List.dropLast_subset
      rw [hys]
      simp
    exact coh_sums X (R, r) hm

/-! ### 大きい順の列 -/

/-- 大きい順の列で、後ろの要素は前の要素以下 -/
theorem le_of_nfl_append : ∀ {L : List Tm} {R : Tm} {rest : List Tm}, NFL (L ++ R :: rest) →
    ∀ s, s ∈ L → cmp R s ≠ .gt
  | [], _, _, _, s, hs => by cases hs
  | a :: L, R, rest, h, s, hs => by
    rcases List.mem_cons.mp hs with rfl | hs
    · exact le_head_of_nfl h R (List.mem_append_right _ List.mem_cons_self)
    · exact le_of_nfl_append (nfl_tail h) s hs

/-- 大きい順の列の要素は和以下 -/
theorem le_ofSummands_of_mem {l : List Tm} {s : Tm} (h : NFL l) (hs : s ∈ l) : Le s (ofSummands l) := by
  obtain ⟨L, M, rfl⟩ := List.append_of_mem hs
  have hS : NFL (s :: M) := nfl_append_right h
  have hsF := hS.1 s List.mem_cons_self
  have h1 : Le s (ofSummands (s :: M)) := by
    apply le_of_ne_gtY hsF.1 (wnf_ofSummands hS)
    have e : cmp s (ofSummands (s :: M)) = cmpList [s] (s :: M) := by
      rw [cmp_eq, summands_ofSummands _ (nfl_principal hS), summands_principal hsF.2]
    rw [e, cmpList_cons_cons_eq _ _ (cmpP_self s)]
    cases M with
    | nil => rw [cmpList_nil_nil]; decide
    | cons _ _ => rw [cmpList_nil_cons]; decide
  exact le_transY hsF.1 (wnf_ofSummands hS) (wnf_ofSummands h) h1 (le_ofSummands_prepend h)

/-- `y` の先頭が `pre` の各加数以下なら、`pre ⊕ y` の加数は列の連結 -/
theorem summands_oadd_pre {pre : List Tm} {y : Tm} (hpre : NFL pre) (hy : WNF y)
    (hge : ∀ s h r, s ∈ pre → summands y = h :: r → leB h s = true) :
    summands (oadd (ofSummands pre) y) = pre ++ summands y := by
  have hp := nfl_principal hpre
  cases hs : summands y with
  | nil => rw [eq_zero_of_summands_nil hs, oadd_zero, summands_ofSummands _ hp, List.append_nil]
  | cons h r =>
    have hY := nfl_summands hy
    rw [summands_oadd hs (by rw [summands_ofSummands _ hp]; exact hp) (nfl_principal hY), hs,
      summands_ofSummands _ hp, takeWhile_of_all (fun s hs' => hge s h r hs' hs)]

/-- `y < R` なら `y` の先頭は `pre` の各加数以下 -/
theorem head_le_pre {pre rest : List Tm} {R y : Tm} (h : NFL (pre ++ R :: rest)) (hy : WNF y)
    (hyR : Lt y R) : ∀ s h' r, s ∈ pre → summands y = h' :: r → leB h' s = true := by
  intro s h' r hs e
  have hRm := h.1 R (List.mem_append_right _ List.mem_cons_self)
  have hsF := (h.1 s (List.mem_append_left _ hs)).1
  have hY := nfl_summands hy
  have hhm := hY.1 h' (by rw [e]; exact List.mem_cons_self)
  have h1 : Lt h' R := by
    unfold Lt
    rw [cmp_principal hhm.2 hRm.2]
    exact head_lt_prin e hRm.2 hyR
  have h2 : Le R s := le_of_ne_gtY hRm.1 hsF (le_of_nfl_append h s hs)
  rw [leB_iff]
  exact ne_gt_of_le (Or.inr (lt_of_lt_of_leY hhm.1 hRm.1 hsF h1 h2))

/-- `X` の加数が `pre ++ R :: rest` で `y < R` なら `pre ⊕ y < X` -/
theorem oadd_pre_lt {pre rest : List Tm} {R y : Tm} (h : NFL (pre ++ R :: rest)) (hy : WNF y)
    (hyR : Lt y R) : Lt (oadd (ofSummands pre) y) (ofSummands (pre ++ R :: rest)) := by
  have hRp := (h.1 R (List.mem_append_right _ List.mem_cons_self)).2
  unfold Lt
  rw [cmp_eq, summands_oadd_pre (nfl_append_left h) hy (head_le_pre h hy hyR),
    summands_ofSummands _ (nfl_principal h), cmpList_append_same]
  cases e : summands y with
  | nil => exact cmpList_nil_cons _ _
  | cons h' r => exact cmpList_head_lt _ _ (head_lt_prin e hRp hyR)

/-- 辞書式の区間：`pre ++ Y ≤ V < pre ++ Z` なら `V` は `pre` で始まる -/
theorem prefix_of_between : ∀ {pre V Y Z : List Tm}, NFL (pre ++ Y) → NFL V →
    cmpList (pre ++ Y) V ≠ .gt → cmpList V (pre ++ Z) = .lt → ∃ V', V = pre ++ V'
  | [], V, _, _, _, _, _, _ => ⟨V, rfl⟩
  | a :: pre, [], Y, Z, _, _, h1, _ => by
    rw [List.cons_append, cmpList_cons_nil] at h1
    exact absurd rfl h1
  | a :: pre, b :: V, Y, Z, hA, hV, h1, h2 => by
    have ha := hA.1 a List.mem_cons_self
    have hb := hV.1 b List.mem_cons_self
    rw [List.cons_append] at h1 h2
    cases e : cmpP a b with
    | lt =>
      have e' : cmpP b a = .gt := by rw [cmpP_swapP ha hb, e]; rfl
      rw [cmpList_cons_cons_ne _ _ (by rw [e']; decide), e'] at h2
      cases h2
    | gt =>
      rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e] at h1
      exact absurd rfl h1
    | eq =>
      have hab := eq_of_cmpP_eqY ha.1 hb.1 ha.2 hb.2 e
      subst hab
      rw [cmpList_cons_cons_eq _ _ e] at h1
      rw [cmpList_cons_cons_eq _ _ e] at h2
      obtain ⟨V', hV'⟩ := prefix_of_between (nfl_tail hA) (nfl_tail hV) h1 h2
      exact ⟨V', by rw [hV']; rfl⟩

/-! ### 大きさの議論 -/

theorem size_lt_of_mem_subs_ne : ∀ {t s : Tm}, s ∈ subs t → s ≠ t → s.size < t.size
  | .zero, s, h, hne | .one, s, h, hne | .K _, s, h, hne => by
    simp only [subs, List.mem_singleton] at h
    exact absurd h hne
  | .plus a b, s, h, hne => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    rcases h with h | h | h
    · exact absurd h hne
    · have := size_le_of_mem_subs h
      simp only [Tm.size]; omega
    · have := size_le_of_mem_subs h
      simp only [Tm.size]; omega
  | .Om a, s, h, hne => by
    simp only [subs, List.mem_cons] at h
    rcases h with h | h
    · exact absurd h hne
    · have := size_le_of_mem_subs h
      simp only [Tm.size]; omega
  | .Xi n a, s, h, hne => by
    simp only [subs, List.mem_cons] at h
    rcases h with h | h
    · exact absurd h hne
    · have := size_le_of_mem_subs h
      simp only [Tm.size]; omega
  | .Psi x k a, s, h, hne => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    rcases h with h | (h | h) | h
    · exact absurd h hne
    · have := size_le_of_mem_subs h
      simp only [Tm.size]; omega
    · have := size_le_of_mem_subs h
      simp only [Tm.size]; omega
    · have := size_le_of_mem_subs h
      simp only [Tm.size]; omega

theorem ne_of_size_lt {v t : Tm} (h : v.size < t.size) : v ≠ t := fun e => by
  rw [e] at h
  exact Nat.lt_irrefl _ h

/-- `x ∈ C(g0, d)` で、`x` の部分項が `g0` 未満なら `g` 未満のとき、`x ∈ C(g, d)` -/
theorem inC_mono_all {x g0 g d : Tm} (hx : WNF x) (hd : WNF d) (h0 : inC x g0 d = true)
    (hg : ∀ v, v ∈ subs x → Lt v g0 → Lt v g) : inC x g d = true :=
  (inC_fr (R := d) x h0 (fun _ _ hw => hw) hg).mpr fun w hw =>
    WFY.inC_of_ltY _ (hx.of_mem_subs (fr_spec hw).1) hd (fr_spec hw).2

/-- `x ∈ C(g, d)` の判定に `x` 自身は現れないので、真の部分項だけ見ればよい -/
theorem inC_mono_proper {g0 g d : Tm} (hd : WNF d) : ∀ {x : Tm}, WNF x → inC x g0 d = true →
    (∀ v, v ∈ subs x → v ≠ x → Lt v g0 → Lt v g) → inC x g d = true
  | .zero, _, _, _ => inC_zero _ _
  | .one, _, _, _ => inC_one _ _
  | .K _, _, _, _ => inC_K _ _ _
  | .plus a b, hx, h0, hg => by
    obtain ⟨ha, hb, -, -⟩ := hx.plus
    rw [inC_plus, Bool.and_eq_true] at h0 ⊢
    refine ⟨inC_mono_all ha hd h0.1 fun v hv => hg v (subs_plus_l hv) (ne_of_size_lt ?_),
      inC_mono_all hb hd h0.2 fun v hv => hg v (subs_plus_r hv) (ne_of_size_lt ?_)⟩
    · have := size_le_of_mem_subs hv
      simp only [Tm.size]; omega
    · have := size_le_of_mem_subs hv
      simp only [Tm.size]; omega
  | .Om a, hx, h0, hg => by
    rw [inC_om] at h0 ⊢
    refine inC_mono_all hx.om.1 hd h0 fun v hv => hg v (subs_om hv) (ne_of_size_lt ?_)
    have := size_le_of_mem_subs hv
    simp only [Tm.size]; omega
  | .Xi n a, hx, h0, hg => by
    rcases inC_xi_iff.mp h0 with h | ⟨h1, h2⟩
    · exact inC_xi_iff.mpr (Or.inl h)
    · have hne : ∀ v, v ∈ subs a → v ≠ Tm.Xi n a := fun v hv => ne_of_size_lt (by
        have := size_le_of_mem_subs hv
        simp only [Tm.size]; omega)
      exact inC_xi_iff.mpr (Or.inr ⟨inC_mono_all hx.xi.2.1 hd h1 fun v hv =>
        hg v (subs_xi hv) (hne v hv), hg a (mem_subs_xi n a) (hne a (self_mem_subs a)) h2⟩)
  | .Psi s k δ, hx, h0, hg => by
    rcases inC_psi_iff.mp h0 with h | ⟨hk, hs, hδ, hlt⟩
    · exact inC_psi_iff.mpr (Or.inl h)
    · have hP := hx.psi
      have hne1 : ∀ v, v ∈ subs k → v ≠ Tm.Psi s k δ := fun v hv => ne_of_size_lt (by
        have := size_le_of_mem_subs hv
        simp only [Tm.size]; omega)
      have hne2 : ∀ v, v ∈ subs s → v ≠ Tm.Psi s k δ := fun v hv => ne_of_size_lt (by
        have := size_le_of_mem_subs hv
        simp only [Tm.size]; omega)
      have hne3 : ∀ v, v ∈ subs δ → v ≠ Tm.Psi s k δ := fun v hv => ne_of_size_lt (by
        have := size_le_of_mem_subs hv
        simp only [Tm.size]; omega)
      exact inC_psi_iff.mpr (Or.inr ⟨
        inC_mono_all hP.piF hd hk fun v hv => hg v (subs_psi_p hv) (hne1 v hv),
        inC_mono_all hP.xiF hd hs fun v hv => hg v (subs_psi_s hv) (hne2 v hv),
        inC_mono_all hP.aF hd hδ fun v hv => hg v (subs_psi_a hv) (hne3 v hv),
        hg δ (subs_psi_a (self_mem_subs δ)) (hne3 δ (self_mem_subs δ)) hlt⟩)

/-- 大きさの議論：`X` の加数が `pre ++ R :: rest`、`y < R` のとき、`pre` の加数 `s` の真の部分項 `v` で
    `v < X` なら `v < pre ⊕ y` -/
theorem lt_pre_of_subs {pre rest : List Tm} {R y s v : Tm} (h : NFL (pre ++ R :: rest)) (hy : WNF y)
    (hyR : Lt y R) (hs : s ∈ pre) (hv : v ∈ subs s) (hvs : v ≠ s) (hvF : WNF v)
    (hvX : Lt v (ofSummands (pre ++ R :: rest))) : Lt v (oadd (ofSummands pre) y) := by
  have hpre := nfl_append_left h
  have hpF := wnf_ofSummands hpre
  have hA : WNF (oadd (ofSummands pre) y) := wnf_oadd hpF hy
  by_cases hlt : Lt v (oadd (ofSummands pre) y)
  · exact hlt
  exfalso
  have hle : Le (oadd (ofSummands pre) y) v := le_of_not_ltY hvF hA hlt
  have hsum := summands_oadd_pre hpre hy (head_le_pre h hy hyR)
  have h1 : cmpList (pre ++ summands y) (summands v) ≠ .gt := by
    rw [← hsum, ← cmp_eq]
    exact ne_gt_of_le hle
  have h2 : cmpList (summands v) (pre ++ R :: rest) = .lt := by
    have := hvX
    unfold Lt at this
    rwa [cmp_eq, summands_ofSummands _ (nfl_principal h)] at this
  have hAN : NFL (pre ++ summands y) := hsum ▸ nfl_summands hA
  obtain ⟨V', hV'⟩ := prefix_of_between hAN (nfl_summands hvF) h1 h2
  have hsv : s ∈ subs v := mem_subs_of_mem_summands (by rw [hV']; exact List.mem_append_left _ hs)
  have e1 := size_lt_of_mem_subs_ne hv hvs
  have e2 := size_le_of_mem_subs hsv
  omega

/-- `pre` は `C(pre ⊕ y, d)` に入る（大きさの議論） -/
theorem inC_pre {pre rest : List Tm} {R y d : Tm} (h : NFL (pre ++ R :: rest)) (hy : WNF y)
    (hyR : Lt y R) (hd : WNF d)
    (hX : inC (ofSummands (pre ++ R :: rest)) (ofSummands (pre ++ R :: rest)) d = true) :
    inC (ofSummands pre) (oadd (ofSummands pre) y) d = true := by
  rw [inC_ofSummands]
  intro s hs
  have hsX := (inC_ofSummands _).mp hX s (List.mem_append_left _ hs)
  have hsF := (h.1 s (List.mem_append_left _ hs)).1
  exact inC_mono_proper hd hsF hsX fun v hv hne hvX =>
    lt_pre_of_subs h hy hyR hs hv hne (hsF.of_mem_subs hv) hvX

/-- 標準形の末尾は部分項 -/
theorem tail_mem_subs : ∀ {v : Tm} {L M : List Tm}, WNF v → summands v = L ++ M → M ≠ [] →
    ofSummands M ∈ subs v
  | v, [], M, hv, e, _ => by
    rw [List.nil_append] at e
    rw [← e, ofSummands_summands v hv]
    exact self_mem_subs v
  | .plus a b, _ :: L, M, hv, e, hM => by
    rw [summands_plus, List.cons_append, List.cons.injEq] at e
    exact subs_plus_r (tail_mem_subs hv.plus.2.1 e.2 hM)
  | .zero, _ :: _, _, _, e, _ => by simp [summands] at e
  | .one, _ :: L, M, _, e, hM | .K _, _ :: L, M, _, e, hM | .Om _, _ :: L, M, _, e, hM
  | .Xi _ _, _ :: L, M, _, e, hM | .Psi _ _ _, _ :: L, M, _, e, hM => by
    simp only [summands, List.cons_append, List.cons.injEq] at e
    have := e.2.symm
    rw [List.append_eq_nil_iff] at this
    exact absurd this.2 hM

/-- 隙間の性質から：`R` の真の部分項 `v` で `v < X` なら `v < pre ⊕ y`（`R[n] ≤ y`、`y ≠ 0`） -/
theorem lt_approx_of_gap {pre rest : List Tm} {R y x v : Tm} (h : NFL (pre ++ R :: rest)) (hy : WNF y)
    (hy0 : y ≠ .zero) (hyR : Lt y R) (hx : WNF x) (hxy : Le x y)
    (hgap : ∀ u, u ∈ subs R → u ≠ R → Lt u R → Lt u x)
    (hv : v ∈ subs R) (hne : v ≠ R) (hvF : WNF v) (hvX : Lt v (ofSummands (pre ++ R :: rest))) :
    Lt v (oadd (ofSummands pre) y) := by
  have hpre := nfl_append_left h
  have hA : WNF (oadd (ofSummands pre) y) := wnf_oadd (wnf_ofSummands hpre) hy
  by_cases hlt : Lt v (oadd (ofSummands pre) y)
  · exact hlt
  exfalso
  have hle : Le (oadd (ofSummands pre) y) v := le_of_not_ltY hvF hA hlt
  have hsum := summands_oadd_pre hpre hy (head_le_pre h hy hyR)
  have h1 : cmpList (pre ++ summands y) (summands v) ≠ .gt := by
    rw [← hsum, ← cmp_eq]
    exact ne_gt_of_le hle
  have h2 : cmpList (summands v) (pre ++ R :: rest) = .lt := by
    have := hvX
    unfold Lt at this
    rwa [cmp_eq, summands_ofSummands _ (nfl_principal h)] at this
  have hAN : NFL (pre ++ summands y) := hsum ▸ nfl_summands hA
  obtain ⟨V', hV'⟩ := prefix_of_between hAN (nfl_summands hvF) h1 h2
  rw [hV', cmpList_append_same] at h1 h2
  have hVN : NFL V' := nfl_append_right (hV' ▸ nfl_summands hvF)
  cases V' with
  | nil =>
    cases e : summands y with
    | nil => exact hy0 (eq_zero_of_summands_nil e)
    | cons a l =>
      rw [e, cmpList_cons_nil] at h1
      exact h1 rfl
  | cons h' V'' =>
    have hRm := h.1 R (List.mem_append_right _ List.mem_cons_self)
    have hhm := hVN.1 h' List.mem_cons_self
    rcases cmpList_lt_cases h2 with e | ⟨e, -⟩
    · have hv'F : WNF (ofSummands (h' :: V'')) := wnf_ofSummands hVN
      have hv'R : Lt (ofSummands (h' :: V'')) R := by
        unfold Lt
        rw [cmp_eq, summands_ofSummands _ (nfl_principal hVN), summands_principal hRm.2]
        exact cmpList_head_lt _ _ e
      have hsub := subs_trans hv (tail_mem_subs hvF hV' (by simp))
      have hlt' := hgap _ hsub hv'R.ne hv'R
      have hyv : Le y (ofSummands (h' :: V'')) := by
        apply le_of_ne_gtY hy hv'F
        rw [cmp_eq, summands_ofSummands _ (nfl_principal hVN)]
        exact h1
      exact not_lt_of_leY hx hv'F (le_transY hx hy hv'F hxy hyv) hlt'
    · have hab := eq_of_cmpP_eqY hhm.1 hRm.1 hhm.2 hRm.2 e
      subst hab
      have hsv : h' ∈ subs v := mem_subs_of_mem_summands (by rw [hV']; simp)
      have e1 := size_lt_of_mem_subs_ne hv hne
      have e2 := size_le_of_mem_subs hsv
      omega

/-! ### 近似の崩壊の不変量 -/

theorem zero_oadd {y : Tm} (hy : WNF y) : oadd .zero y = y := by
  unfold oadd
  cases hs : summands y with
  | nil => exact (eq_zero_of_summands_nil hs).symm
  | cons h r =>
    simp only [summands, List.takeWhile_nil, List.nil_append]
    rw [← hs]
    exact ofSummands_summands y hy

theorem mem_summands_oadd_right {x y s : Tm} (hx : WNF x) (hy : WNF y) (hs : s ∈ summands y) :
    s ∈ summands (oadd x y) := by
  cases e : summands y with
  | nil =>
    rw [e] at hs
    cases hs
  | cons h r =>
    rw [summands_oadd e (nfl_principal (nfl_summands hx)) (nfl_principal (nfl_summands hy))]
    exact List.mem_append_right _ hs

/-- `b ≤ b ⊕ ξ` -/
theorem le_oadd_left {b ξ : Tm} (hb : WNF b) (hξ : WNF ξ) : Le b (oadd b ξ) := by
  by_cases h0 : ξ = .zero
  · rw [h0, oadd_zero]
    exact Or.inl rfl
  · exact Or.inr (lt_oadd_left hb hξ h0)

theorem wnf_of_argR {κ r : Tm} (hκ : WNF κ) (hr : argR? κ = some r) : WNF r := by
  cases κ with
  | Xi n q =>
    simp only [argR?, Option.some.injEq] at hr
    subst hr
    exact hκ.xi.2.1
  | Psi ζ k b =>
    simp only [argR?, Option.some.injEq] at hr
    subst hr
    exact hκ.psi.aF
  | _ => simp [argR?] at hr

/-- 近似 `pre ⊕ (x # P)` -/
def approx (pre : List Tm) (P x : Tm) : Tm := oadd (ofSummands pre) (nsum x P)

theorem combine_psi0_approx {π : Tm} {pre : List Tm} {P x : Tm} (hx : WNF x) :
    combine (.psi0 π) pre .zero P x = approx pre P x := by
  show oadd (ofSummands pre) (nsum (oadd .zero x) P) = _
  rw [zero_oadd hx]
  rfl

theorem inC_nsum_left {a b g d : Tm} (ha : WNF a) (hb : WNF b) (h : inC (nsum a b) g d = true) :
    inC a g d = true := by
  rw [inC_iff_summands ha]
  rw [inC_iff_summands (wnf_nsum ha hb)] at h
  intro s hs
  apply h s
  rw [summands_nsum ha hb]
  exact (merge_perm _ _).mem_iff.mpr (List.mem_append_left _ hs)

theorem inC_nsum_right {a b g d : Tm} (ha : WNF a) (hb : WNF b) (h : inC (nsum a b) g d = true) :
    inC b g d = true := by
  rw [inC_iff_summands hb]
  rw [inC_iff_summands (wnf_nsum ha hb)] at h
  intro s hs
  apply h s
  rw [summands_nsum ha hb]
  exact (merge_perm _ _).mem_iff.mpr (List.mem_append_right _ hs)

/-- 近似の崩壊の Mahlo 添字 `ξ` の仮定（`ξ = 0` なら自明） -/
structure IdxHyp (ξ π X : Tm) : Prop where
  hF : WNF ξ
  hπ : Lt ξ π
  hm : Lt ξ (mi π)
  hC : inC ξ (mi π) π = true

theorem IdxHyp.zero {π X : Tm} (ht : WNF (.Psi .zero π X)) : IdxHyp .zero π X :=
  ⟨WNF.zero, zero_lt ht.psi.tgt.ne_zero, mi_pos ht.psi.piF ht.psi.tgt, inC_zero _ _⟩

/-- 分割 `pre ++ R :: rest` と、`R` 未満の `x`（`R[n]` の役）についての、近似 `pre ⊕ (x # P)` の崩壊 `Ψ^ξ_π` の仮定。
    `x` の `C` への所属は、`R[n]`・対角化の項のそれぞれで示して渡す -/
structure Approx1 (ξ π X P : Tm) (pre rest : List Tm) (R x : Tm) : Prop where
  ht : WNF (.Psi .zero π X)
  hsum : summands X = pre ++ R :: rest
  hx : WNF x
  hxR : Lt x R
  hPF : WNF P
  hPR : Lt P R
  hPπ : Lt P π
  /-- 目標の引数の下限 -/
  hr : ∀ r, argR? π = some r → Lt r (approx pre P x)
  /-- `x` は `C(A, π)` に入る -/
  hCx : inC x (approx pre P x) π = true
  /-- Mahlo 添字 -/
  hI : IdxHyp ξ π X
  hξA : Le ξ (approx pre P x)

namespace Approx1

variable {ξ π X P : Tm} {pre rest : List Tm} {R x : Tm}

theorem hX (H : Approx1 ξ π X P pre rest R x) : WNF X := H.ht.psi.aF
theorem hπF (H : Approx1 ξ π X P pre rest R x) : WNF π := H.ht.psi.piF

theorem hN (H : Approx1 ξ π X P pre rest R x) : NFL (pre ++ R :: rest) := H.hsum ▸ nfl_summands H.hX

theorem hXeq (H : Approx1 ξ π X P pre rest R x) : X = ofSummands (pre ++ R :: rest) := by
  rw [← H.hsum, ofSummands_summands X H.hX]

theorem hRm (H : Approx1 ξ π X P pre rest R x) : R ∈ summands X := by
  rw [H.hsum]
  exact List.mem_append_right _ List.mem_cons_self

theorem hRF (H : Approx1 ξ π X P pre rest R x) : WNF R :=
  (H.hN.1 R (List.mem_append_right _ List.mem_cons_self)).1

theorem hRp (H : Approx1 ξ π X P pre rest R x) : isPrincipal R = true :=
  (H.hN.1 R (List.mem_append_right _ List.mem_cons_self)).2

theorem hpreN (H : Approx1 ξ π X P pre rest R x) : NFL pre := nfl_append_left H.hN

theorem hpreF (H : Approx1 ξ π X P pre rest R x) : WNF (ofSummands pre) := wnf_ofSummands H.hpreN

theorem hy (H : Approx1 ξ π X P pre rest R x) : WNF (nsum x P) := wnf_nsum H.hx H.hPF

theorem hyR (H : Approx1 ξ π X P pre rest R x) : Lt (nsum x P) R :=
  nsum_lt_prin H.hx H.hPF H.hRp H.hxR H.hPR

theorem hAF (H : Approx1 ξ π X P pre rest R x) : WNF (approx pre P x) := wnf_oadd H.hpreF H.hy

theorem hAlt (H : Approx1 ξ π X P pre rest R x) : Lt (approx pre P x) X := by
  rw [H.hXeq]
  exact oadd_pre_lt H.hN H.hy H.hyR

theorem hC (H : Approx1 ξ π X P pre rest R x) :
    inC (approx pre P x) (approx pre P x) π = true := by
  have hXC : inC (ofSummands (pre ++ R :: rest)) (ofSummands (pre ++ R :: rest)) π = true := by
    rw [← H.hXeq]
    exact H.ht.psi.Ca
  exact inC_oadd H.hpreF H.hy (inC_pre H.hN H.hy H.hyR H.hπF hXC)
    (inC_nsum H.hx H.hPF H.hCx (WFY.inC_of_ltY _ H.hPF H.hπF H.hPπ))

theorem hξπ (H : Approx1 ξ π X P pre rest R x) : Lt ξ π := H.hI.hπ

/-- 近似の崩壊は標準形 -/
theorem hnf (H : Approx1 ξ π X P pre rest R x) : WNF (.Psi ξ π (approx pre P x)) :=
  WNF.mk_psi {
    tgt := H.ht.psi.tgt
    xiF := H.hI.hF
    piF := H.hπF
    aF := H.hAF
    le := ne_gt_of_le H.hξA
    Ca := H.hC
    Cxi := WFY.inC_of_ltY _ H.hI.hF H.hπF H.hξπ
    Cpi := inC_tgt H.hπF H.ht.psi.tgt H.hAF H.hr
    mlt := H.hI.hm
    mC := H.hI.hC }

theorem fr_pre (H : Approx1 ξ π X P pre rest R x) {w : Tm} (h : w ∈ fr π (ofSummands pre)) :
    w ∈ fr π X := by
  obtain ⟨s, hs, hw⟩ := (mem_fr_iff H.hpreF).mp h
  rw [summands_ofSummands _ (nfl_principal H.hpreN)] at hs
  exact (mem_fr_iff H.hX).mpr ⟨s, by rw [H.hsum]; exact List.mem_append_left _ hs, hw⟩

/-- 近似の前線は 3 つの部分のどれか -/
theorem mem_fr_approx (H : Approx1 ξ π X P pre rest R x) {w : Tm} (h : w ∈ fr π (approx pre P x)) :
    w ∈ fr π (ofSummands pre) ∨ w ∈ fr π x ∨ w ∈ fr π P := by
  rcases mem_fr_oadd H.hpreF H.hy h with h | h
  · exact Or.inl h
  · rcases mem_fr_nsum H.hx H.hPF h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem fr_approx_of_pre (H : Approx1 ξ π X P pre rest R x) {w : Tm}
    (h : w ∈ fr π (ofSummands pre)) : w ∈ fr π (approx pre P x) :=
  fr_oadd_of_left H.hpreF H.hy (fun s hd r' hs e => by
    rw [summands_ofSummands _ (nfl_principal H.hpreN)] at hs
    exact head_le_pre H.hN H.hy H.hyR s hd r' hs e) h

theorem fr_approx_of_x (H : Approx1 ξ π X P pre rest R x) {w : Tm} (h : w ∈ fr π x) :
    w ∈ fr π (approx pre P x) :=
  fr_oadd_of_right H.hpreF H.hy (fr_nsum_of_left H.hx H.hPF h)

/-- 成分が `C(g, d)` に入るなら近似の崩壊も入る -/
theorem inC_node (H : Approx1 ξ π X P pre rest R x) {g d : Tm} (hk : inC π g d = true)
    (hz : inC ξ g d = true) (hpre : inC (ofSummands pre) g d = true) (hx : inC x g d = true)
    (hP : inC P g d = true) (hlt : Lt (approx pre P x) g) :
    inC (.Psi ξ π (approx pre P x)) g d = true :=
  inC_psi_iff.mpr (Or.inr ⟨hk, hz, inC_oadd H.hpreF H.hy hpre (inC_nsum H.hx H.hPF hx hP), hlt⟩)

/-- 近似の引数は上端 `pre ⊕ R` 未満 -/
theorem hAtop (H : Approx1 ξ π X P pre rest R x) : Lt (approx pre P x) (oadd (ofSummands pre) R) :=
  oadd_lt_oadd H.hpreF H.hy H.hRF H.hyR

/-- 2 点の比較：`x < x'` で `x` が `x'` の成分に含まれるなら、近似の崩壊も単調 -/
theorem hltS {x' : Tm} (H : Approx1 ξ π X P pre rest R x) (H' : Approx1 ξ π X P pre rest R x')
    (hxx : Lt x x')
    (hS1 : inC x' (approx pre P x') (.Psi ξ π (approx pre P x')) = true →
      inC x (approx pre P x') (.Psi ξ π (approx pre P x')) = true)
    (hS2 : inC x' (approx pre P x') π = true → inC x (approx pre P x') π = true) :
    Lt (.Psi ξ π (approx pre P x)) (.Psi ξ π (approx pre P x')) := by
  have hu := H'.hnf
  have hA' := H'.hAF
  have hAmono : Lt (approx pre P x) (approx pre P x') :=
    oadd_lt_oadd H.hpreF H.hy H'.hy (nsum_lt_left H.hx H'.hx H.hPF hxx)
  have hle : Le (.Psi ξ π (approx pre P x')) π := Or.inr (lt_psi_targetY hu)
  refine psi_lt_psi_of_arg H.hnf hu hAmono fun w hw => ?_
  rcases H.mem_fr_approx hw with h | h | h
  · exact FWOrder.k2 hu w (H'.fr_approx_of_pre h)
  · have h1 := inC_of_fr_lt H'.hx H.hπF hu hA' hA' H'.hCx hle (Or.inl rfl)
      fun z hz => FWOrder.k2 hu z (H'.fr_approx_of_x hz)
    have h4 := (inC_frY H.hx H.hπF hu hA' hA' (hS2 H'.hCx) hle (Or.inl rfl)).mp (hS1 h1) w h
    exact coll_psiY hu w (H.hx.of_mem_subs (fr_spec h).1) h4 (fr_spec h).2
  · exact FWOrder.k2 hu w (fr_oadd_of_right H'.hpreF H'.hy (fr_nsum_of_right H'.hx H'.hPF h))

/-- 2 点の上界 -/
theorem hubS {x' : Tm} (H : Approx1 ξ π X P pre rest R x) (H' : Approx1 ξ π X P pre rest R x')
    (hxx : Lt x x')
    (hmono : Lt (.Psi ξ π (approx pre P x)) (.Psi ξ π (approx pre P x')))
    (g d : Tm) (hg : WNF g) (hd : WNF d)
    (hS : Le d π → inC x' g d = true → inC π g d = true → inC (ofSummands pre) g d = true →
      inC P g d = true → Lt (approx pre P x) g → inC x g d = true)
    (h : inC (.Psi ξ π (approx pre P x')) g d = true) :
    inC (.Psi ξ π (approx pre P x)) g d = true := by
  have hAmono : Lt (approx pre P x) (approx pre P x') :=
    oadd_lt_oadd H.hpreF H.hy H'.hy (nsum_lt_left H.hx H'.hx H.hPF hxx)
  by_cases hdy : Lt (.Psi ξ π (approx pre P x')) d
  · exact WFY.inC_of_ltY _ H.hnf hd (lt_transY H.hnf H'.hnf hd hmono hdy)
  rcases inC_psi_iff.mp h with h' | ⟨hk, hz, hδ, hlt⟩
  · exact absurd h' hdy
  · have hdπ : Le d π := le_transY hd H'.hnf H.hπF (le_of_not_ltY H'.hnf hd hdy)
      (Or.inr (lt_psi_targetY H'.hnf))
    have hlt' : Lt (approx pre P x) g := lt_transY H.hAF H'.hAF hg hAmono hlt
    refine inC_psi_iff.mpr (Or.inr ⟨hk, hz, ?_, hlt'⟩)
    have hmem : ∀ s, s ∈ pre ++ summands (nsum x' P) → inC s g d = true := by
      intro s hs
      refine inC_of_mem_summands H'.hAF hδ ?_
      show s ∈ summands (oadd (ofSummands pre) (nsum x' P))
      rw [summands_oadd_pre H'.hpreN H'.hy (head_le_pre H'.hN H'.hy H'.hyR)]
      exact hs
    have hy' : inC (nsum x' P) g d = true :=
      (inC_iff_summands H'.hy).mpr fun s hs => hmem s (List.mem_append_right _ hs)
    have hpreC : inC (ofSummands pre) g d = true := by
      rw [inC_ofSummands]
      exact fun s hs => hmem s (List.mem_append_left _ hs)
    have hPC := inC_nsum_right H'.hx H'.hPF hy'
    exact inC_oadd H.hpreF H.hy hpreC (inC_nsum H.hx H.hPF
      (hS hdπ (inC_nsum_left H'.hx H'.hPF hy') hk hpreC hPC hlt') hPC)

/-- 近似の引数の部品 -/
theorem inC_parts (H : Approx1 ξ π X P pre rest R x) {g d : Tm}
    (h : inC (approx pre P x) g d = true) :
    inC (ofSummands pre) g d = true ∧ inC P g d = true := by
  have hmem : ∀ s, s ∈ pre ++ summands (nsum x P) → inC s g d = true := by
    intro s hs
    refine inC_of_mem_summands H.hAF h ?_
    show s ∈ summands (oadd (ofSummands pre) (nsum x P))
    rw [summands_oadd_pre H.hpreN H.hy (head_le_pre H.hN H.hy H.hyR)]
    exact hs
  have hy : inC (nsum x P) g d = true :=
    (inC_iff_summands H.hy).mpr fun s hs => hmem s (List.mem_append_right _ hs)
  refine ⟨?_, inC_nsum_right H.hx H.hPF hy⟩
  rw [inC_ofSummands]
  exact fun s hs => hmem s (List.mem_append_left _ hs)

/-- 近似の引数は `C(A, y)` に入る -/
theorem inC_self (H : Approx1 ξ π X P pre rest R x) :
    inC (approx pre P x) (approx pre P x) (.Psi ξ π (approx pre P x)) = true := by
  have hy := H.hnf
  exact inC_of_fr_lt H.hAF H.hπF hy H.hAF H.hAF H.hC (Or.inr (lt_psi_targetY hy)) (Or.inl rfl)
    fun w hw => FWOrder.k2 hy w hw

end Approx1

/-- `x ∈ C(A, π)`：`R` の上界と隙間から -/
theorem inC_approx_of_ub {π X P : Tm} {pre rest : List Tm} {R x : Tm}
    (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest) (hx : WNF x)
    (hx0 : x = .zero → ∀ v, v ∈ subs R → v = R) (hxR : Lt x R) (hPF : WNF P) (hPR : Lt P R)
    (hr : ∀ r, argR? π = some r → Lt r (approx pre P x))
    (hub : inC R (approx pre P x) π = true → inC π (approx pre P x) π = true →
      inC x (approx pre P x) π = true)
    (hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v x) :
    inC x (approx pre P x) π = true := by
  have hX := ht.psi.aF
  have hπF := ht.psi.piF
  have hN : NFL (pre ++ R :: rest) := hsum ▸ nfl_summands hX
  have hRm : R ∈ summands X := by
    rw [hsum]
    exact List.mem_append_right _ List.mem_cons_self
  have hRN := hN.1 R (List.mem_append_right _ List.mem_cons_self)
  have hy := wnf_nsum hx hPF
  have hyR : Lt (nsum x P) R := nsum_lt_prin hx hPF hRN.2 hxR hPR
  have hy0 : x ≠ .zero → nsum x P ≠ .zero := by
    intro hx1 e
    have h := le_nsum_left hx hPF
    rw [e] at h
    rcases h with h | h
    · exact hx1 h
    · exact not_lt_zero _ h
  have hA : WNF (approx pre P x) := wnf_oadd (wnf_ofSummands (nfl_append_left hN)) hy
  have hXe : X = ofSummands (pre ++ R :: rest) := by rw [← hsum, ofSummands_summands X hX]
  have hRA : inC R (approx pre P x) π = true :=
    inC_mono_proper hπF hRN.1 (inC_of_mem_summands hX ht.psi.Ca hRm) fun v hv hne hvX =>
      lt_approx_of_gap hN hy (hy0 fun e => hne (hx0 e v hv)) hyR hx (le_nsum_left hx hPF) hgap hv hne
        (hRN.1.of_mem_subs hv) (by rw [← hXe]; exact hvX)
  exact hub hRA (inC_tgt hπF ht.psi.tgt hA hr)

/-- 種の仮定 -/
structure SeedHyp (π X P R : Tm) : Prop where
  hPF : WNF P
  hPR : Lt P R
  hPπ : Lt P π
  /-- 種は後者でない -/
  hPs : ¬ isSucc P = true

theorem seed_zero {π X R : Tm} (hπ : π ≠ .zero) (hR0 : R ≠ .zero) : SeedHyp π X .zero R where
  hPF := WNF.zero
  hPR := zero_lt hR0
  hPπ := zero_lt hπ
  hPs := by simp [isSucc, summands]

/-- 有効性の調整 `c` の仮定：`R` 未満で、目標 `π` の成分 -/
structure AdjHyp (π R c : Tm) : Prop where
  hF : WNF c
  hR : Lt c R
  hU : ∀ g d, WNF d → Le d π → inC π g d = true → inC c g d = true

theorem AdjHyp.zero {π R : Tm} (hR0 : R ≠ .zero) : AdjHyp π R .zero :=
  ⟨WNF.zero, zero_lt hR0, fun _ _ _ _ _ => inC_zero _ _⟩

/-- 近似は `x` について単調 -/
theorem approx_mono {pre : List Tm} {P x x' : Tm} (hpre : WNF (ofSummands pre)) (hx : WNF x)
    (hx' : WNF x') (hP : WNF P) (h : Lt x x') : Lt (approx pre P x) (approx pre P x') :=
  oadd_lt_oadd hpre (wnf_nsum hx hP) (wnf_nsum hx' hP) (nsum_lt_left hx hx' hP h)

/-- 近似の族：`t[n] = Ψ^ξ_π(pre ⊕ (x_n # P))` -/
structure AFam (ξ π X P : Tm) (pre rest : List Tm) (R : Tm) (x : Nat → Tm) : Prop where
  A : ∀ n, Approx1 ξ π X P pre rest R (x n)
  mono : ∀ n, Lt (x n) (x (n + 1))
  ub : ∀ g d n, WNF g → WNF d → Le d π → inC R g d = true → inC (ofSummands pre) g d = true →
    Le (oadd (ofSummands pre) R) g → inC π g d = true → inC P g d = true → inC (x n) g d = true
  ub2 : ∀ g d n, WNF g → WNF d → Le d π → inC (x (n + 1)) g d = true → inC π g d = true →
    inC (ofSummands pre) g d = true → inC P g d = true → Lt (approx pre P (x n)) g →
    inC (x n) g d = true

/-- 共終数 `ω` の列の局所的な性質：良さ・非零・梯子の上界 -/
structure NatL (t : Tm) (s : SeqD) : Prop where
  good : NatGood t s
  pos : ∀ n, s.nat n ≠ .zero
  ub2 : ∀ g d n, WNF g → WNF d → inC (s.nat (n + 1)) g d = true → inC (s.nat n) g d = true

/-- 共終数 `ω` の列の不変量（隙間を除く）：良さ・上界・梯子の上界 -/
structure NatUB (t : Tm) (s : SeqD) : Prop where
  good : NatGood t s
  pos : ∀ n, s.nat n ≠ .zero
  /-- 上界：`t ∈ C(g, d)` なら `t[n] ∈ C(g, d)` -/
  ub : ∀ g d n, WNF g → WNF d → inC t g d = true → inC (s.nat n) g d = true
  /-- 梯子の上界：`t[n+1] ∈ C(g, d)` なら `t[n] ∈ C(g, d)` -/
  ub2 : ∀ g d n, WNF g → WNF d → inC (s.nat (n + 1)) g d = true → inC (s.nat n) g d = true

/-- 隙間：`t` の真の部分項で `t` 未満のものは `t[n]` 未満 -/
def NatGap (t : Tm) (s : SeqD) : Prop :=
  ∀ n v, v ∈ subs t → v ≠ t → Lt v t → Lt v (s.nat n)

theorem NatUB.shift {t : Tm} {s : SeqD} (h : NatUB t s) : NatUB t (.shift s) :=
  ⟨natGood_shift h.good, fun n => h.pos (n + 1), fun g d n => h.ub g d (n + 1),
    fun g d n => h.ub2 g d (n + 1)⟩

theorem NatL.shift {t : Tm} {s : SeqD} (h : NatL t s) : NatL t (.shift s) :=
  ⟨natGood_shift h.good, fun n => h.pos (n + 1), fun g d n => h.ub2 g d (n + 1)⟩

/-- 局所的な性質と上界から不変量へ -/
theorem NatL.toUB {t : Tm} {s : SeqD} (h : NatL t s)
    (hub : ∀ g d n, WNF g → WNF d → inC t g d = true → inC (s.nat n) g d = true) : NatUB t s :=
  ⟨h.good, h.pos, hub, h.ub2⟩

/-- 上の項を取り替える -/
theorem NatL.lower {t t' : Tm} {s : SeqD} (h : NatL t s) (hlt : ∀ n, Lt (s.nat n) t') : NatL t' s :=
  ⟨fun n => ⟨(h.good n).1, hlt n, (h.good n).2.2⟩, h.pos, h.ub2⟩

theorem NatGap.shift {t : Tm} {s : SeqD} (h : NatGap t s) : NatGap t (.shift s) :=
  fun n => h (n + 1)

/-- 種の倍数 `[n] = p·(n+k)`（`k ≥ 1`） -/
theorem natUB_mul {t p : Tm} (hp : WNF p) (hpp : isPrincipal p = true) (htp : isPrincipal t = true)
    (hlt : Lt p t) (hC : ∀ g d, WNF g → WNF d → inC t g d = true → inC p g d = true) {k : Nat}
    (hk : 1 ≤ k) : NatUB t (.mul p k) where
  good := natGood_mul hp hpp htp hlt k
  pos n := ofSummands_ne_zero (by simp; omega) (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact hpp)
  ub g d n hg hd h := inC_mulNat (hC g d hg hd h) _
  ub2 g d n _ _ h := by
    refine inC_mulNat ?_ _
    exact (inC_ofSummands _).mp h p (List.mem_replicate.mpr ⟨by omega, rfl⟩)

/-- 引数の下限がない目標への崩壊では、`app` は常に作られる -/
theorem mkApp_noArg {ceil τ : Tm} {pre : List Tm} {R : Tm} {r : SeqD} {P c : Tm}
    (hτ : argR? τ = none) (hP : P = .zero ∨ ltB P R = true) :
    mkApp ceil (.psi0 τ) pre R r P c = some (.app ceil (.psi0 τ) pre R r P (kAdj τ ceil (.psi0 τ) pre R r)) := by
  unfold mkApp
  rcases hP with rfl | hP
  · simp [Gen.tgt?, hτ, tailRaw]
  · simp [hP, Gen.tgt?, hτ, tailRaw]

/-- 近似の族から `ω` 型の列の局所的な性質 -/
theorem natL_of_fam {ξ π X P : Tm} {pre rest : List Tm} {R : Tm} {x : Nat → Tm} {s : SeqD}
    (F : AFam ξ π X P pre rest R x) (he : ∀ n, s.nat n = .Psi ξ π (approx pre P (x n))) :
    NatL π s := by
  have hm : ∀ n, Lt (.Psi ξ π (approx pre P (x n))) (.Psi ξ π (approx pre P (x (n + 1)))) := fun n => by
    have Ha := F.A (n + 1)
    have hu := Ha.hnf
    have hAA := approx_mono (F.A n).hpreF (F.A n).hx Ha.hx (F.A n).hPF (F.mono n)
    have h1 := Ha.inC_parts Ha.inC_self
    have h2 := Ha.inC_parts Ha.hC
    exact (F.A n).hltS Ha (F.mono n)
      (fun h => F.ub2 _ _ n Ha.hAF hu (Or.inr (lt_psi_targetY hu)) h
        (inC_tgt_of_k2t hu fun w hw => FWOrder.k2t hu w hw) h1.1 h1.2 hAA)
      (fun h => F.ub2 _ _ n Ha.hAF Ha.hπF (Or.inl rfl) h
        (inC_tgt Ha.hπF Ha.ht.psi.tgt Ha.hAF Ha.hr) h2.1 h2.2 hAA)
  refine ⟨fun n => ?_, fun n => ?_, fun g d n hg hd h => ?_⟩
  · rw [he n, he (n + 1)]
    exact ⟨(F.A n).hnf, lt_psi_targetY (F.A n).hnf, hm n⟩
  · rw [he n]
    intro h
    cases h
  · rw [he (n + 1)] at h
    rw [he n]
    exact (F.A n).hubS (F.A (n + 1)) (F.mono n) (hm n) g d hg hd
      (fun hle h' hk hpre hP hlt => F.ub2 g d n hg hd hle h' hk hpre hP hlt) h

/-- 近似の族の上界（成分が `C(g, d)` に入るとき） -/
theorem AFam.ubC {ξ π X P : Tm} {pre rest : List Tm} {R : Tm} {x : Nat → Tm} {s : SeqD}
    (F : AFam ξ π X P pre rest R x) (he : ∀ n, s.nat n = .Psi ξ π (approx pre P (x n)))
    {g d : Tm} (hg : WNF g) (hd : WNF d) (hle : Le d π) (hk : inC π g d = true)
    (hRC : inC R g d = true) (hpre : inC (ofSummands pre) g d = true)
    (hT : Le (oadd (ofSummands pre) R) g) (hP : inC P g d = true) (hz : inC ξ g d = true) (n : Nat) :
    inC (s.nat n) g d = true := by
  rw [he n]
  have H := F.A n
  exact H.inC_node hk hz hpre (F.ub g d n hg hd hle hRC hpre hT hk hP) hP
    (lt_of_lt_of_leY H.hAF (wnf_oadd H.hpreF H.hRF) hg H.hAtop hT)

/-- 分割の上端は `X` 以下 -/
theorem top_le {X R : Tm} {pre rest : List Tm} (hX : WNF X) (hsum : summands X = pre ++ R :: rest) :
    Le (oadd (ofSummands pre) R) X := by
  have hN : NFL (pre ++ R :: rest) := hsum ▸ nfl_summands hX
  have hRN := hN.1 R (List.mem_append_right _ List.mem_cons_self)
  have hpN := nfl_append_left hN
  have hT : WNF (oadd (ofSummands pre) R) := wnf_oadd (wnf_ofSummands hpN) hRN.1
  have hge : ∀ s h r, s ∈ pre → summands R = h :: r → leB h s = true := by
    intro s h r hs e
    rw [summands_principal hRN.2] at e
    simp only [List.cons.injEq] at e
    rw [← e.1, leB_iff]
    exact le_of_nfl_append hN s hs
  apply le_of_ne_gtY hT hX
  rw [cmp_eq, summands_oadd_pre hpN hRN.1 hge, hsum, summands_principal hRN.2, cmpList_append_same,
    cmpList_cons_cons_eq _ _ (cmpP_self R)]
  cases rest with
  | nil => rw [cmpList_nil_nil]; decide
  | cons _ _ => rw [cmpList_nil_cons]; decide

/-- `t ∈ C(g, d)` で `t` が `d` 以上なら成分が入る -/
theorem comp_of_inC {π X g d : Tm} (ht : WNF (.Psi .zero π X)) (hd : WNF d)
    (hdt : ¬ Lt (.Psi .zero π X) d) (h : inC (.Psi .zero π X) g d = true) :
    Le d π ∧ inC π g d = true ∧ inC X g d = true ∧ Lt X g := by
  rcases inC_psi_iff.mp h with h' | ⟨hk, -, hδ, hlt⟩
  · exact absurd h' hdt
  · exact ⟨le_transY hd ht ht.psi.piF (le_of_not_ltY ht hd hdt) (Or.inr (lt_psi_targetY ht)), hk, hδ, hlt⟩

/-- `pre` は `X` の成分 -/
theorem inC_pre_of_X {X R g d : Tm} {pre rest : List Tm} (hX : WNF X)
    (hsum : summands X = pre ++ R :: rest) (h : inC X g d = true) :
    inC (ofSummands pre) g d = true := by
  rw [inC_ofSummands]
  intro s hs
  exact inC_of_mem_summands hX h (by rw [hsum]; exact List.mem_append_left _ hs)

/-- 近似の族の一つずらし -/
theorem AFam.shift {ξ π X P : Tm} {pre rest : List Tm} {R : Tm} {x : Nat → Tm}
    (F : AFam ξ π X P pre rest R x) : AFam ξ π X P pre rest R (fun n => x (n + 1)) :=
  ⟨fun n => F.A (n + 1), fun n => F.mono (n + 1), fun g d n => F.ub g d (n + 1),
    fun g d n => F.ub2 g d (n + 1)⟩

/-! ### 種の上界 -/

/-- 後者の種 `Ψ^0_π(pred X)` は `t = Ψ^0_π(X)` と同じ上界を持つ -/
theorem inC_seed_succ {π X g d : Tm} (ht : WNF (.Psi .zero π X)) (hs : isSucc X = true)
    (hp : WNF (.Psi .zero π (pred X))) (hg : WNF g) (hd : WNF d)
    (h : inC (.Psi .zero π X) g d = true) : inC (.Psi .zero π (pred X)) g d = true := by
  have hX := ht.psi.aF
  rcases inC_psi_iff.mp h with h' | ⟨hk, hz, hδ, hlt⟩
  · exact WFY.inC_of_ltY _ hp hd (lt_transY hp ht hd (psi_pred_lt hp ht hs) h')
  · refine inC_psi_iff.mpr (Or.inr ⟨hk, hz, ?_, lt_transY (wnf_pred hX) hX hg (pred_lt hX hs) hlt⟩)
    unfold pred
    rw [inC_ofSummands]
    intro s hsm
    exact inC_of_mem_summands hX hδ (List.dropLast_subset _ hsm)

/-- 引数の前線の元は `t = Ψ^0_π(X)` と同じ上界を持つ -/
theorem inC_seed_fr {π X w g d : Tm} (ht : WNF (.Psi .zero π X)) (hw : w ∈ fr π X) (hg : WNF g)
    (hd : WNF d) (h : inC (.Psi .zero π X) g d = true) : inC w g d = true := by
  have hP := ht.psi
  have hwF : WNF w := hP.aF.of_mem_subs (fr_spec hw).1
  by_cases h1 : Lt (.Psi .zero π X) d
  · exact WFY.inC_of_ltY _ hwF hd (lt_transY hwF ht hd (FWOrder.k2 ht w hw) h1)
  · rcases inC_psi_iff.mp h with h' | ⟨-, -, hδ, hlt⟩
    · exact absurd h' h1
    · have hdπ : Le d π := le_transY hd ht hP.piF (le_of_not_ltY ht hd h1) (Or.inr (lt_psi_targetY ht))
      exact (inC_frY hP.aF hP.piF hd hP.aF hg hP.Ca hdπ (Or.inr hlt)).mp hδ w hw

/-! ### 目標が `Ω_c`：後者の引数 -/

/-! ### 目標が `Ω_c`：極限の引数 -/

theorem summands_pre_last {X : Tm} (hX0 : X ≠ .zero) :
    summands X = preT (info X).sums ++ [lastT (info X).sums] := by
  rw [preT_info, lastT_info]
  cases e : (summands X).getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp e) (summands_ne_nil hX0)
  | some a =>
    obtain ⟨L, hL⟩ := List.getLast?_eq_some_iff.mp e
    rw [hL, List.dropLast_concat]
    rfl

end RTKA.Fund
