import Compact.FS.Front

/-! 近似の崩壊の列（`app`）の枠組み。

`ψ` への崩壊の近似は `A_n = pre ⊕ ((c + R[n]) # P)`（`combine`）。列 `Ψ^0_π(A_n)` が `t = Ψ^0_π(X)` について
良いための十分条件（`natGood_app_psi0`）：

* `A_n` は標準形で `A_n ∈ C(A_n, π)`、目標の引数 `r` より大きい（`Ψ^0_π(A_n)` が標準形、`wnf_psi0`）。
* `A_n < X` で、`A_n` の前線（`π` について）の元は全て `t` 未満（`Ψ^0_π(A_n) < t`、`psi_lt_psi_of_arg`）。
* `A_n < A_{n+1}` で、`A_n` の前線の元は全て `Ψ^0_π(A_{n+1})` 未満（単調）。

近似の形だけで決まる部分（標準形・順序）もここで示す。そのために自然な和の可換性を示す。 -/

namespace RTKA.Fund

open Tm W

/-! ### 自然な和の可換性 -/

theorem merge_perm : ∀ l m : List Tm, (merge l m).Perm (l ++ m)
  | [], m => by rw [merge.eq_1]; exact List.Perm.refl _
  | x :: xs, [] => by rw [merge.eq_2, List.append_nil]
  | x :: xs, y :: ys => by
    rw [merge.eq_3]
    split
    · exact (merge_perm xs (y :: ys)).cons x
    · refine ((merge_perm (x :: xs) ys).cons y).trans ?_
      exact List.perm_middle.symm
termination_by l m => l.length + m.length

/-- 大きい順に並んだ標準形の主要項の列は、同じ要素からなれば等しい -/
theorem eq_of_perm_nfl : ∀ {l m : List Tm}, NFL l → NFL m → l.Perm m → l = m
  | [], m, _, _, h => h.nil_eq
  | a :: as, [], _, _, h => absurd h.symm.nil_eq (List.cons_ne_nil a as).symm
  | a :: as, b :: bs, hl, hm, h => by
    have hab : a = b := by
      by_cases hne : a = b
      · exact hne
      exfalso
      have ha : a ∈ bs := by
        rcases List.mem_cons.mp (h.mem_iff.mp List.mem_cons_self) with e | e
        · exact absurd e hne
        · exact e
      have hb : b ∈ as := by
        rcases List.mem_cons.mp (h.mem_iff.mpr List.mem_cons_self) with e | e
        · exact absurd e.symm hne
        · exact e
      have haF := (hl.1 a List.mem_cons_self).1
      have hbF := (hm.1 b List.mem_cons_self).1
      have h1 := le_head_of_nfl hm a ha
      have h2 := le_head_of_nfl hl b hb
      exact hne (le_antisymmY haF hbF (le_of_ne_gtY haF hbF h1) (le_of_ne_gtY hbF haF h2))
    subst hab
    rw [eq_of_perm_nfl (nfl_tail hl) (nfl_tail hm) (h.cons_inv)]

theorem merge_comm {l m : List Tm} (hl : NFL l) (hm : NFL m) : merge l m = merge m l :=
  eq_of_perm_nfl (nfl_merge hl hm) (nfl_merge hm hl)
    ((merge_perm l m).trans (List.perm_append_comm.trans (merge_perm m l).symm))

theorem nsum_comm {x y : Tm} (hx : WNF x) (hy : WNF y) : nsum x y = nsum y x := by
  unfold nsum
  rw [merge_comm (nfl_summands hx) (nfl_summands hy)]

theorem nsum_lt_left {x x' y : Tm} (hx : WNF x) (hx' : WNF x') (hy : WNF y) (h : Lt x x') :
    Lt (nsum x y) (nsum x' y) := by
  rw [nsum_comm hx hy, nsum_comm hx' hy]
  exact nsum_lt_right hy hx hx' h

/-! ### ψ への崩壊の近似 -/

theorem wnf_combine_psi0 {π : Tm} {pre : List Tm} {c P x : Tm} (hpre : WNF (ofSummands pre)) (hc : WNF c)
    (hP : WNF P) (hx : WNF x) : WNF (combine (.psi0 π) pre c P x) :=
  wnf_oadd hpre (wnf_nsum (wnf_oadd hc hx) hP)

theorem combine_psi0_lt {π : Tm} {pre : List Tm} {c P x y : Tm} (hpre : WNF (ofSummands pre)) (hc : WNF c)
    (hP : WNF P) (hx : WNF x) (hy : WNF y) (h : Lt x y) :
    Lt (combine (.psi0 π) pre c P x) (combine (.psi0 π) pre c P y) :=
  oadd_lt_oadd hpre (wnf_nsum (wnf_oadd hc hx) hP) (wnf_nsum (wnf_oadd hc hy) hP)
    (nsum_lt_left (wnf_oadd hc hx) (wnf_oadd hc hy) hP (oadd_lt_oadd hc hx hy h))

/-! ### 近似の崩壊の列が良いための条件 -/

/-- `R` の共終数が正則項でなければ、`app` の列は `g(pre ⊕ (c, P, R[n]))` -/
theorem app_nat_of_not_big {τ : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD} {P c : Tm}
    (hdom : ∀ σ, r.dom ≠ .big σ) (n : Nat) :
    (SeqD.app τ g pre R r P c).nat n = g.ap (combine g pre c P (r.nat n)) := by
  show (match r.dom with
    | .big σ => if ltB σ τ then zero else g.ap (argOf τ σ g pre R r c P (gam τ σ g pre R r c P n))
    | _ => g.ap (combine g pre c P (r.nat n))) = _
  split
  · rename_i σ h; exact absurd h (hdom σ)
  · rfl

/-- ψ への崩壊の近似の列 `Ψ^0_π(A_n)` が `t = Ψ^0_π(X)` について良いための条件 -/
theorem natGood_app_psi0 {π X ceil : Tm} {pre : List Tm} {R : Tm} {r : SeqD} {P c : Tm}
    (ht : WNF (.Psi .zero π X)) (hdom : ∀ σ, r.dom ≠ .big σ)
    (hA : ∀ n, WNF (combine (.psi0 π) pre c P (r.nat n)))
    (hC : ∀ n, inC (combine (.psi0 π) pre c P (r.nat n)) (combine (.psi0 π) pre c P (r.nat n)) π = true)
    (hr : ∀ n r', argR? π = some r' → Lt r' (combine (.psi0 π) pre c P (r.nat n)))
    (hlt : ∀ n, Lt (combine (.psi0 π) pre c P (r.nat n)) X)
    (hmono : ∀ n, Lt (combine (.psi0 π) pre c P (r.nat n)) (combine (.psi0 π) pre c P (r.nat (n + 1))))
    (hfrt : ∀ n w, w ∈ fr π (combine (.psi0 π) pre c P (r.nat n)) → Lt w (.Psi .zero π X))
    (hfrm : ∀ n w, w ∈ fr π (combine (.psi0 π) pre c P (r.nat n)) →
      Lt w (.Psi .zero π (combine (.psi0 π) pre c P (r.nat (n + 1))))) :
    NatGood (.Psi .zero π X) (.app ceil (.psi0 π) pre R r P c) := by
  have hP := ht.psi
  have hnf : ∀ n, WNF (.Psi .zero π (combine (.psi0 π) pre c P (r.nat n))) := fun n =>
    wnf_psi0 hP.piF hP.tgt (hA n) (hC n) (hr n)
  intro n
  rw [app_nat_of_not_big hdom n, app_nat_of_not_big hdom (n + 1)]
  exact ⟨hnf n, psi_lt_psi_of_arg (hnf n) ht (hlt n) (hfrt n),
    psi_lt_psi_of_arg (hnf n) (hnf (n + 1)) (hmono n) (hfrm n)⟩

/-- 一つずらした列も良い -/
theorem natGood_shift {t : Tm} {s : SeqD} (h : NatGood t s) : NatGood t (.shift s) := fun n => h (n + 1)

/-! ### 目標未満の加数は崩壊未満 -/

/-- `z < π` で `z ∈ C(B, π)`、`z` の前線（`π` について）の元が全て `Ψ^ξ_π(B)` 未満なら `z < Ψ^ξ_π(B)` -/
theorem lt_psi_of_below_tgt {ξ π B z : Tm} (hu : WNF (.Psi ξ π B)) (hz : WNF z) (hzπ : Lt z π)
    (hC : inC z B π = true) (hfr : ∀ w, w ∈ fr π z → Lt w (.Psi ξ π B)) : Lt z (.Psi ξ π B) := by
  have hP := hu.psi
  exact coll_psiY hu z hz
    (inC_of_fr_lt hz hP.piF hu hP.aF hP.aF hC (Or.inr (lt_psi_targetY hu)) (Or.inl rfl) hfr) hzπ

/-! ### 和・自然な和・近似の前線 -/

theorem fr_ofSummands (R : Tm) : ∀ l : List Tm, fr R (ofSummands l) = l.flatMap (fr R)
  | [] => rfl
  | [a] => by simp [ofSummands]
  | a :: b :: rest => by
    show fr R (.plus a (ofSummands (b :: rest))) = _
    rw [fr, fr_ofSummands R (b :: rest)]
    simp [List.flatMap_cons]

/-- 標準形の項の前線は、加数の前線を並べたもの -/
theorem mem_fr_iff {R x w : Tm} (hx : WNF x) : w ∈ fr R x ↔ ∃ s, s ∈ summands x ∧ w ∈ fr R s := by
  have e := ofSummands_summands x hx
  rw [show fr R x = fr R (ofSummands (summands x)) by rw [e], fr_ofSummands, List.mem_flatMap]

theorem summands_nsum {x y : Tm} (hx : WNF x) (hy : WNF y) :
    summands (nsum x y) = merge (summands x) (summands y) :=
  summands_ofSummands _ (nfl_principal (nfl_merge (nfl_summands hx) (nfl_summands hy)))

theorem mem_fr_nsum {R x y w : Tm} (hx : WNF x) (hy : WNF y) (h : w ∈ fr R (nsum x y)) :
    w ∈ fr R x ∨ w ∈ fr R y := by
  obtain ⟨s, hs, hw⟩ := (mem_fr_iff (wnf_nsum hx hy)).mp h
  rw [summands_nsum hx hy] at hs
  rcases mem_merge hs with hs | hs
  · exact Or.inl ((mem_fr_iff hx).mpr ⟨s, hs, hw⟩)
  · exact Or.inr ((mem_fr_iff hy).mpr ⟨s, hs, hw⟩)

theorem fr_nsum_of_left {R x y w : Tm} (hx : WNF x) (hy : WNF y) (h : w ∈ fr R x) : w ∈ fr R (nsum x y) := by
  obtain ⟨s, hs, hw⟩ := (mem_fr_iff hx).mp h
  refine (mem_fr_iff (wnf_nsum hx hy)).mpr ⟨s, ?_, hw⟩
  rw [summands_nsum hx hy]
  exact (merge_perm _ _).mem_iff.mpr (List.mem_append_left _ hs)

theorem fr_nsum_of_right {R x y w : Tm} (hx : WNF x) (hy : WNF y) (h : w ∈ fr R y) : w ∈ fr R (nsum x y) := by
  obtain ⟨s, hs, hw⟩ := (mem_fr_iff hy).mp h
  refine (mem_fr_iff (wnf_nsum hx hy)).mpr ⟨s, ?_, hw⟩
  rw [summands_nsum hx hy]
  exact (merge_perm _ _).mem_iff.mpr (List.mem_append_right _ hs)

theorem mem_fr_oadd {R x y w : Tm} (hx : WNF x) (hy : WNF y) (h : w ∈ fr R (oadd x y)) :
    w ∈ fr R x ∨ w ∈ fr R y := by
  cases hs : summands y with
  | nil => rw [eq_zero_of_summands_nil hs, oadd_zero] at h; exact Or.inl h
  | cons hd r =>
    obtain ⟨s, hsm, hw⟩ := (mem_fr_iff (wnf_oadd hx hy)).mp h
    rw [summands_oadd hs (nfl_principal (nfl_summands hx)) (nfl_principal (nfl_summands hy))] at hsm
    rcases List.mem_append.mp hsm with hsm | hsm
    · exact Or.inl ((mem_fr_iff hx).mpr ⟨s, (List.takeWhile_sublist _).subset hsm, hw⟩)
    · exact Or.inr ((mem_fr_iff hy).mpr ⟨s, hsm, hw⟩)

theorem fr_oadd_of_right {R x y w : Tm} (hx : WNF x) (hy : WNF y) (h : w ∈ fr R y) : w ∈ fr R (oadd x y) := by
  cases hs : summands y with
  | nil => rw [eq_zero_of_summands_nil hs] at h; simp [fr] at h
  | cons hd r =>
    obtain ⟨s, hsm, hw⟩ := (mem_fr_iff hy).mp h
    refine (mem_fr_iff (wnf_oadd hx hy)).mpr ⟨s, ?_, hw⟩
    rw [summands_oadd hs (nfl_principal (nfl_summands hx)) (nfl_principal (nfl_summands hy))]
    exact List.mem_append_right _ hsm

theorem takeWhile_of_all {α : Type} {p : α → Bool} : ∀ {l : List α}, (∀ a, a ∈ l → p a = true) → l.takeWhile p = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.takeWhile_cons_of_pos (h a List.mem_cons_self),
      takeWhile_of_all (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- 左の加数が全て残る（右の先頭以上）なら、左の前線は和の前線に含まれる -/
theorem fr_oadd_of_left {R x y w : Tm} (hx : WNF x) (hy : WNF y)
    (hkeep : ∀ s hd r, s ∈ summands x → summands y = hd :: r → leB hd s = true)
    (h : w ∈ fr R x) : w ∈ fr R (oadd x y) := by
  cases hs : summands y with
  | nil => rw [eq_zero_of_summands_nil hs, oadd_zero]; exact h
  | cons hd r =>
    obtain ⟨s, hsm, hw⟩ := (mem_fr_iff hx).mp h
    refine (mem_fr_iff (wnf_oadd hx hy)).mpr ⟨s, ?_, hw⟩
    rw [summands_oadd hs (nfl_principal (nfl_summands hx)) (nfl_principal (nfl_summands hy))]
    apply List.mem_append_left
    rw [takeWhile_of_all (fun s' hs' => hkeep s' hd r hs' hs)]
    exact hsm

/-- ψ への崩壊の近似の前線は、前の部分・調整・`R` の値・種の前線のどれか -/
theorem mem_fr_combine_psi0 {R π : Tm} {pre : List Tm} {c P x w : Tm} (hpre : WNF (ofSummands pre))
    (hc : WNF c) (hP : WNF P) (hx : WNF x) (h : w ∈ fr R (combine (.psi0 π) pre c P x)) :
    w ∈ fr R (ofSummands pre) ∨ w ∈ fr R c ∨ w ∈ fr R x ∨ w ∈ fr R P := by
  rcases mem_fr_oadd hpre (wnf_nsum (wnf_oadd hc hx) hP) h with h | h
  · exact Or.inl h
  · rcases mem_fr_nsum (wnf_oadd hc hx) hP h with h | h
    · rcases mem_fr_oadd hc hx h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

theorem fr_combine_psi0_of_x {R π : Tm} {pre : List Tm} {c P x w : Tm} (hpre : WNF (ofSummands pre))
    (hc : WNF c) (hP : WNF P) (hx : WNF x) (h : w ∈ fr R x) : w ∈ fr R (combine (.psi0 π) pre c P x) :=
  fr_oadd_of_right hpre (wnf_nsum (wnf_oadd hc hx) hP)
    (fr_nsum_of_left (wnf_oadd hc hx) hP (fr_oadd_of_right hc hx h))

theorem fr_combine_psi0_of_P {R π : Tm} {pre : List Tm} {c P x w : Tm} (hpre : WNF (ofSummands pre))
    (hc : WNF c) (hP : WNF P) (hx : WNF x) (h : w ∈ fr R P) : w ∈ fr R (combine (.psi0 π) pre c P x) :=
  fr_oadd_of_right hpre (wnf_nsum (wnf_oadd hc hx) hP) (fr_nsum_of_right (wnf_oadd hc hx) hP h)

end RTKA.Fund
