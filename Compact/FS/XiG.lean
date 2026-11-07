import Compact.FS.Lim

/-! `Ξ_m(pre ⊕ (c # (P # x)))` の族の仮定 `XiG` と、その基本的な性質。 -/

namespace RTKA.Fund

open Tm W

theorem inC_oadd_parts {pre rest : List Tm} {R y g d : Tm} (hN : NFL (pre ++ R :: rest)) (hy : WNF y)
    (hyR : Lt y R) (h : inC (oadd (ofSummands pre) y) g d = true) :
    inC (ofSummands pre) g d = true ∧ inC y g d = true := by
  have hA : WNF (oadd (ofSummands pre) y) := wnf_oadd (wnf_ofSummands (nfl_append_left hN)) hy
  have hmem : ∀ s, s ∈ pre ++ summands y → inC s g d = true := by
    intro s hs
    refine inC_of_mem_summands hA h ?_
    rw [summands_oadd_pre (nfl_append_left hN) hy (head_le_pre hN hy hyR)]
    exact hs
  refine ⟨?_, (inC_iff_summands hy).mpr fun s hs => hmem s (List.mem_append_right _ hs)⟩
  rw [inC_ofSummands]
  exact fun s hs => hmem s (List.mem_append_left _ hs)

/-- `Ξ` の引数 -/
def xA (c : Tm) (pre : List Tm) (P x : Tm) : Tm := oadd (ofSummands pre) (nsum c (nsum P x))

theorem combine_xi (m : Nat) (c : Tm) (pre : List Tm) (P x : Tm) :
    combine (.xi m) pre c P x = xA c pre P x := rfl

/-- `Ξ_m(pre ⊕ (c # (P # x)))` の族の仮定 -/
structure XiG (m : Nat) (q P c : Tm) (pre rest : List Tm) (R : Tm) : Prop where
  ht : WNF (.Xi m q)
  hsum : summands q = pre ++ R :: rest
  hPF : WNF P
  hPR : Lt P R
  hPK : Lt P (.K m)
  hc : c = .zero ∨ c = .one
  hR1 : R ≠ .one

namespace XiG

variable {m : Nat} {q P c : Tm} {pre rest : List Tm} {R : Tm}

theorem hm (G : XiG m q P c pre rest R) : 1 ≤ m := G.ht.xi.1
theorem hqF (G : XiG m q P c pre rest R) : WNF q := G.ht.xi.2.1
theorem hqC (G : XiG m q P c pre rest R) : inC q q (.K m) = true := G.ht.xi.2.2.2.2
theorem hKF (G : XiG m q P c pre rest R) : WNF (.K m) := WNF.K' G.hm
theorem hN (G : XiG m q P c pre rest R) : NFL (pre ++ R :: rest) := G.hsum ▸ nfl_summands G.hqF
theorem hRF (G : XiG m q P c pre rest R) : WNF R :=
  (G.hN.1 R (List.mem_append_right _ List.mem_cons_self)).1
theorem hRp (G : XiG m q P c pre rest R) : isPrincipal R = true :=
  (G.hN.1 R (List.mem_append_right _ List.mem_cons_self)).2
theorem hpreF (G : XiG m q P c pre rest R) : WNF (ofSummands pre) :=
  wnf_ofSummands (nfl_append_left G.hN)
theorem hRm (G : XiG m q P c pre rest R) : R ∈ summands q := by
  rw [G.hsum]
  exact List.mem_append_right _ List.mem_cons_self
theorem hTF (G : XiG m q P c pre rest R) : WNF (oadd (ofSummands pre) R) := wnf_oadd G.hpreF G.hRF
theorem hTq (G : XiG m q P c pre rest R) : Le (oadd (ofSummands pre) R) q := top_le G.hqF G.hsum
theorem hcF (G : XiG m q P c pre rest R) : WNF c := by
  rcases G.hc with rfl | rfl
  · exact WNF.zero
  · exact WNF.one
theorem hcC (G : XiG m q P c pre rest R) (g d : Tm) : inC c g d = true := by
  rcases G.hc with rfl | rfl
  · exact inC_zero _ _
  · exact inC_one _ _
theorem hR0 (G : XiG m q P c pre rest R) : R ≠ .zero := by
  intro e
  have := G.hRp
  rw [e] at this
  cases this
theorem hcR (G : XiG m q P c pre rest R) : Lt c R := by
  rcases G.hc with rfl | rfl
  · exact zero_lt G.hR0
  · rcases triY WNF.one G.hRF with h | h | h
    · exact h
    · exact absurd h.symm G.hR1
    · exact absurd (lt_oneY G.hRF h) G.hR0
theorem hρK (G : XiG m q P c pre rest R) : Lt (.Xi m q) (.K m) :=
  (lt_K_iffY G.ht G.hm).mpr (Nat.le_refl _)

theorem hyF (G : XiG m q P c pre rest R) {x : Tm} (hx : WNF x) : WNF (nsum P x) := wnf_nsum G.hPF hx
theorem hEF (G : XiG m q P c pre rest R) {x : Tm} (hx : WNF x) : WNF (nsum c (nsum P x)) :=
  wnf_nsum G.hcF (G.hyF hx)
theorem hER (G : XiG m q P c pre rest R) {x : Tm} (hx : WNF x) (hxR : Lt x R) :
    Lt (nsum c (nsum P x)) R :=
  nsum_lt_prin G.hcF (G.hyF hx) G.hRp G.hcR (nsum_lt_prin G.hPF hx G.hRp G.hPR hxR)
theorem hAF (G : XiG m q P c pre rest R) {x : Tm} (hx : WNF x) : WNF (xA c pre P x) :=
  wnf_oadd G.hpreF (G.hEF hx)
theorem hAT (G : XiG m q P c pre rest R) {x : Tm} (hx : WNF x) (hxR : Lt x R) :
    Lt (xA c pre P x) (oadd (ofSummands pre) R) :=
  oadd_lt_oadd G.hpreF (G.hEF hx) G.hRF (G.hER hx hxR)
theorem hAlt (G : XiG m q P c pre rest R) {x U : Tm} (hx : WNF x) (hxR : Lt x R) (hU : WNF U)
    (hTU : Le (oadd (ofSummands pre) R) U) : Lt (xA c pre P x) U :=
  lt_of_lt_of_leY (G.hAF hx) G.hTF hU (G.hAT hx hxR) hTU

theorem inC_A (G : XiG m q P c pre rest R) {x g d : Tm} (hx : WNF x)
    (hpre : inC (ofSummands pre) g d = true) (hxC : inC x g d = true) (hP : inC P g d = true) :
    inC (xA c pre P x) g d = true :=
  inC_oadd G.hpreF (G.hEF hx) hpre (inC_nsum G.hcF (G.hyF hx) (G.hcC g d) (inC_nsum G.hPF hx hP hxC))

theorem parts (G : XiG m q P c pre rest R) {x g d : Tm} (hx : WNF x) (hxR : Lt x R)
    (h : inC (xA c pre P x) g d = true) :
    inC (ofSummands pre) g d = true ∧ inC x g d = true ∧ inC P g d = true := by
  obtain ⟨h1, h2⟩ := inC_oadd_parts G.hN (G.hEF hx) (G.hER hx hxR) h
  have h3 := inC_nsum_right G.hcF (G.hyF hx) h2
  exact ⟨h1, inC_nsum_right G.hPF hx h3, inC_nsum_left G.hPF hx h3⟩

theorem qparts (G : XiG m q P c pre rest R) {g d : Tm} (h : inC q g d = true) :
    inC R g d = true ∧ inC (ofSummands pre) g d = true :=
  ⟨inC_of_mem_summands G.hqF h G.hRm, inC_pre_of_X G.hqF G.hsum h⟩

/-- `x` は `Ξ` の引数以下 -/
theorem hxA (G : XiG m q P c pre rest R) {x : Tm} (hx : WNF x) : Le x (xA c pre P x) :=
  le_transY hx (G.hyF hx) (G.hAF hx) (le_nsum_right G.hPF hx)
    (le_transY (G.hyF hx) (G.hEF hx) (G.hAF hx) (le_nsum_right G.hcF (G.hyF hx))
      (le_oadd_right G.hpreF (G.hEF hx)))

theorem hA_ne (G : XiG m q P c pre rest R) (hc0 : c = .zero → P ≠ .zero) {x : Tm} (hx : WNF x) :
    xA c pre P x ≠ .zero := by
  intro e
  have h1 : Le (nsum c (nsum P x)) (xA c pre P x) := le_oadd_right G.hpreF (G.hEF hx)
  rw [e] at h1
  have h2 : nsum c (nsum P x) = .zero := by
    rcases h1 with h | h
    · exact h
    · exact absurd h (not_lt_zero _)
  rcases G.hc with rfl | rfl
  · rw [zero_nsum _ (G.hyF hx)] at h2
    have h3 := le_nsum_left G.hPF hx
    rw [h2] at h3
    rcases h3 with h | h
    · exact hc0 rfl h
    · exact not_lt_zero _ h
  · have h3 := le_nsum_left WNF.one (G.hyF hx)
    rw [h2] at h3
    rcases h3 with h | h
    · cases h
    · exact not_lt_zero _ h

theorem hqe (G : XiG m q P c pre rest R) : q = ofSummands (pre ++ R :: rest) := by
  rw [← G.hsum, ofSummands_summands q G.hqF]

/-- 引数の比較 -/
theorem hA0le (G : XiG m q P c pre rest R) {x : Tm} (hx : WNF x) :
    Le (approx pre P x) (xA c pre P x) := by
  have h0 : approx pre P x = oadd (ofSummands pre) (nsum P x) := by
    unfold approx
    rw [nsum_comm hx G.hPF]
  rw [h0]
  rcases le_nsum_right G.hcF (G.hyF hx) with h | h
  · exact Or.inl (congrArg (oadd (ofSummands pre)) h)
  · exact Or.inr (oadd_lt_oadd G.hpreF (G.hyF hx) (G.hEF hx) h)

theorem hAmono (G : XiG m q P c pre rest R) {x x' : Tm} (hx : WNF x) (hx' : WNF x') (h : Lt x x') :
    Lt (xA c pre P x) (xA c pre P x') :=
  oadd_lt_oadd G.hpreF (G.hEF hx) (G.hEF hx')
    (nsum_lt_right G.hcF (G.hyF hx) (G.hyF hx') (nsum_lt_right G.hPF hx hx' h))

/-- `pre` と `R` の真の部分項は、`q` 未満なら `Ξ` の引数未満 -/
theorem lt_xA (G : XiG m q P c pre rest R) {x S u : Tm} (hx : WNF x) (hxR : Lt x R)
    (hx0 : x = .zero → ∀ v, v ∈ subs R → v = R) (hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v x)
    (hS : S ∈ pre ++ [R]) (hu : u ∈ subs S) (hne : u ≠ S) (hl : Lt u q) : Lt u (xA c pre P x) := by
  have hS' : S ∈ pre ++ R :: rest := by
    rcases List.mem_append.mp hS with h | h
    · exact List.mem_append_left _ h
    · rw [List.mem_singleton.mp h]
      exact List.mem_append_right _ List.mem_cons_self
  have huF := (G.hN.1 S hS').1.of_mem_subs hu
  have h1 : Lt u (approx pre P x) :=
    lt_approx_summand G.hN hx G.hPF (nsum_lt_prin hx G.hPF G.hRp hxR G.hPR) hx0 hgap hS hu hne
      (by rw [← G.hqe]; exact hl)
  exact lt_of_lt_of_leY huF (wnf_oadd G.hpreF (wnf_nsum hx G.hPF)) (G.hAF hx) h1 (G.hA0le hx)

/-- `x ∈ C(A, K_m)` -/
theorem hCx (G : XiG m q P c pre rest R) {x : Tm} (hx : WNF x) (hxR : Lt x R)
    (hx0 : x = .zero → ∀ v, v ∈ subs R → v = R)
    (hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v x)
    (hub : inC R (approx pre P x) (.K m) = true → inC (ofSummands pre) (approx pre P x) (.K m) = true →
      inC x (approx pre P x) (.K m) = true) :
    inC x (xA c pre P x) (.K m) = true := by
  obtain ⟨h1, h2⟩ := inC_R_A G.hqF G.hKF G.hqC G.hsum hx hx0 hxR G.hPF G.hPR hgap
  exact inC_of_fr_lt hx G.hKF G.hKF (wnf_oadd G.hpreF (wnf_nsum hx G.hPF)) (G.hAF hx) (hub h1 h2)
    (Or.inl rfl) (G.hA0le hx) fun w hw => (fr_spec hw).2

/-- 標準形 -/
theorem nf (G : XiG m q P c pre rest R) {x : Tm} (hne : xA c pre P x ≠ .zero) (hx : WNF x) (hxR : Lt x R)
    (hC : inC x (xA c pre P x) (.K m) = true) : WNF (.Xi m (xA c pre P x)) := by
  have hAq : Lt (xA c pre P x) q := G.hAlt hx hxR G.hqF G.hTq
  have hle : Le (xA c pre P x) (succK m) :=
    le_transY (G.hAF hx) G.hqF (WNF.succK G.hm) (Or.inr hAq) (le_of_ne_gtY G.hqF (WNF.succK G.hm) G.ht.xi.2.2.2.1)
  have hXe : q = ofSummands (pre ++ R :: rest) := by rw [← G.hsum, ofSummands_summands q G.hqF]
  have hpre : inC (ofSummands pre) (xA c pre P x) (.K m) = true :=
    inC_pre G.hN (G.hEF hx) (G.hER hx hxR) G.hKF (by rw [← hXe]; exact G.hqC)
  exact wnf_xi_mk G.hm (G.hAF hx) hne (ne_gt_of_le hle)
    (G.inC_A hx hpre hC (WFY.inC_of_ltY _ G.hPF G.hKF G.hPK))

theorem hqρ (G : XiG m q P c pre rest R) : inC q q (.Xi m q) = true :=
  inC_of_fr_lt G.hqF G.hKF G.ht G.hqF G.hqF G.hqC (Or.inr G.hρK) (Or.inl rfl)
    fun w hw => FWOrder.k2x G.ht w hw

/-- 崩壊の性質 -/
theorem ltρ (G : XiG m q P c pre rest R) {x : Tm} (hx : WNF x) (hxR : Lt x R)
    (hxC : inC x q (.Xi m q) = true) (hPC : inC P q (.Xi m q) = true) :
    Lt (.Xi m (xA c pre P x)) (.Xi m q) := by
  have hAq : Lt (xA c pre P x) q := G.hAlt hx hxR G.hqF G.hTq
  exact (lt_xi_xi0 hAq.ne).mpr (Or.inl ⟨hAq, G.inC_A hx (G.qparts G.hqρ).2 hxC hPC⟩)

/-- 2 点の比較 -/
theorem lt2 (G : XiG m q P c pre rest R) {x x' : Tm} (hx : WNF x) (hx' : WNF x') (hxR' : Lt x' R)
    (hxx : Lt x x') (hy' : WNF (.Xi m (xA c pre P x')))
    (hS : inC x' (xA c pre P x') (.Xi m (xA c pre P x')) = true →
      inC (ofSummands pre) (xA c pre P x') (.Xi m (xA c pre P x')) = true →
      inC P (xA c pre P x') (.Xi m (xA c pre P x')) = true →
      inC x (xA c pre P x') (.Xi m (xA c pre P x')) = true) :
    Lt (.Xi m (xA c pre P x)) (.Xi m (xA c pre P x')) := by
  have hAA := G.hAmono hx hx' hxx
  have hAF' := G.hAF hx'
  have hK' : Lt (.Xi m (xA c pre P x')) (.K m) := (lt_K_iffY hy' G.hm).mpr (Nat.le_refl _)
  have hC' : inC (xA c pre P x') (xA c pre P x') (.Xi m (xA c pre P x')) = true :=
    inC_of_fr_lt hAF' G.hKF hy' hAF' hAF' hy'.xi.2.2.2.2 (Or.inr hK') (Or.inl rfl)
      fun w hw => FWOrder.k2x hy' w hw
  obtain ⟨h1, h2, h3⟩ := G.parts hx' hxR' hC'
  exact (lt_xi_xi0 hAA.ne).mpr (Or.inl ⟨hAA, G.inC_A hx h1 (hS h2 h1 h3) h3⟩)

/-- 2 点の上界 -/
theorem ub2 (G : XiG m q P c pre rest R) {x x' g d : Tm} (hx : WNF x) (hx' : WNF x') (hxR' : Lt x' R)
    (hxx : Lt x x') (hy : WNF (.Xi m (xA c pre P x))) (hy' : WNF (.Xi m (xA c pre P x')))
    (hmono : Lt (.Xi m (xA c pre P x)) (.Xi m (xA c pre P x'))) (hd : WNF d)
    (hg : WNF g) (hS : inC x' g d = true → inC (ofSummands pre) g d = true → inC P g d = true →
      Lt (approx pre P x) g → inC x g d = true)
    (h : inC (.Xi m (xA c pre P x')) g d = true) :
    inC (.Xi m (xA c pre P x)) g d = true := by
  by_cases hdy : Lt (.Xi m (xA c pre P x')) d
  · exact WFY.inC_of_ltY _ hy hd (lt_transY hy hy' hd hmono hdy)
  rcases inC_xi_iff.mp h with h' | ⟨hδ, hlt⟩
  · exact absurd h' hdy
  · obtain ⟨h1, h2, h3⟩ := G.parts hx' hxR' hδ
    have hAg : Lt (xA c pre P x) g := lt_transY (G.hAF hx) (G.hAF hx') hg (G.hAmono hx hx' hxx) hlt
    have hA0g : Lt (approx pre P x) g :=
      lt_of_le_of_ltY (wnf_oadd G.hpreF (wnf_nsum hx G.hPF)) (G.hAF hx) hg (G.hA0le hx) hAg
    exact inC_xi_iff.mpr (Or.inr ⟨G.inC_A hx h1 (hS h2 h1 h3 hA0g) h3, hAg⟩)

/-- 種は `Ξ` の未満 -/
theorem seed_lt (G : XiG m q P c pre rest R) {x : Tm} (hx : WNF x) (hy : WNF (.Xi m (xA c pre P x)))
    (hp : P ∈ fr (.K m) P) : Lt P (.Xi m (xA c pre P x)) :=
  FWOrder.k2x hy P (fr_oadd_of_right G.hpreF (G.hEF hx) (fr_nsum_of_right G.hcF (G.hyF hx)
    (fr_nsum_of_left G.hPF hx hp)))

end XiG

end RTKA.Fund
