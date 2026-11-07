import Compact.FS.Diag

/-! 近似 `pre ⊕ ((c + x_n) # P)` の内側の族 `x`（`Inner`）。

`x_n = R[n]`（`R` の共終数が `ω`）・`x_n = R[γ_n]`（`R` の共終数が目標以上の正則項で、`γ` は塔）を同じ形で扱う。
`fam_inner` が `Inner` から近似の族 `AFam` を作る。 -/

namespace RTKA.Fund

open Tm W

/-- `R`・`pre` は近似の引数の `C` に入る -/
theorem inC_R_A {κ X P : Tm} {pre rest : List Tm} {R x : Tm} (hX : WNF X) (hκ : WNF κ)
    (hXC : inC X X κ = true) (hsum : summands X = pre ++ R :: rest) (hx : WNF x)
    (hx0 : x = .zero → ∀ v, v ∈ subs R → v = R) (hxR : Lt x R) (hPF : WNF P) (hPR : Lt P R)
    (hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v x) :
    inC R (approx pre P x) κ = true ∧ inC (ofSummands pre) (approx pre P x) κ = true := by
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
  have hXe : X = ofSummands (pre ++ R :: rest) := by rw [← hsum, ofSummands_summands X hX]
  exact ⟨inC_mono_proper hκ hRN.1 (inC_of_mem_summands hX hXC hRm) fun v hv hne hvX =>
      lt_approx_of_gap hN hy (hy0 fun e => hne (hx0 e v hv)) hyR hx (le_nsum_left hx hPF) hgap hv hne
        (hRN.1.of_mem_subs hv) (by rw [← hXe]; exact hvX),
    inC_pre hN hy hyR hκ (by rw [← hXe]; exact hXC)⟩

/-- `pre` と `R` の真の部分項は、`X` 未満なら近似未満 -/
theorem lt_approx_summand {pre rest : List Tm} {R x P S u : Tm} (hN : NFL (pre ++ R :: rest)) (hx : WNF x)
    (hP : WNF P) (hyR : Lt (nsum x P) R) (hx0 : x = .zero → ∀ v, v ∈ subs R → v = R)
    (hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v x) (hS : S ∈ pre ++ [R]) (hu : u ∈ subs S) (hne : u ≠ S)
    (hlt : Lt u (ofSummands (pre ++ R :: rest))) : Lt u (approx pre P x) := by
  have hy := wnf_nsum hx hP
  rcases List.mem_append.mp hS with hs | hs
  · have hsF := (hN.1 S (List.mem_append_left _ hs)).1
    exact lt_pre_of_subs hN hy hyR hs hu hne (hsF.of_mem_subs hu) hlt
  · have e := List.mem_singleton.mp hs
    subst e
    have hRF := (hN.1 S (List.mem_append_right _ List.mem_cons_self)).1
    refine lt_approx_of_gap hN hy (fun e0 => ?_) hyR hx (le_nsum_left hx hP) hgap hu hne
      (hRF.of_mem_subs hu) hlt
    have h := le_nsum_left hx hP
    rw [e0] at h
    rcases h with h | h
    · exact hne (hx0 h u hu)
    · exact not_lt_zero _ h

/-- 近似の内側の族。上界は、`g` が上端 `pre ⊕ R` 以上か、その段の近似の引数のとき -/
structure Inner (P c : Tm) (pre : List Tm) (R : Tm) (x : Nat → Tm) : Prop where
  hx : ∀ n, WNF (x n)
  hxR : ∀ n, Lt (x n) R
  mono : ∀ n, Lt (x n) (x (n + 1))
  zero : ∀ n, x n = .zero → ∀ v, v ∈ subs R → v = R
  gap : ∀ n v, v ∈ subs R → v ≠ R → Lt v R → Lt v (x n)
  ub : ∀ g d n, WNF g → WNF d → inC R g d = true →
    inC (ofSummands pre) g d = true → inC c g d = true → inC P g d = true →
    (Le (oadd (ofSummands pre) R) g ∨ g = approx pre P (oadd c (x n))) → inC (x n) g d = true
  ub2 : ∀ g d n, WNF g → WNF d → inC (x (n + 1)) g d = true →
    inC (ofSummands pre) g d = true → inC c g d = true → inC P g d = true →
    Lt (approx pre P (oadd c (x n))) g → inC (x n) g d = true

/-- `ω` 型の加数 -/
theorem inner_nat {P c : Tm} {pre : List Tm} {R : Tm} {r : SeqD} (hR : NatInv R r) :
    Inner P c pre R r.nat where
  hx n := (hR.1.good n).1
  hxR n := (hR.1.good n).2.1
  mono n := (hR.1.good n).2.2
  zero n e := absurd e (hR.1.pos n)
  gap := hR.2
  ub g d n hg hd hRC _ _ _ _ := hR.1.ub g d n hg hd hRC
  ub2 g d n hg hd h _ _ _ _ := hR.1.ub2 g d n hg hd h

/-- 一つずらした族 -/
theorem Inner.shift {P c : Tm} {pre : List Tm} {R : Tm} {x : Nat → Tm} (I : Inner P c pre R x) :
    Inner P c pre R (fun n => x (n + 1)) where
  hx n := I.hx (n + 1)
  hxR n := I.hxR (n + 1)
  mono n := I.mono (n + 1)
  zero n := I.zero (n + 1)
  gap n := I.gap (n + 1)
  ub g d n := I.ub g d (n + 1)
  ub2 g d n := I.ub2 g d (n + 1)

/-- 内側の族から近似の族へ -/
theorem fam_inner {ξ π X P c : Tm} {pre rest : List Tm} {R : Tm} {x : Nat → Tm}
    (I : Inner P c pre R x) (htπ : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (S : SeedHyp π X P R) (adj : AdjHyp π R c)
    (hV : ∀ q, argR? π = some q → Lt q (approx pre P (oadd c (x 0))))
    (hI : IdxHyp ξ π X) (hξ : Le ξ (ofSummands pre)) :
    AFam ξ π X P pre rest R (fun n => oadd c (x n)) := by
  have hπF := htπ.psi.piF
  have hX := htπ.psi.aF
  have hXC := htπ.psi.Ca
  have hN : NFL (pre ++ R :: rest) := hsum ▸ nfl_summands hX
  have hRN := hN.1 R (List.mem_append_right _ List.mem_cons_self)
  have hpreF := wnf_ofSummands (nfl_append_left hN)
  have hRm : R ∈ summands X := by
    rw [hsum]
    exact List.mem_append_right _ List.mem_cons_self
  have hXe : X = ofSummands (pre ++ R :: rest) := by rw [← hsum, ofSummands_summands X hX]
  have hxF := I.hx
  have hyF : ∀ n, WNF (oadd c (x n)) := fun n => wnf_oadd adj.hF (hxF n)
  have hmono : ∀ n, Lt (oadd c (x n)) (oadd c (x (n + 1))) :=
    fun n => oadd_lt_oadd adj.hF (hxF n) (hxF (n + 1)) (I.mono n)
  have hle0 : ∀ n, Le (oadd c (x 0)) (oadd c (x n)) := by
    intro n
    induction n with
    | zero => exact Or.inl rfl
    | succ k ih => exact Or.inr (lt_of_le_of_ltY (hyF 0) (hyF k) (hyF (k + 1)) ih (hmono k))
  have hxz : ∀ n, oadd c (x n) = .zero → ∀ v, v ∈ subs R → v = R := fun n e => by
    have h1 := le_oadd_right adj.hF (hxF n)
    rw [e] at h1
    rcases h1 with h1 | h1
    · exact I.zero n h1
    · exact absurd h1 (not_lt_zero _)
  have hgap : ∀ n v, v ∈ subs R → v ≠ R → Lt v R → Lt v (oadd c (x n)) :=
    fun n v hv hne hlt => lt_of_lt_of_leY (hRN.1.of_mem_subs hv) (hxF n) (hyF n)
      (I.gap n v hv hne hlt) (le_oadd_right adj.hF (hxF n))
  refine ⟨fun n => ?_, hmono, fun g d n hg hd hle' hRC hpre hgT hk hP => ?_,
    fun g d n hg hd hle' h hk hpre hP hlt => ?_⟩
  · have hy := wnf_nsum (hyF n) S.hPF
    have hxR : Lt (oadd c (x n)) R := oadd_lt_prin adj.hF (hxF n) hRN.2 adj.hR (I.hxR n)
    have hyR : Lt (nsum (oadd c (x n)) P) R := nsum_lt_prin (hyF n) S.hPF hRN.2 hxR S.hPR
    have hA : WNF (approx pre P (oadd c (x n))) := wnf_oadd hpreF hy
    have hr : ∀ q, argR? π = some q → Lt q (approx pre P (oadd c (x n))) := fun q hq => by
      rcases hle0 n with e | h2
      · rw [← e]
        exact hV q hq
      · exact lt_transY (wnf_of_argR hπF hq) (wnf_oadd hpreF (wnf_nsum (hyF 0) S.hPF)) hA
          (hV q hq) (approx_mono hpreF (hyF 0) (hyF n) S.hPF h2)
    have hPπC : ∀ {g : Tm}, inC P g π = true := WFY.inC_of_ltY _ S.hPF hπF S.hPπ
    exact
      { ht := htπ, hsum := hsum, hx := hyF n, hxR, hPF := S.hPF, hPR := S.hPR, hPπ := S.hPπ
        hr := hr, hI := hI
        hξA := le_transY hI.hF hpreF hA hξ (le_oadd_left hpreF hy)
        hCx := inC_approx_of_ub htπ hsum (hyF n) (hxz n) hxR S.hPF S.hPR hr
          (fun hRA hπA => by
            have hpreA : inC (ofSummands pre) (approx pre P (oadd c (x n))) π = true :=
              inC_pre hN hy hyR hπF (by rw [← hXe]; exact hXC)
            have hcA := adj.hU _ π hπF (Or.inl rfl) hπA
            exact inC_oadd adj.hF (hxF n) hcA
              (I.ub _ π n hA hπF hRA hpreA hcA hPπC (Or.inr rfl)))
          (hgap n) }
  · have hcC := adj.hU g d hd hle' hk
    exact inC_oadd adj.hF (hxF n) hcC (I.ub g d n hg hd hRC hpre hcC hP (Or.inl hgT))
  · have hcC := adj.hU g d hd hle' hk
    exact inC_oadd adj.hF (hxF n) hcC
      (I.ub2 g d n hg hd (inC_of_oadd_right adj.hF (hxF (n + 1)) h) hpre hcC hP hlt)

/-- 塔の前の段の近似は、後の段の近似を越えない -/
theorem DiagHyp.approx_lt {ξ σ X G : Tm} {pre rest : List Tm} {R : Tm} {r : SeqD} {P c : Tm}
    (H : DiagHyp ξ σ X G .zero pre rest R r) (hc : WNF c) (hP : WNF P) {j n : Nat} (hj : j < n) :
    Lt (approx pre .zero (xT ξ σ pre r G .zero j)) (approx pre P (oadd c (xT ξ σ pre r G .zero n))) := by
  have Hj := (H.tower j).2.2
  have hxn := (H.tower n).2.2.hx
  have hy := wnf_oadd hc hxn
  have hyn := wnf_nsum hy hP
  refine oadd_lt_oadd H.hpreF Hj.hy hyn (lt_of_lt_of_leY Hj.hy hy hyn ?_ (le_nsum_left hy hP))
  rw [nsum_zero _ Hj.hx]
  exact lt_of_lt_of_leY Hj.hx hxn hy (H.xT_lt hj) (le_oadd_right hc hxn)

/-- 種を外に足す型の塔 `x_n = R[γ_n]` -/
theorem DiagHyp.inner_out {σ X G : Tm} {pre rest : List Tm} {R : Tm} {r : SeqD} {P c : Tm}
    (H : DiagHyp .zero σ X G .zero pre rest R r) (hc : WNF c) (hP : WNF P) (hPs : ¬ isSucc P = true)
    (hGC : ∀ g d, WNF d → inC c g d = true → inC P g d = true → inC G g d = true) :
    Inner P c pre R (xT .zero σ pre r G .zero) where
  hx n := (H.tower n).2.2.hx
  hxR n := (H.tower n).2.2.hxR
  mono := H.xT_mono
  zero := H.x_zero
  gap := H.x_gap
  ub g d n hg hd hRC hpre hcC hPC hgc := by
    have hGd := hGC g d hd hcC hPC
    rcases hgc with hT | rfl
    · exact (H.xT_inC_T hg hd hRC hpre hT hGd (inC_zero _ _) (inC_zero _ _) n).2
    · by_cases hx0 : xT .zero σ pre r G .zero n = .zero
      · rw [hx0]
        exact inC_zero _ _
      · have hxF := (H.tower n).2.2.hx
        have hy := wnf_oadd hc hxF
        have hy0 : oadd c (xT .zero σ pre r G .zero n) ≠ .zero := fun e => by
          have h1 := le_oadd_right hc hxF
          rw [e] at h1
          rcases h1 with h1 | h1
          · exact hx0 h1
          · exact not_lt_zero _ h1
        exact (H.gamT_inC hg hd (approx_pos H.hpreF hy hP hy0) (H.ok_approx (π := d) hc hP hPs n) hRC
          (H.hRU.hσC _ _ hg hd hRC) (inC_zero _ _) hpre hGd (inC_zero _ _) n
          (fun j hj => H.approx_lt hc hP hj) n (Nat.le_refl n)).2
  ub2 g d n hg hd h _ _ _ _ := H.out_step hg hd n h

end RTKA.Fund
