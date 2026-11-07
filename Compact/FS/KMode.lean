import Compact.FS.OmCases

/-! `K_m` の対角化（ψ・Mahlo 型の生成）。

`t = Ψ^0_π(X)`、最後に近い加数 `R` の共終数が `K_m`（`π < K_m`）のとき、`t[n] = Ψ^ξ_π(pre ⊕ ((c + R[γ_n]) # P))`。

* 正準な塔（`pre ⊕ R < K_m⁺`）：`γ_0 = G`（`c` の中の Ξ_m で閉じた節点）、`γ_{k+1} = Ξ_m(pre ⊕ R[γ_k])`。
* 旧方式（`pre ⊕ R ≥ K_m⁺`）：`γ_0 = 0`、`γ_{k+1}` は `Ξ_m(K_m⁺)`（近似の引数がちょうど `K_m⁺` のとき）か `virtK m k`。

どちらも `Inner` を作って `appPack_of_inner` に渡す。 -/

namespace RTKA.Fund

open Tm W

theorem wnf_xi_mk {n : Nat} {a : Tm} (h1 : 1 ≤ n) (ha : WNF a) (h0 : a ≠ .zero)
    (hle : cmp a (succK n) ≠ .gt) (hC : inC a a (.K n) = true) : WNF (.Xi n a) := by
  show isNF (.Xi n a) = true
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
  exact ⟨⟨⟨⟨h1, ha⟩, h0⟩, hle⟩, hC⟩

theorem col_K_zero {m k : Nat} : col (.K m) .zero k = .Xi m .one := rfl

theorem col_K_le {m k : Nat} {δ : Tm} (h0 : δ ≠ .zero) (hle : leB δ (succK m) = true) :
    col (.K m) δ k = .Xi m δ := by
  show (if δ = zero then Xi m one else if leB δ (succK m) then Xi m δ else virtK m k) = _
  rw [ite_eq_right h0, ite_eq_left hle]

theorem col_K_gt {m k : Nat} {δ : Tm} (h0 : δ ≠ .zero) (hle : ¬ leB δ (succK m) = true) :
    col (.K m) δ k = virtK m k := by
  show (if δ = zero then Xi m one else if leB δ (succK m) then Xi m δ else virtK m k) = _
  rw [ite_eq_right h0, ite_eq_right hle]

/-! ### 正準な塔 -/

/-- 正準な塔 -/
def kTow (m : Nat) (pre : List Tm) (r : SeqD) (G : Tm) : Nat → Tm
  | 0 => G
  | k + 1 => col (.K m) (oadd (ofSummands pre) (r.big (kTow m pre r G k))) k

/-- 正準な塔の仮定 -/
structure KCanon (m : Nat) (X : Tm) (pre rest : List Tm) (R : Tm) (r : SeqD) (G : Tm) : Prop where
  hm : 1 ≤ m
  hX : WNF X
  hXC : inC X X (.K m) = true
  hsum : summands X = pre ++ R :: rest
  hB : BigInv R (.K m) r
  hT : Lt (oadd (ofSummands pre) R) (succK m)
  hGF : WNF G
  hGK : Lt G (.K m)

namespace KCanon

variable {m : Nat} {X : Tm} {pre rest : List Tm} {R : Tm} {r : SeqD} {G : Tm}

theorem hKF (H : KCanon m X pre rest R r G) : WNF (.K m) := WNF.K' H.hm
theorem hN (H : KCanon m X pre rest R r G) : NFL (pre ++ R :: rest) := H.hsum ▸ nfl_summands H.hX
theorem hRF (H : KCanon m X pre rest R r G) : WNF R :=
  (H.hN.1 R (List.mem_append_right _ List.mem_cons_self)).1
theorem hRp (H : KCanon m X pre rest R r G) : isPrincipal R = true :=
  (H.hN.1 R (List.mem_append_right _ List.mem_cons_self)).2
theorem hpreF (H : KCanon m X pre rest R r G) : WNF (ofSummands pre) :=
  wnf_ofSummands (nfl_append_left H.hN)
theorem hTF (H : KCanon m X pre rest R r G) : WNF (oadd (ofSummands pre) R) := wnf_oadd H.hpreF H.hRF

theorem hxF (H : KCanon m X pre rest R r G) {γ : Tm} (hγ : WNF γ) (hγK : Lt γ (.K m)) : WNF (r.big γ) :=
  (H.hB.1.good.1 γ hγ hγK).1
theorem hxR (H : KCanon m X pre rest R r G) {γ : Tm} (hγ : WNF γ) (hγK : Lt γ (.K m)) : Lt (r.big γ) R :=
  (H.hB.1.good.1 γ hγ hγK).2

/-- 1 段の `δ = pre ⊕ R[γ]` の性質 -/
theorem step (H : KCanon m X pre rest R r G) {γ : Tm} (hγ : WNF γ) (hγK : Lt γ (.K m)) :
    WNF (oadd (ofSummands pre) (r.big γ)) ∧ Lt (oadd (ofSummands pre) (r.big γ)) (succK m) ∧
      inC (r.big γ) (oadd (ofSummands pre) (r.big γ)) (.K m) = true ∧
      inC (oadd (ofSummands pre) (r.big γ)) (oadd (ofSummands pre) (r.big γ)) (.K m) = true := by
  have hx := H.hxF hγ hγK
  have hxR := H.hxR hγ hγK
  have hδ := wnf_oadd H.hpreF hx
  have hδT : Lt (oadd (ofSummands pre) (r.big γ)) (oadd (ofSummands pre) R) :=
    oadd_lt_oadd H.hpreF hx H.hRF hxR
  have hδS := lt_transY hδ H.hTF (WNF.succK H.hm) hδT H.hT
  have hR0 : Lt .zero R := lt_of_le_of_ltY WNF.zero hx H.hRF (zero_le _) hxR
  obtain ⟨h1, h2⟩ := inC_R_A H.hX H.hKF H.hXC H.hsum hx (H.hB.1.pos γ hγ hγK) hxR WNF.zero hR0
    (H.hB.2 γ hγ hγK)
  rw [approx_zero_eq hx] at h1 h2
  have hxC : inC (r.big γ) (oadd (ofSummands pre) (r.big γ)) (.K m) = true := by
    by_cases hx0 : r.big γ = .zero
    · rw [hx0]
      exact inC_zero _ _
    · refine H.hB.1.ub _ _ γ hδ H.hKF hγ hγK ?_ (bigOK_none rfl) h1 (WFY.inC_of_ltY _ hγ H.hKF hγK)
      exact lt_of_lt_of_leY WNF.zero hx hδ (zero_lt hx0) (le_oadd_right H.hpreF hx)
  exact ⟨hδ, hδS, hxC, inC_oadd H.hpreF hx h2 hxC⟩

end KCanon

/-- `Ξ_m(1)` は標準形 -/
theorem wnf_xi_one {m : Nat} (hm : 1 ≤ m) : WNF (.Xi m .one) :=
  wnf_xi_mk hm WNF.one (by intro e; cases e)
    (ne_gt_of_le (Or.inr (lt_of_lev_lt' (a := .one) (b := succK m) (by
      have h1 : lev (succK m) = m + 1 := rfl
      have h2 : lev Tm.one = 1 := rfl
      omega)))) (inC_one _ _)

/-- 1 段の `col` の形 -/
theorem col_form {m k : Nat} {δ : Tm} (hm : 1 ≤ m) (hδ : WNF δ) (hδS : Lt δ (succK m))
    (hC : inC δ δ (.K m) = true) :
    ∃ D, col (.K m) δ k = .Xi m D ∧ WNF (.Xi m D) ∧ ((δ = .zero ∧ D = .one) ∨ (δ ≠ .zero ∧ D = δ)) := by
  by_cases h0 : δ = .zero
  · subst h0
    exact ⟨.one, rfl, wnf_xi_one hm, Or.inl ⟨rfl, rfl⟩⟩
  · refine ⟨δ, col_K_le h0 (leB_iff.mpr (ne_gt_of_le (Or.inr hδS))),
      wnf_xi_mk hm hδ h0 (ne_gt_of_le (Or.inr hδS)) hC, Or.inr ⟨h0, rfl⟩⟩

namespace KCanon

variable {m : Nat} {X : Tm} {pre rest : List Tm} {R : Tm} {r : SeqD} {G : Tm}

/-- 塔の各段 -/
theorem tower (H : KCanon m X pre rest R r G) : ∀ k, WNF (kTow m pre r G k) ∧ Lt (kTow m pre r G k) (.K m)
  | 0 => ⟨H.hGF, H.hGK⟩
  | k + 1 => by
    obtain ⟨hγ, hγK⟩ := tower H k
    obtain ⟨hδ, hδS, -, hC⟩ := H.step hγ hγK
    obtain ⟨D, e, hy, -⟩ := col_form (k := k) H.hm hδ hδS hC
    show WNF (col (.K m) _ k) ∧ Lt (col (.K m) _ k) (.K m)
    rw [e]
    exact ⟨hy, (lt_K_iffY hy H.hm).mpr (Nat.le_refl _)⟩

/-- 塔の 1 段の形 -/
theorem form (H : KCanon m X pre rest R r G) (k : Nat) :
    ∃ D, kTow m pre r G (k + 1) = .Xi m D ∧ WNF (.Xi m D) ∧
      ((oadd (ofSummands pre) (r.big (kTow m pre r G k)) = .zero ∧ D = .one) ∨
        (oadd (ofSummands pre) (r.big (kTow m pre r G k)) ≠ .zero ∧
          D = oadd (ofSummands pre) (r.big (kTow m pre r G k)))) := by
  obtain ⟨hγ, hγK⟩ := H.tower k
  obtain ⟨hδ, hδS, -, hC⟩ := H.step hγ hγK
  exact col_form H.hm hδ hδS hC

theorem x_zero_of (H : KCanon m X pre rest R r G) {x : Tm} (hx : WNF x)
    (h : oadd (ofSummands pre) x = .zero) : x = .zero := by
  have h1 := le_oadd_right H.hpreF hx
  rw [h] at h1
  rcases h1 with h1 | h1
  · exact h1
  · exact absurd h1 (not_lt_zero _)

/-- 塔は単調 -/
theorem mono (H : KCanon m X pre rest R r G) (k : Nat) :
    Lt (kTow m pre r G k) (kTow m pre r G (k + 1)) := by
  obtain ⟨hγ, hγK⟩ := H.tower k
  obtain ⟨hδ, hδS, hxC, hC⟩ := H.step hγ hγK
  obtain ⟨D, e, hy, hD⟩ := H.form k
  have hx := H.hxF hγ hγK
  have hyK : Lt (.Xi m D) (.K m) := (lt_K_iffY hy H.hm).mpr (Nat.le_refl _)
  rw [e]
  rcases hD with ⟨h0, rfl⟩ | ⟨h0, rfl⟩
  · have hx0 := H.x_zero_of hx h0
    have h1 : inC (r.big (kTow m pre r G k)) .one (.Xi m .one) = true := by
      rw [hx0]
      exact inC_zero _ _
    exact coll_xi0 hy _ hγ (H.hB.1.lo _ _ _ hy hγ hγK h1) hγK
  · have h1 : inC (r.big (kTow m pre r G k)) (oadd (ofSummands pre) (r.big (kTow m pre r G k)))
        (.Xi m (oadd (ofSummands pre) (r.big (kTow m pre r G k)))) = true :=
      inC_of_fr_lt hx H.hKF hy hδ hδ hxC (Or.inr hyK) (Or.inl rfl) fun w hw =>
        FWOrder.k2x hy w (fr_oadd_of_right H.hpreF hx hw)
    exact coll_xi0 hy _ hγ (H.hB.1.lo _ _ _ hy hγ hγK h1) hγK

theorem x_mono (H : KCanon m X pre rest R r G) (k : Nat) :
    Lt (r.big (kTow m pre r G k)) (r.big (kTow m pre r G (k + 1))) :=
  H.hB.1.good.2 _ _ (H.tower k).1 (H.tower (k + 1)).1 (H.mono k) (H.tower (k + 1)).2

theorem x_F (H : KCanon m X pre rest R r G) (k : Nat) : WNF (r.big (kTow m pre r G k)) :=
  H.hxF (H.tower k).1 (H.tower k).2

theorem x_lt (H : KCanon m X pre rest R r G) {j : Nat} :
    ∀ {n : Nat}, j < n → Lt (r.big (kTow m pre r G j)) (r.big (kTow m pre r G n))
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    by_cases hj : j = n
    · rw [hj]
      exact H.x_mono n
    · exact lt_transY (H.x_F j) (H.x_F n) (H.x_F (n + 1)) (x_lt H (by omega)) (H.x_mono n)

/-- 1 段目以降の `R[γ]` は `1` でない -/
theorem x_ne_one (H : KCanon m X pre rest R r G) (k : Nat) :
    r.big (kTow m pre r G (k + 1)) ≠ .one := by
  intro e
  obtain ⟨hγ, hγK⟩ := H.tower (k + 1)
  have h1 : inC (r.big (kTow m pre r G (k + 1))) .zero .zero = true := by
    rw [e]
    exact inC_one _ _
  have h2 := H.hB.1.lo _ _ _ WNF.zero hγ hγK h1
  obtain ⟨D, e', -, -⟩ := H.form k
  rw [e'] at h2
  rcases inC_xi_iff.mp h2 with h | ⟨-, h⟩
  · exact not_lt_zero _ h
  · exact not_lt_zero _ h

theorem hone (H : KCanon m X pre rest R r G) : Lt .one R := by
  have h1 : Lt .one (.K m) := lt_of_lev_lt' (a := .one) (b := .K m) (by
    have := H.hm
    simp only [lev]
    omega)
  exact lt_of_lt_of_leY WNF.one H.hKF H.hRF h1 H.hB.1.hσle

end KCanon

/-- 正準な塔の内側の族 -/
theorem KCanon.inner {m : Nat} {X P c : Tm} {pre rest : List Tm} {R : Tm} {r : SeqD} {G : Tm}
    (H : KCanon m X pre rest R r G) (hc : WNF c) (hP : WNF P)
    (hGC : ∀ g d, WNF d → inC c g d = true → inC P g d = true → inC G g d = true) :
    Inner P c pre R (fun n => r.big (kTow m pre r G n)) where
  hx := H.x_F
  hxR n := H.hxR (H.tower n).1 (H.tower n).2
  mono := H.x_mono
  zero n := H.hB.1.pos _ (H.tower n).1 (H.tower n).2
  gap n := H.hB.2 _ (H.tower n).1 (H.tower n).2
  ub g d n hg hd hRC hpre hcC hPC hor := by
    by_cases hx0 : r.big (kTow m pre r G n) = .zero
    · simp only [hx0]
      exact inC_zero _ _
    have hxn := H.x_F n
    have hy := wnf_oadd hc hxn
    have hxy : Le (r.big (kTow m pre r G n)) (approx pre P (oadd c (r.big (kTow m pre r G n)))) :=
      le_transY hxn hy (wnf_oadd H.hpreF (wnf_nsum hy hP)) (le_oadd_right hc hxn)
        (le_transY hy (wnf_nsum hy hP) (wnf_oadd H.hpreF (wnf_nsum hy hP)) (le_nsum_left hy hP)
          (le_oadd_right H.hpreF (wnf_nsum hy hP)))
    have hlt : ∀ j, j < n → Lt (oadd (ofSummands pre) (r.big (kTow m pre r G j))) g ∧
        Lt .one g := by
      intro j hj
      rcases hor with hT | rfl
      · have h1 : Lt (oadd (ofSummands pre) (r.big (kTow m pre r G j))) (oadd (ofSummands pre) R) :=
          oadd_lt_oadd H.hpreF (H.x_F j) H.hRF (H.hxR (H.tower j).1 (H.tower j).2)
        refine ⟨lt_of_lt_of_leY (wnf_oadd H.hpreF (H.x_F j)) H.hTF hg h1 hT, ?_⟩
        exact lt_of_lt_of_leY WNF.one H.hTF hg
          (lt_of_lt_of_leY WNF.one H.hRF H.hTF H.hone (le_oadd_right H.hpreF H.hRF)) hT
      · refine ⟨oadd_lt_oadd H.hpreF (H.x_F j) (wnf_nsum hy hP) ?_, ?_⟩
        · exact lt_of_lt_of_leY (H.x_F j) hxn (wnf_nsum hy hP) (H.x_lt hj)
            (le_transY hxn hy (wnf_nsum hy hP) (le_oadd_right hc hxn) (le_nsum_left hy hP))
        · have h1 : Lt .one (r.big (kTow m pre r G n)) := by
            cases n with
            | zero => exact absurd hj (Nat.not_lt_zero _)
            | succ k =>
              rcases triY WNF.one hxn with h | h | h
              · exact h
              · exact absurd h.symm (H.x_ne_one k)
              · exact absurd (lt_oneY hxn h) hx0
          exact lt_of_lt_of_leY WNF.one hxn hg h1 hxy
    have h0 : Lt .zero g := by
      rcases hor with hT | rfl
      · exact lt_of_lt_of_leY WNF.zero H.hTF hg
          (lt_of_lt_of_leY WNF.zero H.hRF H.hTF (lt_transY WNF.zero WNF.one H.hRF
            (zero_lt (by intro e; cases e)) H.hone) (le_oadd_right H.hpreF H.hRF)) hT
      · exact lt_of_lt_of_leY WNF.zero hxn hg (zero_lt hx0) hxy
    have hub : ∀ k, inC (kTow m pre r G k) g d = true → inC (r.big (kTow m pre r G k)) g d = true :=
      fun k h => H.hB.1.ub g d _ hg hd (H.tower k).1 (H.tower k).2 h0 (bigOK_none rfl) hRC h
    have hall : ∀ k, k ≤ n → inC (kTow m pre r G k) g d = true := by
      intro k
      induction k with
      | zero => exact fun _ => hGC g d hd hcC hPC
      | succ k ih =>
        intro hk
        have hk' := ih (by omega)
        obtain ⟨D, e, -, hD⟩ := H.form k
        rw [e]
        obtain ⟨h1, h2⟩ := hlt k (by omega)
        rcases hD with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact inC_xi_iff.mpr (Or.inr ⟨inC_one _ _, h2⟩)
        · exact inC_xi_iff.mpr (Or.inr ⟨inC_oadd H.hpreF (H.x_F k) hpre (hub k hk'), h1⟩)
    exact hub n (hall n (Nat.le_refl n))
  ub2 g d n hg hd h _ _ _ _ := by
    obtain ⟨hγ, hγK⟩ := H.tower n
    obtain ⟨hγ', hγK'⟩ := H.tower (n + 1)
    have hm := H.mono n
    have hC := H.hB.1.lo _ _ _ hd hγ' hγK' h
    obtain ⟨D, e, -, hD⟩ := H.form n
    rw [e] at hC
    rcases inC_xi_iff.mp hC with h1 | ⟨h1, -⟩
    · rw [← e] at h1
      exact H.hB.1.ub2 g d _ _ hg hd hγ hγ' hm hγK' h
        (WFY.inC_of_ltY _ hγ hd (lt_transY hγ hγ' hd hm h1))
    · rcases hD with ⟨h0, -⟩ | ⟨-, rfl⟩
      · rw [H.x_zero_of (H.hxF hγ hγK) h0]
        exact inC_zero _ _
      · exact inC_of_oadd_right H.hpreF (H.hxF hγ hγK) h1

theorem canonK_psi {g : Gen} {ξ π : Tm} {m : Nat} {pre : List Tm} {R : Tm} (hg : GenPsi g ξ π) :
    canonK (.K m) g pre R = !kOld m pre R := by
  rcases hg with ⟨rfl, -⟩ | rfl <;> rfl

theorem outsideMode_psi {τ : Tm} {g : Gen} {ξ π : Tm} {m : Nat} {pre : List Tm} {R : Tm}
    (hg : GenPsi g ξ π) : outsideMode τ (.K m) g pre R = kOld m pre R := by
  rcases hg with ⟨rfl, -⟩ | rfl <;> rfl

/-- 正準な塔の添字 -/
theorem gam_canon {τ c P : Tm} {g : Gen} {m : Nat} {pre : List Tm} {R : Tm} {r : SeqD}
    (hc : canonK (.K m) g pre R = true) :
    ∀ n, gam τ (.K m) g pre R r c P n = kTow m pre r (kStart m c P) n
  | 0 => by simp only [gam, hc, ↓reduceIte, kTow]
  | k + 1 => by
    have ih := gam_canon (τ := τ) (c := c) (P := P) (r := r) hc k
    simp only [gam, hc, ↓reduceIte, kTow]
    rw [ih]

theorem argOf_canon {τ c P γ : Tm} {g : Gen} {m : Nat} {pre : List Tm} {R : Tm} {r : SeqD}
    (hc : canonK (.K m) g pre R = true) :
    argOf τ (.K m) g pre R r c P γ = combine g pre c P (r.big γ) := by
  unfold argOf
  simp only [hc, ↓reduceIte]

theorem validR_lt' {σ δ q : Tm} (h : validR σ δ = true) (hq : argR? σ = some q) : Lt q δ := by
  unfold validR at h
  rw [hq] at h
  exact ltB_iff.mp h

/-- 正準な塔の近似の列 -/
theorem appPack_canon {ξ π X P c ceil : Tm} {g : Gen} {m : Nat} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ π) (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (S : SeedHyp π X P R) (adj : AdjHyp π R c)
    (hV : ∀ q, argR? π = some q → Lt q (approx pre P (oadd c (r.big .zero))))
    (hI : IdxHyp ξ π X) (hξ : Le ξ (ofSummands pre)) (hd : r.dom = .big (.K m))
    (hlt : ltB (.K m) ceil = false) (hπK : Lt π (.K m)) (hB : BigInv R (.K m) r)
    (hcan : canonK (.K m) g pre R = true) :
    AppPack ξ π X P pre rest R (.app ceil g pre R r P c) := by
  have hP := ht.psi
  have hm : 1 ≤ m := hB.1.hσF.k
  have hKF := WNF.K' hm
  have hX := hP.aF
  have hN : NFL (pre ++ R :: rest) := hsum ▸ nfl_summands hX
  have hRF := (hN.1 R (List.mem_append_right _ List.mem_cons_self)).1
  have hpreF := wnf_ofSummands (nfl_append_left hN)
  obtain ⟨hGF, hGK, hGC⟩ := start_spec hm adj.hF S.hPF
  have hT : Lt (oadd (ofSummands pre) R) (succK m) := by
    rw [canonK_psi hg] at hcan
    have h1 : ¬ leB (succK m) (oadd (ofSummands pre) R) = true := by
      intro h
      have h2 : kOld m pre R = true := h
      rw [h2] at hcan
      cases hcan
    refine lt_of_gtY (WNF.succK hm) (wnf_oadd hpreF hRF) ?_
    rw [leB_iff] at h1
    simpa using h1
  have H : KCanon m X pre rest R r (kStart m c P) :=
    ⟨hm, hX, inC_mono_d hP.piF hKF (Or.inr hπK) hX hP.Ca, hsum, hB, hT, hGF, hGK⟩
  have I := H.inner adj.hF S.hPF hGC
  have h0F := (hB.1.good.1 .zero WNF.zero (zero_lt (by intro e; cases e))).1
  have hV' : ∀ q, argR? π = some q →
      Lt q (approx pre P (oadd c (r.big (kTow m pre r (kStart m c P) 0)))) := by
    intro q hq
    show Lt q (approx pre P (oadd c (r.big (kStart m c P))))
    by_cases hG0 : kStart m c P = .zero
    · rw [hG0]
      exact hV q hq
    · have h1 := hB.1.good.2 .zero _ WNF.zero hGF (zero_lt hG0) hGK
      have hxG := (hB.1.good.1 _ hGF hGK).1
      exact lt_transY (wnf_of_argR hP.piF hq) (wnf_oadd hpreF (wnf_nsum (wnf_oadd adj.hF h0F) S.hPF))
        (wnf_oadd hpreF (wnf_nsum (wnf_oadd adj.hF hxG) S.hPF)) (hV q hq)
        (approx_mono hpreF (wnf_oadd adj.hF h0F) (wnf_oadd adj.hF hxG) S.hPF
          (oadd_lt_oadd adj.hF h0F hxG h1))
  refine appPack_of_inner I ht hsum S adj hV' hI hξ fun n => ?_
  rw [app_nat_big hd hlt, gam_canon hcan, argOf_canon hcan, hg.comb, hg.ap]

/-- `canonSecondValid` の内容 -/
theorem canonSecond_spec {τ ceil P k : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD}
    (h : canonSecondValid τ ceil g pre R r P k = true) :
    ∃ m, r.dom = .big (.K m) ∧ ltB (.K m) ceil = false ∧ canonK (.K m) g pre R = true ∧
      validR τ (combine g pre k P (r.big (col (.K m) (oadd (ofSummands pre) (r.big (kStart m k P))) 0))) = true := by
  unfold canonSecondValid at h
  split at h
  · rename_i m hd
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨m, hd, h.1.1, h.1.2, h.2⟩
  · cases h

/-- 一つずらした正準な塔の近似の列 -/
theorem appPack_shift {ξ π X P ceil k : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ π) (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (S : SeedHyp π X P R) (adj : AdjHyp π R k) (hI : IdxHyp ξ π X) (hξ : Le ξ (ofSummands pre))
    (hπK : ∀ m, 1 ≤ m → ¬ Lt (.K m) ceil → Lt π (.K m)) (hs : canonSecondValid π ceil g pre R r P k = true)
    (hR : ∀ m, r.dom = .big (.K m) → BigInv R (.K m) r) :
    AppPack ξ π X P pre rest R (.shift (.app ceil g pre R r P k)) ∧
      (SeqD.shift (.app ceil g pre R r P k)).dom = .omega := by
  obtain ⟨m, hd, hlt, hcan, hv⟩ := canonSecond_spec hs
  have hB := hR m hd
  have hP := ht.psi
  have hm : 1 ≤ m := hB.1.hσF.k
  have hKF := WNF.K' hm
  have hX := hP.aF
  have hN : NFL (pre ++ R :: rest) := hsum ▸ nfl_summands hX
  have hRF := (hN.1 R (List.mem_append_right _ List.mem_cons_self)).1
  have hRp := (hN.1 R (List.mem_append_right _ List.mem_cons_self)).2
  have hpreF := wnf_ofSummands (nfl_append_left hN)
  have hR0 : R ≠ .zero := by
    intro e
    rw [e] at hRp
    cases hRp
  have hπK' : Lt π (.K m) := hπK m hm fun h => by
    rw [ltB_iff.mpr h] at hlt
    cases hlt
  obtain ⟨hGF, hGK, hGC⟩ := start_spec hm adj.hF S.hPF
  have hT : Lt (oadd (ofSummands pre) R) (succK m) := by
    rw [canonK_psi hg] at hcan
    have h1 : ¬ leB (succK m) (oadd (ofSummands pre) R) = true := by
      intro h
      have h2 : kOld m pre R = true := h
      rw [h2] at hcan
      cases hcan
    refine lt_of_gtY (WNF.succK hm) (wnf_oadd hpreF hRF) ?_
    rw [leB_iff] at h1
    simpa using h1
  have H : KCanon m X pre rest R r (kStart m k P) :=
    ⟨hm, hX, inC_mono_d hP.piF hKF (Or.inr hπK') hX hP.Ca, hsum, hB, hT, hGF, hGK⟩
  have I := (H.inner adj.hF S.hPF hGC).shift
  have hdt := app_dom_big_ge (P := P) (c := k) (g := g) (pre := pre) (R := R) hd hlt
  refine ⟨appPack_of_inner I ht hsum S adj (fun q hq => ?_) hI hξ fun n => ?_, hdt⟩
  · have := validR_lt' hv hq
    rwa [hg.comb] at this
  · show (SeqD.app ceil g pre R r P k).nat (n + 1) = _
    rw [app_nat_big hd hlt, gam_canon hcan, argOf_canon hcan, hg.comb, hg.ap]

/-! ### 仮想的な `K_m` への崩壊 -/

section Virt

variable {m : Nat}

theorem hSC (m : Nat) (g d : Tm) : inC (succK m) g d = true := by
  show inC (.Om (.plus (.K m) .one)) g d = true
  rw [inC_om, inC_plus]
  simp [inC_K, inC_one]

theorem succK_tgt (m : Nat) : IsTgt (succK m) := Or.inl ⟨_, rfl, by simp [isSucc, summands]⟩

theorem wnf_psi0K (hm : 1 ≤ m) : WNF (.Psi .zero (succK m) .zero) :=
  wnf_base_om (WNF.succK hm) (by simp [isSucc, summands])

theorem virtG_spec (hm : 1 ≤ m) : ∀ k, WNF (virtG m k) ∧ Lt (virtG m k) (succK m)
  | 0 => ⟨WNF.zero, zero_lt (by intro e; cases e)⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := virtG_spec hm k
    have hψ := wnf_psi0K hm
    have hS := WNF.succK hm
    have hA := wnf_oadd hψ h1
    have hlt := oadd_lt_prin hψ h1 (z := succK m) rfl (lt_psi_targetY hψ) h2
    have hy : WNF (.Psi .zero (succK m) (oadd (.Psi .zero (succK m) .zero) (virtG m k))) :=
      wnf_psi0 hS (succK_tgt m) hA (WFY.inC_of_ltY _ hA hS hlt) fun r h => by
        simp [argR?, succK] at h
    exact ⟨hy, lt_psi_targetY hy⟩

/-- `ψ₀ ⊕ g_k` -/
theorem virtE_F (hm : 1 ≤ m) (k : Nat) : WNF (oadd (.Psi .zero (succK m) .zero) (virtG m k)) :=
  wnf_oadd (wnf_psi0K hm) (virtG_spec hm k).1

theorem virtE_lt (hm : 1 ≤ m) (k : Nat) :
    Lt (oadd (.Psi .zero (succK m) .zero) (virtG m k)) (succK m) :=
  oadd_lt_prin (wnf_psi0K hm) (virtG_spec hm k).1 rfl (lt_psi_targetY (wnf_psi0K hm)) (virtG_spec hm k).2

theorem virtG_mono (hm : 1 ≤ m) (k : Nat) : Lt (virtG m k) (virtG m (k + 1)) := by
  obtain ⟨h1, h2⟩ := virtG_spec hm k
  obtain ⟨hy, -⟩ := virtG_spec hm (k + 1)
  have hψ := wnf_psi0K hm
  have hA := virtE_F hm k
  have hS := WNF.succK hm
  have hy' : WNF (.Psi .zero (succK m) (oadd (.Psi .zero (succK m) .zero) (virtG m k))) := hy
  have hC : inC (oadd (.Psi .zero (succK m) .zero) (virtG m k))
      (oadd (.Psi .zero (succK m) .zero) (virtG m k)) (.Psi .zero (succK m) (oadd (.Psi .zero (succK m) .zero) (virtG m k))) = true :=
    inC_of_fr_lt hA hS hy' hA hA hy'.psi.Ca (Or.inr (lt_psi_targetY hy')) (Or.inl rfl)
      fun w hw => FWOrder.k2 hy' w hw
  exact coll_psiY hy' _ h1 (inC_of_oadd_right hψ h1 hC) h2

theorem virtE_mono (hm : 1 ≤ m) (k : Nat) : Lt (oadd (.Psi .zero (succK m) .zero) (virtG m k))
    (oadd (.Psi .zero (succK m) .zero) (virtG m (k + 1))) :=
  oadd_lt_oadd (wnf_psi0K hm) (virtG_spec hm k).1 (virtG_spec hm (k + 1)).1 (virtG_mono hm k)

theorem virtE_lt_of (hm : 1 ≤ m) {j : Nat} : ∀ {k : Nat}, j < k →
    Lt (oadd (.Psi .zero (succK m) .zero) (virtG m j)) (oadd (.Psi .zero (succK m) .zero) (virtG m k))
  | 0, h => absurd h (Nat.not_lt_zero _)
  | k + 1, h => by
    by_cases hj : j = k
    · rw [hj]
      exact virtE_mono hm k
    · exact lt_transY (virtE_F hm j) (virtE_F hm k) (virtE_F hm (k + 1)) (virtE_lt_of hm (by omega))
        (virtE_mono hm k)

theorem inC_psi0K {g d : Tm} (h0 : Lt .zero g) : inC (.Psi .zero (succK m) .zero) g d = true :=
  inC_psi_iff.mpr (Or.inr ⟨hSC m g d, inC_zero _ _, inC_zero _ _, h0⟩)

theorem inC_virtG (hm : 1 ≤ m) {g d : Tm} (h0 : Lt .zero g) : ∀ k,
    (∀ j, j < k → Lt (oadd (.Psi .zero (succK m) .zero) (virtG m j)) g) → inC (virtG m k) g d = true
  | 0, _ => inC_zero _ _
  | k + 1, h => inC_psi_iff.mpr (Or.inr ⟨hSC m g d, inC_zero _ _,
      inC_oadd (wnf_psi0K hm) (virtG_spec hm k).1 (inC_psi0K h0)
        (inC_virtG hm h0 k fun j hj => h j (by omega)), h k (by omega)⟩)

theorem wnf_xiS (hm : 1 ≤ m) : WNF (.Xi m (succK m)) :=
  wnf_xi_mk hm (WNF.succK hm) (by intro e; cases e) (ne_gt_of_le (Or.inl rfl)) (hSC m _ _)

theorem xiS_lt_K (hm : 1 ≤ m) : Lt (.Xi m (succK m)) (.K m) :=
  (lt_K_iffY (wnf_xiS hm) hm).mpr (Nat.le_refl _)

/-- 仮想的な崩壊の引数 -/
def virtA (m k : Nat) : Tm :=
  nsum (oadd (.Psi .zero (succK m) .zero) (virtG m k)) (.Xi m (succK m))

theorem virtA_F (hm : 1 ≤ m) (k : Nat) : WNF (virtA m k) := wnf_nsum (virtE_F hm k) (wnf_xiS hm)

theorem virtA_lt (hm : 1 ≤ m) (k : Nat) : Lt (virtA m k) (succK m) :=
  nsum_lt_prin (virtE_F hm k) (wnf_xiS hm) rfl (virtE_lt hm k)
    (lt_transY (wnf_xiS hm) (WNF.K' hm) (WNF.succK hm) (xiS_lt_K hm) (WFY.K_lt_succK hm))

theorem virtE_le (hm : 1 ≤ m) (k : Nat) :
    Le (oadd (.Psi .zero (succK m) .zero) (virtG m k)) (virtA m k) :=
  le_nsum_left (virtE_F hm k) (wnf_xiS hm)

theorem virtA_pos (hm : 1 ≤ m) (k : Nat) : Lt .zero (virtA m k) :=
  lt_of_lt_of_leY WNF.zero (wnf_xiS hm) (virtA_F hm k) (zero_lt (by intro e; cases e))
    (le_nsum_right (virtE_F hm k) (wnf_xiS hm))

theorem inC_virtA (hm : 1 ≤ m) {g d : Tm} (h0 : Lt .zero g) (k : Nat)
    (h : ∀ j, j < k → Lt (oadd (.Psi .zero (succK m) .zero) (virtG m j)) g)
    (hx : inC (.Xi m (succK m)) g d = true) : inC (virtA m k) g d = true :=
  inC_nsum (virtE_F hm k) (wnf_xiS hm)
    (inC_oadd (wnf_psi0K hm) (virtG_spec hm k).1 (inC_psi0K h0) (inC_virtG hm h0 k h)) hx

theorem virtA_lt_of (hm : 1 ≤ m) {j k : Nat} (h : j < k) :
    Lt (oadd (.Psi .zero (succK m) .zero) (virtG m j)) (virtA m k) :=
  lt_of_lt_of_leY (virtE_F hm j) (virtE_F hm k) (virtA_F hm k) (virtE_lt_of hm h) (virtE_le hm k)

theorem wnf_virtK (hm : 1 ≤ m) (k : Nat) : WNF (virtK m k) :=
  wnf_xi_mk hm (virtA_F hm k) (fun e => by
      have := virtA_pos hm k
      unfold virtA at this
      rw [e] at this
      exact not_lt_zero _ this) (ne_gt_of_le (Or.inr (virtA_lt hm k)))
    (inC_virtA hm (virtA_pos hm k) k (fun _ h => virtA_lt_of hm h)
      (WFY.inC_of_ltY _ (wnf_xiS hm) (WNF.K' hm) (xiS_lt_K hm)))

theorem virtK_lt_K (hm : 1 ≤ m) (k : Nat) : Lt (virtK m k) (.K m) :=
  (lt_K_iffY (wnf_virtK hm k) hm).mpr (Nat.le_refl _)

theorem xiS_lt_virtK (hm : 1 ≤ m) (k : Nat) : Lt (.Xi m (succK m)) (virtK m k) :=
  FWOrder.k2x (wnf_virtK hm k) _ (fr_nsum_of_right (virtE_F hm k) (wnf_xiS hm) (by
    simp [fr, xiS_lt_K hm]))

theorem virtK_mono (hm : 1 ≤ m) (k : Nat) : Lt (virtK m k) (virtK m (k + 1)) := by
  have hAA : Lt (virtA m k) (virtA m (k + 1)) :=
    nsum_lt_left (virtE_F hm k) (virtE_F hm (k + 1)) (wnf_xiS hm) (virtE_mono hm k)
  exact (lt_xi_xi0 hAA.ne).mpr (Or.inl ⟨hAA, inC_virtA hm (virtA_pos hm (k + 1)) k
    (fun j hj => virtA_lt_of hm (by omega))
    (WFY.inC_of_ltY _ (wnf_xiS hm) (wnf_virtK hm (k + 1)) (xiS_lt_virtK hm (k + 1)))⟩)

theorem inC_xiS {g d : Tm} (hS : Lt (succK m) g) : inC (.Xi m (succK m)) g d = true :=
  inC_xi_iff.mpr (Or.inr ⟨hSC m g d, hS⟩)

theorem inC_virtK (hm : 1 ≤ m) {g d : Tm} (hg : WNF g) (hS : Lt (succK m) g) (k : Nat) :
    inC (virtK m k) g d = true :=
  inC_xi_iff.mpr (Or.inr ⟨inC_virtA hm (lt_transY WNF.zero (WNF.succK hm) hg
      (zero_lt (by intro e; cases e)) hS) k
      (fun j _ => lt_transY (virtE_F hm j) (WNF.succK hm) hg (virtE_lt hm j) hS) (inC_xiS hS),
    lt_transY (virtA_F hm k) (WNF.succK hm) hg (virtA_lt hm k) hS⟩)

end Virt

/-! ### 旧方式の塔 -/

/-- 旧方式の塔 -/
def oT (m : Nat) (pre : List Tm) (r : SeqD) (c P : Tm) : Nat → Tm
  | 0 => .zero
  | k + 1 => col (.K m) (approx pre P (oadd c (r.big (oT m pre r c P k)))) k

/-- 旧方式の塔の仮定 -/
structure KOld (m : Nat) (X c P : Tm) (pre rest : List Tm) (R : Tm) (r : SeqD) : Prop where
  hm : 1 ≤ m
  hX : WNF X
  hsum : summands X = pre ++ R :: rest
  hB : BigInv R (.K m) r
  hc : WNF c
  hP : WNF P
  hT : Le (succK m) (oadd (ofSummands pre) R)
  hRne : R ≠ succK m

namespace KOld

variable {m : Nat} {X c P : Tm} {pre rest : List Tm} {R : Tm} {r : SeqD}

theorem hN (H : KOld m X c P pre rest R r) : NFL (pre ++ R :: rest) := H.hsum ▸ nfl_summands H.hX
theorem hRF (H : KOld m X c P pre rest R r) : WNF R :=
  (H.hN.1 R (List.mem_append_right _ List.mem_cons_self)).1
theorem hRp (H : KOld m X c P pre rest R r) : isPrincipal R = true :=
  (H.hN.1 R (List.mem_append_right _ List.mem_cons_self)).2
theorem hpreN (H : KOld m X c P pre rest R r) : NFL pre := nfl_append_left H.hN
theorem hpreF (H : KOld m X c P pre rest R r) : WNF (ofSummands pre) := wnf_ofSummands H.hpreN
theorem hTF (H : KOld m X c P pre rest R r) : WNF (oadd (ofSummands pre) R) := wnf_oadd H.hpreF H.hRF
theorem hSF (H : KOld m X c P pre rest R r) : WNF (succK m) := WNF.succK H.hm

theorem hsT (H : KOld m X c P pre rest R r) : summands (oadd (ofSummands pre) R) = pre ++ [R] := by
  have hge : ∀ s h r', s ∈ pre → summands R = h :: r' → leB h s = true := by
    intro s h r' hs e
    rw [summands_principal H.hRp] at e
    simp only [List.cons.injEq] at e
    rw [← e.1, leB_iff]
    exact le_of_nfl_append H.hN s hs
  rw [summands_oadd_pre H.hpreN H.hRF hge, summands_principal H.hRp]

/-- 上端は `K_m⁺` より真に大きい -/
theorem hTgt (H : KOld m X c P pre rest R r) : Lt (succK m) (oadd (ofSummands pre) R) := by
  rcases H.hT with e | h
  · exfalso
    have h1 := H.hsT
    rw [← e] at h1
    have h2 : summands (succK m) = [succK m] := rfl
    rw [h2] at h1
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, and_true] at h1
      exact H.hRne h1.symm
    | cons a l =>
      have := congrArg List.length h1
      simp at this
  · exact h

theorem hxF (H : KOld m X c P pre rest R r) {γ : Tm} (hγ : WNF γ) (hγK : Lt γ (.K m)) : WNF (r.big γ) :=
  (H.hB.1.good.1 γ hγ hγK).1
theorem hxR (H : KOld m X c P pre rest R r) {γ : Tm} (hγ : WNF γ) (hγK : Lt γ (.K m)) : Lt (r.big γ) R :=
  (H.hB.1.good.1 γ hγ hγK).2

theorem hAF (H : KOld m X c P pre rest R r) {x : Tm} (hx : WNF x) :
    WNF (approx pre P (oadd c x)) :=
  wnf_oadd H.hpreF (wnf_nsum (wnf_oadd H.hc hx) H.hP)

theorem le_A (H : KOld m X c P pre rest R r) {x : Tm} (hx : WNF x) :
    Le x (approx pre P (oadd c x)) := by
  have hy := wnf_oadd H.hc hx
  have hz := wnf_nsum hy H.hP
  exact le_transY hx hy (H.hAF hx) (le_oadd_right H.hc hx)
    (le_transY hy hz (H.hAF hx) (le_nsum_left hy H.hP) (le_oadd_right H.hpreF hz))

theorem A_mono (H : KOld m X c P pre rest R r) {x x' : Tm} (hx : WNF x) (hx' : WNF x') (h : Lt x x') :
    Lt (approx pre P (oadd c x)) (approx pre P (oadd c x')) :=
  approx_mono H.hpreF (wnf_oadd H.hc hx) (wnf_oadd H.hc hx') H.hP (oadd_lt_oadd H.hc hx hx' h)

/-- 近似の引数は `K_m⁺` 以上 -/
theorem lbA (H : KOld m X c P pre rest R r) {γ : Tm} (hγ : WNF γ) (hγK : Lt γ (.K m)) :
    Le (succK m) (approx pre P (oadd c (r.big γ))) := by
  have hx := H.hxF hγ hγK
  have hSF := H.hSF
  have hA := H.hAF hx
  cases hpe : pre with
  | nil =>
    subst hpe
    have h1 : Lt (succK m) R := by
      have := H.hTgt
      rwa [show ofSummands [] = Tm.zero from rfl, zero_oadd H.hRF] at this
    exact le_transY hSF hx hA (H.hB.1.lbS m rfl h1 γ hγ hγK) (H.le_A hx)
  | cons a l =>
    subst hpe
    have haN := H.hpreN.1 a List.mem_cons_self
    have h1 : Le (succK m) a := le_of_not_ltY haN.1 hSF fun h =>
      Lt.asymmY hSF H.hTF H.hTgt (lt_prin_of_head (by rw [H.hsT]; rfl) rfl haN.2 h)
    have h2 := le_ofSummands_of_mem H.hpreN (List.mem_cons_self : a ∈ a :: l)
    have hz := wnf_nsum (wnf_oadd H.hc hx) H.hP
    exact le_transY hSF haN.1 hA h1 (le_transY haN.1 H.hpreF hA h2 (le_oadd_left H.hpreF hz))

/-- 1 段の形 -/
theorem form (H : KOld m X c P pre rest R r) {k : Nat} (hγ : WNF (oT m pre r c P k))
    (hγK : Lt (oT m pre r c P k) (.K m)) :
    (oT m pre r c P (k + 1) = .Xi m (succK m) ∧
        approx pre P (oadd c (r.big (oT m pre r c P k))) = succK m) ∨
      (oT m pre r c P (k + 1) = virtK m k ∧
        Lt (succK m) (approx pre P (oadd c (r.big (oT m pre r c P k))))) := by
  have hx := H.hxF hγ hγK
  have hne : approx pre P (oadd c (r.big (oT m pre r c P k))) ≠ .zero := by
    intro e
    have h1 := H.lbA hγ hγK
    rw [e] at h1
    rcases h1 with h1 | h1
    · cases h1
    · exact not_lt_zero _ h1
  rcases H.lbA hγ hγK with e | h
  · refine Or.inl ⟨?_, e.symm⟩
    show col (.K m) _ k = _
    rw [col_K_le hne (leB_iff.mpr (ne_gt_of_le (Or.inl e.symm))), ← e]
  · refine Or.inr ⟨?_, h⟩
    show col (.K m) _ k = _
    refine col_K_gt hne fun h' => ?_
    exact not_lt_of_leY (H.hAF hx) H.hSF (le_of_ne_gtY (H.hAF hx) H.hSF (leB_iff.mp h')) h

/-- 塔の各段 -/
theorem tower (H : KOld m X c P pre rest R r) :
    ∀ k, WNF (oT m pre r c P k) ∧ Lt (oT m pre r c P k) (.K m)
  | 0 => ⟨WNF.zero, zero_lt (by intro e; cases e)⟩
  | k + 1 => by
    obtain ⟨hγ, hγK⟩ := tower H k
    rcases H.form hγ hγK with ⟨e, -⟩ | ⟨e, -⟩
    · rw [e]
      exact ⟨wnf_xiS H.hm, xiS_lt_K H.hm⟩
    · rw [e]
      exact ⟨wnf_virtK H.hm k, virtK_lt_K H.hm k⟩

theorem x_F (H : KOld m X c P pre rest R r) (k : Nat) : WNF (r.big (oT m pre r c P k)) :=
  H.hxF (H.tower k).1 (H.tower k).2

/-- 塔は単調 -/
theorem mono (H : KOld m X c P pre rest R r) : ∀ k, Lt (oT m pre r c P k) (oT m pre r c P (k + 1))
  | 0 => by
    obtain ⟨hγ, hγK⟩ := H.tower 0
    rcases H.form hγ hγK with ⟨e, -⟩ | ⟨e, -⟩
    · rw [e]
      exact zero_lt (by intro e; cases e)
    · rw [e]
      exact zero_lt (by intro e; cases e)
  | k + 1 => by
    have ih := mono H k
    obtain ⟨hγ, hγK⟩ := H.tower k
    obtain ⟨hγ', hγK'⟩ := H.tower (k + 1)
    have hx := H.hB.1.good.2 _ _ hγ hγ' ih hγK'
    have hAA := H.A_mono (H.x_F k) (H.x_F (k + 1)) hx
    have hS : Lt (succK m) (approx pre P (oadd c (r.big (oT m pre r c P (k + 1))))) :=
      lt_of_le_of_ltY H.hSF (H.hAF (H.x_F k)) (H.hAF (H.x_F (k + 1))) (H.lbA hγ hγK) hAA
    have e2 : oT m pre r c P (k + 1 + 1) = virtK m (k + 1) := by
      rcases H.form hγ' hγK' with ⟨-, e⟩ | ⟨e, -⟩
      · rw [e] at hS
        exact absurd hS (Lt.irrefl _)
      · exact e
    rw [e2]
    rcases H.form hγ hγK with ⟨e, -⟩ | ⟨e, -⟩
    · rw [e]
      exact xiS_lt_virtK H.hm _
    · rw [e]
      exact virtK_mono H.hm k

theorem x_mono (H : KOld m X c P pre rest R r) (k : Nat) :
    Lt (r.big (oT m pre r c P k)) (r.big (oT m pre r c P (k + 1))) :=
  H.hB.1.good.2 _ _ (H.tower k).1 (H.tower (k + 1)).1 (H.mono k) (H.tower (k + 1)).2

theorem x_lt (H : KOld m X c P pre rest R r) {j : Nat} :
    ∀ {n : Nat}, j < n → Lt (r.big (oT m pre r c P j)) (r.big (oT m pre r c P n))
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    by_cases hj : j = n
    · rw [hj]
      exact H.x_mono n
    · exact lt_transY (H.x_F j) (H.x_F n) (H.x_F (n + 1)) (x_lt H (by omega)) (H.x_mono n)

/-- 塔の上界 -/
theorem inC_step (H : KOld m X c P pre rest R r) {g d : Tm} (hg : WNF g) (k : Nat)
    (hS : Lt (succK m) g) : inC (oT m pre r c P (k + 1)) g d = true := by
  obtain ⟨hγ, hγK⟩ := H.tower k
  rcases H.form hγ hγK with ⟨e, -⟩ | ⟨e, -⟩
  · rw [e]
    exact inC_xiS hS
  · rw [e]
    exact inC_virtK H.hm hg hS k

/-- 内側の族 -/
theorem inner (H : KOld m X c P pre rest R r) : Inner P c pre R (fun n => r.big (oT m pre r c P n)) where
  hx := H.x_F
  hxR n := H.hxR (H.tower n).1 (H.tower n).2
  mono := H.x_mono
  zero n := H.hB.1.pos _ (H.tower n).1 (H.tower n).2
  gap n := H.hB.2 _ (H.tower n).1 (H.tower n).2
  ub g d n hg hd hRC _ _ _ hor := by
    have hxn := H.x_F n
    have hA := H.hAF hxn
    have h0 : Lt .zero g := by
      have h1 : Lt .zero (succK m) := zero_lt (by intro e; cases e)
      rcases hor with hT | rfl
      · exact lt_of_lt_of_leY WNF.zero H.hTF hg (lt_transY WNF.zero H.hSF H.hTF h1 H.hTgt) hT
      · exact lt_of_lt_of_leY WNF.zero H.hSF hg h1 (H.lbA (H.tower n).1 (H.tower n).2)
    have hγ : inC (oT m pre r c P n) g d = true := by
      cases n with
      | zero => exact inC_zero _ _
      | succ k =>
        refine H.inC_step hg k ?_
        rcases hor with hT | rfl
        · exact lt_of_lt_of_leY H.hSF H.hTF hg H.hTgt hT
        · exact lt_of_le_of_ltY H.hSF (H.hAF (H.x_F k)) hA (H.lbA (H.tower k).1 (H.tower k).2)
            (H.A_mono (H.x_F k) hxn (H.x_mono k))
    exact H.hB.1.ub g d _ hg hd (H.tower n).1 (H.tower n).2 h0 (bigOK_none rfl) hRC hγ
  ub2 g d n hg hd h _ _ _ hlt := by
    have hγ : inC (oT m pre r c P n) g d = true := by
      cases n with
      | zero => exact inC_zero _ _
      | succ k =>
        refine H.inC_step hg k ?_
        exact lt_transY H.hSF (H.hAF (H.x_F (k + 1))) hg
          (lt_of_le_of_ltY H.hSF (H.hAF (H.x_F k)) (H.hAF (H.x_F (k + 1)))
            (H.lbA (H.tower k).1 (H.tower k).2) (H.A_mono (H.x_F k) (H.x_F (k + 1)) (H.x_mono k))) hlt
    exact H.hB.1.ub2 g d _ _ hg hd (H.tower n).1 (H.tower (n + 1)).1 (H.mono n) (H.tower (n + 1)).2 h hγ

end KOld

/-- 旧方式の塔の添字 -/
theorem gam_old {τ ξ π c P : Tm} {g : Gen} {m : Nat} {pre : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ π) (hold : kOld m pre R = true) :
    ∀ n, gam τ (.K m) g pre R r c P n = oT m pre r c P n
  | 0 => by
    have h1 := canonK_psi (m := m) (pre := pre) (R := R) hg
    have h2 := outsideMode_psi (τ := τ) (m := m) (pre := pre) (R := R) hg
    rw [hold] at h1 h2
    simp only [gam, h1, h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte, oT]
  | k + 1 => by
    have ih := gam_old (τ := τ) (c := c) (P := P) (r := r) hg hold k
    have h1 := canonK_psi (m := m) (pre := pre) (R := R) hg
    have h2 := outsideMode_psi (τ := τ) (m := m) (pre := pre) (R := R) hg
    rw [hold] at h1 h2
    simp only [gam, argOf, h1, h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte, oT]
    rw [ih, hg.comb]

theorem argOf_old {τ ξ π c P γ : Tm} {g : Gen} {m : Nat} {pre : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ π) (hold : kOld m pre R = true) :
    argOf τ (.K m) g pre R r c P γ = combine g pre c P (r.big γ) := by
  have h1 := canonK_psi (m := m) (pre := pre) (R := R) hg
  have h2 := outsideMode_psi (τ := τ) (m := m) (pre := pre) (R := R) hg
  rw [hold] at h1 h2
  simp only [argOf, h1, h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- 旧方式の塔の近似の列 -/
theorem appPack_old {ξ π X P c ceil : Tm} {g : Gen} {m : Nat} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ π) (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (S : SeedHyp π X P R) (adj : AdjHyp π R c)
    (hV : ∀ q, argR? π = some q → Lt q (approx pre P (oadd c (r.big .zero))))
    (hI : IdxHyp ξ π X) (hξ : Le ξ (ofSummands pre)) (hd : r.dom = .big (.K m))
    (hlt : ltB (.K m) ceil = false) (hB : BigInv R (.K m) r) (hRne : R ≠ succK m)
    (hold : kOld m pre R = true) :
    AppPack ξ π X P pre rest R (.app ceil g pre R r P c) := by
  have hm : 1 ≤ m := hB.1.hσF.k
  have hN : NFL (pre ++ R :: rest) := hsum ▸ nfl_summands ht.psi.aF
  have hRF := (hN.1 R (List.mem_append_right _ List.mem_cons_self)).1
  have hpreF := wnf_ofSummands (nfl_append_left hN)
  have H : KOld m X c P pre rest R r :=
    ⟨hm, ht.psi.aF, hsum, hB, adj.hF, S.hPF,
      le_of_ne_gtY (WNF.succK hm) (wnf_oadd hpreF hRF) (leB_iff.mp hold), hRne⟩
  refine appPack_of_inner H.inner ht hsum S adj hV hI hξ fun n => ?_
  rw [app_nat_big hd hlt, gam_old hg hold, argOf_old hg hold, hg.comb, hg.ap]

/-- `K_m` の対角化 -/
theorem appPack_K {ξ π X P c ceil : Tm} {g : Gen} {m : Nat} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ π) (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (S : SeedHyp π X P R) (adj : AdjHyp π R c)
    (hV : ∀ q, argR? π = some q → Lt q (approx pre P (oadd c (r.big .zero))))
    (hI : IdxHyp ξ π X) (hξ : Le ξ (ofSummands pre)) (hd : r.dom = .big (.K m))
    (hlt : ltB (.K m) ceil = false) (hπK : Lt π (.K m)) (hB : BigInv R (.K m) r) (hRne : R ≠ succK m) :
    AppPack ξ π X P pre rest R (.app ceil g pre R r P c) := by
  cases hold : kOld m pre R with
  | true => exact appPack_old hg ht hsum S adj hV hI hξ hd hlt hB hRne hold
  | false =>
    exact appPack_canon hg ht hsum S adj hV hI hξ hd hlt hπK hB (by rw [canonK_psi hg, hold]; rfl)

end RTKA.Fund
