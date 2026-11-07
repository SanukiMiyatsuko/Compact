import Compact.FS.CofChain

/-! `Ξ` の族の閉包の葉の共終性：鎖の端 `ρ = Ξ_m(q)` の列（`mahloVK`）の葉。

* 列の項は `Ξ_m(A)`（目標は `K_m`）。目標が `t` と `K_m` の間の節点は仮定 `hlow`、目標が `K_m` の節点 `Ξ_m(b)` は
  `b` が `T = pre ⊕ R` 未満なら引数の共終性（`XiS`）、そうでなければ仮定 `hcls`。目標が `K_m` より大きい節点は階が合わない。
* `Ω` の塔 `.tower G`：目標が `t` より大きい節点が `G` 以下か隙間なら、塔は `t` の中で共終。 -/

namespace RTKA.Fund

open Tm W

theorem le_xA {pre : List Tm} {c P x : Tm} (hpreF : WNF (ofSummands pre)) (hc : WNF c) (hP : WNF P)
    (hx : WNF x) : Le (oadd (ofSummands pre) x) (xA c pre P x) := by
  have hy := wnf_nsum hP hx
  have hz := wnf_nsum hc hy
  have h1 : Le x (nsum c (nsum P x)) :=
    le_transY hx hy hz (le_nsum_right hP hx) (le_nsum_right hc hy)
  rcases h1 with e | h
  · exact Or.inl (by unfold xA; rw [← e])
  · exact Or.inr (oadd_lt_oadd hpreF hx hz h)

/-- `K_j`（`j < m`）は階 `m` の下端以下 -/
theorem K_le_floorLev {j m : Nat} (hj : WNF (.K j)) (h : j + 1 ≤ m) : Le (.K j) (floorLev m) := by
  have hj1 : 1 ≤ j := hj.k
  unfold floorLev
  rw [ite_eq_right (by omega : ¬ m ≤ 1)]
  by_cases e : j = m - 1
  · rw [← e]
    exact Or.inl rfl
  · exact Or.inr ((lt_K_iffY hj (by omega)).mpr (by simp only [lev]; omega))

/-- `K_j`（`j < m`）は `Ξ_m(A)` 未満 -/
theorem K_lt_xi {j m : Nat} {A : Tm} (hy : WNF (.Xi m A)) (h : j + 1 ≤ m) : Lt (.K j) (.Xi m A) :=
  K_lt_of_lev hy rfl rfl (by simp only [lev]; exact h)

/-- 同じ `Ξ_m` で引数が小さく、引数の前線が下にあれば小さい -/
theorem le_xi_of_fr {m : Nat} {b b' : Tm} (hx : WNF (.Xi m b)) (hy : WNF (.Xi m b')) (hbb : Le b b')
    (hfr : ∀ f, f ∈ fr (.K m) b → Lt f (.Xi m b')) : Le (.Xi m b) (.Xi m b') := by
  rcases hbb with rfl | h
  · exact Or.inl rfl
  · have hbF := hx.xi.2.1
    have hb'F := hy.xi.2.1
    have hm := hx.xi.1
    have hKF := WNF.K' hm
    have hC : inC b b' (.Xi m b') = true :=
      inC_of_fr_lt hbF hKF hy hbF hb'F hx.xi.2.2.2.2 (Or.inr ((lt_K_iffY hy hm).mpr (Nat.le_refl _))) (Or.inr h)
        hfr
    exact Or.inr ((lt_xi_xi0 h.ne).mpr (Or.inl ⟨h, hC⟩))

/-! ### 引数の共終性 -/

/-- `Ξ` の族の列の項の引数の共終性 -/
def XiS (t T : Tm) (m : Nat) (s : SeqD) : Prop :=
  ∀ b N, WNF (.Xi m b) → Lt (.Xi m b) t → Lt b T → (∀ w, w ∈ parF (.Xi m b) → Lt w (s.nat N)) →
    ∃ n A, N ≤ n ∧ s.nat n = .Xi m A ∧ Lt b A

/-- `ω` 型の加数 -/
theorem xiS_nat {t P c ceil : Tm} {m : Nat} {pre : List Tm} {R : Tm} {r : SeqD} (hN : NFL (pre ++ [R]))
    (hc : WNF c) (hP : WNF P) (hd : r.dom = .omega) (hF : ∀ n, WNF (r.nat n))
    (hmo : ∀ n, Lt (r.nat n) (r.nat (n + 1))) (hRC : SeqC R r) :
    XiS t (oadd (ofSummands pre) R) m (.app ceil (.xi m) pre R r P c) := by
  have hpreF := wnf_ofSummands (nfl_append_left hN)
  have hRC' : ∀ x, WNF x → Lt x R → ∃ n, Lt x (r.nat n) := by
    have := hRC
    unfold SeqC at this
    rwa [hd] at this
  have hdom : ∀ σ, r.dom ≠ .big σ := fun σ e => by
    rw [hd] at e
    cases e
  intro b N hb _ hbT _
  have hbF := hb.xi.2.1
  obtain ⟨b', hb', hb'R, -, hle⟩ := lt_oadd_split hN hbF hbT
  obtain ⟨n₀, hn₀⟩ := hRC' b' hb' hb'R
  have hn : Lt b' (r.nat (max n₀ N)) :=
    lt_of_lt_of_leY hb' (hF n₀) (hF _) hn₀ (mono_le hF hmo (Nat.le_max_left _ _))
  refine ⟨max n₀ N, xA c pre P (r.nat (max n₀ N)), Nat.le_max_right _ _,
    by rw [app_nat_of_not_big hdom]; rfl, ?_⟩
  exact lt_of_lt_of_leY hbF (wnf_oadd hpreF (hF _)) (wnf_oadd hpreF (wnf_nsum hc (wnf_nsum hP (hF _))))
    (lt_of_le_of_ltY hbF (wnf_oadd hpreF hb') (wnf_oadd hpreF (hF _)) hle (oadd_lt_oadd hpreF hb' (hF _) hn))
    (le_xA hpreF hc hP (hF _))

/-- `K_m` 型の加数（値の帰還の塔） -/
theorem xiS_K {π X q P c t : Tm} {m : Nat} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Xi m q)) (G : XiG m q .zero c pre rest R)
    (hc0 : c = .zero → P ≠ .zero) (hd : r.dom = .big (.K m)) (hlt : ltB (.K m) π = false)
    (hB : BigInv R (.K m) r) (hPF : WNF P) (hPπ : Lt P π) (hPn : P = .zero ∨ NodeT P) (hRC : SeqC R r) :
    XiS t (oadd (ofSummands pre) R) m (.app π (.xi m) pre R r P c) := by
  obtain ⟨htow, he⟩ := xi_K_data ht hc G hc0 hd hlt hB hPF hPπ hPn
  have hKF := G.hKF
  have hρ := G.ht
  have hρK := G.hρK
  have hN : NFL (pre ++ [R]) := by
    have h := G.hN
    rw [show pre ++ R :: rest = (pre ++ [R]) ++ rest by simp] at h
    exact nfl_append_left h
  have hpreF := G.hpreF
  have hRC' : ∀ x β, WNF x → Lt x R → WNF β → Lt β (.K m) → Cl (.K m) β →
      (∀ f, f ∈ fr (.K m) x → Lt f β) → Lt x (r.big β) := by
    have := hRC
    unfold SeqC at this
    rwa [hd] at this
  intro b N hb _ hbT hpar
  have hbF := hb.xi.2.1
  obtain ⟨b', hb', hb'R, hsub, hle⟩ := lt_oadd_split hN hbF hbT
  obtain ⟨hβF, hβρ, -, -⟩ := htow (N + 1)
  have hβK : Lt (xiT m c pre r P (N + 1)) (.K m) := lt_transY hβF hρ hKF hβρ hρK
  have hβCl : Cl (.K m) (xiT m c pre r P (N + 1)) := Cl.of_xi hβF
  have hfr : ∀ f, f ∈ fr (.K m) b' → Lt f (xiT m c pre r P (N + 1)) := by
    intro f hf
    have hfb : f ∈ fr (.K m) b := by
      obtain ⟨u, hu, hfu⟩ := (mem_fr_iff hb').mp hf
      exact (mem_fr_iff hbF).mpr ⟨u, hsub u hu, hfu⟩
    have h2 := hpar f hfb
    rwa [he N] at h2
  have h1 := hRC' b' _ hb' hb'R hβF hβK hβCl hfr
  have hxF : WNF (r.big (xiT m c pre r P (N + 1))) := (hB.1.good.1 _ hβF hβK).1
  refine ⟨N + 1, xA c pre .zero (r.big (xiT m c pre r P (N + 1))), by omega, he (N + 1), ?_⟩
  exact lt_of_lt_of_leY hbF (wnf_oadd hpreF hxF) (wnf_oadd hpreF (wnf_nsum G.hcF (wnf_nsum WNF.zero hxF)))
    (lt_of_le_of_ltY hbF (wnf_oadd hpreF hb') (wnf_oadd hpreF hxF) hle (oadd_lt_oadd hpreF hb' hxF h1))
    (le_xA hpreF G.hcF WNF.zero hxF)

/-- 外に足す型の加数（`σ` は `K_m` より大きい目標）：`b ∈ C(b, K_m)` は塔の中に持ち上がる -/
theorem xiS_out {π σ X P c t : Tm} {m : Nat} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (H : DiagHyp .zero σ X .zero .zero pre rest R r) (hd : r.dom = .big σ) (hlt : ltB σ π = false)
    (hne : σ ≠ π) (hRC : SeqC R r) (hm : 1 ≤ m) (hKσ : Lt (.K m) σ) (hc : WNF c) (hP : WNF P) :
    XiS t (oadd (ofSummands pre) R) m (.app π (.xi m) pre R r P c) := by
  have Tw := H.tow hd hRC
  have hKF : WNF (.K m) := WNF.K' hm
  have hγF : ∀ n, WNF (gamT .zero σ pre r .zero .zero (n + 1)) := Tw.hγF
  have hKγ : Lt (.K m) (gamT .zero σ pre r .zero .zero (1 + 1)) := (Tw.hC 0).coll _ hKF (inC_K _ _ _) hKσ
  have hAF : ∀ i, WNF (oadd (ofSummands pre) (r.big (gamT .zero σ pre r .zero .zero (i + 1)))) :=
    fun i => (Tw.hC i).hA
  intro b N hb _ hbT _
  have hbF := hb.xi.2.1
  have hb1 : inC b b (gamT .zero σ pre r .zero .zero (1 + 1)) = true :=
    inC_mono_d hKF (hγF 1) (Or.inr hKγ) hbF hb.xi.2.2.2.2
  obtain ⟨n, hn⟩ := Tw.arg (N := 1) hbF hbT hb1
  have hn' := lt_of_lt_of_leY hbF (hAF n) (hAF _) hn (mono_le' hAF Tw.hAm (Nat.le_max_left n N))
  have hxF : WNF (r.big (gamT .zero σ pre r .zero .zero (max n N + 1))) := (H.tower (max n N + 1)).2.2.hx
  refine ⟨max n N + 1, xA c pre P (xT .zero σ pre r .zero .zero (max n N + 1)), by omega, ?_, ?_⟩
  · rw [app_nat_outG H (by simpa [Gen.tgt?] using hne) rfl hd hlt]
    rfl
  · exact lt_of_lt_of_leY hbF (hAF _) (wnf_oadd H.hpreF (wnf_nsum hc (wnf_nsum hP hxF))) hn'
      (le_xA H.hpreF hc hP hxF)

/-- 共終数が `ceil` 未満の加数の列の引数の共終性 -/
theorem xiB_app {c P ceil σ : Tm} {m : Nat} {pre : List Tm} {R : Tm} {r : SeqD}
    (hN : NFL (pre ++ [R])) (hc : WNF c) (hP : WNF P) (hd : r.dom = .big σ)
    (hU : BigUB R σ r) (hRC : SeqC R r) :
    ∀ b β, WNF b → Lt b (oadd (ofSummands pre) R) → WNF β → Lt β σ → Cl σ β →
      (∀ f, f ∈ fr σ b → Lt f β) → ∃ A, (SeqD.app ceil (.xi m) pre R r P c).big β = .Xi m A ∧ Lt b A := by
  have hpreF := wnf_ofSummands (nfl_append_left hN)
  have hRC' : ∀ x β, WNF x → Lt x R → WNF β → Lt β σ → Cl σ β → (∀ f, f ∈ fr σ x → Lt f β) →
      Lt x (r.big β) := by
    have := hRC
    unfold SeqC at this
    rwa [hd] at this
  intro b β hb hbT hβ hβσ hCl hfr
  obtain ⟨b', hb', hb'R, hsub, hle⟩ := lt_oadd_split hN hb hbT
  have hxF := (hU.good.1 β hβ hβσ).1
  have h1 : Lt b' (r.big β) := hRC' b' β hb' hb'R hβ hβσ hCl fun f hf => by
    obtain ⟨u, hu, hfu⟩ := (mem_fr_iff hb').mp hf
    exact hfr f ((mem_fr_iff hb).mpr ⟨u, hsub u hu, hfu⟩)
  refine ⟨xA c pre P (r.big β), rfl, ?_⟩
  exact lt_of_lt_of_leY hb (wnf_oadd hpreF hxF) (wnf_oadd hpreF (wnf_nsum hc (wnf_nsum hP hxF)))
    (lt_of_le_of_ltY hb (wnf_oadd hpreF hb') (wnf_oadd hpreF hxF) hle (oadd_lt_oadd hpreF hb' hxF h1))
    (le_xA hpreF hc hP hxF)

/-- `Ξ_m` の族の `app` の列の引数の共終性（加数 `R` の共終数で場合分け） -/
theorem xi_argS {π X q P c : Tm} {m : Nat} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Xi m q)) (G : XiG m q P c pre rest R)
    (hc0 : c = .zero → P ≠ .zero) (hRI : SeqI R r) (hRC : SeqC R r)
    (h0 : r.dom ≠ .zero) (h1 : r.dom ≠ .one) (hRsz : R.size < π.size)
    (hPπ : Lt P π) (hqσ : ∀ σ, WNF σ → Le π σ → inC q q σ = true) (hPn : P = .zero ∨ NodeT P) :
    ((SeqD.app π (.xi m) pre R r P c).dom = .omega →
      XiS (.Psi .zero π X) (oadd (ofSummands pre) R) m (.app π (.xi m) pre R r P c)) ∧
    (∀ σ, (SeqD.app π (.xi m) pre R r P c).dom = .big σ → ∀ b β, WNF b →
      Lt b (oadd (ofSummands pre) R) → WNF β → Lt β σ → Cl σ β → (∀ f, f ∈ fr σ b → Lt f β) →
      ∃ A, (SeqD.app π (.xi m) pre R r P c).big β = .Xi m A ∧ Lt b A) := by
  have hπF := ht.psi.piF
  have hN : NFL (pre ++ [R]) := by
    have h := G.hN
    rw [show pre ++ R :: rest = (pre ++ [R]) ++ rest by simp] at h
    exact nfl_append_left h
  have hRI' := hRI
  unfold SeqI at hRI'
  cases hd : r.dom with
  | zero => exact absurd hd h0
  | one => exact absurd hd h1
  | omega =>
    rw [hd] at hRI'
    have hdom : ∀ σ, r.dom ≠ .big σ := fun σ e => by
      rw [hd] at e
      cases e
    refine ⟨fun _ => xiS_nat hN G.hcF G.hPF hd (fun n => (hRI'.1.good n).1) (fun n => (hRI'.1.good n).2.2) hRC,
      fun σ hσ => ?_⟩
    rw [app_dom_nat hdom] at hσ
    cases hσ
  | big σ =>
    rw [hd] at hRI'
    obtain ⟨hBW, hBS, hreg⟩ := hRI'
    have hB : BigInv R σ r := ⟨hBW.1, hBS G.hRp⟩
    have hσF := hB.1.hσF
    by_cases hσπ : Lt σ π
    · have hd' := app_dom_big_lt (P := P) (c := c) (g := .xi m) (pre := pre) (R := R) hd (ltB_iff.mpr hσπ)
      refine ⟨fun h => ?_, fun σ' hσ' => ?_⟩
      · rw [hd'] at h
        cases h
      · rw [hd'] at hσ'
        cases hσ'
        exact xiB_app hN G.hcF G.hPF hd hB.1 hRC
    have hlt' : ltB σ π = false := by
      cases e : ltB σ π with
      | false => rfl
      | true => exact absurd (ltB_iff.mp e) hσπ
    have hdt := app_dom_big_ge (P := P) (c := c) (g := .xi m) (pre := pre) (R := R) hd hlt'
    refine ⟨fun _ => ?_, fun σ' hσ' => by rw [hdt] at hσ'; cases hσ'⟩
    rcases hreg with hσt | ⟨m', rfl⟩
    · have hne : σ ≠ π := fun e => by
        have h2 := size_le_of_mem_subs hB.1.hσs
        rw [e] at h2
        omega
      have hπσ : Le π σ := le_of_not_ltY hσF hπF hσπ
      have hρ := G.ht
      have hπρ : Le π (.Xi m q) := hc.le hπF
      -- `σ ≥ ρ`（鎖の底の補題）
      have hσρ : ¬ Lt σ (.Xi m q) := fun h => hσπ (hc.lt_base hπF hσF h fun g d hg hd' _ hn hC => by
        rcases inC_xi_iff.mp hC with h' | ⟨h1', -⟩
        · exact absurd h' hn
        · exact hB.1.hσC g d hg hd' (G.qparts h1').1)
      -- 補題 Z：`σ ≥ K_m`
      have hqρ : inC q q (.Xi m q) = true := hqσ _ hρ hπρ
      have hσC : inC σ q (.Xi m q) = true := hB.1.hσC q _ G.hqF hρ (G.qparts hqρ).1
      have hnK : ¬ Lt σ (.K m) := not_lt_K_of_inC_mi hρ (Or.inr (Or.inl ⟨m, q, rfl⟩)) (fun c e => by cases e) σ
        hσF hσC (le_of_not_ltY hσF hρ hσρ)
      have hKσ : Lt (.K m) σ := by
        rcases le_of_not_ltY hσF (WNF.K' G.hm) hnK with e | h
        · exact absurd e.symm (IsTgt.ne_K hσt m)
        · exact h
      have hqπ := hqσ π hπF (Or.inl rfl)
      have hσC' := hB.1.hσC q π G.hqF hπF (G.qparts hqπ).1
      have htσ : WNF (.Psi .zero σ q) :=
        wnf_psi0 hσF hσt G.hqF (hqσ σ hσF hπσ) fun q' hq => (arg_of_inC hq hσC' hσπ).2
      have hR0 : Lt .zero R := zero_lt G.hR0
      have H : DiagHyp .zero σ q .zero .zero pre rest R r :=
        { ht := htσ, hsum := G.hsum, hRU := hB.1, hRG := hB.2, hGF := WNF.zero
          hGσ := zero_lt hσt.ne_zero, hGs := by simp [isSucc, summands], hQF := WNF.zero, hQR := hR0
          hQσ := zero_lt hσt.ne_zero
          hI := IdxHyp.zero htσ, hξ := zero_le _ }
      exact xiS_out H hd hlt' hne hRC G.hm hKσ G.hcF G.hPF
    · have hm := G.hm
      have hm' : 1 ≤ m' := hB.1.hσF.k
      have e : m' = m := by
        have h3 : Lt π (.K m') := by
          rcases triY hπF (WNF.K' hm') with h' | h' | h'
          · exact h'
          · exact absurd h' (IsTgt.ne_K ht.psi.tgt m')
          · exact absurd h' hσπ
        have h4 : lev π ≤ m' := (lt_K_iffY hπF hm').mp h3
        have h5 : lev π = m := hc.lev_eq
        have h6 : Le (.K m') R := hB.1.hσle
        have h7 : Le R q := by
          have := le_ofSummands_of_mem (nfl_summands G.hqF) G.hRm
          rwa [ofSummands_summands q G.hqF] at this
        have h8 : Le (.K m') (succK m) :=
          le_transY (WNF.K' hm') G.hqF (WNF.succK hm) (le_transY (WNF.K' hm') G.hRF G.hqF h6 h7)
            (le_of_ne_gtY G.hqF (WNF.succK hm) G.ht.xi.2.2.2.1)
        have h9 : lev (Tm.K m') ≤ lev (succK m) := by
          rcases h8 with e' | e'
          · exact Nat.le_of_eq (congrArg lev e')
          · exact lev_le_of_lt_gen e'
        have h10 : lev (Tm.K m') = m' + 1 := rfl
        have h11 : lev (succK m) = m + 1 := rfl
        omega
      subst e
      have G0 : XiG m' q .zero c pre rest R :=
        ⟨G.ht, G.hsum, WNF.zero, zero_lt G.hR0, zero_lt (by intro e; cases e), G.hc, G.hR1⟩
      exact xiS_K ht hc G0 hc0 hd hlt' hB G.hPF hPπ hPn hRC

/-! ### 段の一歩 -/

/-- `t` より大きい目標を持つ `t` 未満の節点は、目標が `K_m` 未満か `Ξ_m(b)`（`t` の目標の階は `m`） -/
theorem xi_node_split {π X x : Tm} {m : Nat} (ht : WNF (.Psi .zero π X)) (hl : lev π = m) (hm : 1 ≤ m)
    (hx : WNF x) (hxt : Lt x (.Psi .zero π X)) (htk : Lt (.Psi .zero π X) (tgtN x)) :
    Lt (tgtN x) (.K m) ∨ ∃ b, x = .Xi m b := by
  have hkF := tgtN_wnf_lt hx htk
  have hKF : WNF (.K m) := WNF.K' hm
  have h1 := lev_le_of_lt_gen hxt
  rcases triY hkF hKF with hkK | hkK | hkK
  · exact Or.inl hkK
  · cases x with
    | Psi s k a => exact absurd hkK (IsTgt.ne_K hx.psi.tgt m)
    | Xi j b =>
      have e : Tm.K j = .K m := hkK
      cases e
      exact Or.inr ⟨b, rfl⟩
    | _ => exact absurd htk (not_lt_zero _)
  · exfalso
    have h2 := lev_le_of_lt_gen hkK
    cases x with
    | Psi s k a =>
      simp only [lev, tgtN] at h1 h2
      omega
    | Xi j b =>
      simp only [lev, tgtN] at h1 h2
      have e : j = m := by omega
      subst e
      exact Lt.irrefl _ hkK
    | _ => exact absurd htk (not_lt_zero _)

/-- 列の項 `y = Ξ_m(A)` の一歩：節点の目標で分ける -/
theorem leaf_oneX {π X A y x : Tm} {m : Nat} (ht : WNF (.Psi .zero π X)) (hl : lev π = m)
    (hy : WNF y) (hyA : y = .Xi m A)
    (hG : Gp (.Psi .zero π X) y) (hx : WNF x) (hxt : Lt x (.Psi .zero π X))
    (hpar : ∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w y) :
    Lt x y ∨ ∃ a, argR? x = some a ∧ Lt a X ∧ Lt (.Psi .zero π X) (tgtN x) ∧
      (Lt (tgtN x) (.K m) ∨ x = .Xi m a) := by
  subst hyA
  have hm : 1 ≤ m := hy.xi.1
  have C := Clo.xi hy
  have htK : Lt (.Psi .zero π X) (.K m) := (lt_K_iffY ht hm).mpr (by simp only [lev]; omega)
  have hF : ∀ w, w ∈ parF x → Lt w (.Xi m A) := fun w hw =>
    hpar w (parF_sub_parL hw)
      (lt_transY (hx.of_mem_subs (parL_sub (parF_sub_parL hw)).1) hx ht (parF_lt hx hw) hxt)
  have hk : ∀ s k a, x = .Psi s k a → Lt k (.Psi .zero π X) → Lt k (.Xi m A) := fun s k a e h =>
    hpar k (by subst e; exact List.mem_cons_self) h
  rcases node_arg' ht C htK hG hx hxt hF hk with h | ⟨a, harg, haX, -, -, htk, -⟩
  · exact Or.inl h
  rcases xi_node_split ht hl hm hx hxt htk with hkK | ⟨b, rfl⟩
  · exact Or.inr ⟨a, harg, haX, htk, Or.inl hkK⟩
  · exact Or.inr ⟨a, harg, haX, htk, Or.inr (by cases harg; rfl)⟩

/-- `Ξ` の族の列の共終性：段の節点 `Ξ_m(b)` は `b < T` なら引数の共終性、そうでなければ仮定 `hcls` -/
theorem cof_xi {π X T : Tm} {m : Nat} {s : SeqD} (ht : WNF (.Psi .zero π X)) (hl : lev π = m) (hm : 1 ≤ m)
    (hsI : SeqI (.Psi .zero π X) s)
    (hform : ∀ y, InSeq s y → ∃ A, y = .Xi m A)
    (hS : s.dom = .omega → XiS (.Psi .zero π X) T m s)
    (hB : ∀ σ, s.dom = .big σ → ∀ b β, WNF b → Lt b T → WNF β → Lt β σ → Cl σ β →
      (∀ f, f ∈ fr σ b → Lt f β) → ∃ A, s.big β = .Xi m A ∧ Lt b A)
    (hlow : ∀ x y, InSeq s y → WNF x → Lt x (.Psi .zero π X) →
      (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w y) →
      Lt (.Psi .zero π X) (tgtN x) → Lt (tgtN x) (.K m) → Lt x y)
    (hcls : ∀ x y, InSeq s y → WNF x → Lt x (.Psi .zero π X) →
      (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w y) →
      ∀ b, x = .Xi m b → Lt b T ∨ Lt x y) :
    SeqC (.Psi .zero π X) s := by
  have htK : Lt (.Psi .zero π X) (.K m) := (lt_K_iffY ht hm).mpr (by simp only [lev]; omega)
  have hxK : ∀ {x : Tm}, WNF x → Lt x (.Psi .zero π X) → Lt x (.K m) := fun hx hxt =>
    lt_transY hx ht (WNF.K' hm) hxt htK
  have hparF : ∀ {x y : Tm}, WNF x → Lt x (.Psi .zero π X) →
      (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w y) → ∀ w, w ∈ parF x → Lt w y := fun hx hxt hpar w hw =>
    hpar w (parF_sub_parL hw)
      (lt_transY (hx.of_mem_subs (parL_sub (parF_sub_parL hw)).1) hx ht (parF_lt hx hw) hxt)
  unfold SeqC
  cases hd : s.dom with
  | zero => trivial
  | one => trivial
  | omega =>
    have hNI : NatInv (.Psi .zero π X) s := by
      unfold SeqI at hsI
      rwa [hd] at hsI
    have hyF : ∀ n, WNF (s.nat n) := fun n => (hNI.1.good n).1
    have hmo : ∀ n, Lt (s.nat n) (s.nat (n + 1)) := fun n => (hNI.1.good n).2.2
    refine cof_nat hyF hmo fun x hx hxt N hpar => ?_
    obtain ⟨A, hA⟩ := hform _ (Or.inl ⟨hd, N, rfl⟩)
    rcases leaf_oneX ht hl (hyF N) hA (fun v hv hne hl' => hNI.2 N v hv hne hl') hx hxt hpar with
      h | ⟨a, harg, -, htk, hkK | rfl⟩
    · exact ⟨N, h⟩
    · exact ⟨N, hlow x _ (Or.inl ⟨hd, N, rfl⟩) hx hxt hpar htk hkK⟩
    · rcases hcls _ (s.nat N) (Or.inl ⟨hd, N, rfl⟩) hx hxt hpar a rfl with haT | h
      · obtain ⟨n, B, hNn, hB', haB⟩ := hS hd a N hx hxt haT (hparF hx hxt hpar)
        have hy := hyF n
        refine ⟨n, ?_⟩
        rw [hB'] at hy ⊢
        exact (Clo.xi hy).lt hx (hxK hx hxt) (fun w hw => by
          rw [← hB']
          exact lt_of_lt_of_leY (hx.of_mem_subs (parL_sub (parF_sub_parL hw)).1) (hyF N) (hyF n)
            (hparF hx hxt hpar w hw) (mono_le hyF hmo hNn)) fun a' e' => by
          cases e'
          exact haB
      · exact ⟨N, h⟩
  | big σ =>
    have hsI' := hsI
    unfold SeqI at hsI'
    rw [hd] at hsI'
    obtain ⟨⟨hU, -⟩, hG, -⟩ := hsI'
    have hσF := hU.hσF
    have hYF : ∀ β, WNF β → Lt β σ → WNF (s.big β) := fun β hβ hβσ => (hU.good.1 β hβ hβσ).1
    refine cof_big hσF (fun β hβ hβσ hCl => Cl.le_big hCl hU hβ hβσ) hYF
      fun x β hx hxt hβ hβσ hCl hfr hσx hpar => ?_
    have hy := hYF β hβ hβσ
    obtain ⟨A, hA⟩ := hform _ (Or.inr ⟨σ, β, hd, hβ, hβσ, rfl⟩)
    rcases leaf_oneX ht hl hy hA (fun v hv hne hl' => hG rfl β hβ hβσ v hv hne hl') hx hxt hpar with
      h | ⟨a, harg, -, htk, hkK | rfl⟩
    · exact h
    · exact hlow x _ (Or.inr ⟨σ, β, hd, hβ, hβσ, rfl⟩) hx hxt hpar htk hkK
    · rcases hcls _ (s.big β) (Or.inr ⟨σ, β, hd, hβ, hβσ, rfl⟩) hx hxt hpar a rfl with haT | h
      · obtain ⟨B, hB', haB⟩ := hB σ hd a β hx.xi.2.1 haT hβ hβσ hCl fun f hf => hfr f (by
          have h2 : ¬ Lt (.Xi m a) σ := not_lt_of_leY hσF hx hσx
          rw [fr]
          simp only [h2, ↓reduceIte]
          exact hf)
        rw [hB'] at hy ⊢
        exact (Clo.xi hy).lt hx (hxK hx hxt) (fun w hw => by
          have := hparF hx hxt hpar w hw
          rwa [hB'] at this) fun a' e' => by
            cases e'
            exact haB
      · exact h

/-! ### `Ω` の塔 -/

/-- `Ω` の塔の列の共終性：目標が `t` より大きい節点は `G` 以下か隙間、`t` 未満の `K` は `G` 以下 -/
theorem leaf_tower {π X G : Tm} (ht : WNF (.Psi .zero π X)) (hGF : WNF G)
    (hsI : SeqI (.Psi .zero π X) (.tower G))
    (hK : ∀ j, WNF (.K j) → Lt (.K j) (.Psi .zero π X) → Le (.K j) G)
    (hN : ∀ x, WNF x → Lt x (.Psi .zero π X) → Lt (.Psi .zero π X) (tgtN x) →
      Le x G ∨ SubLe (.Psi .zero π X) x) :
    SeqC (.Psi .zero π X) (.tower G) := by
  have hNI : NatInv (.Psi .zero π X) (.tower G) := hsI
  have hyF : ∀ n, WNF ((SeqD.tower G).nat n) := fun n => wnf_tower hGF (n + 1)
  have hmo : ∀ n, Lt ((SeqD.tower G).nat n) ((SeqD.tower G).nat (n + 1)) := fun n => tower_mono hGF (n + 1)
  have hG0 : ∀ n, Lt G ((SeqD.tower G).nat n) := fun n =>
    lt_of_lt_of_leY hGF (wnf_tower hGF 1) (hyF n) (tower_mono hGF 0) (mono_le hyF hmo (Nat.zero_le n))
  have hGp : ∀ n, Gp (.Psi .zero π X) ((SeqD.tower G).nat n) := fun n v hv hne hl => hNI.2 n v hv hne hl
  have hparF : ∀ {x : Tm} {N : Nat}, WNF x → Lt x (.Psi .zero π X) →
      (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w ((SeqD.tower G).nat N)) →
      ∀ w, w ∈ parF x → Lt w ((SeqD.tower G).nat N) := fun hx hxt hpar w hw =>
    hpar w (parF_sub_parL hw)
      (lt_transY (hx.of_mem_subs (parL_sub (parF_sub_parL hw)).1) hx ht (parF_lt hx hw) hxt)
  show ∀ x, WNF x → Lt x (.Psi .zero π X) → ∃ n, Lt x ((SeqD.tower G).nat n)
  refine cof_nat hyF hmo fun x hx hxt N hpar => ?_
  have hle : ∀ {x : Tm}, WNF x → Le x G → ∃ n, Lt x ((SeqD.tower G).nat n) := fun hx h =>
    ⟨0, lt_of_le_of_ltY hx hGF (hyF 0) h (hG0 0)⟩
  -- 節点
  have hnode : ∀ s k a, x = .Psi s k a → ∃ n, Lt x ((SeqD.tower G).nat n) := by
    intro s k a e
    subst e
    have hP := hx.psi
    by_cases htk : Lt (.Psi .zero π X) k
    · rcases hN _ hx hxt htk with h | h
      · exact hle hx h
      · exact ⟨N, h.lt ht hx (hyF N) (hGp N)⟩
    · have hkt : Lt k (.Psi .zero π X) := by
        rcases le_of_not_ltY ht hP.piF htk with e | h
        · exact absurd (e ▸ hP.tgt) (fun h => not_tgt_psi0 h)
        · exact h
      have hk := hpar k List.mem_cons_self hkt
      exact ⟨N, lt_transY hx hP.piF (hyF N) (lt_psi_targetY hx) hk⟩
  cases x with
  | zero => exact ⟨0, lt_of_le_of_ltY WNF.zero hGF (hyF 0) (zero_le _) (hG0 0)⟩
  | one => exact ⟨0, one_lt_om (hyF 0)⟩
  | K j => exact hle hx (hK j hx hxt)
  | plus a b =>
    have ha := hparF hx hxt hpar a (by simp [parF])
    exact ⟨N, (lt_plus_prin_iffY hx rfl).mpr ha⟩
  | Om e =>
    have heF := hx.om.1
    have he := hparF hx hxt hpar e (by simp [parF])
    refine ⟨N + 1, ?_⟩
    show Lt (.Om e) (.Om (succT (tower G (N + 1))))
    exact (lt_om_iffY heF (succT_WNF (hyF N))).mpr (lt_transY heF (hyF N) (succT_WNF (hyF N)) he (lt_succT _))
  | Xi j b =>
    have hj := hx.xi.1
    have hKF := WNF.K' hj
    have hxK : Lt (.Xi j b) (.K j) := (lt_K_iffY hx hj).mpr (Nat.le_refl _)
    by_cases htk : Lt (.Psi .zero π X) (.K j)
    · rcases hN _ hx hxt htk with h | h
      · exact hle hx h
      · exact ⟨N, h.lt ht hx (hyF N) (hGp N)⟩
    · have hKt : Lt (.K j) (.Psi .zero π X) := by
        rcases le_of_not_ltY ht hKF htk with e | h
        · cases e
        · exact h
      obtain ⟨n, hn⟩ := hle hKF (hK j hKF hKt)
      exact ⟨n, lt_transY hx hKF (hyF n) hxK hn⟩
  | Psi s k a => exact hnode s k a rfl

end RTKA.Fund
