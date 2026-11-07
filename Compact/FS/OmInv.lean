import Compact.FS.Start

/-! 崩壊 `t = Ψ^0_π(X)` の、`app` 型の列の不変量。加数の種類をまとめて扱う。

加数 `R` の列の共終数で分ける（`g` は `ψ`・Mahlo 型の生成、`c` は有効性の調整、`P` は種）：

* `ω`：`t[n] = Ψ^ξ_π(pre ⊕ ((c + R[n]) # P))`（`appPack_nat`）。
* `σ > π`（`K_m` でない）：添字が塔の対角化、種は外（`appPack_out`）。
* `σ = π`：目標そのものへの対角化、種は 0 番目の近似の中（`appPack_in`）。
* `σ < π`：`t` の共終数も `σ`（`bigUB_app`）。

`AppPack` は `ω` 型の `t` の列について、隙間の証明に要る形（近似の族）をまとめたもの。 -/

namespace RTKA.Fund

open Tm W

/-- `C(g, d)` は `d` について単調 -/
theorem inC_mono_d {g d d' : Tm} (hd : WNF d) (hd' : WNF d') (hle : Le d d') :
    ∀ {x : Tm}, WNF x → inC x g d = true → inC x g d' = true
  | .zero, _, _ => inC_zero _ _
  | .one, _, _ => inC_one _ _
  | .K _, _, _ => inC_K _ _ _
  | .plus a b, hx, h => by
    obtain ⟨ha, hb, -, -⟩ := hx.plus
    rw [inC_plus, Bool.and_eq_true] at h ⊢
    exact ⟨inC_mono_d hd hd' hle ha h.1, inC_mono_d hd hd' hle hb h.2⟩
  | .Om a, hx, h => by
    rw [inC_om] at h ⊢
    exact inC_mono_d hd hd' hle hx.om.1 h
  | .Xi n a, hx, h => by
    rcases inC_xi_iff.mp h with h1 | ⟨h1, h2⟩
    · exact inC_xi_iff.mpr (Or.inl (lt_of_lt_of_leY hx hd hd' h1 hle))
    · exact inC_xi_iff.mpr (Or.inr ⟨inC_mono_d hd hd' hle hx.xi.2.1 h1, h2⟩)
  | .Psi s k a, hx, h => by
    rcases inC_psi_iff.mp h with h1 | ⟨h1, h2, h3, h4⟩
    · exact inC_psi_iff.mpr (Or.inl (lt_of_lt_of_leY hx hd hd' h1 hle))
    · have hP := hx.psi
      exact inC_psi_iff.mpr (Or.inr ⟨inC_mono_d hd hd' hle hP.piF h1,
        inC_mono_d hd hd' hle hP.xiF h2, inC_mono_d hd hd' hle hP.aF h3, h4⟩)

/-- 引数の下限のある項が `d` 未満でなく `C(g, d)` に入るなら、引数は `C(g, d)` に入り `g` 未満 -/
theorem arg_of_inC {σ q g d : Tm} (hq : argR? σ = some q) (h : inC σ g d = true) (hnd : ¬ Lt σ d) :
    inC q g d = true ∧ Lt q g := by
  cases σ with
  | Xi n p =>
    simp only [argR?, Option.some.injEq] at hq
    subst hq
    rcases inC_xi_iff.mp h with h' | h'
    · exact absurd h' hnd
    · exact h'
  | Psi ζ κ b =>
    simp only [argR?, Option.some.injEq] at hq
    subst hq
    rcases inC_psi_iff.mp h with h' | ⟨-, -, h1, h2⟩
    · exact absurd h' hnd
    · exact ⟨h1, h2⟩
  | _ => simp [argR?] at hq

/-- 近似の 1 点が `t` 未満の部分項を越える -/
theorem gap_point {ξ π X P : Tm} {pre rest : List Tm} {R x v : Tm}
    (H : Approx1 ξ π X P pre rest R x)
    (hx0 : x = .zero → ∀ v, v ∈ subs R → v = R)
    (hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v x)
    (hF : ∀ f, f ∈ fr π X → Lt f (.Psi ξ π (approx pre P x)))
    (hrest : ∀ s, s ∈ rest → ∀ w, w ∈ subs s → Lt w (.Psi .zero π X) →
      Lt w (.Psi ξ π (approx pre P x)))
    (hv : v ∈ subs (.Psi .zero π X)) (hne : v ≠ .Psi .zero π X)
    (hlt : Lt v (.Psi .zero π X)) : Lt v (.Psi ξ π (approx pre P x)) := by
  refine gap_of_arg_gen H.ht H.hnf (fun u hu h => ?_) hv hne hlt
  refine lt_of_summands_sub H.hX H.ht rfl (by intro e; cases e) (fun s hs w hw hl => ?_) hu h
  rw [H.hsum] at hs
  rcases List.mem_append.mp hs with hs | hs
  · exact H.lt_of_sub_summand hx0 hgap hF (Or.inl hs) hw hl
  · rcases List.mem_cons.mp hs with rfl | hs
    · exact H.lt_of_sub_summand hx0 hgap hF (Or.inr rfl) hw hl
    · exact hrest s hs w hw hl

/-- `ω` 型の `t` の列の、近似の族 -/
structure AppPack (ξ π X P : Tm) (pre rest : List Tm) (R : Tm) (s : SeqD) : Prop where
  L : NatL π s
  /-- 上界（成分が `C(g, d)` に入るとき） -/
  ubC : ∀ g d n, WNF g → WNF d → Le d π → inC π g d = true → inC R g d = true →
    inC (ofSummands pre) g d = true → Le (oadd (ofSummands pre) R) g → inC P g d = true →
    inC ξ g d = true → inC (s.nat n) g d = true
  ex : ∃ (P' : Tm) (x : Nat → Tm), (P' = P ∨ P' = .zero) ∧
    (∀ n, s.nat n = .Psi ξ π (approx pre P' (x n))) ∧
    (∀ n, Approx1 ξ π X P' pre rest R (x n)) ∧
    (∀ n, x n = .zero → ∀ v, v ∈ subs R → v = R) ∧
    (∀ n v, v ∈ subs R → v ≠ R → Lt v R → Lt v (x n))
  hseed : P ∈ fr π P → ∀ n, Lt P (s.nat n)

/-- 一つずらした列 -/
theorem AppPack.shift {ξ π X P : Tm} {pre rest : List Tm} {R : Tm} {s : SeqD}
    (pk : AppPack ξ π X P pre rest R s) : AppPack ξ π X P pre rest R (.shift s) := by
  obtain ⟨P', x, hP', he, A, hx0, hgap⟩ := pk.ex
  exact ⟨pk.L.shift, fun g d n => pk.ubC g d (n + 1), ⟨P', fun n => x (n + 1), hP', fun n => he (n + 1),
    fun n => A (n + 1), fun n => hx0 (n + 1), fun n => hgap (n + 1)⟩, fun hp n => pk.hseed hp (n + 1)⟩

/-- 種・添字の上界から `t` の不変量 -/
theorem AppPack.ub {ξ π X P : Tm} {pre rest : List Tm} {R : Tm} {s : SeqD}
    (pk : AppPack ξ π X P pre rest R s) (hPF : WNF P) (hξF : WNF ξ)
    (hPt : Lt P (.Psi .zero π X)) (hξt : Lt ξ (.Psi .zero π X))
    (hPC : ∀ g d, WNF g → WNF d → inC (.Psi .zero π X) g d = true → inC P g d = true)
    (hU : ∀ g d, WNF g → WNF d → inC (.Psi .zero π X) g d = true → inC ξ g d = true) :
    NatUB (.Psi .zero π X) s := by
  obtain ⟨_, _, _, _, A, _, _⟩ := pk.ex
  have H := A 0
  have ht := H.ht
  have hX := ht.psi.aF
  have hπF := ht.psi.piF
  have hTF := wnf_oadd H.hpreF H.hRF
  have hXt : inC X X (.Psi .zero π X) = true :=
    inC_of_fr_lt hX hπF ht hX hX ht.psi.Ca (Or.inr (lt_psi_targetY ht)) (Or.inl rfl)
      fun w hw => FWOrder.k2 ht w hw
  have hlt : ∀ n, Lt (s.nat n) (.Psi .zero π X) := fun n =>
    coll_psiY ht _ (pk.L.good n).1
      (pk.ubC X _ n hX ht (Or.inr (lt_psi_targetY ht)) (inC_tgt_of_k2t ht fun w hw => FWOrder.k2t ht w hw)
        (inC_of_mem_summands hX hXt H.hRm) (inC_pre_of_X hX H.hsum hXt) (top_le hX H.hsum)
        (WFY.inC_of_ltY _ hPF ht hPt) (WFY.inC_of_ltY _ hξF ht hξt)) (pk.L.good n).2.1
  refine (pk.L.lower hlt).toUB fun g d n hg hd h => ?_
  have hF := (pk.L.good n).1
  by_cases hdt : Lt (.Psi .zero π X) d
  · exact WFY.inC_of_ltY _ hF hd (lt_transY hF ht hd (hlt n) hdt)
  obtain ⟨hle, hk, hδ, hlt'⟩ := comp_of_inC ht hd hdt h
  exact pk.ubC g d n hg hd hle hk (inC_of_mem_summands hX hδ H.hRm) (inC_pre_of_X hX H.hsum hδ)
    (Or.inr (lt_of_le_of_ltY hTF hX hg (top_le hX H.hsum) hlt'))
    (hPC g d hg hd h) (hU g d hg hd h)

/-- 調整つきの `x` の隙間 -/
theorem adj_gap {c y R : Tm} (hc : WNF c) (hy : WNF y) (hRF : WNF R)
    (hg : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v y) :
    ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v (oadd c y) := fun v hv hne hlt =>
  lt_of_lt_of_leY (hRF.of_mem_subs hv) hy (wnf_oadd hc hy) (hg v hv hne hlt) (le_oadd_right hc hy)

theorem adj_zero {c y R : Tm} (hc : WNF c) (hy : WNF y)
    (h0 : y = .zero → ∀ v, v ∈ subs R → v = R) :
    oadd c y = .zero → ∀ v, v ∈ subs R → v = R := fun e => by
  have h1 := le_oadd_right hc hy
  rw [e] at h1
  rcases h1 with h1 | h1
  · exact h0 h1
  · exact absurd h1 (not_lt_zero _)

/-- 内側の族から近似の列の族 -/
theorem appPack_of_inner {ξ π X P c : Tm} {pre rest : List Tm} {R : Tm} {x : Nat → Tm} {s : SeqD}
    (I : Inner P c pre R x) (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (S : SeedHyp π X P R) (adj : AdjHyp π R c)
    (hV : ∀ q, argR? π = some q → Lt q (approx pre P (oadd c (x 0))))
    (hI : IdxHyp ξ π X) (hξ : Le ξ (ofSummands pre))
    (he : ∀ n, s.nat n = .Psi ξ π (approx pre P (oadd c (x n)))) :
    AppPack ξ π X P pre rest R s := by
  have F := fam_inner I ht hsum S adj hV hI hξ
  have hN : NFL (pre ++ R :: rest) := hsum ▸ nfl_summands ht.psi.aF
  have hRF : WNF R := (hN.1 R (List.mem_append_right _ List.mem_cons_self)).1
  exact
    { L := natL_of_fam F he
      ubC := fun g d n hg hd hle hk hRC hpre hT hP hz => F.ubC he hg hd hle hk hRC hpre hT hP hz n
      ex := ⟨P, fun n => oadd c (x n), Or.inl rfl, he, F.A,
        fun n => adj_zero adj.hF (I.hx n) (I.zero n),
        fun n => adj_gap adj.hF (I.hx n) hRF (I.gap n)⟩
      hseed := fun hp n => by
        rw [he n]
        exact (F.A n).hseed hp }

/-- 共終数 `ω` の加数 -/
theorem appPack_nat {ξ π X P c ceil : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ π) (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (S : SeedHyp π X P R) (adj : AdjHyp π R c)
    (hV : ∀ q, argR? π = some q → Lt q (approx pre P (oadd c (r.nat 0))))
    (hI : IdxHyp ξ π X) (hξ : Le ξ (ofSummands pre))
    (hdom : ∀ σ, r.dom ≠ .big σ) (hR : NatInv R r) :
    AppPack ξ π X P pre rest R (.app ceil g pre R r P c) :=
  appPack_of_inner (inner_nat hR) ht hsum S adj hV hI hξ fun n => by
    rw [app_nat_of_not_big hdom n, hg.comb, hg.ap]

theorem ltB_self (c : Tm) : ltB c c = false := by
  simp [ltB, cmp_self]

/-- 共終数 `σ ≠ π`（`K_m` でない）の加数：種を外に足す対角化。`Ψ^0_σ(X)` が標準形であることを仮定する -/
theorem appPack_diag {ξ π σ X P c ceil : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ π) (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (S : SeedHyp π X P R) (adj : AdjHyp π R c) (hσt : IsTgt σ) (htσ : WNF (.Psi .zero σ X))
    (hV : ∀ q, argR? π = some q → Lt q (approx pre P (oadd c (r.big .zero))))
    (hI : IdxHyp ξ π X) (hξ : Le ξ (ofSummands pre))
    (hd : r.dom = .big σ) (hlt : ltB σ ceil = false) (hne : σ ≠ π) (hR : BigInv R σ r) :
    AppPack ξ π X P pre rest R (.app ceil g pre R r P c) := by
  have hX := ht.psi.aF
  have hN : NFL (pre ++ R :: rest) := hsum ▸ nfl_summands hX
  have hpreF := wnf_ofSummands (nfl_append_left hN)
  have hR0 : Lt .zero R := lt_of_le_of_ltY WNF.zero S.hPF
    (hX.of_mem_subs (mem_subs_of_mem_summands (by
      rw [hsum]
      exact List.mem_append_right _ List.mem_cons_self))) (zero_le _) S.hPR
  have hσF := hR.1.hσF
  obtain ⟨hGF, hGσ, hGs, hGC⟩ := sStart_spec (T := oadd (ofSummands pre) R) hσF hσt.ne_zero adj.hF S.hPF
  have H : DiagHyp .zero σ X (sStart σ (oadd (ofSummands pre) R) c P) .zero pre rest R r :=
    { ht := htσ, hsum, hRU := hR.1, hRG := hR.2, hGF, hGσ, hGs, hQF := WNF.zero, hQR := hR0
      hQσ := zero_lt hσt.ne_zero
      hI := IdxHyp.zero htσ, hξ := zero_le _ }
  have hV' : ∀ q, argR? π = some q → Lt q (approx pre P (oadd c
      (xT .zero σ pre r (sStart σ (oadd (ofSummands pre) R) c P) .zero 0))) := fun q hq => by
    have h0F := (hR.1.good.1 .zero WNF.zero (zero_lt hσt.ne_zero)).1
    have hxG := (hR.1.good.1 _ hGF hGσ).1
    rw [H.xT_eq 0]
    show Lt q (approx pre P (oadd c (r.big (sStart σ (oadd (ofSummands pre) R) c P))))
    by_cases hG0 : sStart σ (oadd (ofSummands pre) R) c P = .zero
    · rw [hG0]
      exact hV q hq
    · have h1 := hR.1.good.2 .zero _ WNF.zero hGF (zero_lt hG0) hGσ
      exact lt_transY (wnf_of_argR ht.psi.piF hq) (wnf_oadd hpreF (wnf_nsum (wnf_oadd adj.hF h0F) S.hPF))
        (wnf_oadd hpreF (wnf_nsum (wnf_oadd adj.hF hxG) S.hPF)) (hV q hq)
        (approx_mono hpreF (wnf_oadd adj.hF h0F) (wnf_oadd adj.hF hxG) S.hPF
          (oadd_lt_oadd adj.hF h0F hxG h1))
  exact appPack_of_inner (H.inner_out adj.hF S.hPF S.hPs hGC) ht hsum S adj hV' hI hξ
    (app_nat_out (P := P) (c := c) hg H hne rfl hd hlt)

/-- 共終数 `σ > π`（`K_m` でない）の加数：種を外に足す対角化 -/
theorem appPack_out {ξ π σ X P c ceil : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ π) (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (S : SeedHyp π X P R) (adj : AdjHyp π R c) (hσt : IsTgt σ)
    (hV : ∀ q, argR? π = some q → Lt q (approx pre P (oadd c (r.big .zero))))
    (hI : IdxHyp ξ π X) (hξ : Le ξ (ofSummands pre))
    (hd : r.dom = .big σ) (hlt : ltB σ ceil = false) (hπσ : Lt π σ) (hR : BigInv R σ r) :
    AppPack ξ π X P pre rest R (.app ceil g pre R r P c) := by
  have hP := ht.psi
  have hσF := hR.1.hσF
  have hne : σ ≠ π := fun e => by
    rw [e] at hπσ
    exact Lt.irrefl _ hπσ
  have hRm : R ∈ summands X := by
    rw [hsum]
    exact List.mem_append_right _ List.mem_cons_self
  have hRC := inC_of_mem_summands hP.aF hP.Ca hRm
  have hσC := hR.1.hσC X π hP.aF hP.piF hRC
  have htσ : WNF (.Psi .zero σ X) :=
    wnf_psi0 hσF hσt hP.aF (inC_mono_d hP.piF hσF (Or.inr hπσ) hP.aF hP.Ca)
      (fun q hq => (arg_of_inC hq hσC (Lt.asymmY hP.piF hσF hπσ)).2)
  exact appPack_diag hg ht hsum S adj hσt htσ hV hI hξ hd hlt hne hR

/-- 共終数が目標そのものの加数 -/
theorem appPack_in {ξ π X P ceil : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ π) (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (S : SeedHyp π X P R) (hI : IdxHyp ξ π X) (hξ : Le ξ (ofSummands pre))
    (hd : r.dom = .big π) (hlt : ltB π ceil = false) (hR : BigInv R π r) :
    AppPack ξ π X P pre rest R (.app ceil g pre R r P .zero) := by
  have H : DiagHyp ξ π X .zero P pre rest R r :=
    { ht, hsum, hRU := hR.1, hRG := hR.2, hGF := WNF.zero, hGσ := zero_lt ht.psi.tgt.ne_zero
      hGs := by simp [isSucc, summands]
      hQF := S.hPF, hQR := S.hPR, hQσ := S.hPπ, hI, hξ }
  have he := app_nat_in hg H hd hlt
  have hU := H.natL_in he
  refine ⟨hU, fun g d n hg' hd' _ _ hRC hpre hT hP hz => ?_,
    ⟨.zero, xT ξ π pre r .zero P, Or.inr rfl, fun n => by rw [he n, gamT_succ],
    fun n => (H.tower n).2.2, H.x_zero, H.x_gap⟩, fun hp n => ?_⟩
  · rw [he n]
    exact (H.xT_inC_T hg' hd' hRC hpre hT (inC_zero _ _) hP hz (n + 1)).1
  have Ha := (H.tower 0).2.2
  have h0 : Lt P (gamT ξ π pre r .zero P 1) := by
    rw [gamT_succ]
    exact FWOrder.k2 Ha.hnf P (Ha.fr_approx_of_x (fr_nsum_of_right H.h0F H.hQF hp))
  have hm := le_of_mono (y := fun k => (SeqD.app ceil g pre R r P .zero).nat k)
    (fun k => (hU.good k).1) (fun k => (hU.good k).2.2) n
  have h1 : Lt P ((SeqD.app ceil g pre R r P .zero).nat 0) := by
    rw [he 0]
    exact h0
  exact lt_of_lt_of_leY S.hPF (hU.good 0).1 (hU.good n).1 h1 hm

/-- 共終数が目標未満の加数の、添字 `η` の近似の仮定 -/
theorem approx1_big {ξ π σ X P c : Tm} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (S : SeedHyp π X P R) (adj : AdjHyp π R c)
    (hV : ∀ q, argR? π = some q → Lt q (approx pre P (oadd c (r.big .zero))))
    (hI : IdxHyp ξ π X) (hξ : Le ξ (ofSummands pre))
    (hdc : Lt σ π) (hσ0 : Lt .zero σ) (hR : BigInv R σ r) {η : Tm}
    (hη : WNF η) (hησ : Lt η σ) : Approx1 ξ π X P pre rest R (oadd c (r.big η)) := by
  have hP := ht.psi
  have hX := hP.aF
  have hπF := hP.piF
  have hσF := hR.1.hσF
  have hyF := (hR.1.good.1 η hη hησ).1
  have hyR := (hR.1.good.1 η hη hησ).2
  have hxF := wnf_oadd adj.hF hyF
  have hηπ := lt_transY hη hσF hπF hησ hdc
  have hRm : R ∈ summands X := by
    rw [hsum]
    exact List.mem_append_right _ List.mem_cons_self
  have hRF := hX.of_mem_subs (mem_subs_of_mem_summands hRm)
  have hRp := nfl_principal (nfl_summands hX) R hRm
  have hN : NFL (pre ++ R :: rest) := hsum ▸ nfl_summands hX
  have hpreF := wnf_ofSummands (nfl_append_left hN)
  have hxR : Lt (oadd c (r.big η)) R := oadd_lt_prin adj.hF hyF hRp adj.hR hyR
  have hy0F := (hR.1.good.1 .zero WNF.zero hσ0).1
  have hr : ∀ q, argR? π = some q → Lt q (approx pre P (oadd c (r.big η))) := fun q hq => by
    by_cases h0 : η = .zero
    · rw [h0]
      exact hV q hq
    · exact lt_transY (wnf_of_argR hπF hq) (wnf_oadd hpreF (wnf_nsum (wnf_oadd adj.hF hy0F) S.hPF))
        (wnf_oadd hpreF (wnf_nsum hxF S.hPF)) (hV q hq)
        (approx_mono hpreF (wnf_oadd adj.hF hy0F) hxF S.hPF
          (oadd_lt_oadd adj.hF hy0F hyF (hR.1.good.2 .zero η WNF.zero hη (zero_lt h0) hησ)))
  have hAF := wnf_oadd hpreF (wnf_nsum hxF S.hPF)
  exact
    { ht, hsum, hx := hxF, hxR, hPF := S.hPF, hPR := S.hPR, hPπ := S.hPπ
      hI, hξA := le_transY hI.hF hpreF hAF hξ (le_oadd_left hpreF (wnf_nsum hxF S.hPF))
      hr := hr
      hCx := inC_approx_of_ub ht hsum hxF (adj_zero adj.hF hyF (hR.1.pos η hη hησ)) hxR S.hPF S.hPR hr
        (fun hRA hπA => by
          refine inC_oadd adj.hF hyF (adj.hU _ _ hπF (Or.inl rfl) hπA) ?_
          by_cases hy0 : r.big η = .zero
          · rw [hy0]
            exact inC_zero _ _
          · have hx0 : oadd c (r.big η) ≠ .zero := fun e => by
              have h1 := le_oadd_right adj.hF hyF
              rw [e] at h1
              rcases h1 with h1 | h1
              · exact hy0 h1
              · exact absurd h1 (not_lt_zero _)
            exact hR.1.ub _ _ η hAF hπF hη hησ (approx_pos hpreF hxF S.hPF hx0)
              (Or.inl (Or.inr hdc)) hRA (WFY.inC_of_ltY _ hη hπF hηπ))
        (adj_gap adj.hF hyF hRF (hR.2 η hη hησ)) }

/-- 共終数が目標未満の加数の列の、`t` によらない性質 -/
structure BigPack (ξ π σ X P : Tm) (pre rest : List Tm) (R : Tm) (s : SeqD) : Prop where
  good : BigGood π σ s
  pos : ∀ η, WNF η → Lt η σ → s.big η ≠ .zero
  /-- 列の項は `π` への崩壊 -/
  psi : ∀ η, ∃ A, s.big η = .Psi ξ π A
  /-- 上界（成分が `C(g, d)` に入るとき） -/
  ubC : ∀ g d η, WNF g → WNF d → WNF η → Lt η σ → Lt .zero g → BigOK σ g d → Le d π →
    inC π g d = true → inC R g d = true → inC (ofSummands pre) g d = true →
    Le (oadd (ofSummands pre) R) g → inC P g d = true → inC ξ g d = true → inC η g d = true →
    inC (s.big η) g d = true
  ub2 : ∀ g d η₁ η₂, WNF g → WNF d → WNF η₁ → WNF η₂ → Lt η₁ η₂ → Lt η₂ σ →
    inC (s.big η₂) g d = true → inC η₁ g d = true → inC (s.big η₁) g d = true
  lo : ∀ g d η, WNF d → WNF η → Lt η σ → inC (s.big η) g d = true → inC η g d = true
  ns : ∀ η, WNF η → Lt η σ → ¬ isSucc η = true → ¬ isSucc (s.big η) = true

/-- 共終数が目標未満の加数：近似の族の性質。`σ` が近似の崩壊未満であることを仮定する -/
theorem bigPack_app {ξ π σ X P c ceil : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ π) (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (S : SeedHyp π X P R) (adj : AdjHyp π R c)
    (hV : ∀ q, argR? π = some q → Lt q (approx pre P (oadd c (r.big .zero))))
    (hI : IdxHyp ξ π X) (hξ : Le ξ (ofSummands pre))
    (hdc : Lt σ π) (hσ0 : Lt .zero σ) (hR : BigInv R σ r)
    (hσy : ∀ η, WNF η → Lt η σ → Lt σ (.Psi ξ π (approx pre P (oadd c (r.big η))))) :
    BigPack ξ π σ X P pre rest R (.app ceil g pre R r P c) := by
  have hP := ht.psi
  have hπF := hP.piF
  have hσF := hR.1.hσF
  have hR1 := hR.1
  have hX := hP.aF
  have A := fun {η : Tm} (hη : WNF η) (hησ : Lt η σ) =>
    approx1_big ht hsum S adj hV hI hξ hdc hσ0 hR hη hησ
  have he : ∀ η, WNF η → Lt η σ → (SeqD.app ceil g pre R r P c).big η =
      .Psi ξ π (approx pre P (oadd c (r.big η))) := fun η _ _ => by
    show g.ap (combine g pre c P (r.big η)) = _
    rw [hg.comb, hg.ap]
  have hyF : ∀ η, WNF η → Lt η σ → WNF (r.big η) := fun η hη hησ => (hR1.good.1 η hη hησ).1
  have hS2 : ∀ {η₁ η₂ g' d : Tm}, WNF η₁ → WNF η₂ → Lt η₁ η₂ → Lt η₂ σ → WNF g' → WNF d → Le d π →
      inC π g' d = true → inC η₁ g' d = true → inC (oadd c (r.big η₂)) g' d = true →
      inC (oadd c (r.big η₁)) g' d = true := by
    intro η₁ η₂ g' d h₁ h₂ hlt h₂σ hg' hd hdπ hπC hC h'
    have h₁σ := lt_transY h₁ h₂ hσF hlt h₂σ
    exact inC_oadd adj.hF (hyF η₁ h₁ h₁σ) (adj.hU g' d hd hdπ hπC)
      (hR1.ub2 g' d η₁ η₂ hg' hd h₁ h₂ hlt h₂σ (inC_of_oadd_right adj.hF (hyF η₂ h₂ h₂σ) h') hC)
  have hmono : ∀ η₁ η₂, WNF η₁ → WNF η₂ → Lt η₁ η₂ → Lt η₂ σ →
      Lt (.Psi ξ π (approx pre P (oadd c (r.big η₁)))) (.Psi ξ π (approx pre P (oadd c (r.big η₂)))) := by
    intro η₁ η₂ h₁ h₂ hlt h₂σ
    have h₁σ := lt_transY h₁ h₂ hσF hlt h₂σ
    have H₁ := A h₁ h₁σ
    have H₂ := A h₂ h₂σ
    have hu := H₂.hnf
    exact H₁.hltS H₂ (oadd_lt_oadd adj.hF (hyF η₁ h₁ h₁σ) (hyF η₂ h₂ h₂σ) (hR1.good.2 η₁ η₂ h₁ h₂ hlt h₂σ))
      (fun h => hS2 h₁ h₂ hlt h₂σ H₂.hAF hu (Or.inr (lt_psi_targetY hu))
        (inC_tgt_of_k2t hu fun w hw => FWOrder.k2t hu w hw)
        (WFY.inC_of_ltY _ h₁ hu (lt_transY h₁ hσF hu h₁σ (hσy η₂ h₂ h₂σ))) h)
      (fun h => hS2 h₁ h₂ hlt h₂σ H₂.hAF hπF (Or.inl rfl)
        (inC_tgt hπF hP.tgt H₂.hAF H₂.hr)
        (WFY.inC_of_ltY _ h₁ hπF (lt_transY h₁ hσF hπF h₁σ hdc)) h)
  refine
    { good := ⟨fun η hη hησ => ?_, fun η₁ η₂ h₁ h₂ hlt hησ => ?_⟩
      pos := fun η hη hησ e => ?_
      psi := fun η => ⟨approx pre P (oadd c (r.big η)), by
        show g.ap (combine g pre c P (r.big η)) = _
        rw [hg.comb, hg.ap]⟩
      ubC := fun g' e η hg' he' hη hησ h0 hok hle' hk hRC hpre hT hPC hz hηC => ?_
      ub2 := fun g' e η₁ η₂ hg' he' h₁ h₂ hlt hησ h hηC => ?_
      lo := fun g' e η he' hη hησ h => ?_
      ns := fun η hη hησ _ => ?_ }
  · rw [he η hη hησ]
    exact ⟨(A hη hησ).hnf, lt_psi_targetY (A hη hησ).hnf⟩
  · rw [he η₁ h₁ (lt_transY h₁ h₂ hσF hlt hησ), he η₂ h₂ hησ]
    exact hmono η₁ η₂ h₁ h₂ hlt hησ
  · rw [he η hη hησ] at e
    cases e
  · rw [he η hη hησ]
    have H := A hη hησ
    exact H.inC_node hk hz hpre (inC_oadd adj.hF (hyF η hη hησ) (adj.hU g' e he' hle' hk)
      (hR1.ub g' e η hg' he' hη hησ h0 hok hRC hηC)) hPC
      (lt_of_lt_of_leY H.hAF (wnf_oadd H.hpreF H.hRF) hg' H.hAtop hT)
  · have h₁σ := lt_transY h₁ h₂ hσF hlt hησ
    rw [he η₂ h₂ hησ] at h
    rw [he η₁ h₁ h₁σ]
    exact (A h₁ h₁σ).hubS (A h₂ hησ)
      (oadd_lt_oadd adj.hF (hyF η₁ h₁ h₁σ) (hyF η₂ h₂ hησ) (hR1.good.2 η₁ η₂ h₁ h₂ hlt hησ))
      (hmono η₁ η₂ h₁ h₂ hlt hησ) g' e hg' he'
      (fun hle' h' hk _ _ _ => hS2 h₁ h₂ hlt hησ hg' he' hle' hk hηC h') h
  · rw [he η hη hησ] at h
    have Hη := A hη hησ
    rcases inC_psi_iff.mp h with h' | ⟨-, -, hδ, -⟩
    · exact WFY.inC_of_ltY _ hη he' (lt_transY hη hσF he' hησ
        (lt_transY hσF Hη.hnf he' (hσy η hη hησ) h'))
    · have hy : inC (nsum (oadd c (r.big η)) P) g' e = true :=
        (inC_iff_summands Hη.hy).mpr fun s hs =>
          inC_of_mem_summands Hη.hAF hδ (mem_summands_oadd_right Hη.hpreF Hη.hy hs)
      exact hR1.lo g' e η he' hη hησ
        (inC_of_oadd_right adj.hF (hyF η hη hησ) (inC_nsum_left Hη.hx S.hPF hy))
  · rw [he η hη hησ, isSucc_principal rfl]
    simp

/-- 共終数が目標未満の加数：`t` の列の不変量（隙間を除く） -/
theorem bigUB_app {ξ π σ X P c ceil : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ π) (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (S : SeedHyp π X P R) (adj : AdjHyp π R c)
    (hV : ∀ q, argR? π = some q → Lt q (approx pre P (oadd c (r.big .zero))))
    (hI : IdxHyp ξ π X) (hξ : Le ξ (ofSummands pre))
    (hdc : Lt σ π) (hσ0 : Lt .zero σ) (hR : BigInv R σ r)
    (hσy : ∀ η, WNF η → Lt η σ → Lt σ (.Psi ξ π (approx pre P (oadd c (r.big η)))))
    (hPt : Lt P (.Psi .zero π X)) (hξt : Lt ξ (.Psi .zero π X))
    (hPC : ∀ g d, WNF g → WNF d → inC (.Psi .zero π X) g d = true → inC P g d = true)
    (hU : ∀ g d, WNF g → WNF d → inC (.Psi .zero π X) g d = true → inC ξ g d = true) :
    BigUB (.Psi .zero π X) σ (.app ceil g pre R r P c) := by
  have B := bigPack_app (ceil := ceil) hg ht hsum S adj hV hI hξ hdc hσ0 hR hσy
  have hP := ht.psi
  have hπF := hP.piF
  have hσF := hR.1.hσF
  have hR1 := hR.1
  have hX := hP.aF
  have hRm : R ∈ summands X := by
    rw [hsum]
    exact List.mem_append_right _ List.mem_cons_self
  have hRF := hX.of_mem_subs (mem_subs_of_mem_summands hRm)
  have hle : Le (.Psi .zero π X) π := Or.inr (lt_psi_targetY ht)
  have hRt : inC R X (.Psi .zero π X) = true :=
    inC_of_fr_lt hRF hπF ht hX hX (inC_of_mem_summands hX hP.Ca hRm) hle (Or.inl rfl) fun w hw =>
      FWOrder.k2 ht w ((mem_fr_iff hX).mpr ⟨R, hRm, hw⟩)
  have hσt : Lt σ (.Psi .zero π X) := coll_psiY ht σ hσF (hR1.hσC X _ hX ht hRt) hdc
  have hTF := wnf_oadd (wnf_ofSummands (nfl_append_left (hsum ▸ nfl_summands hX))) hRF
  have hXt : inC X X (.Psi .zero π X) = true :=
    inC_of_fr_lt hX hπF ht hX hX hP.Ca hle (Or.inl rfl) fun w hw => FWOrder.k2 ht w hw
  have hX0 : Lt .zero X := zero_lt (by
    intro e
    rw [e] at hRm
    cases hRm)
  have hltt : ∀ η, WNF η → Lt η σ → Lt ((SeqD.app ceil g pre R r P c).big η) (.Psi .zero π X) :=
    fun η hη hησ => coll_psiY ht _ (B.good.1 η hη hησ).1
      (B.ubC X _ η hX ht hη hησ hX0 (Or.inl (Or.inr hσt)) hle
        (inC_tgt_of_k2t ht fun w hw => FWOrder.k2t ht w hw) hRt (inC_pre_of_X hX hsum hXt)
        (top_le hX hsum) (WFY.inC_of_ltY _ S.hPF ht hPt) (WFY.inC_of_ltY _ hI.hF ht hξt)
        (WFY.inC_of_ltY _ hη ht (lt_transY hη hσF ht hησ hσt))) (B.good.1 η hη hησ).2
  refine
    { good := ⟨fun η hη hησ => ⟨(B.good.1 η hη hησ).1, hltt η hη hησ⟩, B.good.2⟩
      pos := fun η hη hησ e => absurd e (B.pos η hη hησ)
      hσF := hσF
      hσle := Or.inr hσt
      hσs := subs_psi_a (subs_trans (mem_subs_of_mem_summands hRm) hR1.hσs)
      hσC := fun g' e hg' he' h => ?_
      ub := fun g' e η hg' he' hη hησ h0 hok h hηC => ?_
      ub2 := B.ub2
      lo := B.lo
      ns := fun _ η hη hησ hs => B.ns η hη hησ hs
      lbK := fun m e _ η hη hησ => by
        obtain ⟨A, hA⟩ := B.psi η
        have hF := (B.good.1 η hη hησ).1
        rw [hA] at hF ⊢
        exact Or.inr (K_lt_psi hF (e ▸ hdc))
      lbS := fun m e h η hη hησ => by
        obtain ⟨A, hA⟩ := B.psi η
        have hF := (B.good.1 η hη hησ).1
        rw [hA] at hF ⊢
        have hm : 1 ≤ m := (e ▸ hσF : WNF (.K m)).k
        exact Or.inr (succK_lt_psi hm hF (lt_transY (WNF.succK hm) ht hπF h (lt_psi_targetY ht))) }
  · rcases inC_psi_iff.mp h with h' | ⟨-, -, hδ, -⟩
    · exact WFY.inC_of_ltY _ hσF he' (lt_transY hσF ht he' hσt h')
    · exact hR1.hσC g' e hg' he' (inC_of_mem_summands hX hδ hRm)
  · have hF := (B.good.1 η hη hησ).1
    by_cases hdt : Lt (.Psi .zero π X) e
    · exact WFY.inC_of_ltY _ hF he' (lt_transY hF ht he' (hltt η hη hησ) hdt)
    obtain ⟨hle', hk, hδ, hlt⟩ := comp_of_inC ht he' hdt h
    exact B.ubC g' e η hg' he' hη hησ h0 hok hle' hk (inC_of_mem_summands hX hδ hRm)
      (inC_pre_of_X hX hsum hδ)
      (Or.inr (lt_of_le_of_ltY (wnf_oadd (wnf_ofSummands (nfl_append_left (hsum ▸ nfl_summands hX))) hRF) hX
        hg' (top_le hX hsum) hlt))
      (hPC g' e hg' he' h) (hU g' e hg' he' h) hηC

end RTKA.Fund
