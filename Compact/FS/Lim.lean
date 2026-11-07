import Compact.FS.MkApp
import Compact.FS.KMode

/-! 一般の目標 `π` の崩壊 `t = Ψ^0_π(X)` の列の不変量：加数の種類の場合分け（`pack_app`）と、極限の引数（`seqI_limit`）。

目標の族の閉包（`famSeq`）は仮定として渡し、後のファイルで示す。 -/

namespace RTKA.Fund

open Tm W

/-- 共終数になる正則項 -/
def RegTerm (σ : Tm) : Prop := IsTgt σ ∨ ∃ m, σ = .K m

theorem RegTerm.ne_zero {σ : Tm} (h : RegTerm σ) : σ ≠ .zero := by
  rcases h with h | ⟨m, rfl⟩
  · exact h.ne_zero
  · intro e
    cases e

/-- 列の不変量（共終数ごと） -/
def SeqI (t : Tm) (s : SeqD) : Prop :=
  match s.dom with
  | .omega => NatInv t s
  | .big σ => BigInvW t σ s ∧ (isPrincipal t = true → BigGap t σ s) ∧ RegTerm σ
  | _ => True

theorem seqI_nat {t : Tm} {s : SeqD} (hd : s.dom = .omega) (h : NatInv t s) : SeqI t s := by
  unfold SeqI
  rw [hd]
  exact h

theorem seqI_big {t σ : Tm} {s : SeqD} (hd : s.dom = .big σ) (hr : RegTerm σ) (h : BigInv t σ s) :
    SeqI t s := by
  unfold SeqI
  rw [hd]
  exact ⟨h.weak, fun _ => h.2, hr⟩

/-- 列の項 -/
def InSeq (s : SeqD) (y : Tm) : Prop :=
  (s.dom = .omega ∧ ∃ n, y = s.nat n) ∨ ∃ σ η, s.dom = .big σ ∧ WNF η ∧ Lt η σ ∧ y = s.big η

/-- 共終数が `ceil` 未満の加数のデータ -/
structure BigData (ξ π X P : Tm) (pre rest : List Tm) (R ceil : Tm) (r s : SeqD) (σ : Tm) : Prop where
  ht : WNF (.Psi .zero π X)
  hsum : summands X = pre ++ R :: rest
  S : SeedHyp π X P R
  hI : IdxHyp ξ π X
  hξ : Le ξ (ofSummands pre)
  hσc : Lt σ ceil
  hσπ : Lt σ π
  hreg : RegTerm σ
  hB : BigInv R σ r
  hd : r.dom = .big σ
  ex : ∃ g c, GenPsi g ξ π ∧ s = .app ceil g pre R r P c ∧ AdjHyp π R c ∧
    ∀ q, argR? π = some q → Lt q (approx pre P (oadd c (r.big .zero)))

/-- 列の記述 `s` の族 -/
def Pack (ξ π X P : Tm) (pre rest : List Tm) (R ceil : Tm) (r s : SeqD) : Prop :=
  (AppPack ξ π X P pre rest R s ∧ s.dom = .omega) ∨ ∃ σ, BigData ξ π X P pre rest R ceil r s σ

/-- `K_m⁺` の共終数は `K_m` でない -/
theorem dom_ne_succK {R : Tm} {m : Nat} (h : (info R).seq.dom = .big (.K m)) : R ≠ succK m := by
  rintro rfl
  have e : (info (succK m)).seq = .reg (succK m) (base (succK m)) := by
    simp [info, succK, isSucc, summands]
  rw [e] at h
  simp [SeqD.dom, succK] at h

theorem first_of_big {r : SeqD} {σ : Tm} (hd : r.dom = .big σ) : r.first = r.big .zero := by
  unfold SeqD.first
  rw [hd]

theorem first_of_nat {r : SeqD} (hd : r.dom = .omega) : r.first = r.nat 0 := by
  unfold SeqD.first
  rw [hd]

/-- 目標そのものへの対角化では、素の 0 番目の近似で既に引数の下限を越える -/
theorem valid_in {ξ π X P : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ π) (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (S : SeedHyp π X P R) (hd : r.dom = .big π) (hR : BigInv R π r) :
    validR π (combine g pre .zero P r.first) = true := by
  have hπF := ht.psi.piF
  have hX := ht.psi.aF
  have hN : NFL (pre ++ R :: rest) := hsum ▸ nfl_summands hX
  have hRN := hN.1 R (List.mem_append_right _ List.mem_cons_self)
  have hXe : X = ofSummands (pre ++ R :: rest) := by rw [← hsum, ofSummands_summands X hX]
  have hσ0 : Lt .zero π := zero_lt ht.psi.tgt.ne_zero
  have hxF := (hR.1.good.1 .zero WNF.zero hσ0).1
  have hxR := (hR.1.good.1 .zero WNF.zero hσ0).2
  rw [first_of_big hd, hg.comb]
  refine validR_of fun q hq => ?_
  have hqs : q ∈ subs R := subs_trans hR.1.hσs (mem_subs_arg hq)
  have hne : q ≠ R := ne_of_size_lt (Nat.lt_of_lt_of_le (size_arg_lt hq) (size_le_of_mem_subs hR.1.hσs))
  have hO := wnf_oadd WNF.zero hxF
  rw [zero_oadd hxF]
  have hy := wnf_nsum hxF S.hPF
  have hyR := nsum_lt_prin hxF S.hPF hRN.2 hxR S.hPR
  have hy0 : nsum (r.big .zero) P ≠ .zero := fun e => by
    have h1 := le_nsum_left hxF S.hPF
    rw [e] at h1
    rcases h1 with h1 | h1
    · exact hne (hR.1.pos _ WNF.zero hσ0 h1 q hqs)
    · exact not_lt_zero _ h1
  exact lt_approx_of_gap hN hy hy0 hyR hxF (le_nsum_left hxF S.hPF) (hR.2 _ WNF.zero hσ0) hqs hne
    (wnf_of_argR hπF hq) (by rw [← hXe]; exact arg_lt_of_psi ht hq)

/-- 目標そのものへの対角化に調整はない -/
theorem kAdj_in {ξ π ceil : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD} (hg : GenPsi g ξ π)
    (hπ : IsTgt π) (hd : r.dom = .big π) : kAdj π ceil g pre R r = .zero := by
  have ho : outsideMode ceil π g pre R = false := by
    rw [outsideMode_tgt hπ, hg.tgt]
    simp
  unfold kAdj
  rw [hd]
  rcases hπ with ⟨c, rfl, -⟩ | ⟨n, q, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩ <;> simp [ho]

/-- 加数の共終数による場合分け -/
theorem pack_app {ξ π X P c ceil : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ π) (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (S : SeedHyp π X P R) (adj : AdjHyp π R c)
    (hv0 : kAdj π ceil g pre R r = .zero → validR π (combine g pre .zero P r.first) = true → c = .zero)
    (hV : ∀ q, argR? π = some q → Lt q (approx pre P (oadd c r.first)))
    (hI : IdxHyp ξ π X) (hξ : Le ξ (ofSummands pre))
    (hRI : SeqI R r) (h0 : r.dom ≠ .zero) (h1 : r.dom ≠ .one) (hRp : isPrincipal R = true)
    (hcF : WNF ceil) (hc : Le ceil π)
    (hlow : ∀ σ, IsTgt σ → r.dom = .big σ → BigUB R σ r → Lt σ π → ¬ Lt σ ceil → WNF (.Psi .zero σ X))
    (hπK : ∀ m, 1 ≤ m → ¬ Lt (.K m) ceil → Lt π (.K m))
    (hRne : ∀ m, r.dom = .big (.K m) → R ≠ succK m) :
    Pack ξ π X P pre rest R ceil r (.app ceil g pre R r P c) := by
  have hπF := ht.psi.piF
  unfold SeqI at hRI
  cases hd : r.dom with
  | zero => exact absurd hd h0
  | one => exact absurd hd h1
  | omega =>
    rw [hd] at hRI
    have hdom : ∀ σ, r.dom ≠ .big σ := fun σ e => by
      rw [hd] at e
      cases e
    rw [first_of_nat hd] at hV
    exact Or.inl ⟨appPack_nat hg ht hsum S adj hV hI hξ hdom hRI, app_dom_nat hdom⟩
  | big σ =>
    rw [hd] at hRI
    obtain ⟨hBW, hBS, hreg⟩ := hRI
    have hB : BigInv R σ r := ⟨hBW.1, hBS hRp⟩
    have hσF := hB.1.hσF
    have hV' := hV
    rw [first_of_big hd] at hV'
    by_cases hσc : Lt σ ceil
    · exact Or.inr ⟨σ, ⟨ht, hsum, S, hI, hξ, hσc, lt_of_lt_of_leY hσF hcF hπF hσc hc, hreg, hB, hd, g, c, hg,
        rfl, adj, hV'⟩⟩
    have hlt' : ltB σ ceil = false := by
      cases e : ltB σ ceil with
      | false => rfl
      | true => exact absurd (ltB_iff.mp e) hσc
    have hdt := app_dom_big_ge (P := P) (c := c) (g := g) (pre := pre) (R := R) hd hlt'
    rcases hreg with hσt | ⟨m, rfl⟩
    · rcases triY hσF hπF with h | h | h
      · exact Or.inl ⟨appPack_diag hg ht hsum S adj hσt (hlow σ hσt hd hB.1 h hσc) hV' hI hξ hd hlt'
          (fun e => by rw [e] at h; exact Lt.irrefl _ h) hB, hdt⟩
      · subst h
        have hc0 := hv0 (kAdj_in hg hσt hd) (valid_in hg ht hsum S hd hB)
        subst hc0
        exact Or.inl ⟨appPack_in hg ht hsum S hI hξ hd hlt' hB, hdt⟩
      · exact Or.inl ⟨appPack_out hg ht hsum S adj hσt hV' hI hξ hd hlt' h hB, hdt⟩
    · exact Or.inl ⟨appPack_K hg ht hsum S adj hV' hI hξ hd hlt' (hπK m hB.1.hσF.k hσc) hB (hRne m hd), hdt⟩

theorem foldr_maxOpt_spec {f : Tm → Option Tm} {G : Tm} : ∀ {l : List Tm},
    (l.map f).foldr maxOpt none = some G → ∃ e, e ∈ l ∧ f e = some G
  | [], h => by simp at h
  | a :: l, h => by
    simp only [List.map_cons, List.foldr_cons] at h
    rcases maxOpt_cases h with h' | h'
    · exact ⟨a, List.mem_cons_self, h'⟩
    · obtain ⟨e, he, hf⟩ := foldr_maxOpt_spec h'
      exact ⟨e, List.mem_cons_of_mem _ he, hf⟩

/-- 目標の前線の中の閉じた点は `AdjHyp` を満たす -/
theorem frCl_adj {π R σ : Tm} {cl : Tm → Bool} (hπF : WNF π) (hR0 : R ≠ .zero) (hRF : WNF R) (hσF : WNF σ)
    (hσR : Le σ R) (hcl : ∀ G, WNF G → cl G = true → Lt G σ) : AdjHyp π R (frCl cl π) := by
  unfold frCl
  cases h : ((frB π π).map (fun e => maxCl cl e e)).foldr maxOpt none with
  | none => exact AdjHyp.zero hR0
  | some G =>
    obtain ⟨e, he, hf⟩ := foldr_maxOpt_spec h
    rw [frB_eq_fr] at he
    obtain ⟨h1, h2, h3⟩ := maxCl_spec hf
    have heF : WNF e := hπF.of_mem_subs (fr_spec he).1
    have hGF := heF.of_mem_subs h1
    refine ⟨hGF, lt_of_lt_of_leY hGF hσF hRF (hcl G hGF h2) hσR, fun g' d hd' hdπ hC => ?_⟩
    refine inC_of_selfVis hGF hd' heF h3 (fr_of_inC π (fun u hu hn hud => hn ?_) hC e he)
    exact lt_of_lt_of_leY (hπF.of_mem_subs hu) hd' hπF hud hdπ

/-- 対角化の調整は `AdjHyp` を満たす -/
theorem kAdj_spec {π R ceil : Tm} {g : Gen} {pre : List Tm} {r : SeqD} (hπF : WNF π) (hR0 : R ≠ .zero)
    (hRF : WNF R) (hK : ∀ σ, r.dom = .big σ → WNF σ ∧ Le σ R) :
    AdjHyp π R (kAdj π ceil g pre R r) := by
  unfold kAdj
  split
  · rename_i m hd
    split
    · obtain ⟨hKF, hKR⟩ := hK _ hd
      exact frCl_adj hπF hR0 hRF hKF hKR fun G hG h => closedPt_lt hKF.k hG h
    · exact AdjHyp.zero hR0
  · rename_i σ _ hd
    split
    · obtain ⟨hKF, hKR⟩ := hK _ hd
      exact frCl_adj hπF hR0 hRF hKF hKR fun G hG h => closedS_lt hKF hG h
    · exact AdjHyp.zero hR0
  · exact AdjHyp.zero hR0

/-- `mkApp` の出力の族 -/
theorem pack_mkApp {ξ π X P ceil : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r s : SeqD}
    (hg : GenPsi g ξ π) (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (S : SeedHyp π X P R) (hR1 : R ≠ .one) (hx0 : WNF r.first) (hx0R : Lt r.first R)
    (h : mkApp ceil g pre R r P .zero = some s)
    (hI : IdxHyp ξ π X) (hξ : Le ξ (ofSummands pre))
    (hRI : SeqI R r) (h0 : r.dom ≠ .zero) (h1 : r.dom ≠ .one) (hRp : isPrincipal R = true)
    (hcF : WNF ceil) (hc : Le ceil π)
    (hlow : ∀ σ, IsTgt σ → r.dom = .big σ → BigUB R σ r → Lt σ π → ¬ Lt σ ceil → WNF (.Psi .zero σ X))
    (hπK : ∀ m, 1 ≤ m → ¬ Lt (.K m) ceil → Lt π (.K m))
    (hRne : ∀ m, r.dom = .big (.K m) → R ≠ succK m) :
    Pack ξ π X P pre rest R ceil r s := by
  have hRN := (hsum ▸ nfl_summands ht.psi.aF : NFL (pre ++ R :: rest)).1 R
    (List.mem_append_right _ List.mem_cons_self)
  have hR0 : R ≠ .zero := fun e => by
    have h' := hRN.2
    rw [e] at h'
    cases h'
  have hk : AdjHyp π R (kAdj π ceil g pre R r) := kAdj_spec ht.psi.piF hR0 hRN.1 fun σ hd => by
    have h' := hRI
    unfold SeqI at h'
    rw [hd] at h'
    exact ⟨h'.1.1.hσF, h'.1.1.hσle⟩
  obtain ⟨c, adj, hv0, -, ⟨rfl, hV⟩ | ⟨rfl, hs⟩⟩ := mkApp_psi hg ht hsum S hR1 hx0 hx0R hk h
  · exact pack_app hg ht hsum S adj hv0 hV hI hξ hRI h0 h1 hRp hcF hc hlow hπK hRne
  · refine Or.inl (appPack_shift hg ht hsum S adj hI hξ hπK hs fun m hd => ?_)
    have h' := hRI
    unfold SeqI at h'
    rw [hd] at h'
    exact ⟨h'.1.1, h'.2.1 hRp⟩

/-- 列の不変量 -/
theorem Pack.inv {ξ π X P : Tm} {pre rest : List Tm} {R ceil : Tm} {r s : SeqD}
    (pk : Pack ξ π X P pre rest R ceil r s)
    (hF : ∀ y, InSeq s y → ∀ f, f ∈ fr π X → Lt f y)
    (hrest : ∀ y, InSeq s y → ∀ s', s' ∈ rest → ∀ w, w ∈ subs s' → Lt w (.Psi .zero π X) → Lt w y)
    (hPF : WNF P) (hξF : WNF ξ) (hPt : Lt P (.Psi .zero π X)) (hξt : Lt ξ (.Psi .zero π X))
    (hPC : ∀ g d, WNF g → WNF d → inC (.Psi .zero π X) g d = true → inC P g d = true)
    (hU : ∀ g d, WNF g → WNF d → inC (.Psi .zero π X) g d = true → inC ξ g d = true) :
    SeqI (.Psi .zero π X) s := by
  rcases pk with ⟨pk, hdt⟩ | ⟨σ, D⟩
  · exact seqI_nat hdt (natInv_of_pack pk (fun n f hf => hF _ (Or.inl ⟨hdt, n, rfl⟩) f hf)
      (fun n s' hs' => hrest _ (Or.inl ⟨hdt, n, rfl⟩) s' hs') hPF hξF hPt hξt hPC hU)
  · obtain ⟨g, c, hg, rfl, adj, hV⟩ := D.ex
    have hσ0 : Lt .zero σ := zero_lt D.hreg.ne_zero
    have hd' := app_dom_big_lt (P := P) (c := c) (g := g) (pre := pre) (R := R) D.hd (ltB_iff.mpr D.hσc)
    refine seqI_big hd' D.hreg (bigInv_app hg D.ht D.hsum D.S adj hV D.hI D.hξ D.hσπ hσ0 D.hB
      (fun η hη hησ f hf => ?_) (fun η hη hησ s' hs' w hw hl => ?_) hPt hξt hPC hU)
    · have := hF _ (Or.inr ⟨σ, η, hd', hη, hησ, rfl⟩) f hf
      rwa [app_big_eq hg] at this
    · have := hrest _ (Or.inr ⟨σ, η, hd', hη, hησ, rfl⟩) s' hs' w hw hl
      rwa [app_big_eq hg] at this

/-- 列の項の形 -/
theorem Pack.form {ξ π X P : Tm} {pre rest : List Tm} {R ceil : Tm} {r s : SeqD}
    (pk : Pack ξ π X P pre rest R ceil r s) {y : Tm} (hy : InSeq s y) :
    ∃ P' x, (P' = P ∨ P' = .zero) ∧ y = .Psi ξ π (approx pre P' x) ∧ Approx1 ξ π X P' pre rest R x ∧
      (x = .zero → ∀ v, v ∈ subs R → v = R) ∧ (∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v x) := by
  rcases pk with ⟨pk, hdt⟩ | ⟨σ, D⟩
  · obtain ⟨P', x, hP', he, A, hx0, hgap⟩ := pk.ex
    rcases hy with ⟨-, n, rfl⟩ | ⟨σ, η, hd, -⟩
    · exact ⟨P', x n, hP', he n, A n, hx0 n, hgap n⟩
    · rw [hdt] at hd
      cases hd
  · obtain ⟨g, c, hg, rfl, adj, hV⟩ := D.ex
    have hσ0 : Lt .zero σ := zero_lt D.hreg.ne_zero
    have hd' := app_dom_big_lt (P := P) (c := c) (g := g) (pre := pre) (R := R) D.hd (ltB_iff.mpr D.hσc)
    rcases hy with ⟨hdt, -⟩ | ⟨σ', η, hd, hη, hησ, rfl⟩
    · rw [hd'] at hdt
      cases hdt
    · rw [hd'] at hd
      cases hd
      have hRF := D.hB.1
      have hyF := (hRF.good.1 η hη hησ).1
      have hRW : WNF R := (D.ht.psi.aF).of_mem_subs (mem_subs_of_mem_summands (by
        rw [D.hsum]
        exact List.mem_append_right _ List.mem_cons_self))
      exact ⟨P, oadd c (r.big η), Or.inl rfl, app_big_eq hg,
        approx1_big D.ht D.hsum D.S adj hV D.hI D.hξ D.hσπ hσ0 D.hB hη hησ,
        adj_zero adj.hF hyF (hRF.pos η hη hησ), adj_gap adj.hF hyF hRW (D.hB.2 η hη hησ)⟩

/-- 種は列の項の未満 -/
theorem Pack.seed {ξ π X P : Tm} {pre rest : List Tm} {R ceil : Tm} {r s : SeqD}
    (pk : Pack ξ π X P pre rest R ceil r s) (hp : P ∈ fr π P) {y : Tm} (hy : InSeq s y) : Lt P y := by
  rcases pk with ⟨pk, hdt⟩ | ⟨σ, D⟩
  · rcases hy with ⟨-, n, rfl⟩ | ⟨σ, η, hd, -⟩
    · exact pk.hseed hp n
    · rw [hdt] at hd
      cases hd
  · obtain ⟨g, c, hg, rfl, adj, hV⟩ := D.ex
    have hσ0 : Lt .zero σ := zero_lt D.hreg.ne_zero
    have hd' := app_dom_big_lt (P := P) (c := c) (g := g) (pre := pre) (R := R) D.hd (ltB_iff.mpr D.hσc)
    rcases hy with ⟨hdt, -⟩ | ⟨σ', η, hd, hη, hησ, rfl⟩
    · rw [hd'] at hdt
      cases hdt
    rw [hd'] at hd
    cases hd
    rw [app_big_eq hg]
    exact (approx1_big D.ht D.hsum D.S adj hV D.hI D.hξ D.hσπ hσ0 D.hB hη hησ).hseed hp

/-- 添字の種は列の項の未満 -/
theorem Pack.idx {ξ π X P : Tm} {pre rest : List Tm} {R ceil : Tm} {r s : SeqD}
    (pk : Pack ξ π X P pre rest R ceil r s) (hp : ξ ∈ fr π ξ) {y : Tm} (hy : InSeq s y) : Lt ξ y := by
  obtain ⟨P', x, -, rfl, H, -, -⟩ := pk.form hy
  exact FWOrder.k2s H.hnf ξ hp

/-- 列の 0 番目は列の項 -/
theorem Pack.first_mem {ξ π X P : Tm} {pre rest : List Tm} {R ceil : Tm} {r s : SeqD}
    (pk : Pack ξ π X P pre rest R ceil r s) : InSeq s s.first := by
  rcases pk with ⟨-, hdt⟩ | ⟨σ, D⟩
  · exact Or.inl ⟨hdt, 0, by unfold SeqD.first; rw [hdt]⟩
  · obtain ⟨g, c, hg, rfl, -, -⟩ := D.ex
    have hd' := app_dom_big_lt (P := P) (c := c) (g := g) (pre := pre) (R := R) D.hd (ltB_iff.mpr D.hσc)
    refine Or.inr ⟨σ, .zero, hd', WNF.zero, zero_lt D.hreg.ne_zero, ?_⟩
    unfold SeqD.first
    rw [hd']

/-- 列の項は 0 番目以上 -/
theorem Pack.le_first {ξ π X P : Tm} {pre rest : List Tm} {R ceil : Tm} {r s : SeqD}
    (pk : Pack ξ π X P pre rest R ceil r s) {y : Tm} (hy : InSeq s y) : Le s.first y := by
  rcases pk with ⟨pk, hdt⟩ | ⟨σ, D⟩
  · rcases hy with ⟨-, n, rfl⟩ | ⟨σ, η, hd, -⟩
    · have hm := le_of_mono (y := s.nat) (fun k => (pk.L.good k).1) (fun k => (pk.L.good k).2.2) n
      unfold SeqD.first
      rw [hdt]
      exact hm
    · rw [hdt] at hd
      cases hd
  · obtain ⟨g, c, hg, rfl, adj, hV⟩ := D.ex
    have hσ0 : Lt .zero σ := zero_lt D.hreg.ne_zero
    have hd' := app_dom_big_lt (P := P) (c := c) (g := g) (pre := pre) (R := R) D.hd (ltB_iff.mpr D.hσc)
    rcases hy with ⟨hdt, -⟩ | ⟨σ', η, hd, hη, hησ, rfl⟩
    · rw [hd'] at hdt
      cases hdt
    rw [hd'] at hd
    cases hd
    unfold SeqD.first
    rw [hd']
    by_cases h0 : η = .zero
    · rw [h0]
      exact Or.inl rfl
    have hB := D.hB
    have H₀ := approx1_big D.ht D.hsum D.S adj hV D.hI D.hξ D.hσπ hσ0 hB WNF.zero hσ0
    have H := approx1_big D.ht D.hsum D.S adj hV D.hI D.hξ D.hσπ hσ0 hB hη hησ
    have hyF := (hB.1.good.1 η hη hησ).1
    have hy0 := (hB.1.good.1 .zero WNF.zero hσ0).1
    have hS : ∀ {g' d : Tm}, WNF g' → WNF d → Le d π → inC π g' d = true →
        inC (oadd c (r.big η)) g' d = true → inC (oadd c (r.big .zero)) g' d = true := by
      intro g' d hg' hd' hle hk h
      exact inC_oadd adj.hF hy0 (adj.hU g' d hd' hle hk)
        (hB.1.ub2 g' d .zero η hg' hd' WNF.zero hη (zero_lt h0) hησ
          (inC_of_oadd_right adj.hF hyF h) (inC_zero _ _))
    have hu := H.hnf
    rw [app_big_eq hg, app_big_eq hg]
    exact Or.inr (H₀.hltS H (oadd_lt_oadd adj.hF hy0 hyF (hB.1.good.2 .zero η WNF.zero hη (zero_lt h0) hησ))
      (hS H.hAF hu (Or.inr (lt_psi_targetY hu)) (inC_tgt_of_k2t hu fun w hw => FWOrder.k2t hu w hw))
      (hS H.hAF H.hπF (Or.inl rfl) (inC_tgt H.hπF H.ht.psi.tgt H.hAF H.hr)))

/-- 素の近似の 0 番目は前線の元でない -/
theorem first_ne_fr {π X p x₀ : Tm} {pre : List Tm} {R : Tm}
    (H : Approx1 .zero π X .zero pre [] R x₀) (hx0 : x₀ = .zero → ∀ v, v ∈ subs R → v = R)
    (hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v x₀) (hp : p ∈ fr π X) :
    Tm.Psi .zero π (approx pre .zero x₀) ≠ p := by
  intro e
  obtain ⟨s, hs, hps⟩ := (mem_fr_iff H.hX).mp hp
  rw [H.hsum] at hs
  have hss : s ∈ pre ∨ s = R := by
    rcases List.mem_append.mp hs with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.mp h)
  have hC := H.argCond_summand (.Psi .zero π X) hx0 hgap hss
  have hz : Tm.Psi .zero π (approx pre .zero x₀) ∈ subs s := by
    rw [e]
    exact (fr_spec hps).1
  exact Lt.irrefl _ (hC.1 _ _ _ hz (lt_psi_targetY H.ht) H.hAlt)

/-- 種 `p` は `t` の部分項を支配する：`t` 未満の真の部分項は、`p` より大きい主要項未満 -/
def Dom (t p : Tm) : Prop :=
  ∀ v, v ∈ subs t → v ≠ t → Lt v t → ∀ y, WNF y → isPrincipal y = true → Lt p y → Lt v y

/-- `SeqI` の 0・後者でない項の 0 番目 -/
theorem first_good {R : Tm} {r : SeqD} (hRI : SeqI R r) (h0 : r.dom ≠ .zero) (h1 : r.dom ≠ .one) :
    WNF r.first ∧ Lt r.first R := by
  unfold SeqI at hRI
  cases hd : r.dom with
  | zero => exact absurd hd h0
  | one => exact absurd hd h1
  | omega =>
    rw [hd] at hRI
    rw [first_of_nat hd]
    exact ⟨(hRI.1.good 0).1, (hRI.1.good 0).2.1⟩
  | big σ =>
    rw [hd] at hRI
    rw [first_of_big hd]
    exact hRI.1.1.good.1 .zero WNF.zero (zero_lt hRI.2.2.ne_zero)

/-- `mkApp` が `none` なら、挿入点までの加数は目標の引数の加数で、挿入点は最後の加数でない -/
theorem mkApp_none {π X P ceil R : Tm} {g : Gen} {pre rest : List Tm} {r : SeqD}
    (hg : g.tgt? = some π) (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (hPR : Lt P R) (h : mkApp ceil g pre R r P .zero = none) :
    (∀ s, s ∈ pre ++ [R] → s ∈ subs π) ∧ rest ≠ [] := by
  have hπF := ht.psi.piF
  have hX := ht.psi.aF
  have hN : NFL (pre ++ R :: rest) := hsum ▸ nfl_summands hX
  have hRN := hN.1 R (List.mem_append_right _ List.mem_cons_self)
  unfold mkApp at h
  rw [hg] at h
  dsimp only at h
  rw [ite_eq_right (by simp [ltB_iff.mpr hPR])] at h
  cases htl : tailRaw (argR? π) pre with
  | none =>
    rw [htl] at h
    cases h
  | some rt =>
    rw [htl] at h
    dsimp only at h
    obtain ⟨q, hq, hsq, hrtF⟩ := tailRaw_some hπF htl
    by_cases hle : leB R rt = true
    · have hRrt : Le R rt := le_of_ne_gtY hRN.1 hrtF (leB_iff.mp hle)
      have hqX := arg_lt_of_psi ht hq
      have hqs : ∀ s, s ∈ summands q → s ∈ subs π := fun s hs =>
        subs_trans (mem_subs_arg hq) (mem_subs_of_mem_summands hs)
      have hltL : cmpList (summands rt) (R :: rest) = .lt := by
        have := hqX
        unfold Lt at this
        rwa [cmp_eq, hsq, hsum, cmpList_append_same] at this
      cases hst : summands rt with
      | nil =>
        rw [eq_zero_of_summands_nil hst] at hRrt
        rcases hRrt with e | h'
        · rw [e] at hPR
          exact absurd hPR (not_lt_zero _)
        · exact absurd h' (not_lt_zero _)
      | cons a l =>
        rw [hst] at hltL
        have haN := (nfl_summands hrtF).1 a (by rw [hst]; exact List.mem_cons_self)
        have hRa : R = a := by
          rcases triY hRN.1 haN.1 with h' | h' | h'
          · exfalso
            have h2 := cmpList_head_lt (x := R) (y := a) rest l ((lt_principal_iff hRN.2 haN.2).mp h')
            have h3 : Lt X q := by
              unfold Lt
              rw [cmp_eq, hsum, hsq, hst, cmpList_append_same]
              exact h2
            exact absurd h3 (Lt.asymmY (wnf_of_argR hπF hq) hX hqX)
          · exact h'
          · exact absurd (lt_prin_of_head hst hRN.2 haN.2 h') (not_lt_of_leY hRN.1 hrtF hRrt)
        subst hRa
        refine ⟨fun s hs => ?_, fun e => ?_⟩
        · rcases List.mem_append.mp hs with hs | hs
          · exact hqs s (by rw [hsq]; exact List.mem_append_left _ hs)
          · rw [List.mem_singleton.mp hs]
            exact hqs _ (by rw [hsq, hst]; exact List.mem_append_right _ List.mem_cons_self)
        · rw [e, cmpList_cons_cons_eq _ _ (cmpP_self R)] at hltL
          cases l with
          | nil => rw [cmpList_nil_nil] at hltL; cases hltL
          | cons _ _ => rw [cmpList_cons_nil] at hltL; cases hltL
    · rw [ite_eq_right hle] at h
      split at h
      · cases h
      · split at h <;> cases h

/-- 列の項は標準形 -/
theorem Pack.wnf {ξ π X P : Tm} {pre rest : List Tm} {R ceil : Tm} {r s : SeqD}
    (pk : Pack ξ π X P pre rest R ceil r s) {y : Tm} (hy : InSeq s y) : WNF y := by
  obtain ⟨P', x, -, rfl, H, -, -⟩ := pk.form hy
  exact H.hnf

/-- 列の項は主要項 -/
theorem Pack.prin {ξ π X P : Tm} {pre rest : List Tm} {R ceil : Tm} {r s : SeqD}
    (pk : Pack ξ π X P pre rest R ceil r s) {y : Tm} (hy : InSeq s y) : isPrincipal y = true := by
  obtain ⟨P', x, -, rfl, H, -, -⟩ := pk.form hy
  rfl

/-- 挿入点より後ろの加数は種そのもの -/
theorem rest_eq_seed {X p R R₂ : Tm} {pre pre₂ rest : List Tm}
    (hX : WNF X) (hsum : summands X = pre ++ [R]) (hsum₂ : summands X = pre₂ ++ R₂ :: rest)
    (hpF : WNF p) (hpR : Le p R) (hhd : ∀ a l, rest = a :: l → ¬ Lt p a) (hne : rest ≠ []) :
    R = p ∧ ∀ s, s ∈ rest → s = p := by
  have hRF : WNF R := ((nfl_summands hX).1 R (by rw [hsum]; simp)).1
  cases hr : rest with
  | nil => exact absurd hr hne
  | cons s₀ tl =>
    subst hr
    have hN := nfl_summands hX
    rw [hsum₂] at hN
    have hN₂ : NFL (s₀ :: tl) := nfl_tail (nfl_append_right hN)
    have hs₀F := (hN₂.1 s₀ List.mem_cons_self).1
    have h4 : Le s₀ p := le_of_not_ltY hpF hs₀F (hhd s₀ tl rfl)
    have hRin : R ∈ s₀ :: tl := by
      have e1 : pre ++ [R] = pre₂ ++ R₂ :: (s₀ :: tl) := by rw [← hsum, hsum₂]
      have e2 : (pre ++ [R]).getLast? = some R := by simp
      rw [e1, getLast?_append_cons₂] at e2
      exact List.mem_of_getLast? e2
    have hRs₀ : Le R s₀ := by
      rcases List.mem_cons.mp hRin with h | h
      · exact Or.inl h
      · exact le_of_ne_gtY hRF hs₀F (le_head_of_nfl hN₂ R h)
    have hRe : R = p := le_antisymmY hRF hpF (le_transY hRF hs₀F hpF hRs₀ h4) hpR
    refine ⟨hRe, fun s hs => ?_⟩
    have hsF := (hN₂.1 s hs).1
    have hs₁ : Le s s₀ := by
      rcases List.mem_cons.mp hs with h | h
      · exact Or.inl h
      · exact le_of_ne_gtY hsF hs₀F (le_head_of_nfl hN₂ s h)
    have hNf := nfl_summands hX
    rw [hsum] at hNf
    have hRs : Le R s := by
      have hs'' : s ∈ pre ++ [R] := by
        rw [← hsum, hsum₂]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ hs)
      rcases List.mem_append.mp hs'' with h | h
      · exact le_of_ne_gtY hRF hsF (le_of_nfl_append (rest := []) hNf s h)
      · exact Or.inl (List.mem_singleton.mp h).symm
    exact le_antisymmY hsF hpF (le_transY hsF hs₀F hpF hs₁ h4) (le_transY hpF hRF hsF hpR hRs)

/-- 素の近似の 0 番目が種（最後の加数）未満で、`X` の加数が種か目標の部分項なら、種は `t` の部分項を支配する -/
theorem dom_seed {π X p x₀ : Tm} {pre : List Tm} (H : Approx1 .zero π X .zero pre [] p x₀)
    (hx0 : x₀ = .zero → ∀ v, v ∈ subs p → v = p)
    (hG : ∀ v, v ∈ subs p → v ≠ p → Lt v p → Lt v x₀)
    (hlt : Lt (.Psi .zero π (approx pre .zero x₀)) p) (hpπ : Lt p π)
    (hpt : Lt p (.Psi .zero π X)) (hfr : ∀ f, f ∈ fr π X → Le f p)
    (hsm : ∀ s, s ∈ summands X → s = p ∨ s ∈ subs π) : Dom (.Psi .zero π X) p := by
  intro v hv hne hvt y hyF hyp hpy
  have ht := H.ht
  have hy₀ := H.hnf
  have hπF := ht.psi.piF
  have hX := ht.psi.aF
  have hpF := H.hRF
  have hy0 : y ≠ .zero := fun e => by
    rw [e] at hpy
    exact not_lt_zero _ hpy
  have hy₀y : Lt (.Psi .zero π (approx pre .zero x₀)) y := lt_transY hy₀ hpF hyF hlt hpy
  have hsubπ : ∀ {w : Tm}, w ∈ subs π → Lt w (.Psi .zero π X) → Lt w y := fun {w} hw hl => by
    have hwF := hπF.of_mem_subs hw
    exact lt_transY hwF hy₀ hyF (lt_of_mem_tgt hy₀ hw (lt_transY hwF ht hπF hl (lt_psi_targetY ht))) hy₀y
  simp only [subs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
  rcases hv with e | (h | h) | h
  · exact absurd e hne
  · rw [h]
    exact zero_lt hy0
  · exact hsubπ h hvt
  · refine lt_of_summands_sub hX ht hyp hy0 (fun s hs w hw hl => ?_) h hvt
    rcases hsm s hs with rfl | hsπ
    · by_cases hwp : w = s
      · rw [hwp]
        exact hpy
      · exact lt_transY (hX.of_mem_subs (subs_trans (mem_subs_of_mem_summands hs) hw)) hy₀ hyF
          (sub_lt_first H hx0 hG hlt hpπ hpt hfr hw hwp hl) hy₀y
    · exact hsubπ (subs_trans hsπ hw) hl

theorem mOfT_tgt {π : Tm} (h : IsTgt π) : mOfT π = mi π := by
  rcases h with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩ <;> rfl

/-- 極限の引数の崩壊の列 -/
theorem seqI_limit {π X : Tm} {πf : Fam} (ht : WNF (.Psi .zero π X)) (hX0 : X ≠ .zero)
    (hl : ¬ isSucc X = true)
    (hS : ∀ S, S ∈ summands X → S ≠ .one → SeqI S (info S).seq)
    (hFam : ∀ p W, p ∈ fr π X → (∀ f, f ∈ fr π X → Le f p) → Dom (.Psi .zero π X) p →
      WNF (.Psi .zero π W) → Le (.Psi .zero π W) p →
      (∀ c, π = .Om c → ∀ v, v ∈ subs (.Psi .zero π X) → v ≠ .Psi .zero π X → Lt v (.Psi .zero π X) → Le v p) →
      SeqI (.Psi .zero π X) (famSeq πf π (some p))) :
    SeqI (.Psi .zero π X) (limitSeq π πf π X (info X).sums none) := by
  have hP := ht.psi
  have hX := hP.aF
  have hπF := hP.piF
  have hsum := summands_pre_last hX0
  have hlast : lastS (info X).sums = (info (lastT (info X).sums)).seq := lastS_coh (coh_sums X)
  obtain ⟨pre, hpre⟩ : ∃ pre, pre = preT (info X).sums := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = lastT (info X).sums := ⟨_, rfl⟩
  rw [← hpre, ← hR] at hsum
  rw [← hR] at hlast
  have hRm : R ∈ summands X := by
    rw [hsum]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hRne : R ≠ .one := by
    intro e
    apply hl
    show (summands X).getLast? == some one
    rw [hsum, e]
    simp
  have hRF := hX.of_mem_subs (mem_subs_of_mem_summands hRm)
  have hRp := nfl_principal (nfl_summands hX) R hRm
  have hR0 : R ≠ .zero := by
    intro e
    rw [e] at hRp
    cases hRp
  obtain ⟨h0, h1⟩ := dom_ne_of_principal hRF hRp hRne
  have hRI := hS R hRm hRne
  have hlow : ∀ (R' : Tm) (σ : Tm), IsTgt σ → (info R').seq.dom = .big σ → BigUB R' σ (info R').seq →
      Lt σ π → ¬ Lt σ π → WNF (.Psi .zero σ X) := fun _ _ _ _ _ h h' => absurd h h'
  have hπK : ∀ m, 1 ≤ m → ¬ Lt (.K m) π → Lt π (.K m) := fun m hm h => by
    rcases triY hπF (WNF.K' hm) with h' | h' | h'
    · exact h'
    · exact absurd h' (IsTgt.ne_K hP.tgt m)
    · exact absurd h' h
  have S0 : SeedHyp π X .zero R := seed_zero hP.tgt.ne_zero hR0
  obtain ⟨hx0F, hx0R⟩ := first_good hRI h0 h1
  have hsum0 : summands X = pre ++ R :: [] := hsum
  have hN := nfl_summands hX
  unfold limitSeq
  dsimp only
  rw [← hpre, ← hR, hlast]
  cases hs0 : mkApp π (.psi0 π) pre R (info R).seq .zero .zero with
  | none => exact absurd rfl (mkApp_none rfl ht hsum0 S0.hPR hs0).2
  | some s0 =>
  have pk0 := pack_mkApp (genPsi0 π) ht hsum0 S0 hRne hx0F hx0R hs0 (IdxHyp.zero ht) (zero_le _) hRI h0 h1
    hRp hπF (Or.inl rfl) (hlow R) hπK fun _ hd => dom_ne_succK hd
  obtain ⟨P', x₀, hP', hfirst, H₀, hx₀0, hx₀g⟩ := pk0.form pk0.first_mem
  have e0 : P' = .zero := by
    rcases hP' with h | h <;> exact h
  subst e0
  have hy₀ := H₀.hnf
  simp only [Option.getD_some]
  have hF0 : ∀ f, f ∈ fr π X → WNF f := fun f hf => hX.of_mem_subs (fr_spec hf).1
  have hplain : (∀ f, f ∈ fr π X → Lt f s0.first) → SeqI (.Psi .zero π X) s0 := fun hF =>
    pk0.inv (fun y hy f hf => lt_of_lt_of_leY (hF0 f hf) (hfirst ▸ hy₀) (pk0.wnf hy) (hF f hf)
      (pk0.le_first hy)) (fun _ _ _ hs' => by cases hs') WNF.zero WNF.zero
      (zero_lt (by intro e; cases e)) (zero_lt (by intro e; cases e)) (fun _ _ _ _ _ => inC_zero _ _)
      (fun _ _ _ _ _ => inC_zero _ _)
  have hfrWNF : ∀ x, x ∈ frB π X → WNF x := fun x hx => by
    rw [frB_eq_fr] at hx
    exact hX.of_mem_subs (fr_spec hx).1
  have hmo : maxOpt none (maxL (frB π X)) = maxL (frB π X) := by
    cases maxL (frB π X) <;> rfl
  rw [hmo]
  cases hm : maxL (frB π X) with
  | none =>
    refine hplain fun f hf => ?_
    have := maxL_none hm
    rw [frB_eq_fr] at this
    rw [this] at hf
    cases hf
  | some p =>
    have hpm : p ∈ fr π X := by
      have := maxL_mem hm
      rwa [frB_eq_fr] at this
    have hfrp : ∀ f, f ∈ fr π X → Le f p := fun f hf =>
      le_maxL hfrWNF hm (by rw [frB_eq_fr]; exact hf)
    have hpF : WNF p := hX.of_mem_subs (fr_spec hpm).1
    have hpκ : Lt p π := (fr_spec hpm).2
    have hpt : Lt p (.Psi .zero π X) := FWOrder.k2 ht p hpm
    have hpC : ∀ g d, WNF g → WNF d → inC (.Psi .zero π X) g d = true → inC p g d = true :=
      fun g d hg hd h => inC_seed_fr ht hpm hg hd h
    have hpp : isPrincipal p = true := by
      rcases fr_node hpm with ⟨m, a, rfl⟩ | ⟨s, q, a, rfl⟩ <;> rfl
    have hpn : p ∈ fr π p := by
      rcases fr_node hpm with ⟨m, a, rfl⟩ | ⟨s, q, a, rfl⟩ <;> simp [fr, hpκ]
    have hps : ¬ isSucc p = true := by
      rw [isSucc_principal hpp]
      rcases fr_node hpm with ⟨m, a, rfl⟩ | ⟨s, q, a, rfl⟩ <;> simp
    dsimp only
    by_cases h2 : ltB p s0.first = true
    · rw [ite_eq_left h2]
      exact hplain fun f hf => lt_of_le_of_ltY (hF0 f hf) hpF (hfirst ▸ hy₀) (hfrp f hf) (ltB_iff.mp h2)
    · have hne := first_ne_fr H₀ hx₀0 hx₀g hpm
      have hne'' : ¬ s0.first = p := fun e => hne (by rw [← hfirst]; exact e)
      rw [ite_eq_right h2, ite_eq_right hne'']
      rw [hfirst] at h2
      have hxp : Lt (.Psi .zero π (approx pre .zero x₀)) p := by
        rcases triY hy₀ hpF with h | h | h
        · exact h
        · exact absurd h hne
        · exact absurd (ltB_iff.mpr h) h2
      -- 種は `pre` の前線にない
      have hpre' : ∀ s, s ∈ pre → p ∉ fr π s := by
        intro s hs hps'
        have h3 : p ∈ fr π (ofSummands pre) := (mem_fr_iff H₀.hpreF).mpr
          ⟨s, by rw [summands_ofSummands _ (nfl_principal H₀.hpreN)]; exact hs, hps'⟩
        have h4 := FWOrder.k2 hy₀ p (H₀.fr_approx_of_pre h3)
        exact Lt.asymmY hpF hy₀ h4 hxp
      have hpR : p ∈ fr π R := by
        obtain ⟨s, hs, hps'⟩ := (mem_fr_iff hX).mp hpm
        rw [hsum] at hs
        rcases List.mem_append.mp hs with hs | hs
        · exact absurd hps' (hpre' s hs)
        · rw [List.mem_singleton.mp hs] at hps'
          exact hps'
      have hpleR : Le p R := fr_leY hπF hRF hpR
      unfold insertAtL
      cases hsp : splitGtD p (info X).sums with
      | none =>
        -- 全ての加数は `p` 以下：`X = p`
        have hhead : ∀ a l, summands X = a :: l → ¬ Lt p a := by
          intro a l e h
          have e' : (info X).sums.map Prod.fst = a :: l := by
            rw [info_sums_fst]
            exact e
          cases hxs : (info X).sums with
          | nil =>
            rw [hxs] at e'
            cases e'
          | cons q ys =>
            rw [hxs] at e' hsp
            simp only [List.map_cons, List.cons.injEq] at e'
            have h0' := splitGtD_none_head hsp
            rw [e'.1, ltB_iff.mpr h] at h0'
            cases h0'
        have hnil : pre = [] := by
          cases hpe : pre with
          | nil => rfl
          | cons a l =>
            exfalso
            subst hpe
            have ham : a ∈ a :: l := List.mem_cons_self
            have haN := (hsum ▸ hN : NFL ((a :: l) ++ [R]))
            have haF := (haN.1 a (List.mem_cons_self)).1
            have h3 : Le a p := le_of_not_ltY hpF haF (hhead a _ (by rw [hsum]; rfl))
            have h4 : Le R a := le_of_ne_gtY hRF haF (le_of_nfl_append haN a ham)
            have h5 : a = p := le_antisymmY haF hpF h3 (le_transY hpF hRF haF hpleR h4)
            exact hpre' a ham (by rw [h5]; exact hpn)
        subst hnil
        have hRe : R = p :=
          le_antisymmY hRF hpF (le_of_not_ltY hpF hRF (hhead R [] hsum)) hpleR
        subst hRe
        have hXR : X = R := by
          rw [← ofSummands_summands X hX, hsum]
          rfl
        refine hFam R _ hpm hfrp (dom_seed H₀ hx₀0 hx₀g hxp hpκ hpt hfrp fun s hs => by
          rw [hsum] at hs
          exact Or.inl (List.mem_singleton.mp hs)) hy₀ (Or.inr hxp) fun _ _ v hv hne hl => ?_
        have hvF := ht.of_mem_subs hv
        simp only [subs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
        rcases hv with e | (h | h) | h
        · exact absurd e hne
        · rw [h]
          exact zero_le _
        · exact Or.inr (lt_transY hvF hy₀ hRF
            (lt_of_mem_tgt hy₀ h (lt_transY hvF ht hπF hl (lt_psi_targetY ht))) hxp)
        · rw [hXR] at h
          by_cases hvR : v = R
          · exact Or.inl hvR
          · exact Or.inr (lt_transY hvF hy₀ hRF (sub_lt_first H₀ hx₀0 hx₀g hxp hpκ hpt hfrp h hvR hl) hxp)
      | some q =>
        obtain ⟨pre₂, R₂, r₂⟩ := q
        obtain ⟨L, rest, hys, hL, hpR₂, -, hhd⟩ := splitGtD_spec hsp
        have hpR' : Lt p R₂ := ltB_iff.mp hpR₂
        have hsum₂ : summands X = pre₂ ++ R₂ :: rest.map Prod.fst := by
          rw [← info_sums_fst, hys, List.map_append, hL, List.map_cons]
        have hrc : r₂ = (info R₂).seq := by
          have hm' : (R₂, r₂) ∈ (info X).sums := by
            rw [hys]
            simp
          exact coh_sums X (R₂, r₂) hm'
        subst hrc
        have hRm' : R₂ ∈ summands X := by
          rw [hsum₂]
          exact List.mem_append_right _ List.mem_cons_self
        have hRne' : R₂ ≠ .one := by
          intro e
          rw [e] at hpR'
          have e0 := lt_oneY hpF hpR'
          rcases fr_node hpm with ⟨m, a, e1⟩ | ⟨s, q, a, e1⟩ <;> rw [e0] at e1 <;> cases e1
        have hRF' := hX.of_mem_subs (mem_subs_of_mem_summands hRm')
        have hRp' := nfl_principal (nfl_summands hX) R₂ hRm'
        obtain ⟨h0', h1'⟩ := dom_ne_of_principal hRF' hRp' hRne'
        have hRI' := hS R₂ hRm' hRne'
        obtain ⟨hx1F, hx1R⟩ := first_good hRI' h0' h1'
        have S₂ : SeedHyp π X p R₂ := ⟨hpF, hpR', hpκ, hps⟩
        have hhd' : ∀ a l, rest.map Prod.fst = a :: l → ¬ Lt p a := by
          intro a l e h
          cases hr : rest with
          | nil =>
            rw [hr] at e
            cases e
          | cons q tl =>
            rw [hr] at e
            simp only [List.map_cons, List.cons.injEq] at e
            have := hhd q tl hr
            rw [e.1, ltB_iff.mpr h] at this
            cases this
        have hrs := rest_eq_seed hX hsum hsum₂ hpF hpleR hhd'
        dsimp only
        -- Mahlo 添字 `p` の列
        have hmah : R = p → idxOK π p = true → SeqI (.Psi .zero π X) (deadSeq π πf π p (info X).sums) := by
          intro hRe hc
          subst hRe
          unfold deadSeq
          rw [← hpre, ← hR, hlast, ite_eq_left hc]
          have hc' := hc
          unfold idxOK at hc'
          simp only [Bool.and_eq_true] at hc'
          have hR₂pre : R₂ ∈ pre := by
            have h3 : R₂ ∈ pre ++ [R] := by
              rw [← hsum, hsum₂]
              exact List.mem_append_right _ List.mem_cons_self
            rcases List.mem_append.mp h3 with h | h
            · exact h
            · have e := List.mem_singleton.mp h
              rw [e] at hpR'
              exact absurd hpR' (Lt.irrefl _)
          have hpreN : NFL pre := nfl_append_left (hsum ▸ hN : NFL (pre ++ [R]))
          have hξ : Le R (ofSummands pre) :=
            le_transY hRF hRF' (wnf_ofSummands hpreN) (Or.inr hpR') (le_ofSummands_of_mem hpreN hR₂pre)
          rw [mOfT_tgt hP.tgt] at hc'
          have hI : IdxHyp R π X := ⟨hRF, hpκ, ltB_iff.mp hc'.1, hc'.2⟩
          cases hm3 : mkApp π (.mahlo R π) pre R (info R).seq .zero .zero with
          | some s =>
            have pk := pack_mkApp (Or.inr rfl : GenPsi (.mahlo R π) R π) ht hsum0 S0 hRne hx0F hx0R hm3 hI hξ
              hRI h0 h1 hRp hπF (Or.inl rfl) (hlow R) hπK fun _ hd => dom_ne_succK hd
            simp only
            exact pk.inv (fun y hy f hf => lt_of_le_of_ltY (hF0 f hf) hRF (pk.wnf hy) (hfrp f hf)
              (pk.idx hpn hy)) (fun _ _ _ hs' => by cases hs') WNF.zero hRF
              (zero_lt (by intro e; cases e)) hpt (fun _ _ _ _ _ => inC_zero _ _) hpC
          | none => exact absurd rfl (mkApp_none rfl ht hsum0 S0.hPR hm3).2
        by_cases hC : (!ltB p R && idxOK π p) = true
        · rw [← hR, ite_eq_left hC]
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hC
          refine hmah (le_antisymmY hRF hpF (le_of_not_ltY hpF hRF ?_) hpleR) hC.2
          intro h
          rw [ltB_iff.mpr h] at hC
          cases hC.1
        rw [← hR, ite_eq_right hC]
        cases hm2 : mkApp π (.psi0 π) pre₂ R₂ (info R₂).seq p .zero with
        | some s =>
          have pk := pack_mkApp (genPsi0 π) ht hsum₂ S₂ hRne' hx1F hx1R hm2 (IdxHyp.zero ht) (zero_le _) hRI'
            h0' h1' hRp' hπF (Or.inl rfl) (hlow R₂) hπK fun _ hd => dom_ne_succK hd
          simp only
          refine pk.inv (fun y hy f hf => lt_of_le_of_ltY (hF0 f hf) hpF (pk.wnf hy) (hfrp f hf)
            (pk.seed hpn hy)) (fun y hy s' hs' w hw hl => ?_) hpF WNF.zero hpt
            (zero_lt (by intro e; cases e)) hpC (fun _ _ _ _ _ => inC_zero _ _)
          obtain ⟨hRe, hall⟩ := hrs (fun e => by rw [e] at hs'; cases hs')
          subst hRe
          have hs'e := hall s' hs'
          subst hs'e
          by_cases hwp : w = s'
          · rw [hwp]
            exact pk.seed hpn hy
          · exact lt_transY (hRF.of_mem_subs hw) hy₀ (pk.wnf hy)
              (sub_lt_first H₀ hx₀0 hx₀g hxp hpκ hpt hfrp hw hwp hl)
              (lt_transY hy₀ hRF (pk.wnf hy) hxp (pk.seed hpn hy))
        | none =>
          have hnone := mkApp_none rfl ht hsum₂ hpR' hm2
          obtain ⟨hRe, hall⟩ := hrs hnone.2
          subst hRe
          have hdom : Dom (.Psi .zero π X) R := dom_seed H₀ hx₀0 hx₀g hxp hpκ hpt hfrp fun s hs => by
            rw [hsum₂] at hs
            rcases List.mem_append.mp hs with h | h
            · exact Or.inr (hnone.1 s (List.mem_append_left _ h))
            · rcases List.mem_cons.mp h with h | h
              · rw [h]
                exact Or.inr (hnone.1 R₂ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
              · exact Or.inl (hall s h)
          simp only
          by_cases hc : idxOK π R = true
          · exact hmah rfl hc
          · unfold deadSeq
            rw [if_neg hc]
            exact hFam R _ hpm hfrp hdom hy₀ (Or.inr hxp) fun c e => by
              subst e
              rw [mkApp_noArg rfl (Or.inr hpR₂)] at hm2
              cases hm2

end RTKA.Fund
