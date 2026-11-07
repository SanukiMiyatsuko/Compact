import Compact.FS.CofApp

/-! `mkApp` の出力の列の共終性と、極限の引数の崩壊 `limitSeq`。 -/

namespace RTKA.Fund

open Tm W

/-- 分割の補題（列）：共通の接頭辞で分ける -/
theorem cmpList_cases : ∀ {pre l : List Tm} {R : Tm}, NFL l → (∀ x, x ∈ pre → WNF x ∧ isPrincipal x = true) →
    cmpList l (pre ++ [R]) = .lt → cmpList l pre = .lt ∨ ∃ l', l = pre ++ l' ∧ cmpList l' [R] = .lt
  | [], l, R, _, _, h => Or.inr ⟨l, rfl, h⟩
  | h :: tl, [], R, _, _, _ => Or.inl (cmpList_nil_cons _ _)
  | h :: tl, u :: us, R, hl, hp, e => by
    have hu := hl.1 u List.mem_cons_self
    have hh := hp h List.mem_cons_self
    cases ec : cmpP u h with
    | lt => exact Or.inl (cmpList_head_lt _ _ ec)
    | gt =>
      rw [List.cons_append, cmpList_cons_cons_ne _ _ (by rw [ec]; decide), ec] at e
      cases e
    | eq =>
      have e1 : u = h := eq_of_cmpP_eqY hu.1 hh.1 hu.2 hh.2 ec
      subst e1
      rw [List.cons_append, cmpList_cons_cons_eq _ _ ec] at e
      rcases cmpList_cases (nfl_tail hl) (fun x hx => hp x (List.mem_cons_of_mem _ hx)) e with h' | ⟨l', e', h'⟩
      · refine Or.inl ?_
        rw [cmpList_cons_cons_eq _ _ ec]
        exact h'
      · exact Or.inr ⟨l', by rw [e']; rfl, h'⟩

/-- `a < pre ⊕ R` は `a < pre` か `a = pre ⊕ a'`（`a' < R`） -/
theorem lt_oadd_cases {pre : List Tm} {R a : Tm} (hN : NFL (pre ++ [R])) (ha : WNF a)
    (hlt : Lt a (oadd (ofSummands pre) R)) :
    Lt a (ofSummands pre) ∨ ∃ a', WNF a' ∧ Lt a' R ∧ summands a = pre ++ summands a' ∧
      a = oadd (ofSummands pre) a' := by
  have hRN := hN.1 R (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  have hpreN := nfl_append_left hN
  have hge : ∀ s h r, s ∈ pre → summands R = h :: r → leB h s = true := fun s h r hs e => by
    rw [summands_principal hRN.2] at e
    simp only [List.cons.injEq] at e
    rw [← e.1, leB_iff]
    exact le_of_nfl_append (rest := []) hN s hs
  have hs : summands (oadd (ofSummands pre) R) = pre ++ [R] := by
    rw [summands_oadd_pre hpreN hRN.1 hge, summands_principal hRN.2]
  have h1 : cmpList (summands a) (pre ++ [R]) = .lt := by
    have := hlt
    unfold Lt at this
    rwa [cmp_eq, hs] at this
  rcases cmpList_cases (nfl_summands ha) hpreN.1 h1 with h2 | ⟨l', e, h3⟩
  · refine Or.inl ?_
    unfold Lt
    rw [cmp_eq, summands_ofSummands _ (nfl_principal hpreN)]
    exact h2
  · have hlN : NFL l' := by
      have := nfl_summands ha
      rw [e] at this
      exact nfl_append_right this
    have ha'F := wnf_ofSummands hlN
    have hs' : summands (ofSummands l') = l' := summands_ofSummands _ (nfl_principal hlN)
    have ha'R : Lt (ofSummands l') R := by
      unfold Lt
      rw [cmp_eq, hs', summands_principal hRN.2]
      exact h3
    refine Or.inr ⟨_, ha'F, ha'R, by rw [hs']; exact e, ?_⟩
    have e2 : summands (oadd (ofSummands pre) (ofSummands l')) = pre ++ l' := by
      rw [summands_oadd_pre hpreN ha'F (head_le_pre (rest := []) hN ha'F ha'R), hs']
    rw [← ofSummands_summands a ha, e, ← e2, ofSummands_summands _ (wnf_oadd (wnf_ofSummands hpreN) ha'F)]

/-- 対角化の調整の中身 -/
theorem kAdj_out {τ ceil σ : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD} (hd : r.dom = .big σ)
    (hK : ∀ m, σ ≠ .K m) (hlt : ltB σ ceil = false) (ho : outsideMode ceil σ g pre R = true) :
    kAdj τ ceil g pre R r = frCl (closedS σ (oadd (ofSummands pre) R)) τ := by
  unfold kAdj
  rw [hd]
  cases σ with
  | K m => exact absurd rfl (hK m)
  | _ => simp [hlt, ho]

theorem kAdj_canon {τ ceil : Tm} {m : Nat} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD}
    (hd : r.dom = .big (.K m)) (hlt : ltB (.K m) ceil = false) (hcan : canonK (.K m) g pre R = true) :
    kAdj τ ceil g pre R r = frCl (closedPt m) τ := by
  unfold kAdj
  rw [hd]
  simp [hlt, hcan]

/-- `mkApp` の出力の列の引数の共終性 -/
theorem arg_mkApp {ξ τ X P ceil t : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r s : SeqD}
    (hg : GenPsi g ξ τ) (ht : WNF (.Psi .zero τ X)) (hsum : summands X = pre ++ R :: rest)
    (S : SeedHyp τ X P R) (hR1 : R ≠ .one) (hx0 : WNF r.first) (hx0R : Lt r.first R)
    (h : mkApp ceil g pre R r P .zero = some s) (hI : IdxHyp ξ τ X) (hξ : Le ξ (ofSummands pre))
    (hRI : SeqI R r) (hRC : SeqC R r) (h0 : r.dom ≠ .zero) (h1 : r.dom ≠ .one)
    (hRp : isPrincipal R = true) (hnb : ∀ σ, r.dom = .big σ → ¬ Lt σ ceil)
    (hσlow : ∀ σ, r.dom = .big σ → Lt σ τ → Lt σ ceil)
    (hπK : ∀ m, 1 ≤ m → ¬ Lt (.K m) ceil → Lt τ (.K m))
    (hRne : ∀ m, r.dom = .big (.K m) → R ≠ succK m)
    (htF : WNF t) (htτ : Lt t τ) (hyt : ∀ n, Lt (s.nat n) t) :
    ArgS t (oadd (ofSummands pre) R) ξ τ s := by
  have hP := ht.psi
  have hτF := hP.piF
  have hX := hP.aF
  have hN : NFL (pre ++ R :: rest) := hsum ▸ nfl_summands hX
  have hRN := hN.1 R (List.mem_append_right _ List.mem_cons_self)
  have hRF := hRN.1
  have hpreF := wnf_ofSummands (nfl_append_left hN)
  have hR0 : R ≠ .zero := fun e => by
    rw [e] at hRp
    cases hRp
  have hk : AdjHyp τ R (kAdj τ ceil g pre R r) := kAdj_spec hτF hR0 hRF fun σ hd => by
    have h' := hRI
    unfold SeqI at h'
    rw [hd] at h'
    exact ⟨h'.1.1.hσF, h'.1.1.hσle⟩
  obtain ⟨c, adj, hv0, hck, hs⟩ := mkApp_psi hg ht hsum S hR1 hx0 hx0R hk h
  have hTF := wnf_oadd hpreF hRF
  have hT0 : oadd (ofSummands pre) R ≠ .zero := fun e => by
    have h' := le_oadd_right hpreF hRF
    rw [e] at h'
    rcases h' with h' | h'
    · exact hR0 h'
    · exact not_lt_zero _ h'
  have hTs : ¬ isSucc (oadd (ofSummands pre) R) = true :=
    not_succ_oadd hpreF hRF hR0 (by
      rw [isSucc_principal hRp]
      simpa using hR1)
  have hlA : ∀ c' x, AdjHyp τ R c' → WNF x → Lt x R →
      Lt (approx pre P (oadd c' x)) (oadd (ofSummands pre) R) := fun c' x a' hx hxR =>
    oadd_lt_oadd hpreF (wnf_nsum (wnf_oadd a'.hF hx) S.hPF) hRF
      (nsum_lt_prin (wnf_oadd a'.hF hx) S.hPF hRp (oadd_lt_prin a'.hF hx hRp a'.hR hxR) S.hPR)
  have hAF : ∀ c' x, WNF c' → WNF x → WNF (approx pre P (oadd c' x)) := fun c' x hc hx =>
    wnf_oadd hpreF (wnf_nsum (wnf_oadd hc hx) S.hPF)
  have hτKl : ∀ {m : Nat}, 1 ≤ m → ltB (.K m) ceil = false → Lt τ (.K m) := fun hm hlt =>
    hπK _ hm fun h' => by
      rw [ltB_iff.mpr h'] at hlt
      cases hlt
  have hKC : ∀ {m : Nat} {c' : Tm}, AdjHyp τ R c' → ltB (.K m) ceil = false →
      canonK (.K m) g pre R = true → BigInv R (.K m) r → KCanon m X pre rest R r (kStart m c' P) := by
    intro m c' adj' hlt hcan hB
    have hm : 1 ≤ m := hB.1.hσF.k
    obtain ⟨hGF, hGK, -⟩ := start_spec (c := c') (P := P) hm adj'.hF S.hPF
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
    exact ⟨hm, hX, inC_mono_d hτF (WNF.K' hm) (Or.inr (hτKl hm hlt)) hX hP.Ca, hsum, hB, hT, hGF, hGK⟩
  -- `K` の正準な塔
  have hcanon : ∀ {m : Nat} {d : Nat} {s' : SeqD} {c' : Tm}, AdjHyp τ R c' → r.dom = .big (.K m) →
      ltB (.K m) ceil = false → canonK (.K m) g pre R = true → BigInv R (.K m) r →
      (c' = frCl (closedPt m) τ ∨ ∃ d, WNF d ∧ c' = oadd d (frCl (closedPt m) τ)) →
      (∀ q, argR? τ = some q → Lt q (oadd (ofSummands pre) R)) →
      (∀ n, s'.nat n = (SeqD.app ceil g pre R r P c').nat (n + d)) →
      ArgS t (oadd (ofSummands pre) R) ξ τ s' := by
    intro m d s' c' adj' hd hlt hcan hB hck' hrT hs'
    have hm : 1 ≤ m := hB.1.hσF.k
    have hτK : Lt τ (.K m) := hτKl hm hlt
    have H := hKC adj' hlt hcan hB
    obtain ⟨N, hN'⟩ := pass_canon H hd hRC hτF hP.tgt hτK hrT hTs hT0 adj'.hF S.hPF hck'
    exact argS_canon hg H hd hlt hcan hRC adj'.hF S.hPF htF
      ⟨N, Or.inr (lt_transY htF hτF (H.tower (N + 1)).1 htτ hN')⟩ hs'
  rcases hs with ⟨rfl, hV⟩ | ⟨rfl, hs2⟩
  · have hrT : ∀ q, argR? τ = some q → Lt q (oadd (ofSummands pre) R) := fun q hq =>
      lt_transY (wnf_of_argR hτF hq) (hAF c _ adj.hF hx0) hTF (hV q hq) (hlA c _ adj hx0 hx0R)
    unfold SeqI at hRI
    cases hd : r.dom with
    | zero => exact absurd hd h0
    | one => exact absurd hd h1
    | omega =>
      rw [hd] at hRI
      exact argS_nat hg hN adj.hF S.hPF hd (fun n => (hRI.1.good n).1) (fun n => (hRI.1.good n).2.2) hRC
    | big σ =>
      rw [hd] at hRI
      obtain ⟨hBW, hBS, hreg⟩ := hRI
      have hB : BigInv R σ r := ⟨hBW.1, hBS hRp⟩
      have hσF := hB.1.hσF
      have hσc := hnb σ hd
      have hlt' : ltB σ ceil = false := by
        cases e : ltB σ ceil with
        | false => rfl
        | true => exact absurd (ltB_iff.mp e) hσc
      rcases hreg with hσt | ⟨m, rfl⟩
      · rcases triY hσF hτF with h' | h' | h'
        · exact absurd (hσlow σ hd h') hσc
        · subst h'
          have hc0 := hv0 (kAdj_in hg hσt hd) (valid_in hg ht hsum S hd hB)
          subst hc0
          have H : DiagHyp ξ σ X .zero P pre rest R r :=
            { ht, hsum, hRU := hB.1, hRG := hB.2, hGF := WNF.zero, hGσ := zero_lt hP.tgt.ne_zero
              hGs := by simp [isSucc, summands]
              hQF := S.hPF, hQR := S.hPR, hQσ := S.hPπ, hI, hξ }
          exact argS_in hg H hd hlt' hRC htF hyt
        · have hne : σ ≠ τ := fun e => by
            rw [e] at h'
            exact Lt.irrefl _ h'
          have hRm : R ∈ summands X := by
            rw [hsum]
            exact List.mem_append_right _ List.mem_cons_self
          have hRC' := inC_of_mem_summands hX hP.Ca hRm
          have hσC := hB.1.hσC X τ hX hτF hRC'
          have htσ : WNF (.Psi .zero σ X) :=
            wnf_psi0 hσF hσt hX (inC_mono_d hτF hσF (Or.inr h') hX hP.Ca)
              (fun q hq => (arg_of_inC hq hσC (Lt.asymmY hτF hσF h')).2)
          obtain ⟨hGF, hGσ, hGs, -⟩ := sStart_spec (T := oadd (ofSummands pre) R) hσF hσt.ne_zero adj.hF S.hPF
          have hR0' : Lt .zero R := zero_lt hR0
          have H : DiagHyp .zero σ X (sStart σ (oadd (ofSummands pre) R) c P) .zero pre rest R r :=
            { ht := htσ, hsum, hRU := hB.1, hRG := hB.2, hGF, hGσ, hGs, hQF := WNF.zero, hQR := hR0'
              hQσ := zero_lt hσt.ne_zero
              hI := IdxHyp.zero htσ, hξ := zero_le _ }
          have ho : outsideMode ceil σ g pre R = true := by
            rw [outsideMode_tgt hσt, hg.tgt]
            simp [hne]
          have hK : ∀ m, σ ≠ .K m := fun m e => IsTgt.ne_K hσt m e
          have hck' : c = frCl (closedS σ (oadd (ofSummands pre) R)) τ ∨
              ∃ d, WNF d ∧ c = oadd d (frCl (closedS σ (oadd (ofSummands pre) R)) τ) := by
            rwa [kAdj_out hd hK hlt' ho] at hck
          obtain ⟨N, hN'⟩ := pass_out H hd hRC hσt hτF hP.tgt h' hrT hTs hT0 rfl adj.hF S.hPF hck'
          exact argS_out hg H hne rfl hd hlt' hRC adj.hF S.hPF htF
            ⟨N, Or.inr (lt_transY htF hτF (H.tower (N + 1)).1 htτ hN')⟩
      · have hm : 1 ≤ m := hσF.k
        cases hold : kOld m pre R with
        | true =>
          have H : KOld m X c P pre rest R r :=
            ⟨hm, hX, hsum, hB, adj.hF, S.hPF,
              le_of_ne_gtY (WNF.succK hm) hTF (leB_iff.mp hold), hRne m hd⟩
          exact argS_old hg H hd hlt' hold hRC
        | false =>
          have hcan : canonK (.K m) g pre R = true := by
            rw [canonK_psi hg, hold]
            rfl
          exact hcanon (d := 0) adj hd hlt' hcan hB (by rwa [kAdj_canon hd hlt' hcan] at hck) hrT
            fun n => rfl
  · obtain ⟨m, hd, hlt, hcan, hv⟩ := canonSecond_spec hs2
    have hB : BigInv R (.K m) r := by
      have h' := hRI
      unfold SeqI at h'
      rw [hd] at h'
      exact ⟨h'.1.1, h'.2.1 hRp⟩
    have hrT : ∀ q, argR? τ = some q → Lt q (oadd (ofSummands pre) R) := by
      intro q hq
      have h2 := validR_lt' hv hq
      rw [hg.comb] at h2
      obtain ⟨h3, h4⟩ := (hKC adj hlt hcan hB).tower 1
      obtain ⟨h5, h6⟩ := hB.1.good.1 _ h3 h4
      exact lt_transY (wnf_of_argR hτF hq) (hAF c _ adj.hF h5) hTF h2 (hlA c _ adj h5 h6)
    exact hcanon (d := 1) adj hd hlt hcan hB (by rwa [kAdj_canon hd hlt hcan] at hck) hrT fun n => rfl

end RTKA.Fund
