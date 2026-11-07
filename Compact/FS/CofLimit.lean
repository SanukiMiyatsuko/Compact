import Compact.FS.CofSeed

/-! 極限の引数の崩壊 `limitSeq` の共終性（`seqI_limit` と同じ分岐）。

* 素の列：`T = X` なので段の節点は全て `ArgS`。
* 種の挿入：`a ≥ T` の節点は、残りが種 `p` 一つで、成分の前線が `p` 未満（種の主張で `x < p`）。
* Mahlo 添字 `p` の列：`T = X`。
* 族の閉包：目標 `π` の節点は全て種以下（`LoT`）。 -/

namespace RTKA.Fund

open Tm W

/-- `x` は `t` 未満の `t` の真の部分項以下 -/
def SubLe (t x : Tm) : Prop := ∃ w, w ∈ subs t ∧ w ≠ t ∧ Lt w t ∧ Le x w

theorem SubLe.lt {t x y : Tm} (h : SubLe t x) (ht : WNF t) (hx : WNF x) (hy : WNF y) (hG : Gp t y) : Lt x y := by
  obtain ⟨w, hw, hne, hwt, hxw⟩ := h
  exact lt_of_le_of_ltY hx (ht.of_mem_subs hw) hy hxw (hG w hw hne hwt)

/-- 下の段：目標が `t` より大きく `ρ` 以下の節点は種 `p` 以下か、`t` の部分項以下 -/
def LoT (t ρ p : Tm) : Prop :=
  ∀ x a, WNF x → Lt x t → argR? x = some a → Lt t (tgtN x) → Le (tgtN x) ρ → Le x p ∨ SubLe t x

/-- `mkApp` の出力は `app` か一つずらした `app` -/
theorem mkApp_form {ceil : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD} {P c : Tm} {s : SeqD}
    (h : mkApp ceil g pre R r P c = some s) :
    ∃ c', s = .app ceil g pre R r P c' ∨ s = .shift (.app ceil g pre R r P c') := by
  unfold mkApp at h
  split at h
  · cases h
  · split at h
    · dsimp only at h
      split at h
      · cases h
        exact ⟨_, Or.inl rfl⟩
      · split at h
        · cases h
        · split at h
          · cases h
            exact ⟨_, Or.inl rfl⟩
          · split at h
            · cases h
              exact ⟨_, Or.inr rfl⟩
            · cases h
              exact ⟨_, Or.inl rfl⟩
    · cases h
      exact ⟨_, Or.inl rfl⟩

/-- `mkApp` の出力の共終数は `r` の共終数で決まる -/
theorem mkApp_dom_big {ceil σ : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD} {P c : Tm} {s : SeqD}
    (h : mkApp ceil g pre R r P c = some s) (hd : r.dom = .big σ) (hlt : Lt σ ceil) : s.dom = .big σ := by
  obtain ⟨c', rfl | rfl⟩ := mkApp_form h
  · exact app_dom_big_lt hd (ltB_iff.mpr hlt)
  · exact app_dom_big_lt (c := c') (P := P) (g := g) (pre := pre) (R := R) (τ := ceil) hd (ltB_iff.mpr hlt)

/-- `mkApp` が `none` なら、目標の引数は `pre ⊕ R` 以上 -/
theorem mkApp_none_le {π X P ceil R : Tm} {g : Gen} {pre rest : List Tm} {r : SeqD}
    (hg : g.tgt? = some π) (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (hPR : Lt P R) (h : mkApp ceil g pre R r P .zero = none) :
    ∃ q, argR? π = some q ∧ Le (oadd (ofSummands pre) R) q := by
  have hπF := ht.psi.piF
  have hX := ht.psi.aF
  have hN : NFL (pre ++ R :: rest) := hsum ▸ nfl_summands hX
  have hRN := hN.1 R (List.mem_append_right _ List.mem_cons_self)
  have hpreN := nfl_append_left hN
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
    have hqF := wnf_of_argR hπF hq
    by_cases hle : leB R rt = true
    · have hRrt : Le R rt := le_of_ne_gtY hRN.1 hrtF (leB_iff.mp hle)
      refine ⟨q, hq, ?_⟩
      have hTF := wnf_oadd (wnf_ofSummands hpreN) hRN.1
      have hge : ∀ s h r, s ∈ pre → summands R = h :: r → leB h s = true := fun s h r hs e => by
        rw [summands_principal hRN.2] at e
        simp only [List.cons.injEq] at e
        rw [← e.1, leB_iff]
        exact le_of_nfl_append hN s hs
      have hsT : summands (oadd (ofSummands pre) R) = pre ++ [R] := by
        rw [summands_oadd_pre hpreN hRN.1 hge, summands_principal hRN.2]
      cases hst : summands rt with
      | nil =>
        rw [eq_zero_of_summands_nil hst] at hRrt
        rcases hRrt with e | h'
        · rw [e] at hPR
          exact absurd hPR (not_lt_zero _)
        · exact absurd h' (not_lt_zero _)
      | cons a l =>
        have haN := (nfl_summands hrtF).1 a (by rw [hst]; exact List.mem_cons_self)
        have hRa : Le R a := by
          rcases hRrt with e | h'
          · rw [← e, summands_principal hRN.2] at hst
            simp only [List.cons.injEq] at hst
            exact Or.inl hst.1
          · exact le_head_of_prin_lt hRN.1 hRN.2 hrtF hst h'
        rcases hRa with e | hRa'
        · subst e
          cases l with
          | nil =>
            refine Or.inl (FWOrder.eq hTF hqF ?_)
            rw [cmp_eq, hsT, hsq, hst, cmpList_append_same, cmpList_cons_cons_eq _ _ (cmpP_self R),
              cmpList_nil_nil]
          | cons b l' =>
            refine Or.inr ?_
            unfold Lt
            rw [cmp_eq, hsT, hsq, hst, cmpList_append_same, cmpList_cons_cons_eq _ _ (cmpP_self R)]
            exact cmpList_nil_cons _ _
        · refine Or.inr ?_
          unfold Lt
          rw [cmp_eq, hsT, hsq, hst, cmpList_append_same]
          exact cmpList_head_lt _ _ ((lt_principal_iff hRN.2 haN.2).mp hRa')
    · rw [ite_eq_right hle] at h
      split at h
      · cases h
      · split at h <;> cases h

/-- 目標 `π` の段の下の段：`t` の目標の節点が全て種以下なら `LoT` -/
theorem lot_top {π X p : Tm} (ht : WNF (.Psi .zero π X)) (hpF : WNF p)
    (hw : ∀ w, (w ∈ fr π X ∨ w ∈ fr π π) → Le w p)
    (h : ∀ s a, WNF (.Psi s π a) → Lt (.Psi s π a) (.Psi .zero π X) → Lt a X → Le (.Psi s π a) p) :
    LoT (.Psi .zero π X) π p := by
  have hπF := ht.psi.piF
  have hwF : ∀ w, (w ∈ fr π X ∨ w ∈ fr π π) → WNF w := fun w hw' => by
    rcases hw' with hw' | hw'
    · exact ht.psi.aF.of_mem_subs (fr_spec hw').1
    · exact hπF.of_mem_subs (fr_spec hw').1
  intro x a hx hxt harg htk hkπ
  cases x with
  | Psi s k a' =>
    have hP := hx.psi
    rcases below_psi ht hx hxt with h' | ⟨w, hw', hle⟩ | ⟨htk', ha, -, -, hkC⟩
    · exact absurd h' (Lt.asymmY ht hP.piF htk)
    · exact Or.inl (le_transY hx (hwF w hw') hpF hle (hw w hw'))
    · have hπk := tgt_ge ht hP.piF htk' hkC
      have e : k = π := le_antisymmY hP.piF hπF hkπ hπk
      subst e
      exact Or.inl (h s a' hx hxt ha)
  | Xi j b =>
    obtain ⟨hj, -, -, -, -⟩ := hx.xi
    rcases below_xi ht hx hxt with h' | ⟨w, hw', hle⟩ | ⟨htK, -, -⟩
    · exact absurd h' (Lt.asymmY ht (WNF.K' hj) htk)
    · exact Or.inl (le_transY hx (hwF w (Or.inr hw')) hpF hle (hw w (Or.inr hw')))
    · exfalso
      have hπk := tgt_ge ht (WNF.K' hj) htK (inC_K _ _ _)
      have e : Tm.K j = π := le_antisymmY (WNF.K' hj) hπF hkπ hπk
      exact IsTgt.ne_K ht.psi.tgt j e.symm
  | _ => cases harg

/-- 節点の目標は標準形（`t` より大きい目標） -/
theorem tgtN_wnf_lt {t x : Tm} (hx : WNF x) (h : Lt t (tgtN x)) : WNF (tgtN x) := by
  cases x with
  | Psi s k a => exact hx.psi.piF
  | Xi j b => exact WNF.K' hx.xi.1
  | _ => exact absurd h (not_lt_zero _)

/-- 種の分岐：最後の加数が種 `p`（`pre` の前線にない）なら、引数が `pre` 以上 `X` 未満で添字が `p` 未満の
    `π` への崩壊は `p` 未満 -/
theorem seed_cover {π X p x₀ s a : Tm} {pre : List Tm} (H : Approx1 .zero π X .zero pre [] p x₀)
    (hx0 : x₀ = .zero → ∀ v, v ∈ subs p → v = p)
    (hG : ∀ v, v ∈ subs p → v ≠ p → Lt v p → Lt v x₀)
    (hlt : Lt (.Psi .zero π (approx pre .zero x₀)) p) (hpm : p ∈ fr π X)
    (hfr : ∀ f, f ∈ fr π X → Le f p) (hpre' : ∀ s, s ∈ pre → p ∉ fr π s)
    (hx : WNF (.Psi s π a)) (hxt : Lt (.Psi s π a) (.Psi .zero π X)) (haX : Lt a X)
    (haT : ¬ Lt a (ofSummands pre)) (hsp : Lt s p) : Lt (.Psi s π a) p := by
  have hX := H.hX
  have hπF := H.hπF
  have hpF := H.hRF
  have hy₀ := H.hnf
  have hP := hx.psi
  have hN : NFL (pre ++ [p]) := H.hsum ▸ nfl_summands hX
  have haX' := haX
  rw [eq_oadd_of_sum hX H.hsum] at haX'
  rcases lt_oadd_cases hN hP.aF haX' with h | ⟨a', ha'F, ha'p, hsa, -⟩
  · exact absurd h haT
  refine seed_lt H hx0 hG hlt hpm hfr hx hxt haX fun w hw => ?_
  simp only [parF, List.mem_append] at hw
  rcases hw with (hw | hw) | hw
  · obtain ⟨u, hu, hwu⟩ := (mem_fr_iff hP.aF).mp hw
    rw [hsa] at hu
    rcases List.mem_append.mp hu with hu | hu
    · have hwX : w ∈ fr π X := (mem_fr_iff hX).mpr ⟨u, by rw [H.hsum]; exact List.mem_append_left _ hu, hwu⟩
      rcases hfr w hwX with e | h'
      · subst e
        exact absurd hwu (hpre' u hu)
      · exact h'
    · have hw' : w ∈ fr π a' := (mem_fr_iff ha'F).mpr ⟨u, hu, hwu⟩
      exact lt_of_le_of_ltY (ha'F.of_mem_subs (fr_spec hw').1) ha'F hpF (fr_leY hπF ha'F hw') ha'p
  · exact lt_of_le_of_ltY (hP.xiF.of_mem_subs (fr_spec hw).1) hP.xiF hpF (fr_leY hπF hP.xiF hw) hsp
  · exact lt_transY (hπF.of_mem_subs (fr_spec hw).1) hy₀ hpF (FWOrder.k2t hy₀ w hw) hlt

/-- 残りが種だけなら、残りは一つ -/
theorem pre_split {pre pre₂ rest : List Tm} {R R₂ : Tm} (e : pre ++ [R] = pre₂ ++ R₂ :: rest)
    (hne : rest ≠ []) (hall : ∀ s, s ∈ rest → s = R) (hR : R ∉ pre) : pre = pre₂ ++ [R₂] := by
  rcases List.eq_nil_or_concat rest with h | ⟨l, z, rfl⟩
  · exact absurd h hne
  have e1 : pre ++ [R] = (pre₂ ++ R₂ :: l) ++ [z] := by rw [e]; simp
  have e2 := (List.append_inj' e1 rfl).1
  cases l with
  | nil => exact e2
  | cons w l' =>
    exfalso
    apply hR
    have hw : w = R := hall w (by simp)
    rw [e2, ← hw]
    simp

/-- 目標 `π` の段の `mkApp` の出力の列の共終性：引数が `T = pre ⊕ R` 以上の節点は仮定 `hN` -/
theorem cof_pack {ξ π X P : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r s : SeqD}
    (hg : GenPsi g ξ π) (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (S : SeedHyp π X P R) (hR1 : R ≠ .one) (hx0 : WNF r.first) (hx0R : Lt r.first R)
    (h : mkApp π g pre R r P .zero = some s) (hI : IdxHyp ξ π X) (hξ : Le ξ (ofSummands pre))
    (hRI : SeqI R r) (hRC : SeqC R r) (h0 : r.dom ≠ .zero) (h1 : r.dom ≠ .one)
    (hRp : isPrincipal R = true) (hRne : ∀ m, r.dom = .big (.K m) → R ≠ succK m)
    (pk : Pack ξ π X P pre rest R π r s) (hsI : SeqI (.Psi .zero π X) s)
    (hN : ∀ x y, InSeq s y → WNF x → Lt x (.Psi .zero π X) →
      (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w y) →
      ∀ s' a, x = .Psi s' π a → Lt a X → ¬ Lt a (oadd (ofSummands pre) R) → Lt x y) :
    SeqC (.Psi .zero π X) s := by
  have hP := ht.psi
  have hπF := hP.piF
  have hπt := hP.tgt
  have hπK : ∀ m, 1 ≤ m → ¬ Lt (.K m) π → Lt π (.K m) := fun m hm h' => by
    rcases triY hπF (WNF.K' hm) with h'' | h'' | h''
    · exact h''
    · exact absurd h'' (IsTgt.ne_K hπt m)
    · exact absurd h'' h'
  have hN' : NFL (pre ++ [R]) := by
    have h' : NFL (pre ++ R :: rest) := hsum ▸ nfl_summands hP.aF
    rw [show pre ++ R :: rest = (pre ++ [R]) ++ rest by simp] at h'
    exact nfl_append_left h'
  have hvac : ∀ x, WNF x → Lt (.Psi .zero π X) (tgtN x) → Lt (tgtN x) π → Le π (tgtN x) → False :=
    fun x hx htk hkπ hπk => not_lt_of_leY hπF (tgtN_wnf_lt hx htk) hπk hkπ
  unfold SeqC
  cases hd : s.dom with
  | zero => trivial
  | one => trivial
  | omega =>
    have hNI : NatInv (.Psi .zero π X) s := by
      unfold SeqI at hsI
      rwa [hd] at hsI
    have hform : ∀ n, ∃ A, s.nat n = .Psi ξ π A := fun n => by
      obtain ⟨P', x, -, e, -⟩ := pk.form (Or.inl ⟨hd, n, rfl⟩)
      exact ⟨_, e⟩
    have hnb : ∀ σ, r.dom = .big σ → ¬ Lt σ π := fun σ hd' hlt => by
      rw [mkApp_dom_big h hd' hlt] at hd
      cases hd
    have hS := arg_mkApp hg ht hsum S hR1 hx0 hx0R h hI hξ hRI hRC h0 h1 hRp hnb (fun _ _ h' => h') hπK
      hRne ht (lt_psi_targetY ht) fun n => (hNI.1.good n).2.1
    exact leaf_nat ht hπt (Or.inl rfl) (fun u hu => hu) hNI hform hS
      (fun x _ hx _ _ htk hkπ hπk => (hvac x hx htk hkπ hπk).elim)
      fun x N hx hxt hpar s' a e haX haT => ⟨N, hN x (s.nat N) (Or.inl ⟨hd, N, rfl⟩) hx hxt hpar s' a e haX haT⟩
  | big σ =>
    have hsI' := hsI
    unfold SeqI at hsI'
    rw [hd] at hsI'
    obtain ⟨⟨hU, -⟩, hG, -⟩ := hsI'
    rcases pk with ⟨-, hd'⟩ | ⟨σ', D⟩
    · rw [hd] at hd'
      cases hd'
    obtain ⟨g', c, hg', rfl, adj, -⟩ := D.ex
    have hσσ : σ' = σ := by
      have := app_dom_big_lt (P := P) (c := c) (g := g') (pre := pre) (R := R) (τ := π) D.hd (ltB_iff.mpr D.hσc)
      rw [this] at hd
      cases hd
      rfl
    subst hσσ
    have hS := argB_app (ceil := π) (P := P) hg' hN' adj.hF S.hPF D.hd D.hB.1 hRC
    exact leaf_big ht hπt (Or.inl rfl) (fun u hu => hu) hU.hσF hU (hG rfl) (fun β _ _ => ⟨_, app_big_eq hg'⟩)
      hS (fun x _ hx _ _ _ _ _ _ htk hkπ hπk => (hvac x hx htk hkπ hπk).elim)
      fun x β hx hxt hβ hβσ _ _ hpar s' a e haX haT =>
        hN x _ (Or.inr ⟨σ', β, hd, hβ, hβσ, rfl⟩) hx hxt hpar s' a e haX haT


/-- 極限の引数の崩壊の列の共終性 -/
theorem seqC_limit {π X : Tm} {πf : Fam} (ht : WNF (.Psi .zero π X)) (hX0 : X ≠ .zero)
    (hl : ¬ isSucc X = true)
    (hS : ∀ S, S ∈ summands X → S ≠ .one → SeqI S (info S).seq)
    (hSC : ∀ S, S ∈ summands X → S ≠ .one → SeqC S (info S).seq)
    (hFam : ∀ p W, p ∈ fr π X → (∀ f, f ∈ fr π X → Le f p) → Dom (.Psi .zero π X) p →
      WNF (.Psi .zero π W) → Le (.Psi .zero π W) p →
      (∀ c, π = .Om c → ∀ v, v ∈ subs (.Psi .zero π X) → v ≠ .Psi .zero π X → Lt v (.Psi .zero π X) → Le v p) →
      LoT (.Psi .zero π X) π p → SeqI (.Psi .zero π X) (famSeq πf π (some p)) →
      SeqC (.Psi .zero π X) (famSeq πf π (some p))) :
    SeqI (.Psi .zero π X) (limitSeq π πf π X (info X).sums none) →
      SeqC (.Psi .zero π X) (limitSeq π πf π X (info X).sums none) := by
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
  have hRC := hSC R hRm hRne
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
  have hplain : SeqI (.Psi .zero π X) s0 → SeqC (.Psi .zero π X) s0 := fun hI =>
    cof_pack (genPsi0 π) ht hsum0 S0 hRne hx0F hx0R hs0 (IdxHyp.zero ht) (zero_le _) hRI hRC h0 h1 hRp
      (fun _ hd => dom_ne_succK hd) pk0 hI fun _ _ _ _ _ _ _ _ _ haX haT =>
        absurd (by rwa [eq_oadd_of_sum hX hsum0] at haX) haT
  have hfrWNF : ∀ x, x ∈ frB π X → WNF x := fun x hx => by
    rw [frB_eq_fr] at hx
    exact hX.of_mem_subs (fr_spec hx).1
  have hmo : maxOpt none (maxL (frB π X)) = maxL (frB π X) := by
    cases maxL (frB π X) <;> rfl
  rw [hmo]
  cases hm : maxL (frB π X) with
  | none => exact hplain
  | some p =>
    have hpm : p ∈ fr π X := by
      have := maxL_mem hm
      rwa [frB_eq_fr] at this
    have hfrp : ∀ f, f ∈ fr π X → Le f p := fun f hf =>
      le_maxL hfrWNF hm (by rw [frB_eq_fr]; exact hf)
    have hpF : WNF p := hX.of_mem_subs (fr_spec hpm).1
    have hpκ : Lt p π := (fr_spec hpm).2
    have hpt : Lt p (.Psi .zero π X) := FWOrder.k2 ht p hpm
    have hpn : p ∈ fr π p := by
      rcases fr_node hpm with ⟨m, a, rfl⟩ | ⟨s, q, a, rfl⟩ <;> simp [fr, hpκ]
    dsimp only
    by_cases h2 : ltB p s0.first = true
    · rw [ite_eq_left h2]
      exact hplain
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
      have hwp : ∀ w, (w ∈ fr π X ∨ w ∈ fr π π) → Le w p := fun w hw => by
        rcases hw with hw | hw
        · exact hfrp w hw
        · exact Or.inr (lt_transY (hπF.of_mem_subs (fr_spec hw).1) hy₀ hpF (FWOrder.k2t hy₀ w hw) hxp)
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
          exact Or.inl (List.mem_singleton.mp hs)) hy₀ (Or.inr hxp) (fun _ _ v hv hne hl => ?_) ?_
        · have hvF := ht.of_mem_subs hv
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
        · refine lot_top ht hRF hwp fun s a hx hxt haX => Or.inr ?_
          have hQ := hx.psi
          refine seed_cover H₀ hx₀0 hx₀g hxp hpm hfrp (fun s hs => by cases hs) hx hxt haX
            (fun h => not_lt_zero _ h) ?_
          exact lt_of_le_of_ltY hQ.xiF hQ.aF hRF (le_of_ne_gtY hQ.xiF hQ.aF hQ.le) (by rwa [hXR] at haX)
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
        have hRC' := hSC R₂ hRm' hRne'
        obtain ⟨hx1F, hx1R⟩ := first_good hRI' h0' h1'
        have hps : ¬ isSucc p = true := by
          rw [isSucc_principal (by rcases fr_node hpm with ⟨m, a, rfl⟩ | ⟨s, q, a, rfl⟩ <;> rfl)]
          rcases fr_node hpm with ⟨m, a, rfl⟩ | ⟨s, q, a, rfl⟩ <;> simp
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
        have hN2 : NFL (pre₂ ++ [R₂]) := by
          have h' : NFL (pre₂ ++ R₂ :: rest.map Prod.fst) := hsum₂ ▸ hN
          rw [show pre₂ ++ R₂ :: rest.map Prod.fst = (pre₂ ++ [R₂]) ++ rest.map Prod.fst by simp] at h'
          exact nfl_append_left h'
        have hTF : WNF (oadd (ofSummands pre₂) R₂) := wnf_oadd (wnf_ofSummands (nfl_append_left hN2)) hRF'
        have hmi : idxOK π p = false → Le (mi π) p := fun hidx => by
          refine le_of_not_ltY hpF (WFY.WNF.mi hπF) fun h' => ?_
          have : idxOK π p = true := by
            unfold idxOK
            rw [mOfT_tgt hP.tgt, ltB_iff.mpr h', WFY.inC_of_ltY _ hpF hπF hpκ]
            rfl
          rw [this] at hidx
          cases hidx
        dsimp only
        -- Mahlo 添字 `p` の列
        have hmah : R = p → idxOK π p = true →
            SeqI (.Psi .zero π X) (deadSeq π πf π p (info X).sums) →
            SeqC (.Psi .zero π X) (deadSeq π πf π p (info X).sums) := by
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
            exact fun hI' => cof_pack (Or.inr rfl) ht hsum0 S0 hRne hx0F hx0R hm3 hI hξ hRI hRC h0 h1 hRp
              (fun _ hd => dom_ne_succK hd) pk hI' fun _ _ _ _ _ _ _ _ _ haX haT =>
                absurd (by rwa [eq_oadd_of_sum hX hsum0] at haX) haT
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
          refine fun hI => cof_pack (genPsi0 π) ht hsum₂ S₂ hRne' hx1F hx1R hm2 (IdxHyp.zero ht) (zero_le _) hRI'
            hRC' h0' h1' hRp' (fun _ hd => dom_ne_succK hd) pk hI fun x y hy hx hxt _ s' a e haX haT => ?_
          subst e
          have hne2 : rest.map Prod.fst ≠ [] := fun e' => by
            apply haT
            have hX2 : X = oadd (ofSummands pre₂) R₂ := eq_oadd_of_sum hX (by rw [hsum₂, e'])
            rwa [hX2] at haX
          obtain ⟨hRe, hall⟩ := hrs hne2
          subst hRe
          have hidx : idxOK π R = false := by
            cases e' : idxOK π R with
            | false => rfl
            | true =>
              exfalso
              apply hC
              have : ltB R R = false := by
                cases e'' : ltB R R with
                | false => rfl
                | true => exact absurd (ltB_iff.mp e'') (Lt.irrefl _)
              rw [e', this]
              rfl
          have hpre2 : pre = pre₂ ++ [R₂] :=
            pre_split (by rw [← hsum, hsum₂]) hne2 hall fun h' => hpre' R h' hpn
          have hT : ofSummands pre = oadd (ofSummands pre₂) R₂ := by
            rw [hpre2]
            exact eq_oadd_of_sum (wnf_ofSummands hN2) (summands_ofSummands _ (nfl_principal hN2))
          have hxR := seed_cover H₀ hx₀0 hx₀g hxp hpm hfrp hpre' hx hxt haX (by rwa [hT])
            (lt_of_lt_of_leY hx.psi.xiF (WFY.WNF.mi hπF) hRF hx.psi.mlt (hmi hidx))
          exact lt_transY hx hRF (pk.wnf hy) hxR (pk.seed hpn hy)
        | none =>
          have hnone := mkApp_none rfl ht hsum₂ hpR' hm2
          obtain ⟨q, hq, hTq⟩ := mkApp_none_le rfl ht hsum₂ hpR' hm2
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
            rw [ite_eq_right hc]
            refine hFam R _ hpm hfrp hdom hy₀ (Or.inr hxp) (fun c e => ?_) ?_
            · subst e
              rw [mkApp_noArg rfl (Or.inr hpR₂)] at hm2
              cases hm2
            · have hpre2 : pre = pre₂ ++ [R₂] :=
                pre_split (by rw [← hsum, hsum₂]) hnone.2 hall fun h' => hpre' R h' hpn
              have hT : ofSummands pre = oadd (ofSummands pre₂) R₂ := by
                rw [hpre2]
                exact eq_oadd_of_sum (wnf_ofSummands hN2) (summands_ofSummands _ (nfl_principal hN2))
              have hqF := wnf_of_argR hπF hq
              refine lot_top ht hRF hwp fun s a hx hxt haX => Or.inr ?_
              have haq : Lt q a := arg_lt_of_psi hx hq
              refine seed_cover H₀ hx₀0 hx₀g hxp hpm hfrp hpre' hx hxt haX (fun h' => ?_)
                (lt_of_lt_of_leY hx.psi.xiF (WFY.WNF.mi hπF) hRF hx.psi.mlt (hmi (by simpa using hc)))
              rw [hT] at h'
              exact Lt.asymmY hx.psi.aF hTF h' (lt_of_le_of_ltY hTF hqF hx.psi.aF hTq haq)

end RTKA.Fund
