import Compact.FS.OmCases

/-! Ω 断片（`K`・`Ξ` を含まず、目標が全て `Ω_c` の項）の基本列の不変量。

大きさの帰納法で、断片の全ての標準形 `t` について `SeqInv t (info t).seq`（`seqInv_frag`）。
特に共終数 `ω` の列・共終数 `Ω_{d+1}` の列は標準形で、元の項より小さく、単調（`frag_nat`・`frag_big`）。 -/

namespace RTKA.Fund

open Tm W

theorem one_lt_om {e : Tm} (he : WNF (.Om e)) : Lt .one (.Om e) := by
  rcases triY WNF.one he with h | h | h
  · exact h
  · cases h
  · have := lt_oneY he h
    cases this

/-- `Ω_c` の部分項の主要項が `Ω_c` 未満なら、`c` の隙間のもとで `Ω_{x+1}` 未満 -/
theorem om_gap_head {c x h : Tm} (hOm : WNF (.Om c)) (hxF : WNF x) (hhF : WNF h)
    (hhp : isPrincipal h = true) (hsub : h ∈ subs c) (hlt : Lt h (.Om c))
    (hg : ∀ u, u ∈ subs c → u ≠ c → Lt u c → Le u x) : Lt h (.Om (succT x)) := by
  have hc := hOm.om.1
  have hY : WNF (.Om (succT x)) := WNF.om_succT hxF
  have hSx := succT_WNF hxF
  have hle : ∀ {u : Tm}, WNF u → u ∈ subs c → Lt u c → Lt u (succT x) := fun {u} hu hus hul =>
    lt_of_le_of_ltY hu hxF hSx (hg u hus hul.ne hul) (lt_succT x)
  have hOF : ∀ {u : Tm}, WNF u → IsOF u → u ∈ subs c → Lt u (.Om c) → Lt u (.Om (succT x)) :=
    fun hu hof hus hul => (lt_OF_omG hof hu hSx).mpr (hle hu hus ((lt_OF_omG hof hu hc).mp hul))
  match h, hhF, hhp, hsub, hlt with
  | .one, _, _, _, _ => exact one_lt_om hY
  | .K m, hhF, _, hsub, hlt =>
    have hm := hhF.k
    have h1 : Lt (.K m) c := (lt_K_omY hm hc).mp hlt
    exact (lt_K_omY hm hSx).mpr (hle hhF hsub h1)
  | .Om j, hhF, _, hsub, hlt =>
    have hj := hhF.om.1
    have hjc : Lt j c := (lt_om_iffY hj hc).mp hlt
    exact (lt_om_iffY hj hSx).mpr (hle hj (subs_trans hsub (mem_subs_om j)) hjc)
  | .Xi m b, hhF, _, hsub, hlt => exact hOF hhF (Or.inl ⟨m, b, rfl⟩) hsub hlt
  | .Psi s p a, hhF, _, hsub, hlt =>
    by_cases hp : ∃ e, p = .Om e
    · obtain ⟨e, rfl⟩ := hp
      have hP := hhF.psi
      have hs0 : s = .zero := lt_oneY hP.xiF hP.mlt
      subst hs0
      have he := hP.piF.om.1
      have h1 : ¬ Lt c e := fun h' => Lt.asymmY hhF hOm hlt ((lt_om_psiY hhF).mpr h')
      have h2 : Le e c := le_of_not_ltY hc he h1
      have h3 : e ≠ c := by
        intro e'
        have h4 := size_le_of_mem_subs hsub
        rw [e'] at h4
        simp only [Tm.size] at h4
        omega
      have h4 : Lt e c := h2.resolve_left h3
      have hes : e ∈ subs c :=
        subs_trans hsub (subs_psi_p (mem_subs_om e))
      have h5 := hle he hes h4
      rcases triY hhF hY with h6 | h6 | h6
      · exact h6
      · cases h6
      · exact absurd ((lt_om_psiY hhF).mp h6) (Lt.asymmY he hSx h5)
    · exact hOF hhF (IsOF.psi hhF fun e e' => hp ⟨e, e'⟩) hsub hlt

/-- `Ω_c`（`c` 極限）の隙間 -/
theorem om_gap {c x v : Tm} (ht : WNF (.Om c)) (hxF : WNF x)
    (hg : ∀ u, u ∈ subs c → u ≠ c → Lt u c → Le u x) (hv : v ∈ subs (.Om c)) (hne : v ≠ .Om c)
    (hlt : Lt v (.Om c)) : Lt v (.Om (succT x)) := by
  have hc := ht.om.1
  have hv' : v ∈ subs c := by
    simp only [subs, List.mem_cons] at hv
    rcases hv with h | h
    · exact absurd h hne
    · exact h
  have hvF := hc.of_mem_subs hv'
  cases hs : summands v with
  | nil =>
    rw [eq_zero_of_summands_nil hs]
    exact zero_lt (by intro e; cases e)
  | cons h r =>
    have hN := nfl_summands hvF
    have hhm : h ∈ summands v := by
      rw [hs]
      exact List.mem_cons_self
    have hm := hN.1 h hhm
    have hle : Le h v := by
      have := le_ofSummands_of_mem hN hhm
      rwa [ofSummands_summands v hvF] at this
    have hsub := subs_trans hv' (mem_subs_of_mem_summands hhm)
    exact lt_prin_of_head hs rfl hm.2 (om_gap_head ht hxF hm.1 hm.2 hsub
      (lt_of_le_of_ltY hm.1 hvF ht hle hlt) hg)

theorem natInv_om {c : Tm} {s : SeqD} (ht : WNF (.Om c)) (hs : ¬ isSucc c = true)
    (hc : NatInv c s) : NatInv (.Om c) (.om s) := by
  have hcF := ht.om.1
  have hx := fun n => (hc.1.good n).1
  refine ⟨⟨fun n => ⟨WNF.om_succT (hx n), ?_, ?_⟩, (fun n e => by cases e),
    fun g d n hg hd h => ?_, fun g d n hg hd h => ?_⟩, fun n v hv hne hlt => ?_⟩
  · exact (lt_om_iffY (succT_WNF (hx n)) hcF).mpr
      (succT_lt_of_not_succ (hx n) hcF hs (hc.1.good n).2.1)
  · exact (lt_om_iffY (succT_WNF (hx n)) (succT_WNF (hx (n + 1)))).mpr
      (succT_lt_succT (hx n) (hx (n + 1)) (hc.1.good n).2.2)
  · rw [inC_om] at h
    show inC (.Om (succT (s.nat n))) g d = true
    rw [inC_om]
    exact inC_succT (hc.1.ub g d n hg hd h)
  · have h' : inC (.Om (succT (s.nat (n + 1)))) g d = true := h
    rw [inC_om] at h'
    show inC (.Om (succT (s.nat n))) g d = true
    rw [inC_om]
    exact inC_succT (hc.1.ub2 g d n hg hd (inC_of_succT h'))
  · exact om_gap ht (hx n) (fun u hu hne' hlt' => Or.inr (hc.2 n u hu hne' hlt')) hv hne hlt

theorem bigInv_om {c σ : Tm} {s : SeqD} (ht : WNF (.Om c)) (hs : ¬ isSucc c = true)
    (hc : BigInvW c σ s) : BigInv (.Om c) σ (.om s) := by
  have hcF := ht.om.1
  have hU := hc.1
  have hx := fun ξ hξ hξσ => (hU.good.1 ξ hξ hξσ).1
  refine ⟨⟨⟨fun ξ hξ hξσ => ⟨WNF.om_succT (hx ξ hξ hξσ), ?_⟩, fun ξ η hξ hη hlt hησ => ?_⟩,
    (fun ξ _ _ e => by cases e), hU.hσF, ?_, subs_om hU.hσs, fun g d hg hd h => ?_,
    fun g d ξ hg hd hξ hξσ h0 hok h hξC => ?_, fun g d ξ η hg hd hξ hη hlt hησ h hξC => ?_,
    fun g d ξ hd hξ hξσ h => ?_, fun _ ξ _ _ _ => ?_,
    fun m e h ξ hξ hξσ => ?_, fun m e h ξ hξ hξσ => ?_⟩, fun ξ hξ hξσ v hv hne hlt => ?_⟩
  · exact (lt_om_iffY (succT_WNF (hx ξ hξ hξσ)) hcF).mpr
      (succT_lt_of_not_succ (hx ξ hξ hξσ) hcF hs (hU.good.1 ξ hξ hξσ).2)
  · have hξσ := lt_transY hξ hη hU.hσF hlt hησ
    exact (lt_om_iffY (succT_WNF (hx ξ hξ hξσ)) (succT_WNF (hx η hη hησ))).mpr
      (succT_lt_succT (hx ξ hξ hξσ) (hx η hη hησ) (hU.good.2 ξ η hξ hη hlt hησ))
  · exact Or.inr (lt_of_le_of_ltY hU.hσF hcF ht hU.hσle ht.om.2.2)
  · rw [inC_om] at h
    exact hU.hσC g d hg hd h
  · rw [inC_om] at h
    show inC (.Om (succT (s.big ξ))) g d = true
    rw [inC_om]
    exact inC_succT (hU.ub g d ξ hg hd hξ hξσ h0 hok h hξC)
  · have h' : inC (.Om (succT (s.big η))) g d = true := h
    rw [inC_om] at h'
    show inC (.Om (succT (s.big ξ))) g d = true
    rw [inC_om]
    exact inC_succT (hU.ub2 g d ξ η hg hd hξ hη hlt hησ (inC_of_succT h') hξC)
  · have h' : inC (.Om (succT (s.big ξ))) g d = true := h
    rw [inC_om] at h'
    exact hU.lo g d ξ hd hξ hξσ (inC_of_succT h')
  · show ¬ isSucc (.Om (succT (s.big ξ))) = true
    rw [isSucc_principal rfl]
    simp
  · have hm : 1 ≤ m := by
      have := hU.hσF
      rw [e] at this
      exact this.k
    have hKc : Lt (.K m) c := (lt_K_omY hm hcF).mp h
    have h1 := hU.lbK m e hKc ξ hξ hξσ
    exact Or.inr ((lt_K_omY hm (succT_WNF (hx ξ hξ hξσ))).mpr
      (lt_of_le_of_ltY (WNF.K' hm) (hx ξ hξ hξσ) (succT_WNF (hx ξ hξ hξσ)) h1 (lt_succT _)))
  · have hm : 1 ≤ m := by
      have := hU.hσF
      rw [e] at this
      exact this.k
    have hKF := WNF.K' hm
    have h2 : Lt (succT (.K m)) c := (lt_om_iffY (succT_WNF hKF) hcF).mp h
    have hKc : Lt (.K m) c := lt_transY hKF (succT_WNF hKF) hcF (lt_succT _) h2
    have h1 := hU.lbK m e hKc ξ hξ hξσ
    rcases h1 with h1 | h1
    · have e' : s.big ξ = .K m := h1.symm
      show Le (.Om (succT (.K m))) (.Om (succT (s.big ξ)))
      rw [e']
      exact Or.inl rfl
    · exact Or.inr ((lt_om_iffY (succT_WNF hKF) (succT_WNF (hx ξ hξ hξσ))).mpr
        (succT_lt_succT hKF (hx ξ hξ hξσ) h1))
  · exact om_gap ht (hx ξ hξ hξσ) (hc.2 ξ hξ hξσ) hv hne hlt

/-! ### 和 -/

theorem add_keep {a b x : Tm} (ht : WNF (.plus a b)) (hx : WNF x) (hxb : Lt x b) :
    summands (oadd a x) = a :: summands x := by
  obtain ⟨ha, hb, hap, hb0⟩ := ht.plus
  cases hs : summands x with
  | nil =>
    rw [eq_zero_of_summands_nil hs, oadd_zero, summands_principal hap]
  | cons h r =>
    obtain ⟨h', rest, hsb⟩ := List.exists_cons_of_ne_nil (summands_ne_nil hb0)
    have h1 := head_le_of_lt hs hsb hxb
    have h2 := WNF.plus_head ht hsb
    have hN := nfl_summands hx
    have hNb := nfl_summands hb
    have hhm := hN.1 h (by rw [hs]; exact List.mem_cons_self)
    have hhm' := hNb.1 h' (by rw [hsb]; exact List.mem_cons_self)
    have h3 : Le h h' := by
      apply le_of_ne_gtY hhm.1 hhm'.1
      rw [cmp_principal hhm.2 hhm'.2]
      exact h1
    have h4 : Le h' a := le_of_ne_gtY hhm'.1 ha h2
    have h5 : leB h a = true := by
      rw [leB_iff]
      exact ne_gt_of_le (le_transY hhm.1 hhm'.1 ha h3 h4)
    rw [summands_oadd hs (nfl_principal (nfl_summands ha)) (nfl_principal hN), hs,
      summands_principal hap, List.takeWhile_cons_of_pos h5]
    simp

/-- 和の隙間 -/
theorem gap_plus {a b x v : Tm} (ht : WNF (.plus a b)) (hxF : WNF x) (hx0 : x ≠ .zero) (hxb : Lt x b)
    (hg : ∀ u, u ∈ subs b → u ≠ b → Lt u b → Lt u x) (hv : v ∈ subs (.plus a b))
    (hne : v ≠ .plus a b) (hlt : Lt v (.plus a b)) : Lt v (oadd a x) := by
  obtain ⟨ha, hb, hap, hb0⟩ := ht.plus
  have hA := wnf_oadd ha hxF
  have hsA := add_keep ht hxF hxb
  have hvF := ht.of_mem_subs hv
  by_cases hlt' : Lt v (oadd a x)
  · exact hlt'
  exfalso
  have hle : Le (oadd a x) v := le_of_not_ltY hvF hA hlt'
  have h1 : cmpList ([a] ++ summands x) (summands v) ≠ .gt := by
    show cmpList (a :: summands x) (summands v) ≠ .gt
    rw [← hsA, ← cmp_eq]
    exact ne_gt_of_le hle
  have h2 : cmpList (summands v) ([a] ++ summands b) = .lt := by
    have := hlt
    unfold Lt at this
    rwa [cmp_eq, summands_plus] at this
  have hAN : NFL ([a] ++ summands x) := by
    have := nfl_summands hA
    rw [hsA] at this
    exact this
  obtain ⟨V', hV'⟩ := prefix_of_between hAN (nfl_summands hvF) h1 h2
  rw [hV', cmpList_append_same] at h1 h2
  have hVN : NFL V' := nfl_append_right (hV' ▸ nfl_summands hvF)
  cases V' with
  | nil =>
    cases e : summands x with
    | nil => exact hx0 (eq_zero_of_summands_nil e)
    | cons p q =>
      rw [e, cmpList_cons_nil] at h1
      exact h1 rfl
  | cons h' V'' =>
    simp only [subs, List.mem_cons, List.mem_append] at hv
    rcases hv with e | h | h
    · exact hne e
    · have hsv : a ∈ subs v := mem_subs_of_mem_summands (by rw [hV']; exact List.mem_cons_self)
      have hne' : a ≠ v := by
        intro e
        rw [← e, summands_principal hap] at hV'
        simp at hV'
      have e1 := size_lt_of_mem_subs_ne hsv hne'
      have e2 := size_le_of_mem_subs h
      omega
    · have hv'F : WNF (ofSummands (h' :: V'')) := wnf_ofSummands hVN
      have hv'b : Lt (ofSummands (h' :: V'')) b := by
        unfold Lt
        rw [cmp_eq, summands_ofSummands _ (nfl_principal hVN)]
        exact h2
      have hsub := subs_trans h (tail_mem_subs (L := [a]) hvF hV' (by simp))
      have h3 := hg _ hsub hv'b.ne hv'b
      have h4 : Le x (ofSummands (h' :: V'')) := by
        apply le_of_ne_gtY hxF hv'F
        rw [cmp_eq, summands_ofSummands _ (nfl_principal hVN)]
        exact h1
      exact not_lt_of_leY hxF hv'F h4 h3

/-- 和の隙間（等号つき：`x = 0` もよい） -/
theorem gap_plusW {a b x v : Tm} (ht : WNF (.plus a b)) (hxF : WNF x) (hxb : Lt x b)
    (hg : ∀ u, u ∈ subs b → u ≠ b → Lt u b → Le u x) (hv : v ∈ subs (.plus a b))
    (hne : v ≠ .plus a b) (hlt : Lt v (.plus a b)) : Le v (oadd a x) := by
  obtain ⟨ha, hb, hap, hb0⟩ := ht.plus
  have hA := wnf_oadd ha hxF
  have hsA := add_keep ht hxF hxb
  have hvF := ht.of_mem_subs hv
  by_cases hlt' : Lt v (oadd a x)
  · exact Or.inr hlt'
  have hle : Le (oadd a x) v := le_of_not_ltY hvF hA hlt'
  have h1 : cmpList ([a] ++ summands x) (summands v) ≠ .gt := by
    show cmpList (a :: summands x) (summands v) ≠ .gt
    rw [← hsA, ← cmp_eq]
    exact ne_gt_of_le hle
  have h2 : cmpList (summands v) ([a] ++ summands b) = .lt := by
    have := hlt
    unfold Lt at this
    rwa [cmp_eq, summands_plus] at this
  have hAN : NFL ([a] ++ summands x) := by
    have := nfl_summands hA
    rw [hsA] at this
    exact this
  obtain ⟨V', hV'⟩ := prefix_of_between hAN (nfl_summands hvF) h1 h2
  rw [hV', cmpList_append_same] at h1 h2
  have hVN : NFL V' := nfl_append_right (hV' ▸ nfl_summands hvF)
  cases V' with
  | nil =>
    cases e : summands x with
    | nil =>
      have e0 := eq_zero_of_summands_nil e
      subst e0
      have e1 : v = a := by
        rw [← ofSummands_summands v hvF, hV']
        rfl
      rw [e1, oadd_zero]
      exact Or.inl rfl
    | cons p q =>
      rw [e, cmpList_cons_nil] at h1
      exact absurd rfl h1
  | cons h' V'' =>
    simp only [subs, List.mem_cons, List.mem_append] at hv
    rcases hv with e | h | h
    · exact absurd e hne
    · exfalso
      have hsv : a ∈ subs v := mem_subs_of_mem_summands (by rw [hV']; exact List.mem_cons_self)
      have hne' : a ≠ v := by
        intro e
        rw [← e, summands_principal hap] at hV'
        simp at hV'
      have e1 := size_lt_of_mem_subs_ne hsv hne'
      have e2 := size_le_of_mem_subs h
      omega
    · have hv'F : WNF (ofSummands (h' :: V'')) := wnf_ofSummands hVN
      have hv'b : Lt (ofSummands (h' :: V'')) b := by
        unfold Lt
        rw [cmp_eq, summands_ofSummands _ (nfl_principal hVN)]
        exact h2
      have hsub := subs_trans h (tail_mem_subs (L := [a]) hvF hV' (by simp))
      have h3 := hg _ hsub hv'b.ne hv'b
      have h4 : Le x (ofSummands (h' :: V'')) := by
        apply le_of_ne_gtY hxF hv'F
        rw [cmp_eq, summands_ofSummands _ (nfl_principal hVN)]
        exact h1
      have e2 : ofSummands (h' :: V'') = x := le_antisymmY hv'F hxF h3 h4
      have hsx : summands x = h' :: V'' := by
        rw [← e2, summands_ofSummands _ (nfl_principal hVN)]
      refine Or.inl ?_
      rw [← ofSummands_summands v hvF, hV', ← ofSummands_summands (oadd a x) hA, hsA, hsx]
      rfl

theorem natInv_add {a b : Tm} {s : SeqD} (ht : WNF (.plus a b)) (hb : NatInv b s) :
    NatInv (.plus a b) (.add a s) := by
  obtain ⟨ha, hbF, hap, hb0⟩ := ht.plus
  have hU := hb.1
  have ha0 : a ≠ .zero := by
    intro e
    rw [e] at hap
    cases hap
  have hx := fun n => (hU.good n).1
  refine ⟨⟨fun n => ⟨wnf_oadd ha (hx n), ?_, oadd_lt_oadd ha (hx n) (hx (n + 1)) (hU.good n).2.2⟩,
    fun n => oadd_ne_zero_left ha (hx n) ha0, fun g d n hg hd h => ?_, fun g d n hg hd h => ?_⟩,
    fun n v hv hne hlt => gap_plus ht (hx n) (hU.pos n) (hU.good n).2.1 (hb.2 n) hv hne hlt⟩
  · have := oadd_lt_oadd ha (hx n) hbF (hU.good n).2.1
    rwa [oadd_plus ht] at this
  · rw [inC_plus, Bool.and_eq_true] at h
    exact inC_oadd ha (hx n) h.1 (hU.ub g d n hg hd h.2)
  · have h' : inC (oadd a (s.nat (n + 1))) g d = true := h
    have hA := wnf_oadd ha (hx (n + 1))
    have h1 : inC a g d = true := inC_of_mem_summands hA h' (by
      rw [add_keep ht (hx (n + 1)) (hU.good (n + 1)).2.1]
      exact List.mem_cons_self)
    have h2 : inC (s.nat (n + 1)) g d = true := (inC_iff_summands (hx (n + 1))).mpr fun q hq =>
      inC_of_mem_summands hA h' (mem_summands_oadd_right ha (hx (n + 1)) hq)
    exact inC_oadd ha (hx n) h1 (hU.ub2 g d n hg hd h2)

theorem bigInv_add {a b σ : Tm} {s : SeqD} (ht : WNF (.plus a b)) (hb : BigInvW b σ s) :
    BigInvW (.plus a b) σ (.add a s) := by
  obtain ⟨ha, hbF, hap, hb0⟩ := ht.plus
  have hU := hb.1
  have ha0 : a ≠ .zero := by
    intro e
    rw [e] at hap
    cases hap
  have hx := fun ξ hξ hξσ => (hU.good.1 ξ hξ hξσ).1
  refine ⟨⟨⟨fun ξ hξ hξσ => ⟨wnf_oadd ha (hx ξ hξ hξσ), ?_⟩, fun ξ η hξ hη hlt hησ => ?_⟩,
    fun ξ hξ hξσ e => ?_, hU.hσF, ?_, subs_plus_r hU.hσs, fun g d hg hd h => ?_,
    fun g d ξ hg hd hξ hξσ h0 hok h hξC => ?_, fun g d ξ η hg hd hξ hη hlt hησ h hξC => ?_,
    fun g d ξ hd hξ hξσ h => ?_, (fun h => by cases h),
    fun m he' h ξ hξ hξσ => ?_, fun m he' h ξ hξ hξσ => ?_⟩,
    fun ξ hξ hξσ v hv hne hlt => gap_plusW ht (hx ξ hξ hξσ) (hU.good.1 ξ hξ hξσ).2
      (hb.2 ξ hξ hξσ) hv hne hlt⟩
  · have := oadd_lt_oadd ha (hx ξ hξ hξσ) hbF (hU.good.1 ξ hξ hξσ).2
    rwa [oadd_plus ht] at this
  · have hξσ := lt_transY hξ hη hU.hσF hlt hησ
    exact oadd_lt_oadd ha (hx ξ hξ hξσ) (hx η hη hησ) (hU.good.2 ξ η hξ hη hlt hησ)
  · exact absurd e (oadd_ne_zero_left ha (hx ξ hξ hξσ) ha0)
  · exact Or.inr (lt_of_le_of_ltY hU.hσF hbF ht hU.hσle (lt_plus_rightY ht))
  · rw [inC_plus, Bool.and_eq_true] at h
    exact hU.hσC g d hg hd h.2
  · rw [inC_plus, Bool.and_eq_true] at h
    exact inC_oadd ha (hx ξ hξ hξσ) h.1 (hU.ub g d ξ hg hd hξ hξσ h0 hok h.2 hξC)
  · have h' : inC (oadd a (s.big η)) g d = true := h
    have hξσ := lt_transY hξ hη hU.hσF hlt hησ
    have hA := wnf_oadd ha (hx η hη hησ)
    have h1 : inC a g d = true := inC_of_mem_summands hA h' (by
      rw [add_keep ht (hx η hη hησ) (hU.good.1 η hη hησ).2]
      exact List.mem_cons_self)
    have h2 : inC (s.big η) g d = true := (inC_iff_summands (hx η hη hησ)).mpr fun q hq =>
      inC_of_mem_summands hA h' (mem_summands_oadd_right ha (hx η hη hησ) hq)
    exact inC_oadd ha (hx ξ hξ hξσ) h1 (hU.ub2 g d ξ η hg hd hξ hη hlt hησ h2 hξC)
  · have h' : inC (oadd a (s.big ξ)) g d = true := h
    have hA := wnf_oadd ha (hx ξ hξ hξσ)
    have h2 : inC (s.big ξ) g d = true := (inC_iff_summands (hx ξ hξ hξσ)).mpr fun q hq =>
      inC_of_mem_summands hA h' (mem_summands_oadd_right ha (hx ξ hξ hξσ) hq)
    exact hU.lo g d ξ hd hξ hξσ h2
  · have hm : 1 ≤ m := by
      have := hU.hσF
      rw [he'] at this
      exact this.k
    have hKF := WNF.K' hm
    exact le_transY hKF ha (wnf_oadd ha (hx ξ hξ hξσ))
      (le_of_not_ltY ha hKF fun h' => Lt.asymmY hKF ht h (lt_prin_of_head rfl rfl hap h'))
      (le_oadd_left ha (hx ξ hξ hξσ))
  · have hm : 1 ≤ m := by
      have := hU.hσF
      rw [he'] at this
      exact this.k
    have hKF := WNF.succK hm
    exact le_transY hKF ha (wnf_oadd ha (hx ξ hξ hξσ))
      (le_of_not_ltY ha hKF fun h' => Lt.asymmY hKF ht h (lt_prin_of_head rfl rfl hap h'))
      (le_oadd_left ha (hx ξ hξ hξσ))


/-! ### `X = 0` -/

theorem inC_omHat {x g d : Tm} (h : inC x g d = true) : inC (omHat x) g d = true := by
  unfold omHat
  split
  · exact inC_zero _ _
  · split
    · exact h
    · rw [inC_om]
      exact h

end RTKA.Fund
