import Compact.FS.Cof

/-! 塔が目標を越えること。

閉じた点（`cl`）のうち `z` の中で見える `z` 以下のものが全て始点 `G` 以下なら（`CF cl G z`）、`z` は塔の中に入る
（`tow_pass_tgt`・`tow_pass_K`）。目標の前線の元はこの条件を満たすので、目標は塔の中に入る（`Tow.tgt_pass`）。 -/

namespace RTKA.Fund

open Tm W

/-! ### `selfVis` -/

theorem selfVis_self : ∀ {x : Tm}, ((∃ m a, x = .Xi m a) ∨ ∃ s p a, x = .Psi s p a) → selfVis x x = true := by
  rintro x (⟨m, a, rfl⟩ | ⟨s, p, a, rfl⟩) <;> simp [selfVis]

theorem le_leB {a b : Tm} (h : Le a b) : leB a b = true := by
  rw [leB_iff]
  rcases h with rfl | h
  · rw [cmp_self]
    decide
  · have h' : cmp a b = .lt := h
    rw [h']
    decide

theorem selfVis_mem {w : Tm} : ∀ {e : Tm}, selfVis w e = true → w ∈ subs e
  | .zero, h | .one, h | .K _, h => by simp [selfVis] at h
  | .plus a b, h => by
    simp only [selfVis, Bool.or_eq_true] at h
    rcases h with h | h
    · exact subs_plus_l (selfVis_mem h)
    · exact subs_plus_r (selfVis_mem h)
  | .Om a, h => subs_om (selfVis_mem (e := a) h)
  | .Xi m a, h => by
    simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with rfl | ⟨-, h⟩
    · exact self_mem_subs _
    · exact subs_xi (selfVis_mem h)
  | .Psi s p a, h => by
    simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with rfl | ⟨-, (h | h) | h⟩
    · exact self_mem_subs _
    · exact subs_psi_s (selfVis_mem h)
    · exact subs_psi_p (selfVis_mem h)
    · exact subs_psi_a (selfVis_mem h)

/-- 見える `R` 未満の節点は、前線の元以下 -/
theorem selfVis_fr {w R : Tm} (hwF : WNF w) (hw : Lt w R) : ∀ {e : Tm}, WNF e → selfVis w e = true →
    ∃ u, u ∈ fr R e ∧ Le w u
  | .zero, _, h | .one, _, h | .K _, _, h => by simp [selfVis] at h
  | .plus a b, he, h => by
    obtain ⟨ha, hb, -, -⟩ := he.plus
    simp only [selfVis, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨u, hu, hle⟩ := selfVis_fr hwF hw ha h
      exact ⟨u, by rw [fr, List.mem_append]; exact Or.inl hu, hle⟩
    · obtain ⟨u, hu, hle⟩ := selfVis_fr hwF hw hb h
      exact ⟨u, by rw [fr, List.mem_append]; exact Or.inr hu, hle⟩
  | .Om a, he, h => by
    obtain ⟨u, hu, hle⟩ := selfVis_fr hwF hw he.om.1 (show selfVis w a = true from h)
    exact ⟨u, by rw [fr]; exact hu, hle⟩
  | .Xi m a, he, h => by
    simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    by_cases h1 : Lt (.Xi m a) R
    · refine ⟨.Xi m a, by simp [fr, h1], ?_⟩
      rcases h with e | ⟨h2, -⟩
      · exact Or.inl e.symm
      · exact le_of_ne_gtY hwF he (leB_iff.mp h2)
    · rcases h with e | ⟨-, h2⟩
      · exact absurd (e ▸ hw) h1
      · obtain ⟨u, hu, hle⟩ := selfVis_fr hwF hw he.xi.2.1 h2
        exact ⟨u, by rw [fr]; simp only [h1, ↓reduceIte]; exact hu, hle⟩
  | .Psi s p a, he, h => by
    have hP := he.psi
    simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    by_cases h1 : Lt (.Psi s p a) R
    · refine ⟨.Psi s p a, by simp [fr, h1], ?_⟩
      rcases h with e | ⟨h2, -⟩
      · exact Or.inl e.symm
      · exact le_of_ne_gtY hwF he (leB_iff.mp h2)
    · have hmem : ∀ u, (u ∈ fr R s ∨ u ∈ fr R p) ∨ u ∈ fr R a → u ∈ fr R (.Psi s p a) := fun u hu => by
        rw [fr]
        simp only [h1, ↓reduceIte, List.mem_append]
        exact hu
      rcases h with e | ⟨-, (h2 | h2) | h2⟩
      · exact absurd (e ▸ hw) h1
      · obtain ⟨u, hu, hle⟩ := selfVis_fr hwF hw hP.xiF h2
        exact ⟨u, hmem u (Or.inl (Or.inl hu)), hle⟩
      · obtain ⟨u, hu, hle⟩ := selfVis_fr hwF hw hP.piF h2
        exact ⟨u, hmem u (Or.inl (Or.inr hu)), hle⟩
      · obtain ⟨u, hu, hle⟩ := selfVis_fr hwF hw hP.aF h2
        exact ⟨u, hmem u (Or.inr hu), hle⟩

/-- 前線の元の中で見える節点は、もとの項の中で見える -/
theorem selfVis_of_fr {w u R : Tm} (hR : WNF R) (hwF : WNF w) (hv : selfVis w u = true) (hle : Le w u) :
    ∀ {e : Tm}, WNF e → u ∈ fr R e → selfVis w e = true
  | .zero, _, h | .one, _, h | .K _, _, h => by simp [fr] at h
  | .plus a b, he, h => by
    obtain ⟨ha, hb, -, -⟩ := he.plus
    rw [fr, List.mem_append] at h
    simp only [selfVis, Bool.or_eq_true]
    rcases h with h | h
    · exact Or.inl (selfVis_of_fr hR hwF hv hle ha h)
    · exact Or.inr (selfVis_of_fr hR hwF hv hle hb h)
  | .Om a, he, h => by
    rw [fr] at h
    show selfVis w a = true
    exact selfVis_of_fr hR hwF hv hle he.om.1 h
  | .Xi m a, he, h => by
    rw [fr] at h
    by_cases h1 : Lt (.Xi m a) R
    · simp only [h1, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact hv
    · simp only [h1, ↓reduceIte] at h
      have hu := he.xi.2.1.of_mem_subs (fr_spec h).1
      have h2 : Lt w R := lt_of_le_of_ltY hwF hu hR hle (fr_spec h).2
      have h3 : Lt w (.Xi m a) := lt_of_lt_of_leY hwF hR he h2 (le_of_not_ltY he hR h1)
      simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true]
      exact Or.inr ⟨le_leB (Or.inr h3), selfVis_of_fr hR hwF hv hle he.xi.2.1 h⟩
  | .Psi s p a, he, h => by
    have hP := he.psi
    rw [fr] at h
    by_cases h1 : Lt (.Psi s p a) R
    · simp only [h1, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact hv
    · simp only [h1, ↓reduceIte, List.mem_append] at h
      have hup : ∀ {q : Tm}, WNF q → u ∈ fr R q → leB w (.Psi s p a) = true := fun hq hu' => by
        have hu := hq.of_mem_subs (fr_spec hu').1
        have h2 : Lt w R := lt_of_le_of_ltY hwF hu hR hle (fr_spec hu').2
        exact le_leB (Or.inr (lt_of_lt_of_leY hwF hR he h2 (le_of_not_ltY he hR h1)))
      simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true]
      rcases h with (h | h) | h
      · exact Or.inr ⟨hup hP.xiF h, Or.inl (Or.inl (selfVis_of_fr hR hwF hv hle hP.xiF h))⟩
      · exact Or.inr ⟨hup hP.piF h, Or.inl (Or.inr (selfVis_of_fr hR hwF hv hle hP.piF h))⟩
      · exact Or.inr ⟨hup hP.aF h, Or.inr (selfVis_of_fr hR hwF hv hle hP.aF h)⟩

/-- 主要項の加数は見える -/
theorem selfVis_summand {k : Tm} (hk : (∃ m a, k = .Xi m a) ∨ ∃ s p a, k = .Psi s p a) :
    ∀ {c : Tm}, k ∈ summands c → selfVis k c = true
  | .zero, h => by simp [summands] at h
  | .plus a b, h => by
    simp only [summands, List.mem_cons] at h
    simp only [selfVis, Bool.or_eq_true]
    rcases h with rfl | h
    · exact Or.inl (selfVis_self hk)
    · exact Or.inr (selfVis_summand hk h)
  | .one, h | .K _, h | .Om _, h => by
    simp only [summands, List.mem_singleton] at h
    rcases hk with ⟨m, a, e⟩ | ⟨s, p, a, e⟩ <;> rw [e] at h <;> cases h
  | .Xi m a, h | .Psi _ m a, h => by
    simp only [summands, List.mem_singleton] at h
    subst h
    exact selfVis_self hk

/-! ### 閉じた点の最大性 -/

theorem maxOpt_ge_l {P Q : Option Tm} {p : Tm} (hP : P = some p) (_hp : WNF p) (_hQ : ∀ q, Q = some q → WNF q) :
    ∃ x, maxOpt P Q = some x ∧ Le p x := by
  subst hP
  cases Q with
  | none => exact ⟨p, rfl, Or.inl rfl⟩
  | some q =>
    by_cases h : ltB p q = true
    · exact ⟨q, by simp [maxOpt, h], Or.inr (ltB_iff.mp h)⟩
    · exact ⟨p, by simp [maxOpt, h], Or.inl rfl⟩

theorem maxOpt_ge_r {P Q : Option Tm} {q : Tm} (hQ : Q = some q) (hq : WNF q) (hP : ∀ p, P = some p → WNF p) :
    ∃ x, maxOpt P Q = some x ∧ Le q x := by
  subst hQ
  cases P with
  | none => exact ⟨q, rfl, Or.inl rfl⟩
  | some p =>
    by_cases h : ltB p q = true
    · exact ⟨q, by simp [maxOpt, h], Or.inl rfl⟩
    · exact ⟨p, by simp [maxOpt, h], le_of_not_ltY (hP p rfl) hq fun h' => h (ltB_iff.mpr h')⟩

theorem maxCl_wnf {cl : Tm → Bool} {ub e : Tm} (he : WNF e) (G : Tm) (h : maxCl cl ub e = some G) : WNF G :=
  he.of_mem_subs (maxCl_spec h).1

/-- `maxCl` は見える閉じた点以上 -/
theorem maxCl_ge {cl : Tm → Bool} {ub w : Tm} (hn : (∃ m a, w = .Xi m a) ∨ ∃ s p a, w = .Psi s p a)
    (hwF : WNF w) (hwc : cl w = true) (hle : leB w ub = true) (hv : selfVis w ub = true) :
    ∀ {e : Tm}, WNF e → w ∈ subs e → ∃ G, maxCl cl ub e = some G ∧ Le w G
  | .zero, _, h | .one, _, h | .K _, _, h => by
    simp only [subs, List.mem_singleton] at h
    rcases hn with ⟨m, a, e⟩ | ⟨s, p, a, e⟩ <;> rw [e] at h <;> cases h
  | .plus a b, he, h => by
    obtain ⟨ha, hb, -, -⟩ := he.plus
    simp only [subs, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · rcases hn with ⟨m, a', e⟩ | ⟨s, p, a', e⟩ <;> cases e
    · obtain ⟨G, hG, hl⟩ := maxCl_ge hn hwF hwc hle hv ha h
      obtain ⟨x, hx, hl'⟩ := maxOpt_ge_l hG (maxCl_wnf ha G hG) (maxCl_wnf hb)
      refine ⟨x, hx, le_transY hwF (maxCl_wnf ha G hG) (he.of_mem_subs ?_) hl hl'⟩
      rcases maxOpt_cases hx with h' | h'
      · exact subs_plus_l (maxCl_spec h').1
      · exact subs_plus_r (maxCl_spec h').1
    · obtain ⟨G, hG, hl⟩ := maxCl_ge hn hwF hwc hle hv hb h
      obtain ⟨x, hx, hl'⟩ := maxOpt_ge_r hG (maxCl_wnf hb G hG) (maxCl_wnf ha)
      refine ⟨x, hx, le_transY hwF (maxCl_wnf hb G hG) (he.of_mem_subs ?_) hl hl'⟩
      rcases maxOpt_cases hx with h' | h'
      · exact subs_plus_l (maxCl_spec h').1
      · exact subs_plus_r (maxCl_spec h').1
  | .Om a, he, h => by
    simp only [subs, List.mem_cons] at h
    rcases h with rfl | h
    · rcases hn with ⟨m, a', e⟩ | ⟨s, p, a', e⟩ <;> cases e
    · show ∃ G, maxCl cl ub a = some G ∧ Le w G
      exact maxCl_ge hn hwF hwc hle hv he.om.1 h
  | .Xi m a, he, h => by
    have haF := he.xi.2.1
    have hr : ∀ x, maxCl cl ub (.Xi m a) = some x → x ∈ subs (.Xi m a) := fun x hx => (maxCl_spec hx).1
    simp only [subs, List.mem_cons] at h
    rcases h with rfl | h
    · have e1 : (if cl (.Xi m a) && leB (.Xi m a) ub && selfVis (.Xi m a) ub then some (.Xi m a) else none) =
          some (Tm.Xi m a) := by simp [hwc, hle, hv]
      obtain ⟨x, hx, hl'⟩ := maxOpt_ge_l e1 he (maxCl_wnf haF)
      exact ⟨x, hx, hl'⟩
    · obtain ⟨G, hG, hl⟩ := maxCl_ge hn hwF hwc hle hv haF h
      have hw0 : ∀ q, (if cl (.Xi m a) && leB (.Xi m a) ub && selfVis (.Xi m a) ub
          then some (.Xi m a) else none) = some q → WNF q := fun q hp => by
        split at hp
        · cases hp
          exact he
        · cases hp
      obtain ⟨x, hx, hl'⟩ := maxOpt_ge_r hG (maxCl_wnf haF G hG) hw0
      exact ⟨x, hx, le_transY hwF (maxCl_wnf haF G hG) (he.of_mem_subs (hr x hx)) hl hl'⟩
  | .Psi s p a, he, h => by
    have hP := he.psi
    have hr : ∀ x, maxCl cl ub (.Psi s p a) = some x → x ∈ subs (.Psi s p a) := fun x hx => (maxCl_spec hx).1
    have hw2 : ∀ q, maxOpt (maxCl cl ub s) (maxOpt (maxCl cl ub p) (maxCl cl ub a)) = some q → WNF q := by
      intro q hq
      rcases maxOpt_cases hq with h' | h'
      · exact maxCl_wnf hP.xiF q h'
      · rcases maxOpt_cases h' with h'' | h''
        · exact maxCl_wnf hP.piF q h''
        · exact maxCl_wnf hP.aF q h''
    have hw3 : ∀ q, maxOpt (maxCl cl ub p) (maxCl cl ub a) = some q → WNF q := by
      intro q h'
      rcases maxOpt_cases h' with h'' | h''
      · exact maxCl_wnf hP.piF q h''
      · exact maxCl_wnf hP.aF q h''
    have hw0 : ∀ q, (if cl (.Psi s p a) && leB (.Psi s p a) ub && selfVis (.Psi s p a) ub
        then some (.Psi s p a) else none) = some q → WNF q := fun q hp => by
      split at hp
      · cases hp
        exact he
      · cases hp
    simp only [subs, List.mem_cons, List.mem_append] at h
    have hlast : ∀ {G : Tm}, WNF G → Le w G →
        maxOpt (maxCl cl ub s) (maxOpt (maxCl cl ub p) (maxCl cl ub a)) = some G →
        ∃ G', maxCl cl ub (.Psi s p a) = some G' ∧ Le w G' := fun hGF hl hG => by
      obtain ⟨x, hx, hl'⟩ := maxOpt_ge_r hG hGF hw0
      exact ⟨x, hx, le_transY hwF hGF (he.of_mem_subs (hr x hx)) hl hl'⟩
    rcases h with rfl | (h | h) | h
    · have e1 : (if cl (.Psi s p a) && leB (.Psi s p a) ub && selfVis (.Psi s p a) ub then some (.Psi s p a) else none) =
          some (Tm.Psi s p a) := by simp [hwc, hle, hv]
      obtain ⟨x, hx, hl'⟩ := maxOpt_ge_l e1 he hw2
      exact ⟨x, hx, hl'⟩
    · obtain ⟨G, hG, hl⟩ := maxCl_ge hn hwF hwc hle hv hP.xiF h
      obtain ⟨x, hx, hl'⟩ := maxOpt_ge_l hG (maxCl_wnf hP.xiF G hG) hw3
      exact hlast (hw2 x hx) (le_transY hwF (maxCl_wnf hP.xiF G hG) (hw2 x hx) hl hl') hx
    · obtain ⟨G, hG, hl⟩ := maxCl_ge hn hwF hwc hle hv hP.piF h
      obtain ⟨x, hx, hl'⟩ := maxOpt_ge_l hG (maxCl_wnf hP.piF G hG) (maxCl_wnf hP.aF)
      obtain ⟨x', hx', hl''⟩ := maxOpt_ge_r hx (hw3 x hx) (maxCl_wnf hP.xiF)
      exact hlast (hw2 x' hx') (le_transY hwF (hw3 x hx) (hw2 x' hx')
        (le_transY hwF (maxCl_wnf hP.piF G hG) (hw3 x hx) hl hl') hl'') hx'
    · obtain ⟨G, hG, hl⟩ := maxCl_ge hn hwF hwc hle hv hP.aF h
      obtain ⟨x, hx, hl'⟩ := maxOpt_ge_r hG (maxCl_wnf hP.aF G hG) (maxCl_wnf hP.piF)
      obtain ⟨x', hx', hl''⟩ := maxOpt_ge_r hx (hw3 x hx) (maxCl_wnf hP.xiF)
      exact hlast (hw2 x' hx') (le_transY hwF (hw3 x hx) (hw2 x' hx')
        (le_transY hwF (maxCl_wnf hP.aF G hG) (hw3 x hx) hl hl') hl'') hx'

theorem foldr_maxOpt_ge {f : Tm → Option Tm} {G : Tm} : ∀ {l : List Tm} {e : Tm},
    (∀ e', e' ∈ l → ∀ q, f e' = some q → WNF q) → e ∈ l → f e = some G →
    ∃ x, (l.map f).foldr maxOpt none = some x ∧ Le G x
  | a :: l, e, hf, he, h => by
    simp only [List.map_cons, List.foldr_cons]
    have hw : ∀ q, (l.map f).foldr maxOpt none = some q → WNF q := fun q hq => by
      obtain ⟨e', he', hf'⟩ := foldr_maxOpt_spec hq
      exact hf e' (List.mem_cons_of_mem _ he') q hf'
    rcases List.mem_cons.mp he with rfl | he'
    · exact maxOpt_ge_l h (hf _ List.mem_cons_self _ h) hw
    · obtain ⟨x, hx, hl⟩ := foldr_maxOpt_ge (fun e'' h'' => hf e'' (List.mem_cons_of_mem _ h'')) he' h
      obtain ⟨x', hx', hl'⟩ := maxOpt_ge_r hx (hw x hx) (hf a List.mem_cons_self)
      have hF' : WNF x' := by
        rcases maxOpt_cases hx' with h' | h'
        · exact hf a List.mem_cons_self x' h'
        · exact hw x' h'
      exact ⟨x', hx', le_transY (hf e (List.mem_cons_of_mem _ he') G h) (hw x hx) hF' hl hl'⟩

/-- 目標の前線の中の閉じた点の最大性 -/
theorem frCl_ge {cl : Tm → Bool} {τ e G' : Tm} (hτ : WNF τ) (he : e ∈ fr τ τ) (h : maxCl cl e e = some G') :
    ∃ e', e' ∈ fr τ τ ∧ maxCl cl e' e' = some (frCl cl τ) ∧ Le G' (frCl cl τ) := by
  have hwf : ∀ e', e' ∈ frB τ τ → ∀ q, (fun e => maxCl cl e e) e' = some q → WNF q := fun e' he' q hq => by
    rw [frB_eq_fr] at he'
    exact maxCl_wnf (hτ.of_mem_subs (fr_spec he').1) q hq
  obtain ⟨x, hx, hl⟩ := foldr_maxOpt_ge (f := fun e => maxCl cl e e) hwf (by rw [frB_eq_fr]; exact he) h
  obtain ⟨e', he', hf⟩ := foldr_maxOpt_spec hx
  rw [frB_eq_fr] at he'
  have e1 : frCl cl τ = x := by
    unfold frCl
    rw [hx]
    rfl
  rw [e1]
  exact ⟨e', he', hf, hl⟩

/-- 調整 `c` の中の閉じた点 `k` は始点以下 -/
theorem start_ge {cl : Tm → Bool} {k c P : Tm} (hn : (∃ m a, k = .Xi m a) ∨ ∃ s p a, k = .Psi s p a)
    (hkF : WNF k) (hk : cl k = true) (hcF : WNF c) (hPF : WNF P)
    (hc : c = k ∨ ∃ d, WNF d ∧ c = oadd d k) :
    Le k ((maxOpt (maxCl cl c c) (maxCl cl P P)).getD .zero) := by
  have hkp : isPrincipal k = true := by
    rcases hn with ⟨m, a, rfl⟩ | ⟨s, p, a, rfl⟩ <;> rfl
  have hmem : k ∈ summands c ∧ Le k c := by
    rcases hc with rfl | ⟨d, hd, rfl⟩
    · rw [summands_principal hkp]
      exact ⟨List.mem_singleton.mpr rfl, Or.inl rfl⟩
    · have hs := summands_principal hkp
      have e1 := summands_oadd hs (nfl_principal (nfl_summands hd)) (nfl_principal (nfl_summands hkF))
      rw [e1, hs]
      exact ⟨List.mem_append_right _ (List.mem_singleton.mpr rfl), le_oadd_right hd hkF⟩
  obtain ⟨G₁, hG₁, hl⟩ := maxCl_ge hn hkF hk (le_leB hmem.2) (selfVis_summand hn hmem.1) hcF
    (mem_subs_of_mem_summands hmem.1)
  obtain ⟨x, hx, hl'⟩ := maxOpt_ge_l hG₁ (maxCl_wnf hcF G₁ hG₁) (maxCl_wnf hPF)
  have hxF : WNF x := by
    rcases maxOpt_cases hx with h' | h'
    · exact maxCl_wnf hcF x h'
    · exact maxCl_wnf hPF x h'
  rw [hx]
  exact le_transY hkF (maxCl_wnf hcF G₁ hG₁) hxF hl hl'

/-! ### 閉じた点が始点以下の項 -/

/-- `z` の中で見える `z` 以下の閉じた点は全て `G` 以下 -/
def CF (cl : Tm → Bool) (G z : Tm) : Prop :=
  ∀ w, WNF w → cl w = true → Le w z → selfVis w z = true → Le w G

theorem CF.par {cl : Tm → Bool} {G z w' : Tm} (h : CF cl G z) (hz : WNF z) (hw' : w' ∈ parF z) :
    CF cl G w' := by
  intro w hwF hc hle hv
  have hw'F := hz.of_mem_subs (parL_sub (parF_sub_parL hw')).1
  have hlt := parF_lt hz hw'
  have hwz : Lt w z := lt_of_le_of_ltY hwF hw'F hz hle hlt
  refine h w hwF hc (Or.inr hwz) ?_
  cases z with
  | zero | one | K _ => simp [parF] at hw'
  | plus a b =>
    simp only [parF, List.mem_cons, List.not_mem_nil, or_false] at hw'
    simp only [selfVis, Bool.or_eq_true]
    rcases hw' with rfl | rfl
    · exact Or.inl hv
    · exact Or.inr hv
  | Om e =>
    simp only [parF, List.mem_singleton] at hw'
    rw [hw'] at hv
    exact hv
  | Xi j b =>
    have hKF := WNF.K' hz.xi.1
    simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true]
    exact Or.inr ⟨le_leB (Or.inr hwz), selfVis_of_fr hKF hwF hv hle hz.xi.2.1 hw'⟩
  | Psi s k a =>
    have hP := hz.psi
    simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true]
    simp only [parF, List.mem_append] at hw'
    rcases hw' with (h' | h') | h'
    · exact Or.inr ⟨le_leB (Or.inr hwz), Or.inr (selfVis_of_fr hP.piF hwF hv hle hP.aF h')⟩
    · exact Or.inr ⟨le_leB (Or.inr hwz), Or.inl (Or.inl (selfVis_of_fr hP.piF hwF hv hle hP.xiF h'))⟩
    · exact Or.inr ⟨le_leB (Or.inr hwz), Or.inl (Or.inr (selfVis_of_fr hP.piF hwF hv hle hP.piF h'))⟩

theorem CF.tgt {cl : Tm → Bool} {G s k a : Tm} (h : CF cl G (.Psi s k a)) (hz : WNF (.Psi s k a))
    (hc : cl k = false) : CF cl G k := by
  intro w hwF hcw hle hv
  have hP := hz.psi
  rcases hle with e | hlt
  · rw [e, hc] at hcw
    cases hcw
  · obtain ⟨u, hu, hle'⟩ := selfVis_fr hwF hlt hP.piF hv
    have huF := hP.piF.of_mem_subs (fr_spec hu).1
    have hwz : Lt w (.Psi s k a) := lt_of_le_of_ltY hwF huF hz hle' (FWOrder.k2t hz u hu)
    refine h w hwF hcw (Or.inr hwz) ?_
    simp only [selfVis, Bool.or_eq_true, Bool.and_eq_true]
    exact Or.inr ⟨le_leB (Or.inr hwz), Or.inl (Or.inr hv)⟩

/-- 目標の前線の元は閉じた点が始点以下 -/
theorem cf_front {cl : Tm → Bool} {π e c P : Tm}
    (hnode : ∀ x, cl x = true → (∃ m a, x = .Xi m a) ∨ ∃ s p a, x = .Psi s p a)
    (hπ : WNF π) (he : e ∈ fr π π) (hcF : WNF c) (hPF : WNF P)
    (hc : c = frCl cl π ∨ ∃ d, WNF d ∧ c = oadd d (frCl cl π)) :
    CF cl ((maxOpt (maxCl cl c c) (maxCl cl P P)).getD .zero) e := by
  intro w hwF hcw hle hv
  have heF := hπ.of_mem_subs (fr_spec he).1
  obtain ⟨G', hG', hl⟩ := maxCl_ge (hnode w hcw) hwF hcw (le_leB hle) hv heF (selfVis_mem hv)
  obtain ⟨e', he', hf, hl'⟩ := frCl_ge hπ he hG'
  have he'F := hπ.of_mem_subs (fr_spec he').1
  obtain ⟨h1, h2, -⟩ := maxCl_spec hf
  have hxF := he'F.of_mem_subs h1
  have h3 := start_ge (hnode _ h2) hxF h2 hcF hPF hc
  have hG'F := maxCl_wnf heF G' hG'
  have hsF : WNF ((maxOpt (maxCl cl c c) (maxCl cl P P)).getD .zero) := by
    cases hm : maxOpt (maxCl cl c c) (maxCl cl P P) with
    | none => exact WNF.zero
    | some x =>
      rcases maxOpt_cases hm with h' | h'
      · exact maxCl_wnf hcF x h'
      · exact maxCl_wnf hPF x h'
  exact le_transY hwF hxF hsF (le_transY hwF hG'F hxF hl hl') h3

/-- 目標より大きい崩壊は、引数が目標の引数以下か、目標の前線の元以下 -/
theorem tgt_wit {σ z a T' : Tm} (hσ : WNF σ) (hσt : IsTgt σ) (C : Clo z a T') (hzσ : Lt z σ) (hσT : Lt σ T') :
    (∃ r, argR? σ = some r ∧ Le a r) ∨ ∃ u, u ∈ fr σ σ ∧ Le z u := by
  have hz := C.hy
  have ha := C.hA
  by_cases hr : ∀ r, argR? σ = some r → Lt r a
  · refine Or.inr ?_
    have hC := inC_tgt hσ hσt ha hr
    by_cases hall : ∀ w, w ∈ fr σ σ → Lt w z
    · exact absurd (C.coll σ hσ ((inC_frY hσ hσ hz ha ha hC (Or.inr hzσ) (Or.inl rfl)).mpr
        fun w hw => inC_of_lt_node (fr_node hw) (hall w hw)) hσT) (Lt.asymmY hz hσ hzσ)
    · obtain ⟨w, hw, hn⟩ := exists_of_not_forall_mem _ hall
      exact ⟨w, hw, le_of_not_ltY (hσ.of_mem_subs (fr_spec hw).1) hz hn⟩
  · refine Or.inl ?_
    cases e : argR? σ with
    | none => exact absurd (fun r e' => by rw [e] at e'; cases e') hr
    | some r =>
      refine ⟨r, rfl, le_of_not_ltY (wnf_of_argR hσ e) ha fun h => hr fun r' e' => ?_⟩
      rw [e] at e'
      cases e'
      exact h

/-- 閉じた点が始点以下の `σ` 未満の項は塔の中 -/
theorem tow_pass_tgt {σ T G : Tm} {γ A : Nat → Tm} (H : Tow σ T γ A) (hσt : IsTgt σ) (hGF : WNF G)
    (hG : Lt G (γ 0)) (hfr : ∀ u, u ∈ fr σ σ → Lt u (γ 0)) (hr : ∀ r, argR? σ = some r → Lt r (A 0)) :
    ∀ z, WNF z → Lt z σ → CF (closedS σ T) G z → ∃ n, Lt z (γ n) := by
  have hσF := (H.hC 0).hT
  have hAF := fun n => (H.hC n).hA
  intro z
  induction hn : z.size using Nat.strongRecOn generalizing z with
  | ind n ih =>
    intro hz hzσ hCF
    have hparF : ∀ w, w ∈ parF z → WNF w := fun w hw => hz.of_mem_subs (parL_sub (parF_sub_parL hw)).1
    have hpar : ∀ w, w ∈ parF z → ∃ m, Lt w (γ m) := fun w hw => by
      have hs := (parL_sub (parF_sub_parL hw)).2
      exact ih w.size (by omega) w rfl (hparF w hw) (lt_transY (hparF w hw) hz hσF (parF_lt hz hw) hzσ)
        (hCF.par hz hw)
    obtain ⟨N, hN⟩ := exists_bound (P := fun _ => True) H.hγF H.mono (parF z) hparF fun w hw _ => hpar w hw
    have hlt : ∀ m, (∀ a, argR? z = some a → Lt a (A m)) → ∃ k, Lt z (γ k) := fun m h =>
      ⟨max N m + 1, (H.hC (max N m)).lt hz hzσ (fun w hw => lt_of_lt_of_leY (hparF w hw) (H.hγF N) (H.hγF _)
        (hN w hw trivial) (mono_le H.hγF H.mono (by omega))) fun a e =>
        lt_of_lt_of_leY (wnf_of_argR hz e) (hAF m) (hAF _) (h a e) (mono_le' hAF H.hAm (Nat.le_max_right _ _))⟩
    have hwit : ∀ a T', argR? z = some a → Clo z a T' → Lt σ T' → ∃ k, Lt z (γ k) := fun a T' ea C hσT => by
      rcases tgt_wit hσF hσt C hzσ hσT with ⟨r, e, hle⟩ | ⟨u, hu, hle⟩
      · refine hlt 0 fun a' e' => ?_
        rw [ea] at e'
        cases e'
        exact lt_of_le_of_ltY C.hA (wnf_of_argR hσF e) (hAF 0) hle (hr r e)
      · exact ⟨0, lt_of_le_of_ltY hz (hσF.of_mem_subs (fr_spec hu).1) (H.hγF 0) hle (hfr u hu)⟩
    cases z with
    | Xi j b =>
      have hj := hz.xi.1
      have hl : lev (.Xi j b) ≤ lev σ := lev_le_of_lt_gen hzσ
      simp only [lev] at hl
      by_cases hj' : lev σ = j
      · exact hwit b _ rfl (Clo.xi hz) ((lt_K_iffY hσF hj).mpr (by omega))
      · have hb : isBot σ = false := by
          rcases hσt with ⟨c, rfl, -⟩ | ⟨m, q, rfl⟩ | ⟨ζ, κ, b', rfl, -⟩ <;> rfl
        have hKσ : Lt (.K j) σ := bot_ltY rfl (by simp only [lev]; omega) hσt.principal hb hσF
        have h1 : Lt (.K j) (γ 1) := (H.hC 0).coll _ (WNF.K' hj) (inC_K _ _ _) hKσ
        exact ⟨1, lt_transY hz (WNF.K' hj) (H.hγF 1) ((lt_K_iffY hz hj).mpr (Nat.le_refl _)) h1⟩
    | Psi s k a =>
      have hP := hz.psi
      by_cases hc : closedS σ T (.Psi s k a) = true
      · have h1 := hCF _ hz hc (Or.inl rfl) (selfVis_self (Or.inr ⟨s, k, a, rfl⟩))
        exact ⟨0, lt_of_le_of_ltY hz hGF (H.hγF 0) h1 hG⟩
      have hkc : closedS σ T k = false := by
        cases e : closedS σ T k with
        | false => rfl
        | true =>
          exfalso
          apply hc
          simp [closedS, e]
      rcases triY hP.piF hσF with h | h | h
      · have hs : k.size < (Tm.Psi s k a).size := by
          simp only [Tm.size]
          omega
        obtain ⟨m, hm⟩ := ih k.size (by omega) k rfl hP.piF h (hCF.tgt hz hkc)
        exact ⟨m, lt_transY hz hP.piF (H.hγF m) (lt_psi_targetY hz) hm⟩
      · subst h
        have haT : Lt a T := by
          refine lt_of_gtY H.hTF hP.aF ?_
          refine Classical.byContradiction fun h' => hc ?_
          simp [closedS, leB_iff.mpr h']
        obtain ⟨m, hm⟩ := H.harg a hP.aF haT fun f hf => hpar f (by simp [parF, hf])
        exact hlt m fun a' e => by
          cases e
          exact hm
      · exact hwit a k rfl (Clo.psi hz) h
    | _ => exact hlt 0 fun a e => by cases e

/-- 閉じた点が始点以下の `K_m` 未満の項は塔の中 -/
theorem tow_pass_K {m : Nat} {T G : Tm} {γ A : Nat → Tm} (H : Tow (.K m) T γ A) (hKT : Le (.K m) T)
    (hGF : WNF G) (hG : Lt G (γ 0)) :
    ∀ z, WNF z → Lt z (.K m) → CF (closedPt m) G z → ∃ n, Lt z (γ n) := by
  have hKF := (H.hC 0).hT
  have hm : 1 ≤ m := hKF.k
  have hAF := fun n => (H.hC n).hA
  intro z
  induction hn : z.size using Nat.strongRecOn generalizing z with
  | ind n ih =>
    intro hz hzσ hCF
    have hparF : ∀ w, w ∈ parF z → WNF w := fun w hw => hz.of_mem_subs (parL_sub (parF_sub_parL hw)).1
    have hpar : ∀ w, w ∈ parF z → ∃ m, Lt w (γ m) := fun w hw => by
      have hs := (parL_sub (parF_sub_parL hw)).2
      exact ih w.size (by omega) w rfl (hparF w hw) (lt_transY (hparF w hw) hz hKF (parF_lt hz hw) hzσ)
        (hCF.par hz hw)
    obtain ⟨N, hN⟩ := exists_bound (P := fun _ => True) H.hγF H.mono (parF z) hparF fun w hw _ => hpar w hw
    have hlt : ∀ m, (∀ a, argR? z = some a → Lt a (A m)) → ∃ k, Lt z (γ k) := fun m h =>
      ⟨max N m + 1, (H.hC (max N m)).lt hz hzσ (fun w hw => lt_of_lt_of_leY (hparF w hw) (H.hγF N) (H.hγF _)
        (hN w hw trivial) (mono_le H.hγF H.mono (by omega))) fun a e =>
        lt_of_lt_of_leY (wnf_of_argR hz e) (hAF m) (hAF _) (h a e) (mono_le' hAF H.hAm (Nat.le_max_right _ _))⟩
    have hclosed : closedPt m z = true → ∃ k, Lt z (γ k) := fun hc => by
      have h1 := hCF _ hz hc (Or.inl rfl) (by
        cases z with
        | Xi j b => exact selfVis_self (Or.inl ⟨j, b, rfl⟩)
        | Psi s k a => exact selfVis_self (Or.inr ⟨s, k, a, rfl⟩)
        | _ => simp [closedPt] at hc)
      exact ⟨0, lt_of_le_of_ltY hz hGF (H.hγF 0) h1 hG⟩
    cases z with
    | Xi j b =>
      have hj := hz.xi.1
      have hl : j ≤ m := (lt_K_iffY hz hm).mp hzσ
      by_cases hj' : j = m
      · subst hj'
        by_cases hb : Lt b (.K j)
        · obtain ⟨k, hk⟩ := H.harg b hz.xi.2.1 (lt_of_lt_of_leY hz.xi.2.1 hKF H.hTF hb hKT) hpar
          exact hlt k fun a' e => by
            cases e
            exact hk
        · refine hclosed ?_
          simp only [closedPt, Bool.and_eq_true, beq_iff_eq]
          exact ⟨trivial, le_leB (le_of_not_ltY hz.xi.2.1 hKF hb)⟩
      · have hK1 : Lt (.K j) (.K m) := (lt_K_iffY (WNF.K' hj) hm).mpr (by simp only [lev]; omega)
        have h1 : Lt (.K j) (γ 1) := (H.hC 0).coll _ (WNF.K' hj) (inC_K _ _ _) hK1
        exact ⟨1, lt_transY hz (WNF.K' hj) (H.hγF 1) ((lt_K_iffY hz hj).mpr (Nat.le_refl _)) h1⟩
    | Psi s k a =>
      have hP := hz.psi
      by_cases hc : closedPt m k = true
      · exact hclosed hc
      · have hkc : closedPt m k = false := by simpa using hc
        have hl : lev (.Psi s k a) ≤ m := (lt_K_iffY hz hm).mp hzσ
        have hkK : Lt k (.K m) := (lt_K_iffY hP.piF hm).mpr hl
        have hs : k.size < (Tm.Psi s k a).size := by
          simp only [Tm.size]
          omega
        obtain ⟨j, hj⟩ := ih k.size (by omega) k rfl hP.piF hkK (hCF.tgt hz hkc)
        exact ⟨j, lt_transY hz hP.piF (H.hγF j) (lt_psi_targetY hz) hj⟩
    | _ => exact hlt 0 fun a e => by cases e

/-- 目標 `π` は塔の中 -/
theorem Tow.tgt_pass {σ T π : Tm} {γ A : Nat → Tm} (H : Tow σ T γ A) (hπF : WNF π) (hπt : IsTgt π)
    (hπσ : Lt π σ) (hrT : ∀ r, argR? π = some r → Lt r T) (hTs : ¬ isSucc T = true) (hT0 : T ≠ .zero)
    (hF : ∀ e, e ∈ fr π π → ∃ n, Lt e (γ n)) : ∃ n, Lt π (γ n) := by
  have hTF := H.hTF
  obtain ⟨N, hN⟩ := exists_bound (P := fun _ => True) H.hγF H.mono (fr π π)
    (fun w hw => hπF.of_mem_subs (fr_spec hw).1) fun w hw _ => hF w hw
  by_cases hπN : Lt π (γ N)
  · exact ⟨N, hπN⟩
  obtain ⟨g, hg, hgT, hgr⟩ : ∃ g, WNF g ∧ Lt g T ∧ ∀ r, argR? π = some r → Lt r g := by
    cases e : argR? π with
    | none => exact ⟨.zero, WNF.zero, zero_lt hT0, fun r e' => by cases e'⟩
    | some r =>
      have hrF := wnf_of_argR hπF e
      refine ⟨succT r, succT_WNF hrF, succT_lt_of_not_succ hrF hTF hTs (hrT r e), fun r' e' => ?_⟩
      cases e'
      exact lt_succT _
  have hC := inC_of_fr_lt hπF hπF (H.hγF N) hg hg (inC_tgt hπF hπt hg hgr)
    (le_of_not_ltY hπF (H.hγF N) hπN) (Or.inl rfl) fun w hw => hN w hw trivial
  exact H.hull hg (Or.inr hgT) π hπF hC hπσ

/-- `T` 未満で `C(a, γ_N)` に入る `a` は `A_n` 未満 -/
theorem Tow.arg {σ T a : Tm} {γ A : Nat → Tm} {N : Nat} (H : Tow σ T γ A) (ha : WNF a) (haT : Lt a T)
    (hC : inC a a (γ N) = true) : ∃ n, Lt a (A n) := by
  have hσF := (H.hC 0).hT
  refine H.harg a ha haT fun f hf => ?_
  exact H.hull ha (Or.inr haT) f (ha.of_mem_subs (fr_spec hf).1) (fr_of_inC a (fun u hu hn' hu' =>
    hn' (lt_transY (ha.of_mem_subs hu) (H.hγF N) hσF hu' (H.hlt N))) hC f hf) (fr_spec hf).2

end RTKA.Fund
