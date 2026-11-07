import Compact.FS.Fam

/-! 目標の族の閉包の列の仕様：`insertAtM`・`deadSeqM`。 -/

namespace RTKA.Fund

open Tm W

/-- 種の仮定 -/
structure SeedP (π X p : Tm) : Prop where
  hF : WNF p
  hlt : Lt p (.Psi .zero π X)
  hC : ∀ g d, WNF g → WNF d → inC (.Psi .zero π X) g d = true → inC p g d = true
  hn : (∃ m a, p = .Xi m a) ∨ ∃ s q a, p = .Psi s q a

namespace SeedP

variable {π X p : Tm}

theorem hπ (S : SeedP π X p) (ht : WNF (.Psi .zero π X)) : Lt p π :=
  lt_transY S.hF ht ht.psi.piF S.hlt (lt_psi_targetY ht)

theorem prin (S : SeedP π X p) : isPrincipal p = true := by
  rcases S.hn with ⟨m, a, rfl⟩ | ⟨s, q, a, rfl⟩ <;> rfl

theorem ns (S : SeedP π X p) : ¬ isSucc p = true := by
  rw [isSucc_principal S.prin]
  rcases S.hn with ⟨m, a, rfl⟩ | ⟨s, q, a, rfl⟩ <;> simp

theorem self_fr (S : SeedP π X p) {κ : Tm} (h : Lt p κ) : p ∈ fr κ p := by
  rcases S.hn with ⟨m, a, rfl⟩ | ⟨s, q, a, rfl⟩ <;> simp [fr, h]

theorem ne_one (S : SeedP π X p) : p ≠ .one := by
  rcases S.hn with ⟨m, a, rfl⟩ | ⟨s, q, a, rfl⟩ <;> simp

theorem ad (S : SeedP π X p) {g d : Tm} (h : Ad π X g d) : inC p g d = true :=
  h.seed S.hF S.hlt S.hC

end SeedP

theorem mem_pre_of_split {pre pre₂ rest : List Tm} {R R₂ : Tm} (e : pre ++ [R] = pre₂ ++ R₂ :: rest)
    (h : rest ≠ []) : R₂ ∈ pre := by
  rcases List.eq_nil_or_concat rest with rfl | ⟨l, a, rfl⟩
  · exact absurd rfl h
  · have e' : pre ++ [R] = (pre₂ ++ R₂ :: l) ++ [a] := by simpa using e
    have := (List.append_inj' e' rfl).1
    rw [this]
    simp

namespace MCtx

variable {π X τ Y μ : Tm} {T : Tm → Tm → Prop}

/-- 共終数が `π` 以上で `τ` 未満の正則項への仮想的な崩壊 -/
theorem low (C : MCtx π X τ Y μ T) {p R σ : Tm} {r : SeqD} (Sp : SeedP π X p)
    (hyp : Le (.Psi .zero τ Y) p) (hRm : R ∈ summands Y) (hR : BigUB R σ r) (hσt : IsTgt σ)
    (hστ : Lt σ τ) (hσπ : ¬ Lt σ π) : WNF (.Psi .zero σ (sc Y)) := by
  have hY := C.hYF
  have hτF := C.hτF
  have hπF := C.hπF
  have hσF := hR.hσF
  have hSF : WNF (sc Y) := succT_WNF hY
  have hw := C.hw0
  have hfr : ∀ w, w ∈ fr τ Y → Lt w π := fun w hw' =>
    lt_transY (hY.of_mem_subs (fr_spec hw').1) Sp.hF hπF
      (lt_of_lt_of_leY (hY.of_mem_subs (fr_spec hw').1) hw Sp.hF (FWOrder.k2 hw w hw') hyp) (Sp.hπ C.ht)
  have hπσ : Le π σ := le_of_not_ltY hσF hπF hσπ
  have hC : inC (sc Y) (sc Y) σ = true :=
    inC_of_fr_lt hSF hτF hσF hSF hSF C.hv.psi.Ca (Or.inr hστ) (Or.inl rfl) fun w hw' => by
      have hw1 : w ∈ fr τ Y := by
        have e : fr τ (sc Y) = fr τ Y := fr_succT τ Y
        rwa [e] at hw'
      exact lt_of_lt_of_leY (hY.of_mem_subs (fr_spec hw1).1) hπF hσF (hfr w hw1) hπσ
  have hRF : WNF R := (nfl_summands hY).1 R hRm |>.1
  have hRC : inC R (sc Y) π = true :=
    inC_of_fr_lt hRF hτF hπF hY hSF (inC_of_mem_summands hY C.hYC hRm) C.hle
      (Or.inr (lt_succT Y)) fun w hw' => hfr w ((mem_fr_iff hY).mpr ⟨R, hRm, hw'⟩)
  exact wnf_psi0 hσF hσt hSF hC fun q hq =>
    (arg_of_inC hq (hR.hσC _ π hSF hπF hRC) hσπ).2

end MCtx

/-- 種が `Ψ^0_τ(Y)` 以上で Mahlo 添字に持てるなら、`τ ≤ m(τ)`（K の階） -/
theorem idx_tgt_le {π X τ Y μ p : Tm} {T : Tm → Tm → Prop} (C : MCtx π X τ Y μ T) (hpF : WNF p)
    (hyp : Le (.Psi .zero τ Y) p) (hp : Lt p (mi τ)) :
    Le τ (mi τ) ∧ (validR τ (pred Y) = true → Le τ (pred Y)) := by
  have hw := C.hw0
  have hτF := C.hτF
  have hmF := WFY.WNF.mi hτF
  have hlt : Lt (.Psi .zero τ Y) (mi τ) := lt_of_le_of_ltY hw hpF hmF hyp hp
  have hom : ∀ c, τ ≠ .Om c := fun c e => by
    rw [e] at hlt
    have e0 := lt_oneY (e ▸ hw) hlt
    cases e0
  have h1 : Le τ (mi τ) := by
    refine le_of_not_ltY hmF hτF fun h => ?_
    have hmem : mi τ ∈ subs τ := by
      rcases C.hτt with ⟨c, e, -⟩ | ⟨n, q, e⟩ | ⟨ζ, κ, b, e, -⟩
      · exact absurd e (hom c)
      · rw [e]
        exact subs_xi (self_mem_subs q)
      · rw [e]
        exact subs_psi_s (self_mem_subs ζ)
    exact Lt.asymmY hw hmF (hlt) (lt_of_mem_tgt hw hmem h)
  refine ⟨h1, fun hv => ?_⟩
  unfold validR at hv
  rcases C.hτt with ⟨c, e, -⟩ | ⟨n, q, e⟩ | ⟨ζ, κ, b, e, -⟩
  · exact absurd e (hom c)
  · subst e
    simp only [argR?] at hv
    exact Or.inr (lt_of_le_of_ltY hτF hmF (wnf_pred C.hYF) h1 (ltB_iff.mp hv))
  · subst e
    simp only [argR?] at hv
    have hP := hτF.psi
    exact Or.inr (lt_of_le_of_ltY hτF hP.aF (wnf_pred C.hYF)
      (le_transY hτF hP.xiF hP.aF h1 (le_of_ne_gtY hP.xiF hP.aF hP.le)) (ltB_iff.mp hv))

/-- `Y` の加数の真の部分項は、`Y + 1` 未満なら `A` 未満 -/
def ArgOK (Y A : Tm) : Prop :=
  ∀ S, S ∈ summands Y → ∀ a, a ∈ subs S → a ≠ S → Lt a (sc Y) → Lt a A

/-- `τ` への崩壊で、引数が `Y` 以下で `Y` の部分項を越えるもの -/
def TauForm (τ Y y : Tm) : Prop := ∃ ξ A, y = .Psi ξ τ A ∧ Le A Y ∧ ArgOK Y A

theorem argOK_pred {Y : Tm} (hY : WNF Y) (hs : isSucc Y = true) : ArgOK Y (pred Y) := by
  intro S hS a ha hne hlt
  have hp := wnf_pred hY
  have hsm := hS
  rw [summands_eq_dropLast_one hs] at hsm
  rcases List.mem_append.mp hsm with h | h
  · have hSs : S ∈ subs (pred Y) := mem_subs_of_mem_summands (by
      unfold pred
      rw [summands_ofSummands _ (fun x hx => nfl_principal (nfl_summands hY) x (List.dropLast_subset _ hx))]
      exact h)
    have haF := hp.of_mem_subs (subs_trans hSs ha)
    have h0 := size_lt_of_mem_subs_ne ha hne
    have h1 := size_le_of_mem_subs hSs
    have h2 := size_le_of_mem_subs (mem_subs_of_mem_summands hS)
    have h3 : Lt a Y := (le_of_lt_succT haF hY hlt).resolve_left (ne_of_size_lt (by omega))
    have h4 : Le a (pred Y) := le_of_lt_succT haF hp (by rw [succT_pred hY hs]; exact h3)
    exact h4.resolve_left (ne_of_size_lt (by omega))
  · rw [List.mem_singleton.mp h] at ha hne
    simp only [subs, List.mem_singleton] at ha
    exact absurd ha hne

/-- 列の項の形 -/
theorem pack_tau {ξ τ Y P ceil R : Tm} {pre : List Tm} {r s : SeqD} {y : Tm} (hY : WNF Y)
    (hsum : summands Y = pre ++ [R]) (pk : Pack ξ τ (sc Y) P pre [.one] R ceil r s) (hy : InSeq s y) :
    TauForm τ Y y := by
  obtain ⟨P', x, -, rfl, H, hx0, hxg⟩ := pk.form hy
  refine ⟨ξ, approx pre P' x, rfl, ?_, fun S hS a ha hne hlt => ?_⟩
  · exact Or.inr (lt_of_lt_of_leY H.hAF (wnf_oadd H.hpreF H.hRF) hY H.hAtop (top_le hY hsum))
  · rw [hsum] at hS
    exact lt_approx_summand H.hN H.hx H.hPF H.hyR hx0 hxg hS ha hne (by rw [← H.hXeq]; exact hlt)

/-- 添字の近似の列の出力 -/
theorem mahlo_out {π X τ Y μ : Tm} {T : Tm → Tm → Prop} (C : MCtx π X τ Y μ T)
    (hSμ : ∀ u, u ∈ summands μ → u ≠ .one → SeqI u (info u).seq)
    (hμs : ∀ u, u ∈ summands μ → u ≠ .one → u ∈ subs (.Psi .zero π X) ∧ u.size < π.size)
    (P' : Tm) (pre rest : List Tm) (R : Tm) (hsum : summands μ = pre ++ R :: rest) (hR1 : R ≠ .one)
    (hPR : Lt P' R) (hSP : P' ≠ .zero → SeedP π X P') (hPF : WNF P') :
    IdxOut π X τ Y μ P' pre R (.app π (.idx τ Y) pre R (info R).seq P' .zero) := by
  have ht := C.ht
  have hY := C.hYF
  have hτF := C.hτF
  have hπF := C.hπF
  have hμF := C.hμF
  have hpτ : ∀ {p : Tm}, SeedP π X p → Lt p τ := fun Sp =>
    lt_of_lt_of_leY Sp.hF hπF hτF (Sp.hπ ht) C.hle
  have hRm : R ∈ summands μ := by
    rw [hsum]
    exact List.mem_append_right _ List.mem_cons_self
  have hμ1 : μ ≠ .one := by
    rintro rfl
    simp only [summands, List.mem_singleton] at hRm
    exact hR1 hRm
  have hRF := hμF.of_mem_subs (mem_subs_of_mem_summands hRm)
  have hRp := nfl_principal (nfl_summands hμF) R hRm
  obtain ⟨h0, h1⟩ := dom_ne_of_principal hRF hRp hR1
  have hP0 : P' = .zero ∨ P' ≠ .zero := by
    by_cases h : P' = .zero
    · exact Or.inl h
    · exact Or.inr h
  have hPτ : Lt P' τ := by
    rcases hP0 with rfl | h
    · exact zero_lt C.hτt.ne_zero
    · exact hpτ (hSP h)
  have hPπ : Lt P' π := by
    rcases hP0 with rfl | h
    · exact zero_lt ht.psi.tgt.ne_zero
    · exact (hSP h).hπ ht
  have hPs : ¬ isSucc P' = true := by
    rcases hP0 with rfl | h
    · simp [isSucc, summands]
    · exact (hSP h).ns
  have G : IdxG τ Y μ P' pre rest R :=
    { hv := C.hv, hYF := hY, hYC := C.hYC, hτY := C.hτY, hμF, hsum, hμY := C.hμY hμ1, hμm := C.hμm
      hμ1 := C.hμ1, hμ2 := C.hμ2, hPF, hPR, hPτ }
  exact idx_app C G (hSμ R hRm hR1) h0 h1 hRp (hμs R hRm hR1).1 (hμs R hRm hR1).2 hPs hPπ
    (fun g d h => by
      rcases hP0 with rfl | h'
      · exact inC_zero _ _
      · exact (hSP h').ad h)
    (fun h => (hSP h).self_fr (hpτ (hSP h)))

/-- 目標 `τ` の Mahlo 添字の上限の部品 -/
structure MPar (π X τ : Tm) (τf : Fam) : Prop where
  hf : τf.mdl = (info (mi τ)).sums
  hS : ∀ u, u ∈ summands (mi τ) → u ≠ .one → SeqI u (info u).seq
  hs : ∀ u, u ∈ summands (mi τ) → u ≠ .one → u ∈ subs (.Psi .zero π X) ∧ u.size < π.size
  hσ : ∀ σ, WNF σ → Le π σ → inC (mi τ) (mi τ) σ = true

/-- 目標の Mahlo 添字の上限 -/
theorem mi_facts {τ Y : Tm} (hτF : WNF τ) (hτt : IsTgt τ) (hYF : WNF Y)
    (hτY : ∀ r, argR? τ = some r → Lt r Y) :
    WNF (mi τ) ∧ (mi τ ≠ .one → Le (mi τ) Y) ∧ inC (mi τ) Y τ = true ∧ inC (mi τ) (mi τ) τ = true ∧
      ∀ g d, ¬ Lt τ d → inC τ g d = true → inC (mi τ) g d = true := by
  rcases hτt with ⟨c, rfl, -⟩ | ⟨n, q, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩
  · exact ⟨WNF.one, fun h => absurd rfl h, inC_one _ _, inC_one _ _, fun _ _ _ _ => inC_one _ _⟩
  · have hq := hτY q rfl
    have hqF := hτF.xi.2.1
    have hKF : WNF (.K n) := WNF.K' hτF.xi.1
    have hρK : Lt (.Xi n q) (.K n) := (lt_K_iffY hτF hτF.xi.1).mpr (Nat.le_refl _)
    have hfr : ∀ w, w ∈ fr (.K n) q → Lt w (.Xi n q) := fun w hw => FWOrder.k2x hτF w hw
    refine ⟨hqF, fun _ => Or.inr hq, ?_, ?_, fun g d hn h => ?_⟩
    · exact inC_of_fr_lt hqF hKF hτF hqF hYF hτF.xi.2.2.2.2 (Or.inr hρK) (Or.inr hq) hfr
    · exact inC_of_fr_lt hqF hKF hτF hqF hqF hτF.xi.2.2.2.2 (Or.inr hρK) (Or.inl rfl) hfr
    · rcases inC_xi_iff.mp h with h' | h'
      · exact absurd h' hn
      · exact h'.1
  · have hQ := hτF.psi
    have hb := hτY b rfl
    have hρκ : Lt (.Psi ζ κ b) κ := lt_psi_targetY hτF
    refine ⟨hQ.xiF, fun _ => le_transY hQ.xiF hQ.aF hYF (le_of_ne_gtY hQ.xiF hQ.aF hQ.le) (Or.inr hb),
      ?_, FWOrder.ms hτF, fun g d hn h => ?_⟩
    · exact inC_of_fr_lt hQ.xiF hQ.piF hτF hQ.aF hYF hQ.Cxi (Or.inr hρκ) (Or.inr hb)
        fun w hw => FWOrder.k2s hτF w hw
    · rcases inC_psi_iff.mp h with h' | ⟨-, h2, -, -⟩
      · exact absurd h' hn
      · exact h2

/-- `Y` が後者のとき、一つ下の引数の文脈（Mahlo 添字の上限は `m(τ)`） -/
theorem MCtx.down {π X τ Y μ : Tm} {T : Tm → Tm → Prop} (C : MCtx π X τ Y μ T) (hs : isSucc Y = true)
    (hv : validR τ (pred Y) = true) (hσ : ∀ σ, WNF σ → Le π σ → inC (mi τ) (mi τ) σ = true) :
    MCtx π X τ (pred Y) (mi τ) T := by
  have hτF := C.hτF
  have hY := C.hYF
  have hY₂ := wnf_pred hY
  have hτY : ∀ r, argR? τ = some r → Lt r (pred Y) := fun r hr => by
    unfold validR at hv
    rw [hr] at hv
    exact ltB_iff.mp hv
  obtain ⟨hμF, hμY, hμ1, hμ2, hμC⟩ := mi_facts hτF C.hτt hY₂ hτY
  have hlt : Lt (pred Y) Y := pred_lt hY hs
  have hnd : ∀ {d : Tm}, WNF d → Le d τ → ¬ Lt τ d := fun hd h h' => not_lt_of_leY hd hτF h h'
  have hsub : ∀ u, u ∈ summands (pred Y) → u ∈ summands Y := fun u hu => by
    rw [← succT_pred hY hs, summands_succT]
    exact List.mem_append_left _ hu
  exact
    { ht := C.ht
      hv := by
        show WNF (.Psi .zero τ (succT (pred Y)))
        rw [succT_pred hY hs]
        exact C.hw0
      hYC := inC_pred_self hY hs C.hYC
      hτY := hτY
      hle := C.hle
      hlev := C.hlev
      hYF := hY₂
      hYm := fun u hu => C.hYm u (hsub u hu)
      hμF := hμF
      hμY := hμY
      hμm := Or.inl rfl
      hμ1 := hμ1
      hμ2 := hμ2
      hμσ := hσ
      comp := fun g d h => by
        obtain ⟨h1, h2, h3, h4, -⟩ := C.comp g d h
        exact ⟨h1, h2, inC_pred_of hY h3, lt_transY hY₂ hY h.1 hlt h4, hμC g d (hnd h.2.1 h1) h2⟩
      hT := fun g d h => by
        obtain ⟨hg, hd, hπd, h1, h2, h3, h4, -⟩ := C.hT g d h
        exact ⟨hg, hd, hπd, h1, h2, inC_pred_of hY h3, le_transY hY₂ hY hg (Or.inr hlt) h4,
          hμC g d (hnd hd h1) h2⟩
      ltT := C.ltT
      ltI := fun z hy _ hC => C.ltT _ hy (lt_psi_targetY hy) fun g d h => by
        obtain ⟨hg, -, -, -, h2, h3, h4, -⟩ := C.hT g d h
        exact inC_psi_iff.mpr (Or.inr ⟨h2, hC g d h, inC_pred_of hY h3, lt_of_lt_of_leY hY₂ hY hg hlt h4⟩) }

/-- 添字の閉包の分割 -/
theorem idx_split {π X τ p : Tm} {pre : List Tm} {R : Tm} {r : SeqD} (Sp : SeedP π X p)
    (h : splitGtD p (info (mi τ)).sums = some (pre, R, r)) :
    r = (info R).seq ∧ Lt p R ∧ R ≠ .one ∧
      ∃ rest, summands (mi τ) = pre ++ R :: rest := by
  obtain ⟨L, rest, hys, hL, hpR₂, -, -⟩ := splitGtD_spec h
  have hsum₂ : summands (mi τ) = pre ++ R :: rest.map Prod.fst := by
    rw [← info_sums_fst, hys, List.map_append, hL, List.map_cons]
  have hrc : r = (info R).seq := by
    have hm' : (R, r) ∈ (info (mi τ)).sums := by
      rw [hys]
      simp
    exact coh_sums (mi τ) (R, r) hm'
  have hpR' : Lt p R := ltB_iff.mp hpR₂
  refine ⟨hrc, hpR', fun e => ?_, _, hsum₂⟩
  rw [e] at hpR'
  have e0 := lt_oneY Sp.hF hpR'
  rcases Sp.hn with ⟨m, a, e'⟩ | ⟨s, q, a, e'⟩ <;> rw [e0] at e' <;> cases e'

/-- `τ ≤ m(τ)` なら `m(τ)` の分割は必ずある -/
theorem idx_split_some {π X τ p : Tm} (Sp : SeedP π X p) (hτF : WNF τ)
    (hτp : isPrincipal τ = true) (hmF : WNF (mi τ)) (hpτ : Lt p τ) (hle : Le τ (mi τ)) :
    splitGtD p (info (mi τ)).sums ≠ none := by
  intro hn
  have hm0 : mi τ ≠ .zero := by
    intro e
    rw [e] at hle
    rcases hle with e' | h
    · rw [e'] at hτp
      cases hτp
    · exact not_lt_zero _ h
  obtain ⟨a, l, hsμ⟩ := List.exists_cons_of_ne_nil (summands_ne_nil hm0)
  have e' : (info (mi τ)).sums.map Prod.fst = a :: l := by
    rw [info_sums_fst]
    exact hsμ
  have hle2 : Le τ a := by
    rcases hle with e | h
    · rw [← e, summands_principal hτp] at hsμ
      simp only [List.cons.injEq] at hsμ
      exact Or.inl hsμ.1
    · exact le_head_of_prin_lt hτF hτp hmF hsμ h
  have haF := ((nfl_summands hmF).1 a (by rw [hsμ]; exact List.mem_cons_self)).1
  have hpa : Lt p a := lt_of_lt_of_leY Sp.hF hτF haF hpτ hle2
  cases hxs : (info (mi τ)).sums with
  | nil =>
    rw [hxs] at e'
    cases e'
  | cons q ys =>
    rw [hxs] at e' hn
    simp only [List.map_cons, List.cons.injEq] at e'
    have h0' := splitGtD_none_head hn
    rw [e'.1, ltB_iff.mpr hpa] at h0'
    cases h0'

/-- Mahlo 添字の閉包（`Y = Y'' + 1`、`τ ≤ m(τ)`）：列の項は `Ψ^z_τ(Y'')` -/
theorem idxm_spec {π X τ Y μ p : Tm} {T : Tm → Tm → Prop} {τf : Fam} (C : MCtx π X τ Y μ T)
    (M : MPar π X τ τf) (Sp : SeedP π X p)
    (hD : ∀ y, WNF y → isPrincipal y = true → Lt p y → TauForm τ Y y → Gp (.Psi .zero π X) y)
    (hs : isSucc Y = true) (h1 : Le τ (mi τ)) (h3 : validR τ (pred Y) = true) :
    SeqI (.Psi .zero π X) (match splitGtD p τf.mdl with
      | some (pre, R, r) => .app π (.idx τ (pred Y)) pre R r p .zero
      | none => famSeq τf π (some p)) := by
  have ht := C.ht
  have hτF := C.hτF
  have hY := C.hYF
  have C' := C.down hs h3 M.hσ
  have hpτ : Lt p τ := lt_of_lt_of_leY Sp.hF C.hπF hτF (Sp.hπ ht) C.hle
  have hτp : isPrincipal τ = true := by
    rcases C.hτt with ⟨c, e, -⟩ | ⟨n, q, e⟩ | ⟨ζ, κ, b, e, -⟩ <;> rw [e] <;> rfl
  rw [M.hf]
  cases hsp : splitGtD p (info (mi τ)).sums with
  | none => exact absurd hsp (idx_split_some Sp hτF hτp C'.hμF hpτ h1)
  | some q =>
    obtain ⟨pre, R, r⟩ := q
    obtain ⟨rfl, hpR, hR1, rest, hsum⟩ := idx_split Sp hsp
    simp only
    have o := mahlo_out C' M.hS M.hs p pre rest R hsum hR1 hpR (fun _ => Sp) Sp.hF
    refine o.inv fun y hy => ?_
    obtain ⟨P', x, -, rfl, hyF, -, -, -, -, hPy, -, -⟩ := o.form y hy
    exact hD _ hyF rfl (hPy (by
      rcases Sp.hn with ⟨m, a, e'⟩ | ⟨s, q, a, e'⟩ <;> rw [e'] <;> simp))
      ⟨_, pred Y, rfl, Or.inr (pred_lt hY hs), argOK_pred hY hs⟩

/-- 塞がった挿入 -/
theorem dead_spec {π X τ Y μ p : Tm} {T : Tm → Tm → Prop} {τf : Fam}
    (C : MCtx π X τ Y μ T) (M : MPar π X τ τf) (hS : ∀ u, u ∈ summands Y → u ≠ .one → SeqI u (info u).seq)
    (hY0 : Y ≠ .zero) (Sp : SeedP π X p)
    (hD : ∀ y, WNF y → isPrincipal y = true → Lt p y → TauForm τ Y y → Gp (.Psi .zero π X) y)
    (hyp : Le (.Psi .zero τ Y) p)
    (hpre : ∀ pre R, summands Y = pre ++ [R] → Le p (ofSummands pre))
    (hfam : idxOK τ p = true → isSucc Y = true → validR τ (pred Y) = false →
      SeqI (.Psi .zero π X) (famSeq τf π (some p)))
    (hfam2 : idxOK τ p = false → SeqI (.Psi .zero π X) (famSeq τf π (some p))) :
    SeqI (.Psi .zero π X) (deadSeqM τ τf π p Y (info Y).sums) := by
  have ht := C.ht
  have hY := C.hYF
  have hτF := C.hτF
  have hpπ := Sp.hπ ht
  have hpτ : Lt p τ := lt_of_lt_of_leY Sp.hF C.hπF hτF hpπ C.hle
  unfold deadSeqM
  by_cases hc : idxOK τ p = true
  · rw [ite_eq_left hc]
    have hc₀ := hc
    unfold idxOK at hc
    simp only [Bool.and_eq_true] at hc
    rw [mOfT_tgt C.hτt] at hc
    split
    · rename_i hone
      rw [lastS_dom hY hY0] at hone
      have hs : isSucc Y = true := (dom_eq_one_iff hY).mp hone
      have hYK : Le τ (mi τ) ∧ (validR τ (pred Y) = true → Le τ (pred Y)) :=
        idx_tgt_le C Sp.hF hyp (ltB_iff.mp hc.1)
      by_cases hv : validR τ (pred Y) = true
      · have e : (leB τ (mOfT τ) && leB τ (pred Y) && validR τ (pred Y)) = true := by
          rw [mOfT_tgt C.hτt, leB_iff.mpr (ne_gt_of_le hYK.1), leB_iff.mpr (ne_gt_of_le (hYK.2 hv)), hv]
          rfl
        rw [ite_eq_left e]
        exact idxm_spec C M Sp hD hs hYK.1 hv
      · have e : ¬ (leB τ (mOfT τ) && leB τ (pred Y) && validR τ (pred Y)) = true := fun h => by
          simp only [Bool.and_eq_true] at h
          exact hv h.2
        rw [ite_eq_right e]
        exact hfam hc₀ hs (by simpa using hv)
    · rename_i hone
      have hsum := summands_pre_last hY0
      have hlast : lastS (info Y).sums = (info (lastT (info Y).sums)).seq := lastS_coh (coh_sums Y)
      have hne1 : ¬ isSucc Y = true := fun h => by
        apply hone
        rw [lastS_dom hY hY0]
        exact (dom_eq_one_iff hY).mpr h
      obtain ⟨pre, hpr⟩ : ∃ pre, pre = preT (info Y).sums := ⟨_, rfl⟩
      obtain ⟨R, hR⟩ : ∃ R, R = lastT (info Y).sums := ⟨_, rfl⟩
      rw [← hpr, ← hR] at hsum
      rw [← hR] at hlast
      rw [← hpr, ← hR, hlast]
      have hRm : R ∈ summands Y := by
        rw [hsum]
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      have hRne : R ≠ .one := by
        intro e
        apply hne1
        show (summands Y).getLast? == some one
        rw [hsum, e]
        simp
      have hRF := hY.of_mem_subs (mem_subs_of_mem_summands hRm)
      have hRp := nfl_principal (nfl_summands hY) R hRm
      have hR0 : R ≠ .zero := by
        intro e
        rw [e] at hRp
        cases hRp
      obtain ⟨h0, h1⟩ := dom_ne_of_principal hRF hRp hRne
      have hRI := hS R hRm hRne
      obtain ⟨hx0F, hx0R⟩ := first_good hRI h0 h1
      have hsum' := summands_sc (rest₀ := []) hsum
      have S0 : SeedHyp τ (sc Y) .zero R := seed_zero C.hτt.ne_zero hR0
      have hI : IdxHyp p τ (sc Y) := ⟨Sp.hF, hpτ, ltB_iff.mp hc.1, hc.2⟩
      cases hm3 : mkApp π (.mahlo p τ) pre R (info R).seq .zero .zero with
      | some s =>
        have pk := pack_mkApp (Or.inr rfl : GenPsi (.mahlo p τ) p τ) C.hv hsum' S0 hRne hx0F hx0R hm3 hI
          (hpre pre R hsum) hRI h0 h1 hRp C.hπF C.hle
          (fun σ hσt _ hB hστ hσπ => C.low Sp hyp hRm hB hσt hστ hσπ) (C.τK)
          fun _ hd => dom_ne_succK hd
        simp only
        exact pk.lift C hsum WNF.zero (zero_lt C.ht.psi.tgt.ne_zero) (fun _ _ _ => inC_zero _ _)
          Sp.hF hpπ (fun _ _ h => Sp.ad h) fun y hy =>
            hD y (pk.wnf hy) (pk.prin hy) (pk.idx (Sp.self_fr hpτ) hy) (pack_tau hY hsum pk hy)
      | none => exact absurd rfl (mkApp_none rfl C.hw0 hsum (zero_lt hR0) hm3).2
  · rw [if_neg hc]
    exact hfam2 (by simpa using hc)

/-- 後者の崩壊への種の挿入（隙間は列の項の形ごとに仮定する） -/
theorem insert_specG {π X τ Y μ p : Tm} {T : Tm → Tm → Prop} {τf : Fam}
    (C : MCtx π X τ Y μ T) (M : MPar π X τ τf) (hS : ∀ u, u ∈ summands Y → u ≠ .one → SeqI u (info u).seq)
    (Sp : SeedP π X p) (hyp : Le (.Psi .zero τ Y) p)
    (hA : ∀ y, WNF y → isPrincipal y = true → Lt p y → TauForm τ Y y → Gp (.Psi .zero π X) y)
    (hB : idxOK τ p = false → Dom (.Psi .zero π X) p)
    (hfam0 : splitGtD p (info Y).sums = none → SeqI (.Psi .zero π X) (famSeq τf π (some p)))
    (hfam1 : idxOK τ p = true → isSucc Y = true → validR τ (pred Y) = false →
      SeqI (.Psi .zero π X) (famSeq τf π (some p)))
    (hfam2 : idxOK τ p = false → SeqI (.Psi .zero π X) (famSeq τf π (some p))) :
    SeqI (.Psi .zero π X) (insertAtM τ τf π p Y (info Y).sums) := by
  have hY0' : ∀ {R : Tm}, R ∈ summands Y → Y ≠ .zero := fun hRm e => by
    rw [e] at hRm
    cases hRm
  have ht := C.ht
  have hY := C.hYF
  have hτF := C.hτF
  have hpπ := Sp.hπ ht
  have hpτ : Lt p τ := lt_of_lt_of_leY Sp.hF C.hπF hτF hpπ C.hle
  unfold insertAtM
  cases hsp : splitGtD p (info Y).sums with
  | none => exact hfam0 hsp
  | some q =>
    obtain ⟨pre, R, r⟩ := q
    obtain ⟨L, rest, hys, hL, hpR₂, -, hhd⟩ := splitGtD_spec hsp
    have hpR : Lt p R := ltB_iff.mp hpR₂
    have hsumY : summands Y = pre ++ R :: rest.map Prod.fst := by
      rw [← info_sums_fst, hys, List.map_append, hL, List.map_cons]
    have hrc : r = (info R).seq := by
      have hm' : (R, r) ∈ (info Y).sums := by
        rw [hys]
        simp
      exact coh_sums Y (R, r) hm'
    subst hrc
    have hRm : R ∈ summands Y := by
      rw [hsumY]
      exact List.mem_append_right _ List.mem_cons_self
    have hRne : R ≠ .one := by
      intro e
      rw [e] at hpR
      exact Sp.ne_one (lt_oneY Sp.hF hpR ▸ absurd (lt_oneY Sp.hF hpR) (by
        rcases Sp.hn with ⟨m, a, e'⟩ | ⟨s, q, a, e'⟩ <;> rw [e'] <;> simp))
    have hRF := hY.of_mem_subs (mem_subs_of_mem_summands hRm)
    have hRp := nfl_principal (nfl_summands hY) R hRm
    obtain ⟨h0, h1⟩ := dom_ne_of_principal hRF hRp hRne
    have hRI := hS R hRm hRne
    obtain ⟨hx0F, hx0R⟩ := first_good hRI h0 h1
    have hsum' := summands_sc hsumY
    have S' : SeedHyp τ (sc Y) p R := ⟨Sp.hF, hpR, hpτ, Sp.ns⟩
    dsimp only
    by_cases hC : (!ltB p (lastT (info Y).sums) && idxOK τ p) = true
    · rw [ite_eq_left hC]
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hC
      refine dead_spec C M hS (hY0' hRm) Sp hA hyp (fun pre' R' e => ?_) hfam1 hfam2
      have hR'p : ¬ Lt p R' := by
        have hl : lastT (info Y).sums = R' := by
          have h9 := summands_pre_last (hY0' hRm)
          rw [e] at h9
          have h10 := (List.append_inj' h9 rfl).2
          simp only [List.cons.injEq, and_true] at h10
          exact h10.symm
        intro h
        rw [hl, ltB_iff.mpr h] at hC
        cases hC.1
      have hm2 : R ∈ pre' := by
        have h3 : R ∈ pre' ++ [R'] := by
          rw [← e]
          exact hRm
        rcases List.mem_append.mp h3 with h | h
        · exact h
        · rw [List.mem_singleton.mp h] at hpR
          exact absurd hpR hR'p
      have hN := nfl_summands hY
      rw [e] at hN
      have hpN := nfl_append_left hN
      exact Or.inr (lt_of_lt_of_leY Sp.hF hRF (wnf_ofSummands hpN) hpR (le_ofSummands_of_mem hpN hm2))
    rw [ite_eq_right hC]
    cases hm : mkApp π (.psi0 τ) pre R (info R).seq p .zero with
    | some s =>
      have pk := pack_mkApp (genPsi0 τ) C.hv hsum' S' hRne hx0F hx0R hm (IdxHyp.zero C.hv) (zero_le _) hRI
        h0 h1 hRp C.hπF C.hle (fun σ hσt _ hB hστ hσπ => C.low Sp hyp hRm hB hσt hστ hσπ) (C.τK)
        fun _ hd => dom_ne_succK hd
      simp only
      refine pk.lift C hsumY Sp.hF hpπ (fun _ _ h => Sp.ad h) WNF.zero
        (zero_lt C.ht.psi.tgt.ne_zero) (fun _ _ _ => inC_zero _ _) fun y hy => ?_
      have hpy := pk.seed (Sp.self_fr hpτ) hy
      by_cases hc2 : idxOK τ p = true
      · have hpL : Lt p (lastT (info Y).sums) := by
          have h3 : ltB p (lastT (info Y).sums) = true := by
            cases e : ltB p (lastT (info Y).sums) with
            | true => rfl
            | false =>
              exfalso
              apply hC
              rw [e, hc2]
              rfl
          exact ltB_iff.mp h3
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
        have hrest : rest.map Prod.fst = [] := Classical.byContradiction fun hne => by
          have h4 := (rest_eq_seed hY (summands_pre_last (hY0' hRm)) hsumY Sp.hF (Or.inr hpL) hhd' hne).1
          rw [h4] at hpL
          exact Lt.irrefl _ hpL
        rw [hrest] at hsumY pk
        exact hA y (pk.wnf hy) (pk.prin hy) hpy (pack_tau hY hsumY pk hy)
      · exact fun v hv hne hl => hB (by simpa using hc2) v hv hne hl y (pk.wnf hy) (pk.prin hy) hpy
    | none =>
      simp only
      have hnone := mkApp_none rfl C.hw0 hsumY hpR hm
      refine dead_spec C M hS (hY0' hRm) Sp hA hyp (fun pre' R' e => ?_) hfam1 hfam2
      have hm2 : R ∈ pre' := mem_pre_of_split (by rw [← e, hsumY]) hnone.2
      have hN := nfl_summands hY
      rw [e] at hN
      have hpN := nfl_append_left hN
      exact Or.inr (lt_of_lt_of_leY Sp.hF hRF (wnf_ofSummands hpN) hpR (le_ofSummands_of_mem hpN hm2))

/-- 後者の崩壊への種の挿入 -/
theorem insert_spec {π X τ Y μ p : Tm} {T : Tm → Tm → Prop} {τf : Fam}
    (C : MCtx π X τ Y μ T) (M : MPar π X τ τf) (hS : ∀ u, u ∈ summands Y → u ≠ .one → SeqI u (info u).seq)
    (Sp : SeedP π X p) (hD : Dom (.Psi .zero π X) p) (hyp : Le (.Psi .zero τ Y) p)
    (hfam : SeqI (.Psi .zero π X) (famSeq τf π (some p))) :
    SeqI (.Psi .zero π X) (insertAtM τ τf π p Y (info Y).sums) :=
  insert_specG C M hS Sp hyp (fun y hyF hyp' hl _ v hv hne hl' => hD v hv hne hl' y hyF hyp' hl)
    (fun _ => hD) (fun _ => hfam) (fun _ _ _ => hfam) fun _ => hfam

/-! ### `mahloSeq` -/

theorem splitPosD_spec {th : Tm} {ys : DL} {pre : List Tm} {R : Tm} {r : SeqD}
    (h : splitPosD th ys = some (pre, R, r)) :
    ∃ L rest, ys = L ++ (R, r) :: rest ∧ L.map Prod.fst = pre ∧ leB th R = true := by
  unfold splitPosD at h
  generalize hT : ys.takeWhile (fun s => leB th s.1) = T at h
  cases e : T.getLast? with
  | none => rw [e] at h; cases h
  | some q =>
    rw [e] at h
    obtain ⟨R', r'⟩ := q
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, rfl, rfl⟩ := h
    obtain ⟨L, rfl⟩ := List.getLast?_eq_some_iff.mp e
    refine ⟨L, ys.dropWhile (fun s => leB th s.1), ?_, ?_, ?_⟩
    · have := List.takeWhile_append_dropWhile (p := fun s => leB th s.1) (l := ys)
      rw [hT, List.append_assoc] at this
      exact this.symm
    · rw [← h1, List.dropLast_concat]
    · have : (R', r') ∈ ys.takeWhile (fun s => leB th s.1) := by rw [hT]; simp
      exact mem_takeWhile_imp' (p := fun s : Tm × SeqD => leB th s.1) this

/-- 後者の項の加数（`1` を除く）での分割 -/
theorem split_pos {X p : Tm} {pre : List Tm} {R : Tm} {r : SeqD} (hs : isSucc X = true)
    (h : splitPosD p (info X).sums.dropLast = some (pre, R, r)) :
    (∃ rest, summands X = pre ++ R :: rest) ∧ r = (info R).seq ∧ leB p R = true := by
  obtain ⟨L, rest, hys, hL, hR⟩ := splitPosD_spec h
  refine ⟨?_, ?_, hR⟩
  · have e1 : (info X).sums.dropLast.map Prod.fst = (summands X).dropLast := by
      rw [List.map_dropLast, info_sums_fst]
    rw [hys, List.map_append, hL, List.map_cons] at e1
    refine ⟨rest.map Prod.fst ++ [one], ?_⟩
    rw [summands_eq_dropLast_one hs, ← e1]
    simp
  · have hm : (R, r) ∈ (info X).sums := by
      apply List.dropLast_subset
      rw [hys]
      simp
    exact coh_sums X (R, r) hm

theorem mkApp_idx {ceil κ γ : Tm} {pre : List Tm} {R : Tm} {r : SeqD} {P c : Tm}
    (hP : P = .zero ∨ ltB P R = true) :
    mkApp ceil (.idx κ γ) pre R r P c = some (.app ceil (.idx κ γ) pre R r P c) := by
  unfold mkApp
  rcases hP with rfl | hP
  · simp [Gen.tgt?]
  · simp [hP, Gen.tgt?]

theorem maxO_seed {π X x : Tm} {P : Option Tm} (hx : SeedP π X x) (hP : ∀ p, P = some p → SeedP π X p) :
    SeedP π X (maxO P x) ∧ Le x (maxO P x) ∧ ∀ p, P = some p → Le p (maxO P x) := by
  cases P with
  | none => exact ⟨hx, Or.inl rfl, fun p e => by cases e⟩
  | some p =>
    have hp := hP p rfl
    unfold maxO
    by_cases h : ltB p x = true
    · simp only [h, ↓reduceIte]
      refine ⟨hx, Or.inl rfl, fun p' e => ?_⟩
      cases e
      exact Or.inr (ltB_iff.mp h)
    · simp only [h, ↓reduceIte]
      refine ⟨hp, ?_, fun p' e => ?_⟩
      · exact le_of_not_ltY hp.hF hx.hF fun h' => h (ltB_iff.mpr h')
      · cases e
        exact Or.inl rfl

/-- `0 < z` の Mahlo 添字の崩壊は `Ψ^0` より大きい -/
theorem psi0_lt_idx {τ Y z : Tm} (h0 : WNF (.Psi .zero τ Y)) (hy : WNF (.Psi z τ Y)) (hz : z ≠ .zero) :
    Lt (.Psi .zero τ Y) (.Psi z τ Y) := by
  have hne : Tm.Psi .zero τ Y ≠ .Psi z τ Y := fun e => hz (Tm.Psi.inj e).1.symm
  exact (lt_psi_psiY rfl hne).mpr (Or.inr ⟨lt_psi_targetY hy, lt_psi_targetY h0, Or.inr (Or.inr
    (Or.inl ⟨cmp_self _, rfl, zero_lt hz, inC_zero _ _⟩))⟩)

namespace MCtx

variable {π X τ Y μ : Tm} {T : Tm → Tm → Prop}

/-- Mahlo 添字が `μ` 未満の崩壊は標準形 -/
theorem nfI (C : MCtx π X τ Y μ T) {z : Tm} (hz : WNF z) (hzμ : Lt z μ) (hμ1 : μ ≠ .one)
    (h1 : inC z Y τ = true) (h2 : inC z (mi τ) τ = true) : WNF (.Psi z τ Y) :=
  WNF.mk_psi {
    tgt := C.hτt
    xiF := hz
    piF := C.hτF
    aF := C.hYF
    le := ne_gt_of_le (Or.inr (lt_of_lt_of_leY hz C.hμF C.hYF hzμ (C.hμY hμ1)))
    Ca := C.hYC
    Cxi := h1
    Cpi := inC_tgt C.hτF C.hτt C.hYF C.hτY
    mlt := lt_of_lt_of_leY hz C.hμF (WFY.WNF.mi C.hτF) hzμ C.hμm
    mC := h2 }

/-- Mahlo 添字が `μ` 未満の崩壊は種 -/
theorem seedI (C : MCtx π X τ Y μ T) {z : Tm} (hy : WNF (.Psi z τ Y)) (hzμ : Lt z μ)
    (hT : ∀ g d, T g d → inC z g d = true) (hA : ∀ g d, Ad π X g d → inC z g d = true) :
    SeedP π X (.Psi z τ Y) := by
  have ht := C.ht
  have hC : ∀ g d, Ad π X g d → inC (.Psi z τ Y) g d = true := fun g d h => by
    obtain ⟨-, h2, h3, h4, -⟩ := C.comp g d h
    exact inC_psi_iff.mpr (Or.inr ⟨h2, hA g d h, h3, h4⟩)
  have hlt : Lt (.Psi z τ Y) (.Psi .zero π X) :=
    coll_psiY ht _ hy (hC X _ (Ad.self ht)) (C.ltI z hy hzμ hT)
  refine ⟨hy, hlt, fun g d hg hd h => ?_, Or.inr ⟨z, τ, Y, rfl⟩⟩
  by_cases hdt : Lt (.Psi .zero π X) d
  · exact WFY.inC_of_ltY _ hy hd (lt_transY hy ht hd hlt hdt)
  · exact hC g d ⟨hg, hd, Or.inl ⟨h, hdt⟩⟩

theorem seed0 (C : MCtx π X τ Y μ T) (hμ0 : μ ≠ .zero) : SeedP π X (.Psi .zero τ Y) :=
  C.seedI C.hw0 (zero_lt hμ0) (fun _ _ _ => inC_zero _ _) (fun _ _ _ => inC_zero _ _)

end MCtx

/-- 列 `s0` -/
def s0Of (π τ Y μ : Tm) : SeqD :=
  (mkApp π (.idx τ Y) (preT (info μ).sums) (lastT (info μ).sums) (lastS (info μ).sums) .zero .zero).getD .none

/-- 最初の近似（隙間の下限） -/
def mcanon (π τ Y μ : Tm) : Tm :=
  if μ = .one then .Psi .zero τ Y else if isSucc μ then .Psi (pred μ) τ Y else (s0Of π τ Y μ).first

/-- `mahloSeq` の種の分岐（`μ` が極限で、種が素の 0 番目を越えるとき） -/
def mTail (π τ : Tm) (τf : Fam) (Y μ p : Tm) : SeqD :=
  match splitGtD p (info μ).sums with
  | some (pre, R, r) =>
    match mkApp π (.idx τ Y) pre R r p .zero with
    | some s => s
    | none => insertAtM τ τf π p Y (info Y).sums
  | none => insertAtM τ τf π p Y (info Y).sums

/-- 種が `t` の部分項を支配するときの種の分岐 -/
theorem mahlo_tail_dom {π X τ Y μ p : Tm} {T : Tm → Tm → Prop} {τf : Fam} (C : MCtx π X τ Y μ T)
    (M : MPar π X τ τf)
    (hSY : ∀ u, u ∈ summands Y → u ≠ .one → SeqI u (info u).seq)
    (hSμ : ∀ u, u ∈ summands μ → u ≠ .one → SeqI u (info u).seq)
    (hμs : ∀ u, u ∈ summands μ → u ≠ .one → u ∈ subs (.Psi .zero π X) ∧ u.size < π.size)
    (Sp : SeedP π X p) (hD : Dom (.Psi .zero π X) p) (hyp : Le (.Psi .zero τ Y) p)
    (hfam : SeqI (.Psi .zero π X) (famSeq τf π (some p))) :
    SeqI (.Psi .zero π X) (mTail π τ τf Y μ p) := by
  have hins := insert_spec C M hSY Sp hD hyp hfam
  unfold mTail
  cases hsp : splitGtD p (info μ).sums with
  | none => exact hins
  | some q =>
    obtain ⟨pre₂, R₂, r₂⟩ := q
    obtain ⟨L, rest, hys, hL, hpR₂, -, -⟩ := splitGtD_spec hsp
    have hsum₂ : summands μ = pre₂ ++ R₂ :: rest.map Prod.fst := by
      rw [← info_sums_fst, hys, List.map_append, hL, List.map_cons]
    have hrc : r₂ = (info R₂).seq := by
      have hm' : (R₂, r₂) ∈ (info μ).sums := by
        rw [hys]
        simp
      exact coh_sums μ (R₂, r₂) hm'
    subst hrc
    have hpR' : Lt p R₂ := ltB_iff.mp hpR₂
    have hR₂1 : R₂ ≠ .one := by
      intro e
      rw [e] at hpR'
      have e0 := lt_oneY Sp.hF hpR'
      rcases Sp.hn with ⟨m, a, e'⟩ | ⟨s, q, a, e'⟩ <;> rw [e0] at e' <;> cases e'
    dsimp only
    rw [mkApp_idx (Or.inr hpR₂)]
    simp only
    have o := mahlo_out C hSμ hμs p pre₂ _ R₂ hsum₂ hR₂1 hpR' (fun _ => Sp) Sp.hF
    refine o.inv fun y hy => ?_
    obtain ⟨P', x, -, rfl, hyF, -, -, -, -, hPy, -, -⟩ := o.form y hy
    exact fun v hv hne hl => hD v hv hne hl _ hyF rfl (hPy (by
      rcases Sp.hn with ⟨m, a, e'⟩ | ⟨s, q, a, e'⟩ <;> rw [e'] <;> simp))

/-- `mahloSeq` の仕様 -/
theorem mahlo_spec {π X τ Y μ : Tm} {T : Tm → Tm → Prop} {τf : Fam} {P : Option Tm}
    (C : MCtx π X τ Y μ T) (M : MPar π X τ τf) (hμ0 : μ ≠ .zero)
    (hSY : ∀ u, u ∈ summands Y → u ≠ .one → SeqI u (info u).seq)
    (hSμ : ∀ u, u ∈ summands μ → u ≠ .one → SeqI u (info u).seq)
    (hμs : ∀ u, u ∈ summands μ → u ≠ .one → u ∈ subs (.Psi .zero π X) ∧ u.size < π.size)
    (hP : ∀ p, P = some p → SeedP π X p)
    (hne : ∀ p, P = some p → ¬ isSucc μ = true → μ ≠ .one →
      IdxOut π X τ Y μ .zero (preT (info μ).sums) (lastT (info μ).sums) (s0Of π τ Y μ) →
      (s0Of π τ Y μ).first ≠ p)
    (hG : ∀ y, WNF y → isPrincipal y = true → (∀ p, P = some p → Lt p y) → Le (mcanon π τ Y μ) y →
      (μ = .one ∨ isSucc μ = true ∨ ∀ p, P = some p → ¬ Lt (mcanon π τ Y μ) p) → Gp (.Psi .zero π X) y)
    (hfam : ∀ p', SeedP π X p' → Dom (.Psi .zero π X) p' → Le (.Psi .zero τ Y) p' →
      SeqI (.Psi .zero π X) (famSeq τf π (some p')))
    (hTail : ∀ p, P = some p → ¬ isSucc μ = true → μ ≠ .one → Lt (s0Of π τ Y μ).first p →
      Le (.Psi .zero τ Y) p → SeqI (.Psi .zero π X) (mTail π τ τf Y μ p)) :
    SeqI (.Psi .zero π X) (mahloSeq τ τf π Y (info Y).sums μ (info μ).sums P) := by
  have ht := C.ht
  have hY := C.hYF
  have hτF := C.hτF
  have hπF := C.hπF
  have hμF := C.hμF
  have hw0 := C.hw0
  have hout := mahlo_out C hSμ hμs
  unfold mahloSeq
  by_cases h1 : μ = .one
  · rw [ite_eq_left h1]
    have hc : mcanon π τ Y μ = .Psi .zero τ Y := by
      unfold mcanon
      rw [ite_eq_left h1]
    obtain ⟨S1, S2, S3⟩ := maxO_seed (C.seed0 hμ0) hP
    have hD : Dom (.Psi .zero π X) (maxO P (.Psi .zero τ Y)) := fun v hv hne' hl y hyF hyp hlt =>
      hG y hyF hyp (fun p e => lt_of_le_of_ltY (hP p e).hF S1.hF hyF (S3 p e) hlt)
        (by rw [hc]; exact Or.inr (lt_of_le_of_ltY hw0 S1.hF hyF S2 hlt)) (Or.inl h1) v hv hne' hl
    exact insert_spec C M hSY S1 hD S2 (hfam _ S1 hD S2)
  rw [ite_eq_right h1]
  by_cases hs : isSucc μ = true
  · rw [ite_eq_left hs]
    have hc : mcanon π τ Y μ = .Psi (pred μ) τ Y := by
      unfold mcanon
      rw [ite_eq_right h1, ite_eq_left hs]
    have hpμ : Lt (pred μ) μ := pred_lt hμF hs
    have hpF := wnf_pred hμF
    have hpne : pred μ ≠ .zero := by
      intro e
      apply h1
      rw [← succT_pred hμF hs, e]
      rfl
    have hy₁ : WNF (.Psi (pred μ) τ Y) := C.nfI hpF hpμ h1 (inC_pred_of hμF C.hμ1) (inC_pred_of hμF C.hμ2)
    have Sx : SeedP π X (.Psi (pred μ) τ Y) := C.seedI hy₁ hpμ
      (fun g d h => inC_pred_of hμF (C.hT g d h).2.2.2.2.2.2.2)
      (fun g d h => inC_pred_of hμF (C.comp g d h).2.2.2.2)
    obtain ⟨S1, S2, S3⟩ := maxO_seed Sx hP
    have hgap : ∀ y, WNF y → isPrincipal y = true → Lt (maxO P (.Psi (pred μ) τ Y)) y →
        Gp (.Psi .zero π X) y := fun y hyF hyp hlt =>
      hG y hyF hyp (fun p e => lt_of_le_of_ltY (hP p e).hF S1.hF hyF (S3 p e) hlt)
        (by rw [hc]; exact Or.inr (lt_of_le_of_ltY hy₁ S1.hF hyF S2 hlt)) (Or.inr (Or.inl hs))
    have hD : Dom (.Psi .zero π X) (maxO P (.Psi (pred μ) τ Y)) := fun v hv hne' hl y hyF hyp hlt =>
      hgap y hyF hyp hlt v hv hne' hl
    have hyp₁ := le_transY hw0 hy₁ S1.hF (Or.inr (psi0_lt_idx hw0 hy₁ hpne)) S2
    have hins := insert_spec C M hSY S1 hD hyp₁ (hfam _ S1 hD hyp₁)
    cases hsp : splitPosD π (info μ).sums.dropLast with
    | none => exact hins
    | some q =>
      obtain ⟨pre, R, r⟩ := q
      obtain ⟨⟨rest, hsum⟩, rfl, hπR⟩ := split_pos hs hsp
      have hRm : R ∈ summands μ := by
        rw [hsum]
        exact List.mem_append_right _ List.mem_cons_self
      have hRF := hμF.of_mem_subs (mem_subs_of_mem_summands hRm)
      have hπR' : Le π R := le_of_ne_gtY hπF hRF (leB_iff.mp hπR)
      have hpR : Lt (maxO P (.Psi (pred μ) τ Y)) R := lt_of_lt_of_leY S1.hF hπF hRF (S1.hπ ht) hπR'
      have hR1 : R ≠ .one := by
        intro e
        rw [e] at hpR
        have e0 := lt_oneY S1.hF hpR
        rcases S1.hn with ⟨m, a, e'⟩ | ⟨s, q, a, e'⟩ <;> rw [e0] at e' <;> cases e'
      dsimp only
      rw [mkApp_idx (Or.inr (ltB_iff.mpr hpR))]
      simp only
      have o := hout _ pre rest R hsum hR1 hpR (fun _ => S1) S1.hF
      refine o.inv fun y hy => ?_
      obtain ⟨P', x, -, rfl, hyF, -, -, -, -, hPy, -, -⟩ := o.form y hy
      exact hgap _ hyF rfl (hPy (by
        rcases S1.hn with ⟨m, a, e'⟩ | ⟨s, q, a, e'⟩ <;> rw [e'] <;> simp))
  · rw [ite_eq_right hs]
    have hc : mcanon π τ Y μ = (s0Of π τ Y μ).first := by
      unfold mcanon
      rw [ite_eq_right h1, ite_eq_right hs]
    have hsum := summands_pre_last hμ0
    have hlast : lastS (info μ).sums = (info (lastT (info μ).sums)).seq := lastS_coh (coh_sums μ)
    obtain ⟨pre, hpr⟩ : ∃ pre, pre = preT (info μ).sums := ⟨_, rfl⟩
    obtain ⟨R, hR⟩ : ∃ R, R = lastT (info μ).sums := ⟨_, rfl⟩
    rw [← hpr, ← hR] at hsum
    rw [← hR] at hlast
    have hRm : R ∈ summands μ := by
      rw [hsum]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have hR1 : R ≠ .one := by
      intro e
      apply hs
      show (summands μ).getLast? == some one
      rw [hsum, e]
      simp
    have hRp := nfl_principal (nfl_summands hμF) R hRm
    have hR0 : R ≠ .zero := by
      intro e
      rw [e] at hRp
      cases hRp
    have hs0 : s0Of π τ Y μ = .app π (.idx τ Y) pre R (info R).seq .zero .zero := by
      unfold s0Of
      rw [← hpr, ← hR, hlast, mkApp_idx (Or.inl rfl)]
      rfl
    have o0 := hout .zero pre [] R hsum hR1 (zero_lt hR0) (fun h => absurd rfl h) WNF.zero
    rw [← hs0] at o0
    obtain ⟨P₀, x₀, -, hz₀, hfF, -, -, -, -, -, -, -⟩ := o0.form _ o0.mem
    generalize approx pre P₀ x₀ = z₀ at hz₀
    have hne' : ∀ p, P = some p → (s0Of π τ Y μ).first ≠ p := fun p e =>
      hne p e hs h1 (by rw [← hpr, ← hR]; exact o0)
    rw [← hpr, ← hR, hlast]
    dsimp only
    rw [mkApp_idx (Or.inl rfl)]
    simp only [Option.getD_some]
    rw [← hs0]
    have hle0 : Le (.Psi .zero τ Y) (s0Of π τ Y μ).first := by
      rw [hz₀]
      by_cases hz0 : z₀ = .zero
      · rw [hz0]
        exact Or.inl rfl
      · rw [hz₀] at hfF
        exact Or.inr (psi0_lt_idx hw0 hfF hz0)
    cases P with
    | none =>
      refine o0.inv fun y hy => ?_
      obtain ⟨P', x, -, rfl, hyF, -, -, -, hle, -, -, -⟩ := o0.form y hy
      exact hG _ hyF rfl (fun p e => by cases e) (by rw [hc]; exact hle) (Or.inr (Or.inr fun p e => by cases e))
    | some p =>
      have Sp := hP p rfl
      simp only
      by_cases h2 : ltB p (s0Of π τ Y μ).first = true
      · rw [ite_eq_left h2]
        refine o0.inv fun y hy => ?_
        obtain ⟨P', x, -, rfl, hyF, -, -, -, hle, -, -, -⟩ := o0.form y hy
        exact hG _ hyF rfl (fun p' e => by
          cases e
          exact lt_of_lt_of_leY Sp.hF hfF hyF (ltB_iff.mp h2) hle) (by rw [hc]; exact hle)
          (Or.inr (Or.inr fun p' e => by
            cases e
            rw [hc]
            exact Lt.asymmY Sp.hF hfF (ltB_iff.mp h2)))
      · rw [ite_eq_right h2, ite_eq_right (hne' p rfl)]
        have hlt : Lt (s0Of π τ Y μ).first p := by
          rcases triY hfF Sp.hF with h | h | h
          · exact h
          · exact absurd h (hne' p rfl)
          · exact absurd (ltB_iff.mpr h) h2
        exact hTail p rfl hs h1 hlt (Or.inr (lt_of_le_of_ltY hw0 hfF Sp.hF hle0 hlt))

end RTKA.Fund
