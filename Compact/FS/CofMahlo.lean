import Compact.FS.CofLeaf

/-! 族の閉包の段 `(τ, Y, μ)` の共終性：`insertAtM`・`deadSeqM`。

段の節点 `x = Ψ^s_τ(a)` の扱い：
* `a < T`（挿入点までの引数）：`ArgS`。
* `T ≤ a < Y`：残りの加数は種以下で `τ` 未満なので、`w₀ = Ψ^0_τ(Y)` について成分の前線が `w₀` 未満（`x < w₀ ≤ p`）。
* `a = Y`、添字 `s < μ`：段の添字の閉包（仮定 `N2C`）。
* 下の段（目標が `t` と `τ` の間）：仮定 `LowC`。 -/

namespace RTKA.Fund

open Tm W

/-! ### 和の分割 -/

theorem cmpList_cases2 : ∀ {pre l M : List Tm}, NFL l → (∀ x, x ∈ pre → WNF x ∧ isPrincipal x = true) →
    cmpList l (pre ++ M) = .lt → cmpList l pre = .lt ∨ ∃ l', l = pre ++ l' ∧ cmpList l' M = .lt
  | [], l, M, _, _, h => Or.inr ⟨l, rfl, h⟩
  | h :: tl, [], M, _, _, _ => Or.inl (cmpList_nil_cons _ _)
  | h :: tl, u :: us, M, hl, hp, e => by
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
      rcases cmpList_cases2 (nfl_tail hl) (fun x hx => hp x (List.mem_cons_of_mem _ hx)) e with h' | ⟨l', e', h'⟩
      · refine Or.inl ?_
        rw [cmpList_cons_cons_eq _ _ ec]
        exact h'
      · exact Or.inr ⟨l', by rw [e']; rfl, h'⟩

/-- `ofSummands (L₁ ++ L₂)` 未満で `ofSummands L₁` 以上の項は `L₁ ++ L'`（`L' < L₂`） -/
theorem lt_sum_split {L₁ L₂ : List Tm} {a : Tm} (hN : NFL (L₁ ++ L₂)) (ha : WNF a)
    (hlt : Lt a (ofSummands (L₁ ++ L₂))) (hge : ¬ Lt a (ofSummands L₁)) :
    ∃ L', summands a = L₁ ++ L' ∧ cmpList L' L₂ = .lt := by
  have hN1 := nfl_append_left hN
  have h1 : cmpList (summands a) (L₁ ++ L₂) = .lt := by
    have := hlt
    unfold Lt at this
    rwa [cmp_eq, summands_ofSummands _ (nfl_principal hN)] at this
  rcases cmpList_cases2 (nfl_summands ha) hN1.1 h1 with h2 | ⟨l', e, h3⟩
  · exact absurd (by unfold Lt; rw [cmp_eq, summands_ofSummands _ (nfl_principal hN1)]; exact h2) hge
  · exact ⟨l', e, h3⟩

/-- 並びの元は先頭以下 -/
theorem le_head_mem {h u : Tm} {l : List Tm} (hN : NFL (h :: l)) (hu : u ∈ h :: l) : Le u h := by
  rcases List.mem_cons.mp hu with rfl | hu
  · exact Or.inl rfl
  · obtain ⟨s, t, rfl⟩ := List.append_of_mem hu
    have hN' : NFL ((h :: s) ++ u :: t) := by simpa using hN
    exact le_of_ne_gtY (hN'.1 u (by simp)).1 (hN'.1 h (by simp)).1 (le_of_nfl_append hN' h List.mem_cons_self)

/-! ### 段の仮定 -/

/-- 下の段：目標が `t` と `τ` の間の節点は、種以下か `t` の部分項以下 -/
def LowC (t τ : Tm) (P : Option Tm) : Prop :=
  ∀ x, WNF x → Lt x t → Lt t (tgtN x) → Lt (tgtN x) τ →
    (∃ p, P = some p ∧ Le x p) ∨ SubLe t x

/-- 段の節点の分類 -/
def ClsC (t τ Y μ : Tm) : Prop :=
  ∀ s a, WNF (.Psi s τ a) → Lt (.Psi s τ a) t → Lt a Y ∨ (a = Y ∧ Lt s μ) ∨ SubLe t (.Psi s τ a)

/-- 段の添字の閉包は種 `p` 以下 -/
def N2C (t τ Y μ p : Tm) : Prop :=
  ∀ s, WNF (.Psi s τ Y) → Lt (.Psi s τ Y) t → Lt s μ → Le (.Psi s τ Y) p ∨ SubLe t (.Psi s τ Y)

theorem seqI_gp {t : Tm} {s : SeqD} (hI : SeqI t s) (htp : isPrincipal t = true) {y : Tm}
    (hy : InSeq s y) : Gp t y := by
  rcases hy with ⟨hd, n, rfl⟩ | ⟨σ, η, hd, hη, hησ, rfl⟩
  · unfold SeqI at hI
    rw [hd] at hI
    exact fun v hv hne hl => hI.2 n v hv hne hl
  · unfold SeqI at hI
    rw [hd] at hI
    exact fun v hv hne hl => hI.2.1 htp η hη hησ v hv hne hl

theorem seqI_wnf {t : Tm} {s : SeqD} (hI : SeqI t s) {y : Tm} (hy : InSeq s y) : WNF y := by
  rcases hy with ⟨hd, n, rfl⟩ | ⟨σ, η, hd, hη, hησ, rfl⟩
  · unfold SeqI at hI
    rw [hd] at hI
    exact (hI.1.good n).1
  · unfold SeqI at hI
    rw [hd] at hI
    exact (hI.1.1.good.1 η hη hησ).1


/-- 種以下か部分項以下なら、種より大きい列の項の下 -/
theorem lt_of_le_seed {t p x y : Tm} (ht : WNF t) (hpF : WNF p) (hx : WNF x) (hy : WNF y) (hpy : Lt p y)
    (hG : Gp t y) (h : Le x p ∨ SubLe t x) : Lt x y := by
  rcases h with h | h
  · exact lt_of_le_of_ltY hx hpF hy h hpy
  · exact h.lt ht hx hy hG

/-! ### 段の閉じた点 `w₀ = Ψ^0_τ(Y)` -/

/-- `Y` の加数で `τ` 未満のものは `w₀` 未満 -/
theorem summand_lt_w0 {π X τ Y μ u : Tm} {T : Tm → Tm → Prop} (C : MCtx π X τ Y μ T)
    (hu : u ∈ summands Y) (huτ : Lt u τ) : Lt u (.Psi .zero τ Y) := by
  have hw := C.hw0
  have hY := C.hYF
  have huF := hY.of_mem_subs (mem_subs_of_mem_summands hu)
  have h1 : inC u Y τ = true := inC_of_mem_summands hY C.hYC hu
  have h2 : inC u Y (.Psi .zero τ Y) = true :=
    inC_of_fr_lt huF C.hτF hw hY hY h1 (Or.inr (lt_psi_targetY hw)) (Or.inl rfl) fun w hw' =>
      FWOrder.k2 hw w ((mem_fr_iff hY).mpr ⟨u, hu, hw'⟩)
  exact coll_psiY hw u huF h2 huτ

/-- `a < Y` で成分の前線が `w₀` 未満なら `x < w₀` -/
theorem lt_w0 {π X τ Y μ s a : Tm} {T : Tm → Tm → Prop} (C : MCtx π X τ Y μ T) (hx : WNF (.Psi s τ a))
    (haY : Lt a Y) (hF : ∀ f, f ∈ parF (.Psi s τ a) → Lt f (.Psi .zero τ Y)) :
    Lt (.Psi s τ a) (.Psi .zero τ Y) :=
  (Clo.psi C.hw0).lt hx (lt_psi_targetY hx) hF fun a' e => by
    cases e
    exact haY

/-- `Y = L₁ ⊕ L₂`（`L₂` は `τ` 未満）、`a = L₁ ⊕ L'`（`L' < L₂`）、`s < w₀` なら成分の前線は `w₀` 未満 -/
theorem parF_lt_w0 {π X τ Y μ s a : Tm} {T : Tm → Tm → Prop} {L₁ L₂ L' : List Tm} (C : MCtx π X τ Y μ T)
    (hx : WNF (.Psi s τ a)) (hsum : summands Y = L₁ ++ L₂) (hL₂ : ∀ u, u ∈ L₂ → Lt u τ) (hne : L₂ ≠ [])
    (ha : summands a = L₁ ++ L') (hL' : cmpList L' L₂ = .lt) (hs : Lt s (.Psi .zero τ Y)) :
    ∀ f, f ∈ parF (.Psi s τ a) → Lt f (.Psi .zero τ Y) := by
  have hw := C.hw0
  have hY := C.hYF
  have hτF := C.hτF
  have hP := hx.psi
  have hN : NFL (L₁ ++ L₂) := hsum ▸ nfl_summands hY
  have hL₂N := nfl_append_right hN
  have hL'N : NFL L' := by
    have h := nfl_summands hP.aF
    rw [ha] at h
    exact nfl_append_right h
  obtain ⟨h₂, l₂, e₂⟩ := List.exists_cons_of_ne_nil hne
  have hh₂ : h₂ ∈ L₂ := by rw [e₂]; exact List.mem_cons_self
  have hL₂w : Lt (ofSummands L₂) (.Psi .zero τ Y) := by
    refine lt_prin_of_head (h := h₂) (r := l₂) ?_ rfl (hL₂N.1 h₂ hh₂).2
      (summand_lt_w0 C (by rw [hsum]; exact List.mem_append_right _ hh₂) (hL₂ h₂ hh₂))
    rw [summands_ofSummands _ (nfl_principal hL₂N), e₂]
  have hL'w : Lt (ofSummands L') (.Psi .zero τ Y) := by
    have h1 : Lt (ofSummands L') (ofSummands L₂) := by
      unfold Lt
      rw [cmp_eq, summands_ofSummands _ (nfl_principal hL'N), summands_ofSummands _ (nfl_principal hL₂N)]
      exact hL'
    exact lt_transY (wnf_ofSummands hL'N) (wnf_ofSummands hL₂N) hw h1 hL₂w
  intro f hf
  simp only [parF, List.mem_append] at hf
  rcases hf with (hf | hf) | hf
  · obtain ⟨u, hu, hfu⟩ := (mem_fr_iff hP.aF).mp hf
    rw [ha] at hu
    rcases List.mem_append.mp hu with hu | hu
    · exact FWOrder.k2 hw f ((mem_fr_iff hY).mpr ⟨u, by rw [hsum]; exact List.mem_append_left _ hu, hfu⟩)
    · have huF := (hL'N.1 u hu).1
      have hfF := huF.of_mem_subs (fr_spec hfu).1
      exact lt_of_le_of_ltY hfF (wnf_ofSummands hL'N) hw
        (le_transY hfF huF (wnf_ofSummands hL'N) (fr_leY hτF huF hfu) (le_ofSummands_of_mem hL'N hu)) hL'w
  · exact lt_of_le_of_ltY (hP.xiF.of_mem_subs (fr_spec hf).1) hP.xiF hw (fr_leY hτF hP.xiF hf) hs
  · exact FWOrder.k2t hw f hf

/-- `m(τ) ≤ p < τ` なら `m(τ) ≤ w₀` -/
theorem mi_le_w0 {π X τ Y μ p : Tm} {T : Tm → Tm → Prop} (C : MCtx π X τ Y μ T) (hpF : WNF p)
    (hpτ : Lt p τ) (hmp : Le (mi τ) p) : Le (mi τ) (.Psi .zero τ Y) := by
  have hw := C.hw0
  have hmF := WFY.WNF.mi C.hτF
  refine le_of_not_ltY hw hmF fun h => ?_
  have h1 := (idx_tgt_le C hw (Or.inl rfl) h).1
  exact not_lt_of_leY C.hτF hpF (le_transY C.hτF hmF hpF h1 hmp) hpτ

/-- 添字に持てない種は `m(τ)` 以上 -/
theorem mi_le_of_idx {τ p : Tm} (hτt : IsTgt τ) (hτF : WNF τ) (hpF : WNF p) (hpτ : Lt p τ)
    (h : idxOK τ p = false) : Le (mi τ) p := by
  refine le_of_not_ltY hpF (WFY.WNF.mi hτF) fun h' => ?_
  have : idxOK τ p = true := by
    unfold idxOK
    rw [mOfT_tgt hτt, ltB_iff.mpr h', WFY.inC_of_ltY _ hpF hτF hpτ]
    rfl
  rw [this] at h
  cases h

/-- Mahlo 添字の上限の前線は目標の前線 -/
theorem fr_mi_sub {τ w : Tm} (hτt : IsTgt τ) (h : w ∈ fr τ (mi τ)) : w ∈ fr τ τ := by
  rcases hτt with ⟨c, rfl, -⟩ | ⟨n, q, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩
  · simp [mi, fr] at h
  · have hne : ¬ Lt (Tm.Xi n q) (.Xi n q) := Lt.irrefl _
    rw [fr]
    simp only [hne, ↓reduceIte]
    exact h
  · exact fr_psi_self (Or.inl rfl) h

/-- 挿入点より後ろの引数：残りの加数が `p` 以下で `m(τ) ≤ p` なら `x < w₀` -/
theorem insert_tail_lt {π X τ Y μ p s a R : Tm} {T : Tm → Tm → Prop} {pre rest : List Tm}
    (C : MCtx π X τ Y μ T) (hsumY : summands Y = pre ++ R :: rest) (hrest : ∀ u, u ∈ rest → Le u p)
    (hpF : WNF p) (hpτ : Lt p τ) (hmp : Le (mi τ) p)
    (hx : WNF (.Psi s τ a)) (haY : Lt a Y) (haT : ¬ Lt a (oadd (ofSummands pre) R)) :
    Lt (.Psi s τ a) (.Psi .zero τ Y) := by
  have hY := C.hYF
  have hP := hx.psi
  have hN : NFL (pre ++ R :: rest) := hsumY ▸ nfl_summands hY
  have hsum' : summands Y = (pre ++ [R]) ++ rest := by rw [hsumY]; simp
  have hN' : NFL ((pre ++ [R]) ++ rest) := hsum' ▸ nfl_summands hY
  have hpR := nfl_append_left hN'
  have hT : ofSummands (pre ++ [R]) = oadd (ofSummands pre) R :=
    eq_oadd_of_sum (wnf_ofSummands hpR) (summands_ofSummands _ (nfl_principal hpR))
  have hne : rest ≠ [] := by
    intro e
    apply haT
    have hYe : Y = oadd (ofSummands pre) R := eq_oadd_of_sum hY (by rw [hsumY, e])
    rwa [hYe] at haY
  have hYeq : Y = ofSummands ((pre ++ [R]) ++ rest) := by rw [← hsum', ofSummands_summands Y hY]
  obtain ⟨L', ha, hL'⟩ := lt_sum_split hN' hP.aF (by rw [← hYeq]; exact haY) (by rw [hT]; exact haT)
  have hs : Lt s (.Psi .zero τ Y) :=
    lt_of_lt_of_leY hP.xiF (WFY.WNF.mi C.hτF) C.hw0 hP.mlt (mi_le_w0 C hpF hpτ hmp)
  refine lt_w0 C hx haY (parF_lt_w0 C hx hsum' (fun u hu => ?_) hne ha hL' hs)
  have huF := (hN.1 u (List.mem_append_right _ (List.mem_cons_of_mem _ hu))).1
  exact lt_of_le_of_ltY huF hpF C.hτF (hrest u hu) hpτ


/-- `m(τ)` の加数で `τ` 未満のものは `w₀` 未満 -/
theorem misum_lt_w0 {π X τ Y μ u : Tm} {T : Tm → Tm → Prop} (C : MCtx π X τ Y μ T)
    (hu : u ∈ summands (mi τ)) (huτ : Lt u τ) : Lt u (.Psi .zero τ Y) := by
  have hw := C.hw0
  have hY := C.hYF
  have hτF := C.hτF
  obtain ⟨hmF, -, hm1, -, -⟩ := mi_facts hτF C.hτt hY C.hτY
  have huF := hmF.of_mem_subs (mem_subs_of_mem_summands hu)
  have h1 : inC u Y τ = true := inC_of_mem_summands hmF hm1 hu
  have h2 : inC u Y (.Psi .zero τ Y) = true :=
    inC_of_fr_lt huF hτF hw hY hY h1 (Or.inr (lt_psi_targetY hw)) (Or.inl rfl) fun w hw' =>
      FWOrder.k2t hw w (fr_mi_sub C.hτt ((mem_fr_iff hmF).mpr ⟨u, hu, hw'⟩))
  exact coll_psiY hw u huF h2 huτ

/-- 添字の閉包の残り：`z ≥ T`（`m(τ) = T ⊕ rest`、`rest` は `τ` 未満）で引数の前線が `w₀` 未満なら `x < w₀` -/
theorem idx_tail_lt {π X τ Y μ z a R : Tm} {T : Tm → Tm → Prop} {pre rest : List Tm} (C : MCtx π X τ Y μ T)
    (hsum : summands (mi τ) = pre ++ R :: rest) (hrest : ∀ u, u ∈ rest → Lt u τ)
    (hx : WNF (.Psi z τ a)) (haY : Lt a Y) (hfa : ∀ f, f ∈ fr τ a → Lt f (.Psi .zero τ Y))
    (hzT : ¬ Lt z (oadd (ofSummands pre) R)) : Lt (.Psi z τ a) (.Psi .zero τ Y) := by
  have hw := C.hw0
  have hτF := C.hτF
  have hP := hx.psi
  have hmF := WFY.WNF.mi hτF
  have hsum' : summands (mi τ) = (pre ++ [R]) ++ rest := by rw [hsum]; simp
  have hN' : NFL ((pre ++ [R]) ++ rest) := hsum' ▸ nfl_summands hmF
  have hpR := nfl_append_left hN'
  have hT : ofSummands (pre ++ [R]) = oadd (ofSummands pre) R :=
    eq_oadd_of_sum (wnf_ofSummands hpR) (summands_ofSummands _ (nfl_principal hpR))
  have hmeq : mi τ = ofSummands ((pre ++ [R]) ++ rest) := by rw [← hsum', ofSummands_summands _ hmF]
  have hzm : Lt z (mi τ) := hP.mlt
  refine lt_w0 C hx haY fun f hf => ?_
  simp only [parF, List.mem_append] at hf
  rcases hf with (hf | hf) | hf
  · exact hfa f hf
  · have hne : rest ≠ [] := by
      intro e
      apply hzT
      have h' : mi τ = oadd (ofSummands pre) R := eq_oadd_of_sum hmF (by rw [hsum, e])
      rwa [h'] at hzm
    obtain ⟨L', hz, hL'⟩ := lt_sum_split hN' hP.xiF (by rw [← hmeq]; exact hzm) (by rw [hT]; exact hzT)
    have hL₂N := nfl_append_right hN'
    have hL'N : NFL L' := by
      have h := nfl_summands hP.xiF
      rw [hz] at h
      exact nfl_append_right h
    obtain ⟨h₂, l₂, e₂⟩ := List.exists_cons_of_ne_nil hne
    have hh₂ : h₂ ∈ rest := by rw [e₂]; exact List.mem_cons_self
    have hL₂w : Lt (ofSummands rest) (.Psi .zero τ Y) := by
      refine lt_prin_of_head (h := h₂) (r := l₂) ?_ rfl (hL₂N.1 h₂ hh₂).2
        (misum_lt_w0 C (by rw [hsum]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hh₂)) (hrest h₂ hh₂))
      rw [summands_ofSummands _ (nfl_principal hL₂N), e₂]
    have hL'w : Lt (ofSummands L') (.Psi .zero τ Y) := by
      have h1 : Lt (ofSummands L') (ofSummands rest) := by
        unfold Lt
        rw [cmp_eq, summands_ofSummands _ (nfl_principal hL'N), summands_ofSummands _ (nfl_principal hL₂N)]
        exact hL'
      exact lt_transY (wnf_ofSummands hL'N) (wnf_ofSummands hL₂N) hw h1 hL₂w
    obtain ⟨u, hu, hfu⟩ := (mem_fr_iff hP.xiF).mp hf
    rw [hz] at hu
    rcases List.mem_append.mp hu with hu | hu
    · exact FWOrder.k2t hw f (fr_mi_sub C.hτt ((mem_fr_iff hmF).mpr
        ⟨u, by rw [hsum']; exact List.mem_append_left _ hu, hfu⟩))
    · have huF := (hL'N.1 u hu).1
      have hfF := huF.of_mem_subs (fr_spec hfu).1
      exact lt_of_le_of_ltY hfF (wnf_ofSummands hL'N) hw
        (le_transY hfF huF (wnf_ofSummands hL'N) (fr_leY hτF huF hfu) (le_ofSummands_of_mem hL'N hu)) hL'w
  · exact FWOrder.k2t hw f hf

/-- Mahlo 添字の閉包（`Y = Y'' + 1`、`τ ≤ m(τ)`）の共終性 -/
theorem idxm_cof {π X τ Y μ p : Tm} {T : Tm → Tm → Prop} {τf : Fam} (C : MCtx π X τ Y μ T)
    (M : MPar π X τ τf) (hSmC : ∀ u, u ∈ summands (mi τ) → u ≠ .one → SeqC u (info u).seq)
    (Sp : SeedP π X p) (hs : isSucc Y = true) (h1 : Le τ (mi τ))
    (h3 : validR τ (pred Y) = true) (hτfr : ∀ u, u ∈ fr τ τ → u ∈ fr π π)
    (hLow : LowC (.Psi .zero π X) τ (some p)) (hCls : ClsC (.Psi .zero π X) τ Y μ)
    (hN2 : N2C (.Psi .zero π X) τ Y μ p) (hyp : Le (.Psi .zero τ Y) p) :
    SeqI (.Psi .zero π X) (match splitGtD p τf.mdl with
      | some (pre, R, r) => .app π (.idx τ (pred Y)) pre R r p .zero
      | none => famSeq τf π (some p)) →
    SeqC (.Psi .zero π X) (match splitGtD p τf.mdl with
      | some (pre, R, r) => .app π (.idx τ (pred Y)) pre R r p .zero
      | none => famSeq τf π (some p)) := by
  have ht := C.ht
  have hτF := C.hτF
  have hY := C.hYF
  have C' := C.down hs h3 M.hσ
  have hpF := Sp.hF
  have hpτ : Lt p τ := lt_of_lt_of_leY hpF C.hπF hτF (Sp.hπ ht) C.hle
  have hτp : isPrincipal τ = true := by
    rcases C.hτt with ⟨c, e, -⟩ | ⟨n, q, e⟩ | ⟨ζ, κ, b, e, -⟩ <;> rw [e] <;> rfl
  have hτΩ : ∀ c, τ ≠ .Om c := fun c e => by
    subst e
    rcases h1 with e' | h'
    · cases e'
    · exact absurd (lt_oneY hτF h') (by intro e; cases e)
  have hp0 : p ≠ .zero := by
    rcases Sp.hn with ⟨m', a, e'⟩ | ⟨s, q'', a, e'⟩ <;> rw [e'] <;> simp
  rw [M.hf]
  cases hsp : splitGtD p (info (mi τ)).sums with
  | none => exact absurd hsp (idx_split_some Sp hτF hτp C'.hμF hpτ h1)
  | some q =>
    obtain ⟨pre, R, r⟩ := q
    obtain ⟨rfl, hpR, hR1, rest, hsum⟩ := idx_split Sp hsp
    simp only
    intro hI
    have hmF := C'.hμF
    have hRm : R ∈ summands (mi τ) := by rw [hsum]; exact List.mem_append_right _ List.mem_cons_self
    have hRF := hmF.of_mem_subs (mem_subs_of_mem_summands hRm)
    have hRp := nfl_principal (nfl_summands hmF) R hRm
    obtain ⟨h0, h1'⟩ := dom_ne_of_principal hRF hRp hR1
    have hμ1 : mi τ ≠ .one := by
      intro e
      rw [e] at hRm
      simp only [summands, List.mem_singleton] at hRm
      exact hR1 hRm
    have G : IdxG τ (pred Y) (mi τ) p pre rest R :=
      { hv := C'.hv, hYF := C'.hYF, hYC := C'.hYC, hτY := C'.hτY, hμF := hmF, hsum, hμY := C'.hμY hμ1
        hμm := C'.hμm, hμ1 := C'.hμ1, hμ2 := C'.hμ2, hPF := hpF, hPR := hpR, hPτ := hpτ }
    have o := idx_app C' G (M.hS R hRm hR1) h0 h1' hRp (M.hs R hRm hR1).1 (M.hs R hRm hR1).2 Sp.ns
      (Sp.hπ ht) (fun g d h => Sp.ad h) (fun _ => Sp.self_fr hpτ)
    have hpy : ∀ y, InSeq (.app π (.idx τ (pred Y)) pre R (info R).seq p .zero) y → Lt p y := fun y hy => by
      obtain ⟨P', x, -, -, -, -, -, -, -, hPy, -, -⟩ := o.form y hy
      exact hPy hp0
    have hrest : ∀ u, u ∈ rest → Lt u τ := fun u hu => by
      obtain ⟨L, rest', hys, hL, -, -, hhd'⟩ := splitGtD_spec hsp
      have hsum₂ : summands (mi τ) = pre ++ R :: rest'.map Prod.fst := by
        rw [← info_sums_fst, hys, List.map_append, hL, List.map_cons]
      have e : rest = rest'.map Prod.fst := by
        have := hsum.symm.trans hsum₂
        simpa using this
      have hN := hsum ▸ nfl_summands hmF
      have hNr : NFL rest := nfl_append_right (show NFL ((pre ++ [R]) ++ rest) by simpa using hN)
      rw [e] at hu hNr
      cases hr : rest' with
      | nil =>
        rw [hr] at hu
        cases hu
      | cons q tl =>
        rw [hr] at hu hNr
        simp only [List.map_cons] at hu hNr
        have hq := hhd' q tl hr
        have hqF := (hNr.1 q.1 List.mem_cons_self).1
        have huF := (hNr.1 u hu).1
        have hqp : Le q.1 p := le_of_not_ltY hpF hqF fun h => by
          rw [ltB_iff.mpr h] at hq
          cases hq
        exact lt_of_le_of_ltY huF hpF hτF (le_transY huF hqF hpF (le_head_mem hNr hu) hqp) hpτ
    refine cof_idx_app C' G (M.hS R hRm hR1) (hSmC R hRm hR1) h0 h1' hRp (M.hs R hRm hR1).1
      (M.hs R hRm hR1).2 Sp.ns (Sp.hπ ht) (fun g d h => Sp.ad h) (fun _ => Sp.self_fr hpτ) hτΩ hτfr hI
      (fun x y hy hx hxt _ htk hkτ _ => ?_) fun x y hy hx hxt hpar z a e haX => ?_
    · have hyF := seqI_wnf hI hy
      rcases hLow x hx hxt htk hkτ with ⟨p', e, h⟩ | h
      · cases e
        exact lt_of_le_of_ltY hx hpF hyF h (hpy y hy)
      · exact h.lt ht hx hyF (seqI_gp hI rfl hy)
    · subst e
      have hyF := seqI_wnf hI hy
      have hG := seqI_gp hI rfl hy
      rcases hCls z a hx hxt with haY | ⟨rfl, hzμ⟩ | hsub
      · rcases le_of_lt_succT hx.psi.aF (wnf_pred hY) (by rw [succT_pred hY hs]; exact haY) with e' | h'
        · subst e'
          by_cases hzT : Lt z (oadd (ofSummands pre) R)
          · exact Or.inr (Or.inl ⟨rfl, hzT⟩)
          · refine Or.inr (Or.inr ?_)
            have hfa : ∀ f, f ∈ fr τ (pred Y) → Lt f (.Psi .zero τ Y) := fun f hf => by
              obtain ⟨u, hu, hfu⟩ := (mem_fr_iff (wnf_pred hY)).mp hf
              refine FWOrder.k2 C.hw0 f ((mem_fr_iff hY).mpr ⟨u, ?_, hfu⟩)
              rw [← succT_pred hY hs, summands_succT]
              exact List.mem_append_left _ hu
            have h2 := idx_tail_lt C hsum hrest hx (pred_lt hY hs) hfa hzT
            exact lt_transY hx C.hw0 hyF h2 (lt_of_le_of_ltY C.hw0 hpF hyF hyp (hpy y hy))
        · exact Or.inl h'
      · exact Or.inr (Or.inr (lt_of_le_seed ht hpF hx hyF (hpy y hy) hG (hN2 z hx hxt hzμ)))
      · exact Or.inr (Or.inr (hsub.lt ht hx hyF hG))


/-- 段の引数の加数の共終数が `τ` 未満なら `π` 未満 -/
theorem sigma_low {π X τ Y μ R : Tm} {T : Tm → Tm → Prop} (C : MCtx π X τ Y μ T) (hRm : R ∈ summands Y)
    (hRI : SeqI R (info R).seq) : ∀ σ, (info R).seq.dom = .big σ → Lt σ τ → Lt σ π := fun σ hd hστ => by
  have h' := hRI
  unfold SeqI at h'
  rw [hd] at h'
  have hU := h'.1.1
  exact C.ltT σ hU.hσF hστ fun g d hT => by
    obtain ⟨hg, hd2, -, -, -, h3, -, -⟩ := C.hT g d hT
    exact hU.hσC g d hg hd2 (inC_of_mem_summands C.hYF h3 hRm)

/-- 族への移行の `LoT`：段の節点で引数が `Y` 未満のものが種以下なら -/
theorem lot_level {π X τ Y μ p : Tm} {T : Tm → Tm → Prop} (C : MCtx π X τ Y μ T)
    (hLow : LowC (.Psi .zero π X) τ (some p)) (hCls : ClsC (.Psi .zero π X) τ Y μ)
    (hN2 : N2C (.Psi .zero π X) τ Y μ p)
    (hA : ∀ s a, WNF (.Psi s τ a) → Lt (.Psi s τ a) (.Psi .zero π X) → Lt a Y →
      Le (.Psi s τ a) p ∨ SubLe (.Psi .zero π X) (.Psi s τ a)) : LoT (.Psi .zero π X) τ p := by
  intro x a hx hxt harg htk hkτ
  rcases hkτ with e | hlt
  · cases x with
    | Psi s k a' =>
      have e' : k = τ := e
      subst e'
      rcases hCls s a' hx hxt with haY | ⟨rfl, hsμ⟩ | hsub
      · exact hA s a' hx hxt haY
      · exact hN2 s hx hxt hsμ
      · exact Or.inr hsub
    | Xi j b => exact absurd e.symm (IsTgt.ne_K C.hτt j)
    | _ => cases harg
  · rcases hLow x hx hxt htk hlt with ⟨p', e, h⟩ | h
    · cases e
      exact Or.inl h
    · exact Or.inr h

/-- 塞がった挿入の共終性 -/
theorem dead_cof {π X τ Y μ p : Tm} {T : Tm → Tm → Prop} {τf : Fam}
    (C : MCtx π X τ Y μ T) (M : MPar π X τ τf)
    (hS : ∀ u, u ∈ summands Y → u ≠ .one → SeqI u (info u).seq)
    (hSC : ∀ u, u ∈ summands Y → u ≠ .one → SeqC u (info u).seq)
    (hSmC : ∀ u, u ∈ summands (mi τ) → u ≠ .one → SeqC u (info u).seq)
    (hY0 : Y ≠ .zero) (Sp : SeedP π X p) (hyp : Le (.Psi .zero τ Y) p)
    (hpre : ∀ pre R, summands Y = pre ++ [R] → Le p (ofSummands pre))
    (hτfr : ∀ u, u ∈ fr τ τ → u ∈ fr π π)
    (hLow : LowC (.Psi .zero π X) τ (some p)) (hCls : ClsC (.Psi .zero π X) τ Y μ)
    (hN2 : N2C (.Psi .zero π X) τ Y μ p)
    (hY2 : idxOK τ p = false → ∀ s a, WNF (.Psi s τ a) → Lt (.Psi s τ a) (.Psi .zero π X) → Lt a Y →
      Le (.Psi s τ a) p ∨ SubLe (.Psi .zero π X) (.Psi s τ a))
    (hfam : LoT (.Psi .zero π X) τ p → SeqI (.Psi .zero π X) (famSeq τf π (some p)) →
      SeqC (.Psi .zero π X) (famSeq τf π (some p))) :
    SeqI (.Psi .zero π X) (deadSeqM τ τf π p Y (info Y).sums) →
      SeqC (.Psi .zero π X) (deadSeqM τ τf π p Y (info Y).sums) := by
  have ht := C.ht
  have hY := C.hYF
  have hτF := C.hτF
  have hpF := Sp.hF
  have hpπ := Sp.hπ ht
  have hpτ : Lt p τ := lt_of_lt_of_leY hpF C.hπF hτF hpπ C.hle
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
      have hYK := idx_tgt_le C hpF hyp (ltB_iff.mp hc.1)
      by_cases hv : validR τ (pred Y) = true
      · have e : (leB τ (mOfT τ) && leB τ (pred Y) && validR τ (pred Y)) = true := by
          rw [mOfT_tgt C.hτt, leB_iff.mpr (ne_gt_of_le hYK.1), leB_iff.mpr (ne_gt_of_le (hYK.2 hv)), hv]
          rfl
        rw [ite_eq_left e]
        exact idxm_cof C M hSmC Sp hs hYK.1 hv hτfr hLow hCls hN2 hyp
      · have e : ¬ (leB τ (mOfT τ) && leB τ (pred Y) && validR τ (pred Y)) = true := fun h => by
          simp only [Bool.and_eq_true] at h
          exact hv h.2
        rw [ite_eq_right e]
        refine hfam (lot_level C hLow hCls hN2 fun s a hx _ haY => ?_)
        exfalso
        cases hr : argR? τ with
        | none =>
          unfold validR at hv
          rw [hr] at hv
          exact hv rfl
        | some r =>
          have hrF := wnf_of_argR hτF hr
          have hn : ¬ Lt r (pred Y) := fun h' => hv (by
            unfold validR
            rw [hr]
            exact ltB_iff.mpr h')
          have h3 : Le r (pred Y) := le_of_lt_succT hrF (wnf_pred hY) (by
            rw [succT_pred hY hs]
            exact C.hτY r hr)
          have h4 : r = pred Y := h3.resolve_right hn
          have ha' : Le a (pred Y) :=
            le_of_lt_succT hx.psi.aF (wnf_pred hY) (by rw [succT_pred hY hs]; exact haY)
          rw [← h4] at ha'
          exact not_lt_of_leY hx.psi.aF hrF ha' (arg_lt_of_psi hx hr)
    · rename_i hone
      have hsum := summands_pre_last hY0
      have hlast : lastS (info Y).sums = (info (lastT (info Y).sums)).seq := lastS_coh (coh_sums Y)
      obtain ⟨pre, hpr⟩ : ∃ pre, pre = preT (info Y).sums := ⟨_, rfl⟩
      obtain ⟨R, hR⟩ : ∃ R, R = lastT (info Y).sums := ⟨_, rfl⟩
      rw [← hpr, ← hR] at hsum
      rw [← hR] at hlast
      rw [← hpr, ← hR, hlast]
      have hne1 : ¬ isSucc Y = true := fun h => by
        apply hone
        rw [lastS_dom hY hY0]
        exact (dom_eq_one_iff hY).mpr h
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
      have hRC := hSC R hRm hRne
      obtain ⟨hx0F, hx0R⟩ := first_good hRI h0 h1
      have hsum' := summands_sc (rest₀ := []) hsum
      have S0 : SeedHyp τ (sc Y) .zero R := seed_zero C.hτt.ne_zero hR0
      have hI : IdxHyp p τ (sc Y) := ⟨hpF, hpτ, ltB_iff.mp hc.1, hc.2⟩
      cases hm3 : mkApp π (.mahlo p τ) pre R (info R).seq .zero .zero with
      | some s =>
        have pk := pack_mkApp (Or.inr rfl : GenPsi (.mahlo p τ) p τ) C.hv hsum' S0 hRne hx0F hx0R hm3 hI
          (hpre pre R hsum) hRI h0 h1 hRp C.hπF C.hle
          (fun σ hσt _ hB hστ hσπ => C.low Sp hyp hRm hB hσt hστ hσπ) (C.τK)
          fun _ hd => dom_ne_succK hd
        simp only
        intro hI'
        refine cof_app_lvl (Or.inr rfl : GenPsi (.mahlo p τ) p τ) C.hv hsum' S0 hRne hx0F hx0R hm3 hI
          (hpre pre R hsum) hRI hRC h0 h1 hRp (sigma_low C hRm hRI) C.τK (fun _ hd => dom_ne_succK hd) ht
          C.hle hτfr pk hI' (fun x y hy hx hxt _ htk hkτ _ => ?_) fun x y hy hx hxt _ z a e _ haT => ?_
        · have hyF := seqI_wnf hI' hy
          rcases hLow x hx hxt htk hkτ with ⟨p', e, h⟩ | h
          · cases e
            exact lt_of_le_of_ltY hx hpF hyF h (pk.idx (Sp.self_fr hpτ) hy)
          · exact h.lt ht hx hyF (seqI_gp hI' rfl hy)
        · subst e
          have hyF := seqI_wnf hI' hy
          have hG := seqI_gp hI' rfl hy
          rcases hCls z a hx hxt with haY | ⟨rfl, hzμ⟩ | hsub
          · exact absurd (by rwa [eq_oadd_of_sum hY hsum] at haY) haT
          · exact lt_of_le_seed ht hpF hx hyF (pk.idx (Sp.self_fr hpτ) hy) hG (hN2 z hx hxt hzμ)
          · exact hsub.lt ht hx hyF hG
      | none => exact absurd rfl (mkApp_none rfl C.hw0 hsum (zero_lt hR0) hm3).2
  · rw [ite_eq_right hc]
    exact hfam (lot_level C hLow hCls hN2 (hY2 (by simpa using hc)))

/-- 後者の崩壊への種の挿入の共終性 -/
theorem insert_cof {π X τ Y μ p : Tm} {T : Tm → Tm → Prop} {τf : Fam}
    (C : MCtx π X τ Y μ T) (M : MPar π X τ τf)
    (hS : ∀ u, u ∈ summands Y → u ≠ .one → SeqI u (info u).seq)
    (hSC : ∀ u, u ∈ summands Y → u ≠ .one → SeqC u (info u).seq)
    (hSmC : ∀ u, u ∈ summands (mi τ) → u ≠ .one → SeqC u (info u).seq)
    (Sp : SeedP π X p) (hyp : Le (.Psi .zero τ Y) p) (hτfr : ∀ u, u ∈ fr τ τ → u ∈ fr π π)
    (hLow : LowC (.Psi .zero π X) τ (some p)) (hCls : ClsC (.Psi .zero π X) τ Y μ)
    (hN2 : N2C (.Psi .zero π X) τ Y μ p)
    (hfam : LoT (.Psi .zero π X) τ p → SeqI (.Psi .zero π X) (famSeq τf π (some p)) →
      SeqC (.Psi .zero π X) (famSeq τf π (some p))) :
    SeqI (.Psi .zero π X) (insertAtM τ τf π p Y (info Y).sums) →
      SeqC (.Psi .zero π X) (insertAtM τ τf π p Y (info Y).sums) := by
  have hY0' : ∀ {R : Tm}, R ∈ summands Y → Y ≠ .zero := fun hRm e => by
    rw [e] at hRm
    cases hRm
  have ht := C.ht
  have hY := C.hYF
  have hτF := C.hτF
  have hpF := Sp.hF
  have hpπ := Sp.hπ ht
  have hpτ : Lt p τ := lt_of_lt_of_leY hpF C.hπF hτF hpπ C.hle
  have hw := C.hw0
  unfold insertAtM
  cases hsp : splitGtD p (info Y).sums with
  | none =>
    -- `Y` の加数は全て `p` 以下：`Y < w₀`
    refine hfam (lot_level C hLow hCls hN2 fun s a hx _ haY => Or.inl (Or.inr ?_))
    have hYw : Lt Y (.Psi .zero τ Y) := by
      cases hsY : summands Y with
      | nil =>
        rw [eq_zero_of_summands_nil hsY]
        exact zero_lt (by intro e; cases e)
      | cons u l =>
        have hum : u ∈ summands Y := by rw [hsY]; exact List.mem_cons_self
        have huN := (nfl_summands hY).1 u hum
        have hup : ¬ Lt p u := by
          intro h
          have e' : (info Y).sums.map Prod.fst = u :: l := by
            rw [info_sums_fst]
            exact hsY
          cases hxs : (info Y).sums with
          | nil =>
            rw [hxs] at e'
            cases e'
          | cons q ys =>
            rw [hxs] at e' hsp
            simp only [List.map_cons, List.cons.injEq] at e'
            have h0' := splitGtD_none_head hsp
            rw [e'.1, ltB_iff.mpr h] at h0'
            cases h0'
        have huτ : Lt u τ := lt_of_le_of_ltY huN.1 hpF hτF (le_of_not_ltY hpF huN.1 hup) hpτ
        exact lt_prin_of_head hsY rfl huN.2 (summand_lt_w0 C hum huτ)
    have hP := hx.psi
    refine lt_of_lt_of_leY hx hw hpF (lt_w0 C hx haY fun f hf => ?_) hyp
    have haw : Lt a (.Psi .zero τ Y) := lt_transY hP.aF hY hw haY hYw
    simp only [parF, List.mem_append] at hf
    rcases hf with (hf | hf) | hf
    · exact lt_of_le_of_ltY (hP.aF.of_mem_subs (fr_spec hf).1) hP.aF hw (fr_leY hτF hP.aF hf) haw
    · exact lt_of_le_of_ltY (hP.xiF.of_mem_subs (fr_spec hf).1) hP.xiF hw (fr_leY hτF hP.xiF hf)
        (lt_of_le_of_ltY hP.xiF hP.aF hw (le_of_ne_gtY hP.xiF hP.aF hP.le) haw)
    · exact FWOrder.k2t hw f hf
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
      exact Sp.ne_one (lt_oneY hpF hpR ▸ absurd (lt_oneY hpF hpR) (by
        rcases Sp.hn with ⟨m, a, e'⟩ | ⟨s, q, a, e'⟩ <;> rw [e'] <;> simp))
    have hRF := hY.of_mem_subs (mem_subs_of_mem_summands hRm)
    have hRp := nfl_principal (nfl_summands hY) R hRm
    obtain ⟨h0, h1⟩ := dom_ne_of_principal hRF hRp hRne
    have hRI := hS R hRm hRne
    have hRC := hSC R hRm hRne
    obtain ⟨hx0F, hx0R⟩ := first_good hRI h0 h1
    have hsum' := summands_sc hsumY
    have S' : SeedHyp τ (sc Y) p R := ⟨hpF, hpR, hpτ, Sp.ns⟩
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
    have hrestp : ∀ u, u ∈ rest.map Prod.fst → Le u p := fun u hu => by
      have hN := hsumY ▸ nfl_summands hY
      have hNr : NFL (rest.map Prod.fst) :=
        nfl_append_right (show NFL ((pre ++ [R]) ++ rest.map Prod.fst) by simpa using hN)
      cases hr : rest.map Prod.fst with
      | nil =>
        rw [hr] at hu
        cases hu
      | cons q tl =>
        rw [hr] at hu hNr
        have hqF := (hNr.1 q List.mem_cons_self).1
        exact le_transY (hNr.1 u hu).1 hqF hpF (le_head_mem hNr hu) (le_of_not_ltY hpF hqF (hhd' q tl hr))
    have htail : ∀ s a, WNF (.Psi s τ a) → Lt a Y → ¬ Lt a (oadd (ofSummands pre) R) → idxOK τ p = false →
        Lt (.Psi s τ a) (.Psi .zero τ Y) := fun s a hx haY haT hidx =>
      insert_tail_lt C hsumY hrestp hpF hpτ (mi_le_of_idx C.hτt hτF hpF hpτ hidx) hx haY haT
    dsimp only
    by_cases hC : (!ltB p (lastT (info Y).sums) && idxOK τ p) = true
    · rw [ite_eq_left hC]
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hC
      refine dead_cof C M hS hSC hSmC (hY0' hRm) Sp hyp (fun pre' R' e => ?_) hτfr hLow hCls hN2
        (fun h => by rw [hC.2] at h; cases h) hfam
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
      exact Or.inr (lt_of_lt_of_leY hpF hRF (wnf_ofSummands hpN) hpR (le_ofSummands_of_mem hpN hm2))
    rw [ite_eq_right hC]
    cases hm : mkApp π (.psi0 τ) pre R (info R).seq p .zero with
    | some s =>
      have pk := pack_mkApp (genPsi0 τ) C.hv hsum' S' hRne hx0F hx0R hm (IdxHyp.zero C.hv) (zero_le _) hRI
        h0 h1 hRp C.hπF C.hle (fun σ hσt _ hB hστ hσπ => C.low Sp hyp hRm hB hσt hστ hσπ) (C.τK)
        fun _ hd => dom_ne_succK hd
      simp only
      intro hI
      refine cof_app_lvl (genPsi0 τ) C.hv hsum' S' hRne hx0F hx0R hm (IdxHyp.zero C.hv) (zero_le _) hRI hRC
        h0 h1 hRp (sigma_low C hRm hRI) C.τK (fun _ hd => dom_ne_succK hd) ht C.hle hτfr pk hI
        (fun x y hy hx hxt _ htk hkτ _ => ?_) fun x y hy hx hxt _ z a e _ haT => ?_
      · have hyF := seqI_wnf hI hy
        rcases hLow x hx hxt htk hkτ with ⟨p', e, h⟩ | h
        · cases e
          exact lt_of_le_of_ltY hx hpF hyF h (pk.seed (Sp.self_fr hpτ) hy)
        · exact h.lt ht hx hyF (seqI_gp hI rfl hy)
      · subst e
        have hyF := seqI_wnf hI hy
        have hG := seqI_gp hI rfl hy
        have hpy := pk.seed (Sp.self_fr hpτ) hy
        rcases hCls z a hx hxt with haY | ⟨rfl, hzμ⟩ | hsub
        · have hidx : idxOK τ p = false := by
            cases e' : idxOK τ p with
            | false => rfl
            | true =>
              exfalso
              have hpL : Lt p (lastT (info Y).sums) := by
                have h3 : ltB p (lastT (info Y).sums) = true := by
                  cases e'' : ltB p (lastT (info Y).sums) with
                  | true => rfl
                  | false =>
                    exfalso
                    apply hC
                    rw [e'', e']
                    rfl
                exact ltB_iff.mp h3
              have hrest : rest.map Prod.fst = [] := Classical.byContradiction fun hne => by
                have h4 := (rest_eq_seed hY (summands_pre_last (hY0' hRm)) hsumY hpF (Or.inr hpL) hhd' hne).1
                rw [h4] at hpL
                exact Lt.irrefl _ hpL
              apply haT
              have hYe : Y = oadd (ofSummands pre) R := eq_oadd_of_sum hY (by rw [hsumY, hrest])
              rwa [hYe] at haY
          exact lt_transY hx hw hyF (htail z a hx haY haT hidx) (lt_of_le_of_ltY hw hpF hyF hyp hpy)
        · exact lt_of_le_seed ht hpF hx hyF hpy hG (hN2 z hx hxt hzμ)
        · exact hsub.lt ht hx hyF hG
    | none =>
      simp only
      have hnone := mkApp_none rfl C.hw0 hsumY hpR hm
      obtain ⟨q, hq, hTq⟩ := mkApp_none_le rfl C.hw0 hsumY hpR hm
      refine dead_cof C M hS hSC hSmC (hY0' hRm) Sp hyp (fun pre' R' e => ?_) hτfr hLow hCls hN2
        (fun hidx s a hx _ haY => ?_) hfam
      · have hm2 : R ∈ pre' := mem_pre_of_split (by rw [← e, hsumY]) hnone.2
        have hN := nfl_summands hY
        rw [e] at hN
        have hpN := nfl_append_left hN
        exact Or.inr (lt_of_lt_of_leY hpF hRF (wnf_ofSummands hpN) hpR (le_ofSummands_of_mem hpN hm2))
      · have hqF := wnf_of_argR hτF hq
        have hTF : WNF (oadd (ofSummands pre) R) :=
          wnf_oadd (wnf_ofSummands (nfl_append_left (hsumY ▸ nfl_summands hY : NFL (pre ++ R :: rest.map Prod.fst))))
            hRF
        have haT : ¬ Lt a (oadd (ofSummands pre) R) := fun h' =>
          Lt.asymmY hx.psi.aF hTF h' (lt_of_le_of_ltY hTF hqF hx.psi.aF hTq (arg_lt_of_psi hx hq))
        exact Or.inl (Or.inr (lt_of_lt_of_leY hx hw hpF (htail s a hx haY haT hidx) hyp))


/-! ### `mahloSeq` -/

/-- 和の残りの前線：`z = L₁ ⊕ L'`（`L' < L₂`）で、`L₁` の加数の前線と `L₂` の加数が `w` 未満なら `z` の前線は `w` 未満 -/
theorem tail_fr_lt {τ w z : Tm} {L₁ L₂ : List Tm} (hτF : WNF τ) (hw : WNF w) (hwp : isPrincipal w = true)
    (hN : NFL (L₁ ++ L₂)) (hz : WNF z) (hzlt : Lt z (ofSummands (L₁ ++ L₂))) (hge : ¬ Lt z (ofSummands L₁))
    (hL₁ : ∀ f u, u ∈ L₁ → f ∈ fr τ u → Lt f w) (hL₂ : ∀ u, u ∈ L₂ → Lt u w) :
    ∀ f, f ∈ fr τ z → Lt f w := by
  obtain ⟨L', hzs, hL'⟩ := lt_sum_split hN hz hzlt hge
  have hL₂N := nfl_append_right hN
  have hL'N : NFL L' := by
    have h := nfl_summands hz
    rw [hzs] at h
    exact nfl_append_right h
  intro f hf
  obtain ⟨u, hu, hfu⟩ := (mem_fr_iff hz).mp hf
  rw [hzs] at hu
  rcases List.mem_append.mp hu with hu | hu
  · exact hL₁ f u hu hfu
  · have hne : L₂ ≠ [] := by
      intro e
      rw [e] at hL'
      cases L' with
      | nil => cases hu
      | cons _ _ => simp [cmpList] at hL'
    obtain ⟨h₂, l₂, e₂⟩ := List.exists_cons_of_ne_nil hne
    have hh₂ : h₂ ∈ L₂ := by rw [e₂]; exact List.mem_cons_self
    have hL₂w : Lt (ofSummands L₂) w := by
      refine lt_prin_of_head (h := h₂) (r := l₂) ?_ hwp (hL₂N.1 h₂ hh₂).2 (hL₂ h₂ hh₂)
      rw [summands_ofSummands _ (nfl_principal hL₂N), e₂]
    have h1 : Lt (ofSummands L') (ofSummands L₂) := by
      unfold Lt
      rw [cmp_eq, summands_ofSummands _ (nfl_principal hL'N), summands_ofSummands _ (nfl_principal hL₂N)]
      exact hL'
    have hL'w := lt_transY (wnf_ofSummands hL'N) (wnf_ofSummands hL₂N) hw h1 hL₂w
    have huF := (hL'N.1 u hu).1
    have hfF := huF.of_mem_subs (fr_spec hfu).1
    exact lt_of_le_of_ltY hfF (wnf_ofSummands hL'N) hw
      (le_transY hfF huF (wnf_ofSummands hL'N) (fr_leY hτF huF hfu) (le_ofSummands_of_mem hL'N hu)) hL'w

/-- 同じ目標・同じ引数で添字が小さく、添字の前線が下にあれば小さい -/
theorem le_idx_of_fr {z ζ τ Y : Tm} (hx : WNF (.Psi z τ Y)) (hy : WNF (.Psi ζ τ Y)) (hzζ : Le z ζ)
    (hfr : ∀ f, f ∈ fr τ z → Lt f (.Psi ζ τ Y)) : Le (.Psi z τ Y) (.Psi ζ τ Y) := by
  rcases hzζ with rfl | h
  · exact Or.inl rfl
  · have hP := hx.psi
    exact Or.inr (lt_same_arg hx hy h (inC_of_fr_lt hP.xiF hP.piF hy hP.aF hP.aF hP.Cxi
      (Or.inr (lt_psi_targetY hy)) (Or.inl rfl) hfr))

/-- 種が大きくなっても下の段の仮定は保たれる -/
theorem LowC.mono {t τ p' : Tm} {P : Option Tm} (h : LowC t τ P) (hp : ∀ p, P = some p → Le p p')
    (hx : ∀ {x p : Tm}, Le x p → Le p p' → Le x p') : LowC t τ (some p') := fun x hxF hxt htk hkτ => by
  rcases h x hxF hxt htk hkτ with ⟨p, e, h'⟩ | h'
  · exact Or.inl ⟨p', rfl, hx h' (hp p e)⟩
  · exact Or.inr h'

/-- 添字の閉包の葉（`mahlo_out` の出力）の共終性 -/
theorem idx_leaf_cof {π X τ Y μ : Tm} {T : Tm → Tm → Prop} (C : MCtx π X τ Y μ T)
    (hSμ : ∀ u, u ∈ summands μ → u ≠ .one → SeqI u (info u).seq)
    (hμs : ∀ u, u ∈ summands μ → u ≠ .one → u ∈ subs (.Psi .zero π X) ∧ u.size < π.size)
    (hSμC : ∀ u, u ∈ summands μ → u ≠ .one → SeqC u (info u).seq)
    (P' : Tm) (pre rest : List Tm) (R : Tm) (hsum : summands μ = pre ++ R :: rest) (hR1 : R ≠ .one)
    (hPR : Lt P' R) (hSP : P' ≠ .zero → SeedP π X P') (hPF : WNF P')
    (hτΩ : ∀ c, τ ≠ .Om c) (hτfr : ∀ u, u ∈ fr τ τ → u ∈ fr π π)
    (hlow : ∀ x y, InSeq (.app π (.idx τ Y) pre R (info R).seq P' .zero) y →
      (P' ≠ .zero → Lt P' y) → Le (SeqD.app π (.idx τ Y) pre R (info R).seq P' .zero).first y →
      WNF x → Lt x (.Psi .zero π X) → Lt (.Psi .zero π X) (tgtN x) → Lt (tgtN x) τ → Lt x y)
    (hcls : ∀ x y, InSeq (.app π (.idx τ Y) pre R (info R).seq P' .zero) y →
      (P' ≠ .zero → Lt P' y) → Le (SeqD.app π (.idx τ Y) pre R (info R).seq P' .zero).first y →
      WNF x → Lt x (.Psi .zero π X) → ∀ z a, x = .Psi z τ a →
        Lt a Y ∨ (a = Y ∧ Lt z (oadd (ofSummands pre) R)) ∨ Lt x y) :
    SeqI (.Psi .zero π X) (.app π (.idx τ Y) pre R (info R).seq P' .zero) →
      SeqC (.Psi .zero π X) (.app π (.idx τ Y) pre R (info R).seq P' .zero) := by
  intro hI
  have ht := C.ht
  have hY := C.hYF
  have hτF := C.hτF
  have hπF := C.hπF
  have hμF := C.hμF
  have o := mahlo_out C hSμ hμs P' pre rest R hsum hR1 hPR hSP hPF
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
  have hPy : ∀ y, InSeq (.app π (.idx τ Y) pre R (info R).seq P' .zero) y → P' ≠ .zero → Lt P' y :=
    fun y hy => by
      obtain ⟨P'', x, -, -, -, -, -, -, -, hPy, -, -⟩ := o.form y hy
      exact hPy
  have hfy : ∀ y, InSeq (.app π (.idx τ Y) pre R (info R).seq P' .zero) y →
      Le (SeqD.app π (.idx τ Y) pre R (info R).seq P' .zero).first y := fun y hy => by
    obtain ⟨P'', x, -, -, -, -, -, -, hle, -, -, -⟩ := o.form y hy
    exact hle
  exact cof_idx_app C G (hSμ R hRm hR1) (hSμC R hRm hR1) h0 h1 hRp (hμs R hRm hR1).1 (hμs R hRm hR1).2 hPs
    hPπ (fun g d h => by
      rcases hP0 with rfl | h'
      · exact inC_zero _ _
      · exact (hSP h').ad h)
    (fun h => (hSP h).self_fr (hpτ (hSP h))) hτΩ hτfr hI
    (fun x y hy hx hxt _ htk hkτ _ => hlow x y hy (hPy y hy) (hfy y hy) hx hxt htk hkτ)
    fun x y hy hx hxt _ z a e _ => hcls x y hy (hPy y hy) (hfy y hy) hx hxt z a e


/-- `splitPosD` が `none` なら先頭は閾値未満 -/
theorem splitPosD_none_head {th : Tm} {q : Tm × SeqD} {ys : DL} (h : splitPosD th (q :: ys) = none) :
    leB th q.1 = false := by
  unfold splitPosD at h
  cases e : leB th q.1 with
  | false => rfl
  | true =>
    rw [List.takeWhile_cons, e] at h
    simp only [↓reduceIte] at h
    cases hT : (q :: List.takeWhile (fun s => leB th s.fst) ys).getLast? with
    | none => simp at hT
    | some v =>
      rw [hT] at h
      obtain ⟨R, r⟩ := v
      simp at h

/-- `splitPosD` の分割：残りの先頭は閾値未満 -/
theorem splitPosD_rest {th : Tm} {ys : DL} {pre : List Tm} {R : Tm} {r : SeqD}
    (h : splitPosD th ys = some (pre, R, r)) :
    ∃ L rest, ys = L ++ (R, r) :: rest ∧ L.map Prod.fst = pre ∧ leB th R = true ∧
      ∀ q tl, rest = q :: tl → leB th q.1 = false := by
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
    refine ⟨L, ys.dropWhile (fun s => leB th s.1), ?_, ?_, ?_, fun q tl hq => ?_⟩
    · have := List.takeWhile_append_dropWhile (p := fun s => leB th s.1) (l := ys)
      rw [hT, List.append_assoc] at this
      exact this.symm
    · rw [← h1, List.dropLast_concat]
    · have : (R', r') ∈ ys.takeWhile (fun s => leB th s.1) := by rw [hT]; simp
      exact mem_takeWhile_imp' (p := fun s : Tm × SeqD => leB th s.1) this
    · have hne : ys.dropWhile (fun s => leB th s.1) ≠ [] := by rw [hq]; simp
      have := List.head_dropWhile_not (fun s : Tm × SeqD => leB th s.1) hne
      simp only [hq, List.head_cons] at this
      exact this

/-- 種の上界の取り替え -/
theorem LowC.mono' {t τ p' : Tm} {P : Option Tm} (h : LowC t τ P) (hp'F : WNF p')
    (hp : ∀ p, P = some p → WNF p ∧ Le p p') : LowC t τ (some p') := fun x hxF hxt htk hkτ => by
  rcases h x hxF hxt htk hkτ with ⟨p, e, h'⟩ | h'
  · obtain ⟨hpF, hpp⟩ := hp p e
    exact Or.inl ⟨p', rfl, le_transY hxF hpF hp'F h' hpp⟩
  · exact Or.inr h'

/-- 閾値未満の先頭を持つ並びの元は閾値未満 -/
theorem all_lt_of_head {th : Tm} {l : List Tm} (hthF : WNF th) (hN : NFL l)
    (hh : ∀ q tl, l = q :: tl → ¬ Le th q) : ∀ u, u ∈ l → Lt u th := by
  intro u hu
  cases hl : l with
  | nil =>
    rw [hl] at hu
    cases hu
  | cons q tl =>
    rw [hl] at hu hN
    have hqF := (hN.1 q List.mem_cons_self).1
    have huF := (hN.1 u hu).1
    have hq : Lt q th := by
      rcases triY hqF hthF with h' | h' | h'
      · exact h'
      · exact absurd (Or.inl h'.symm) (hh q tl hl)
      · exact absurd (Or.inr h') (hh q tl hl)
    exact lt_of_le_of_ltY huF hqF hthF (le_head_mem hN hu) hq

/-- `mahloSeq` の共終性 -/
theorem mahlo_cof {π X τ Y μ : Tm} {T : Tm → Tm → Prop} {τf : Fam} {P : Option Tm}
    (C : MCtx π X τ Y μ T) (M : MPar π X τ τf) (hμ0 : μ ≠ .zero)
    (hSY : ∀ u, u ∈ summands Y → u ≠ .one → SeqI u (info u).seq)
    (hSμ : ∀ u, u ∈ summands μ → u ≠ .one → SeqI u (info u).seq)
    (hμs : ∀ u, u ∈ summands μ → u ≠ .one → u ∈ subs (.Psi .zero π X) ∧ u.size < π.size)
    (hSYC : ∀ u, u ∈ summands Y → u ≠ .one → SeqC u (info u).seq)
    (hSμC : ∀ u, u ∈ summands μ → u ≠ .one → SeqC u (info u).seq)
    (hSmC : ∀ u, u ∈ summands (mi τ) → u ≠ .one → SeqC u (info u).seq)
    (hP : ∀ p, P = some p → SeedP π X p)
    (hne : ∀ p, P = some p → ¬ isSucc μ = true → μ ≠ .one →
      IdxOut π X τ Y μ .zero (preT (info μ).sums) (lastT (info μ).sums) (s0Of π τ Y μ) →
      (s0Of π τ Y μ).first ≠ p)
    (hτfr : ∀ u, u ∈ fr τ τ → u ∈ fr π π)
    (hLow : LowC (.Psi .zero π X) τ P) (hCls : ClsC (.Psi .zero π X) τ Y μ)
    (hW : ∀ p, P = some p → ¬ isSucc μ = true → μ ≠ .one → Lt (s0Of π τ Y μ).first p →
      ∀ L₁ L₂, summands μ = L₁ ++ L₂ → (∀ u, u ∈ L₂ → Le u p) →
      ∀ z, WNF (.Psi z τ Y) → Lt (.Psi z τ Y) (.Psi .zero π X) → Lt z μ → ¬ Lt z (ofSummands L₁) →
      Le (.Psi z τ Y) p ∨ SubLe (.Psi .zero π X) (.Psi z τ Y))
    (hfam : ∀ p', SeedP π X p' → Le (.Psi .zero τ Y) p' → LoT (.Psi .zero π X) τ p' →
      SeqI (.Psi .zero π X) (famSeq τf π (some p')) → SeqC (.Psi .zero π X) (famSeq τf π (some p'))) :
    SeqI (.Psi .zero π X) (mahloSeq τ τf π Y (info Y).sums μ (info μ).sums P) →
      SeqC (.Psi .zero π X) (mahloSeq τ τf π Y (info Y).sums μ (info μ).sums P) := by
  have ht := C.ht
  have hY := C.hYF
  have hτF := C.hτF
  have hπF := C.hπF
  have hμF := C.hμF
  have hw0 := C.hw0
  have hτΩ : μ ≠ .one → ∀ c, τ ≠ .Om c := fun h1 c e => by
    have h2 := C.hμm
    rw [e] at h2
    rcases h2 with e' | h'
    · exact h1 e'
    · exact hμ0 (lt_oneY hμF h')
  have hSne : ∀ {p : Tm}, SeedP π X p → p ≠ .zero := fun Sp => by
    rcases Sp.hn with ⟨m, a, e⟩ | ⟨s, q, a, e⟩ <;> rw [e] <;> simp
  unfold mahloSeq
  by_cases h1 : μ = .one
  · rw [ite_eq_left h1]
    obtain ⟨S1, S2, S3⟩ := maxO_seed (C.seed0 hμ0) hP
    refine insert_cof C M hSY hSYC hSmC S1 S2 hτfr (hLow.mono' S1.hF fun p e => ⟨(hP p e).hF, S3 p e⟩) hCls
      (fun s hx _ hsμ => ?_) (hfam _ S1 S2)
    rw [h1] at hsμ
    have e := lt_oneY hx.psi.xiF hsμ
    subst e
    exact Or.inl S2
  rw [ite_eq_right h1]
  by_cases hs : isSucc μ = true
  · rw [ite_eq_left hs]
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
    have hyp₁ := le_transY hw0 hy₁ S1.hF (Or.inr (psi0_lt_idx hw0 hy₁ hpne)) S2
    have hLow' := hLow.mono' S1.hF fun p e => ⟨(hP p e).hF, S3 p e⟩
    -- `pred μ` の前線と、`π` 未満の加数は `y₁ = Ψ^{pred μ}_τ(Y)` 未満
    have hfr₁ : ∀ f u, u ∈ summands (pred μ) → f ∈ fr τ u → Lt f (.Psi (pred μ) τ Y) := fun f u hu hf =>
      FWOrder.k2s hy₁ f ((mem_fr_iff hpF).mpr ⟨u, hu, hf⟩)
    have hsm₁ : ∀ u, u ∈ summands (pred μ) → Lt u π → Lt u (.Psi (pred μ) τ Y) := fun u hu huπ => by
      have huF := hpF.of_mem_subs (mem_subs_of_mem_summands hu)
      have h3 : inC u Y τ = true := inC_of_mem_summands hpF (inC_pred_of hμF C.hμ1) hu
      have h4 : inC u Y (.Psi (pred μ) τ Y) = true :=
        inC_of_fr_lt huF hτF hy₁ hY hY h3 (Or.inr (lt_psi_targetY hy₁)) (Or.inl rfl) fun f hf => hfr₁ f u hu hf
      exact coll_psiY hy₁ u huF h4 (lt_of_lt_of_leY huF hπF hτF huπ C.hle)
    have hsle : ∀ s, WNF (.Psi s τ Y) → Lt s μ → Le s (pred μ) := fun s hx hsμ =>
      le_of_lt_succT hx.psi.xiF hpF (by rw [succT_pred hμF hs]; exact hsμ)
    have hps : summands (pred μ) = (info μ).sums.dropLast.map Prod.fst := by
      rw [sums_pred hμF, info_sums_fst]
    have hS0 : maxO P (.Psi (pred μ) τ Y) ≠ .zero := hSne S1
    cases hsp : splitPosD π (info μ).sums.dropLast with
    | none =>
      -- `pred μ` の加数は全て `π` 未満
      have hall : ∀ u, u ∈ summands (pred μ) → Lt u π := by
        refine all_lt_of_head hπF (nfl_summands hpF) fun q tl e h' => ?_
        rw [hps] at e
        cases hd : (info μ).sums.dropLast with
        | nil =>
          rw [hd] at e
          cases e
        | cons q' tl' =>
          rw [hd] at e hsp
          simp only [List.map_cons, List.cons.injEq] at e
          have hq := splitPosD_none_head hsp
          rw [e.1, leB_iff.mpr (ne_gt_of_le h')] at hq
          cases hq
      refine insert_cof C M hSY hSYC hSmC S1 hyp₁ hτfr hLow' hCls (fun s hx _ hsμ => Or.inl ?_) (hfam _ S1 hyp₁)
      have hpy : Lt (pred μ) (.Psi (pred μ) τ Y) := by
        cases hsp' : summands (pred μ) with
        | nil =>
          rw [eq_zero_of_summands_nil hsp']
          exact zero_lt (by intro e; cases e)
        | cons u l =>
          have hum : u ∈ summands (pred μ) := by rw [hsp']; exact List.mem_cons_self
          exact lt_prin_of_head hsp' rfl ((nfl_summands hpF).1 u hum).2 (hsm₁ u hum (hall u hum))
      have hsF := hx.psi.xiF
      refine le_transY hx hy₁ S1.hF (le_idx_of_fr hx hy₁ (hsle s hx hsμ) fun f hf => ?_) S2
      have hfF := hsF.of_mem_subs (fr_spec hf).1
      exact lt_of_le_of_ltY hfF hpF hy₁ (le_transY hfF hsF hpF (fr_leY hτF hsF hf) (hsle s hx hsμ)) hpy
    | some q =>
      obtain ⟨pre, R, r⟩ := q
      obtain ⟨⟨rest, hsum⟩, rfl, hπR⟩ := split_pos hs hsp
      obtain ⟨L, rest', hys, hL, -, hhd⟩ := splitPosD_rest hsp
      have hRm : R ∈ summands μ := by
        rw [hsum]
        exact List.mem_append_right _ List.mem_cons_self
      have hRF := hμF.of_mem_subs (mem_subs_of_mem_summands hRm)
      have hπR' : Le π R := le_of_ne_gtY hπF hRF (leB_iff.mp hπR)
      have hpR : Lt (maxO P (.Psi (pred μ) τ Y)) R := lt_of_lt_of_leY S1.hF hπF hRF (S1.hπ ht) hπR'
      have hR1 : R ≠ .one := by
        intro e
        rw [e] at hpR
        exact hS0 (lt_oneY S1.hF hpR)
      have hsump : summands (pred μ) = (pre ++ [R]) ++ rest'.map Prod.fst := by
        rw [hps, hys, List.map_append, hL, List.map_cons]
        simp
      have hNp : NFL ((pre ++ [R]) ++ rest'.map Prod.fst) := hsump ▸ nfl_summands hpF
      have hrest' : ∀ u, u ∈ rest'.map Prod.fst → Lt u π := by
        refine all_lt_of_head hπF (nfl_append_right hNp) fun q tl e h' => ?_
        cases hr : rest' with
        | nil =>
          rw [hr] at e
          cases e
        | cons q' tl' =>
          rw [hr] at e
          simp only [List.map_cons, List.cons.injEq] at e
          have hq := hhd q' tl' hr
          rw [e.1, leB_iff.mpr (ne_gt_of_le h')] at hq
          cases hq
      have hT : ofSummands (pre ++ [R]) = oadd (ofSummands pre) R :=
        eq_oadd_of_sum (wnf_ofSummands (nfl_append_left hNp)) (summands_ofSummands _ (nfl_principal
          (nfl_append_left hNp)))
      have hpe : pred μ = ofSummands ((pre ++ [R]) ++ rest'.map Prod.fst) := by
        rw [← hsump, ofSummands_summands _ hpF]
      dsimp only
      rw [mkApp_idx (Or.inr (ltB_iff.mpr hpR))]
      simp only
      intro hI
      refine idx_leaf_cof C hSμ hμs hSμC _ pre rest R hsum hR1 hpR (fun _ => S1) S1.hF (hτΩ h1) hτfr
        (fun x y hy hPy _ hx hxt htk hkτ => ?_) (fun x y hy hPy _ hx hxt z a e => ?_) hI
      · have hyF := seqI_wnf hI hy
        rcases hLow' x hx hxt htk hkτ with ⟨p', e, h⟩ | h
        · cases e
          exact lt_of_le_of_ltY hx S1.hF hyF h (hPy hS0)
        · exact h.lt ht hx hyF (seqI_gp hI rfl hy)
      · subst e
        have hyF := seqI_wnf hI hy
        rcases hCls z a hx hxt with haY | ⟨e', hzμ⟩ | hsub
        · exact Or.inl haY
        · subst a
          by_cases hzT : Lt z (oadd (ofSummands pre) R)
          · exact Or.inr (Or.inl ⟨rfl, hzT⟩)
          · refine Or.inr (Or.inr ?_)
            have hzF := hx.psi.xiF
            have hzle := hsle z hx hzμ
            have hfrz : ∀ f, f ∈ fr τ z → Lt f (.Psi (pred μ) τ Y) := by
              rcases hzle with e | hzp
              · intro f hf
                rw [e] at hf
                exact FWOrder.k2s hy₁ f hf
              · refine tail_fr_lt hτF hy₁ rfl hNp hzF (by rw [← hpe]; exact hzp) (by rw [hT]; exact hzT)
                  (fun f u hu hf => hfr₁ f u (by rw [hsump]; exact List.mem_append_left _ hu) hf)
                  fun u hu => hsm₁ u (by rw [hsump]; exact List.mem_append_right _ hu) (hrest' u hu)
            exact lt_of_le_of_ltY hx S1.hF hyF (le_transY hx hy₁ S1.hF (le_idx_of_fr hx hy₁ hzle hfrz) S2)
              (hPy hS0)
        · exact Or.inr (Or.inr (hsub.lt ht hx hyF (seqI_gp hI rfl hy)))
  · rw [ite_eq_right hs]
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
    have o0 := mahlo_out C hSμ hμs .zero pre [] R hsum hR1 (zero_lt hR0) (fun h => absurd rfl h) WNF.zero
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
    have hTμ : oadd (ofSummands pre) R = μ := (eq_oadd_of_sum hμF hsum).symm
    -- 素の列 `s0`
    have hs0cof : (∀ x y, InSeq (s0Of π τ Y μ) y → WNF y → Gp (.Psi .zero π X) y → Le (s0Of π τ Y μ).first y →
        WNF x → Lt x (.Psi .zero π X) → Lt (.Psi .zero π X) (tgtN x) → Lt (tgtN x) τ → Lt x y) →
        SeqI (.Psi .zero π X) (s0Of π τ Y μ) → SeqC (.Psi .zero π X) (s0Of π τ Y μ) := fun hlow hI => by
      rw [hs0] at hI ⊢
      refine idx_leaf_cof C hSμ hμs hSμC .zero pre [] R hsum hR1 (zero_lt hR0) (fun h => absurd rfl h) WNF.zero
        (hτΩ h1) hτfr (fun x y hy _ hfy hx hxt htk hkτ => ?_) (fun x y hy _ _ hx hxt z a e => ?_) hI
      · exact hlow x y (by rw [hs0]; exact hy) (seqI_wnf hI hy) (seqI_gp hI rfl hy) (by rw [hs0]; exact hfy) hx hxt
          htk hkτ
      · subst e
        rcases hCls z a hx hxt with haY | ⟨rfl, hzμ⟩ | hsub
        · exact Or.inl haY
        · exact Or.inr (Or.inl ⟨rfl, by rw [hTμ]; exact hzμ⟩)
        · exact Or.inr (Or.inr (hsub.lt ht hx (seqI_wnf hI hy) (seqI_gp hI rfl hy)))
    cases P with
    | none =>
      exact hs0cof fun x y _ hyF hG _ hx hxt htk hkτ => by
        rcases hLow x hx hxt htk hkτ with ⟨p, e, -⟩ | h
        · cases e
        · exact h.lt ht hx hyF hG
    | some p =>
      have Sp := hP p rfl
      simp only
      by_cases h2 : ltB p (s0Of π τ Y μ).first = true
      · rw [ite_eq_left h2]
        exact hs0cof fun x y _ hyF hG hfy hx hxt htk hkτ => by
          rcases hLow x hx hxt htk hkτ with ⟨p', e, h⟩ | h
          · cases e
            exact lt_of_le_of_ltY hx Sp.hF hyF h (lt_of_lt_of_leY Sp.hF hfF hyF (ltB_iff.mp h2) hfy)
          · exact h.lt ht hx hyF hG
      · rw [ite_eq_right h2, ite_eq_right (hne' p rfl)]
        have hlt : Lt (s0Of π τ Y μ).first p := by
          rcases triY hfF Sp.hF with h | h | h
          · exact h
          · exact absurd h (hne' p rfl)
          · exact absurd (ltB_iff.mpr h) h2
        have hyp : Le (.Psi .zero τ Y) p := Or.inr (lt_of_le_of_ltY hw0 hfF Sp.hF hle0 hlt)
        cases hsp : splitGtD p (info μ).sums with
        | none =>
          have hall : ∀ u, u ∈ summands μ → Le u p := fun u hu => by
            cases hxs : (info μ).sums with
            | nil =>
              rw [← info_sums_fst, hxs] at hu
              cases hu
            | cons q ys =>
              rw [hxs] at hsp
              have h0' := splitGtD_none_head hsp
              have hN := nfl_summands hμF
              rw [← info_sums_fst, hxs] at hu hN
              simp only [List.map_cons] at hu hN
              have hqF := (hN.1 q.1 List.mem_cons_self).1
              have hqp : Le q.1 p := le_of_not_ltY Sp.hF hqF fun h => by rw [ltB_iff.mpr h] at h0'; cases h0'
              exact le_transY (hN.1 u hu).1 hqF Sp.hF (le_head_mem hN hu) hqp
          exact insert_cof C M hSY hSYC hSmC Sp hyp hτfr hLow hCls (fun s hx hxt hsμ =>
            hW p rfl hs h1 hlt [] (summands μ) (by simp) hall s hx hxt hsμ (fun h => not_lt_zero _ h)) (hfam p Sp hyp)
        | some q =>
          obtain ⟨pre₂, R₂, r₂⟩ := q
          obtain ⟨L, rest, hys, hL, hpR₂, -, hhd⟩ := splitGtD_spec hsp
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
            exact hSne Sp (lt_oneY Sp.hF hpR')
          have hN₂ : NFL ((pre₂ ++ [R₂]) ++ rest.map Prod.fst) := by
            have h' := nfl_summands hμF
            rw [hsum₂] at h'
            simpa using h'
          have hT₂ : ofSummands (pre₂ ++ [R₂]) = oadd (ofSummands pre₂) R₂ :=
            eq_oadd_of_sum (wnf_ofSummands (nfl_append_left hN₂)) (summands_ofSummands _ (nfl_principal
              (nfl_append_left hN₂)))
          have hrestp : ∀ u, u ∈ rest.map Prod.fst → Le u p := by
            intro u hu
            have hNr := nfl_append_right hN₂
            cases hr : rest with
            | nil =>
              rw [hr] at hu
              cases hu
            | cons q tl =>
              rw [hr] at hu hNr
              simp only [List.map_cons] at hu hNr
              have hq := hhd q tl hr
              have hqF := (hNr.1 q.1 List.mem_cons_self).1
              have hqp : Le q.1 p := le_of_not_ltY Sp.hF hqF fun h => by rw [ltB_iff.mpr h] at hq; cases hq
              exact le_transY (hNr.1 u hu).1 hqF Sp.hF (le_head_mem hNr hu) hqp
          dsimp only
          rw [mkApp_idx (Or.inr hpR₂)]
          simp only
          intro hI
          refine idx_leaf_cof C hSμ hμs hSμC p pre₂ _ R₂ hsum₂ hR₂1 hpR' (fun _ => Sp) Sp.hF (hτΩ h1) hτfr
            (fun x y hy hPy _ hx hxt htk hkτ => ?_) (fun x y hy hPy _ hx hxt z a e => ?_) hI
          · have hyF := seqI_wnf hI hy
            rcases hLow x hx hxt htk hkτ with ⟨p', e, h⟩ | h
            · cases e
              exact lt_of_le_of_ltY hx Sp.hF hyF h (hPy (hSne Sp))
            · exact h.lt ht hx hyF (seqI_gp hI rfl hy)
          · subst e
            have hyF := seqI_wnf hI hy
            have hG := seqI_gp hI rfl hy
            rcases hCls z a hx hxt with haY | ⟨rfl, hzμ⟩ | hsub
            · exact Or.inl haY
            · by_cases hzT : Lt z (oadd (ofSummands pre₂) R₂)
              · exact Or.inr (Or.inl ⟨rfl, hzT⟩)
              · exact Or.inr (Or.inr (lt_of_le_seed ht Sp.hF hx hyF (hPy (hSne Sp)) hG
                  (hW p rfl hs h1 hlt (pre₂ ++ [R₂]) (rest.map Prod.fst) (by rw [hsum₂]; simp) hrestp z hx hxt hzμ
                    (by rw [hT₂]; exact hzT))))
            · exact Or.inr (Or.inr (hsub.lt ht hx hyF hG))

end RTKA.Fund
