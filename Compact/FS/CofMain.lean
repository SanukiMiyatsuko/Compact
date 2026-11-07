import Compact.FS.CofFloorX

/-! 共終性の全体：`Ω_c` への崩壊の倍数の列、`X = 0`、崩壊 `t = Ψ^0_π(X)` の全分岐（`seqC_psi0`）と
標準形全体の定理（`seqC_all`）。 -/

namespace RTKA.Fund

open Tm W

/-! ### 倍数の列 -/

theorem cmpList_le_rep {p : Tm} (hpp : isPrincipal p = true) :
    ∀ l : List Tm, (∀ u, u ∈ l → isPrincipal u = true ∧ Le u p) →
      cmpList l (List.replicate (l.length + 1) p) = .lt
  | [], _ => by simp [cmpList]
  | u :: l, h => by
    obtain ⟨hup, hle⟩ := h u List.mem_cons_self
    have ih := cmpList_le_rep hpp l fun v hv => h v (List.mem_cons_of_mem _ hv)
    have hc : cmpP u p = .eq ∨ cmpP u p = .lt := by
      rcases hle with e | hlt
      · left
        rw [e]
        have := cmp_self p
        rwa [cmp_principal hpp hpp] at this
      · right
        have := hlt
        unfold Lt at this
        rwa [cmp_principal hup hpp] at this
    show cmpList (u :: l) (p :: List.replicate (l.length + 1) p) = .lt
    rcases hc with hc | hc
    · simp only [cmpList, hc]
      exact ih
    · simp only [cmpList, hc]

/-- 加数が全て主要項 `p` 以下なら `p` の倍数未満 -/
theorem lt_mulNat_of_le {x p : Tm} (hx : WNF x) (hpp : isPrincipal p = true)
    (h : ∀ u, u ∈ summands x → Le u p) : Lt x (mulNat p ((summands x).length + 1)) := by
  unfold Lt
  rw [cmp_eq, summands_mulNat hpp]
  exact cmpList_le_rep hpp _ fun u hu => ⟨nfl_principal (nfl_summands hx) u hu, h u hu⟩

/-- 倍数の列の共終性：`t` 未満の主要項が全て `p` 以下なら `p·n` は `t` の中で共終 -/
theorem leaf_mul {t p : Tm} (ht : WNF t) (hp : WNF p) (hpp : isPrincipal p = true)
    (hprin : ∀ h, WNF h → isPrincipal h = true → Lt h t → Le h p) : SeqC t (.mul p 2) := by
  show ∀ x, WNF x → Lt x t → ∃ n, Lt x ((SeqD.mul p 2).nat n)
  intro x hx hxt
  refine ⟨(summands x).length, ?_⟩
  show Lt x (mulNat p ((summands x).length + 2))
  have h1 := lt_mulNat_of_le hx hpp fun u hu => by
    have huF := hx.of_mem_subs (mem_subs_of_mem_summands hu)
    have hux : Le u x := by
      have := le_ofSummands_of_mem (nfl_summands hx) hu
      rwa [ofSummands_summands x hx] at this
    exact hprin u huF (nfl_principal (nfl_summands hx) u hu) (lt_of_le_of_ltY huF hx ht hux hxt)
  exact lt_transY hx (wnf_mulNat hp hpp _) (wnf_mulNat hp hpp _) h1 (mulNat_lt_succ hpp _)

/-- `Ω_c` への崩壊の種 `p`：`t` 未満の主要項は `p` 以下 -/
theorem om_prin_le {c X p W : Tm} (ht : WNF (.Psi .zero (.Om c) X)) (hp : WNF p)
    (hw : WNF (.Psi .zero (.Om c) W)) (hle : Le (.Psi .zero (.Om c) W) p)
    (hΩ : ∀ v, v ∈ subs (.Psi .zero (.Om c) X) → v ≠ .Psi .zero (.Om c) X →
      Lt v (.Psi .zero (.Om c) X) → Le v p)
    (hL : LoT (.Psi .zero (.Om c) X) (.Om c) p) :
    ∀ h, WNF h → isPrincipal h = true → Lt h (.Psi .zero (.Om c) X) → Le h p := by
  have hπF := ht.psi.piF
  have hπt := ht.psi.tgt
  have hlew : ∀ {h : Tm}, WNF h → Lt h (.Psi .zero (.Om c) W) → Le h p := fun hF h' =>
    Or.inr (lt_of_lt_of_leY hF hw hp h' hle)
  have hsub : ∀ {h : Tm}, WNF h → SubLe (.Psi .zero (.Om c) X) h → Le h p := fun hF ⟨w', hws, hne, hwt, hhw⟩ =>
    le_transY hF (ht.of_mem_subs hws) hp hhw (hΩ w' hws hne hwt)
  -- `t` 未満の目標は `Ψ^0_{Ω_c}(W)` 未満
  have htgt : ∀ {k : Tm}, WNF k → IsTgt k → Lt k (.Psi .zero (.Om c) X) → Lt k (.Psi .zero (.Om c) W) := by
    intro k hkF hkt hk
    by_cases hkΩ : ∃ e, k = .Om e
    · obtain ⟨e, rfl⟩ := hkΩ
      exact (lt_om_psiY hw).mpr ((lt_om_psiY ht).mp hk)
    · have hOF := tgt_isOF hkF hkt fun e h' => hkΩ ⟨e, h'⟩
      exact (lt_OF_psiOm hOF hkF hw).mpr ((lt_OF_psiOm hOF hkF ht).mp hk)
  intro h hF hp' hl
  have hhΩ : Lt h (.Om c) := lt_transY hF ht hπF hl (lt_psi_targetY ht)
  cases h with
  | zero => cases hp'
  | plus a b => cases hp'
  | one => exact le_transY WNF.one hw hp (Or.inr (one_lt_of_prin hw rfl (by intro e; cases e))) hle
  | K j => exact hlew hF (coll_psiY hw _ hF (inC_K _ _ _) hhΩ)
  | Om e => exact hlew hF ((lt_om_psiY hw).mpr ((lt_om_psiY ht).mp hl))
  | Xi j b =>
    have hj := hF.xi.1
    have hKF := WNF.K' hj
    have hxK : Lt (.Xi j b) (.K j) := (lt_K_iffY hF hj).mpr (Nat.le_refl _)
    by_cases htk : Lt (.Psi .zero (.Om c) X) (.K j)
    · have hπK : Lt (.Om c) (.K j) := by
        rcases tgt_ge ht hKF htk (inC_K _ _ _) with e | h'
        · cases e
        · exact h'
      rcases tgt_wit hπF hπt (Clo.xi hF) hhΩ hπK with ⟨r, e, -⟩ | ⟨u, hu, hxu⟩
      · cases e
      · exact hsub hF (subLe_frπ ht hu hxu)
    · have hKt : Lt (.K j) (.Psi .zero (.Om c) X) := by
        rcases le_of_not_ltY ht hKF htk with e | h'
        · cases e
        · exact h'
      exact hlew hF (lt_transY hF hKF hw hxK
        (coll_psiY hw _ hKF (inC_K _ _ _) (lt_transY hKF ht hπF hKt (lt_psi_targetY ht))))
  | Psi s k a =>
    have hQ := hF.psi
    by_cases htk : Lt (.Psi .zero (.Om c) X) k
    · by_cases hkπ : Le k (.Om c)
      · rcases hL (.Psi s k a) a hF hl rfl htk hkπ with h' | h'
        · exact h'
        · exact hsub hF h'
      · have hπk : Lt (.Om c) k := Classical.byContradiction fun h' => hkπ (le_of_not_ltY hπF hQ.piF h')
        rcases tgt_wit hπF hπt (Clo.psi hF) hhΩ hπk with ⟨r, e, -⟩ | ⟨u, hu, hxu⟩
        · cases e
        · exact hsub hF (subLe_frπ ht hu hxu)
    · have hkt : Lt k (.Psi .zero (.Om c) X) := by
        rcases le_of_not_ltY ht hQ.piF htk with e | h'
        · exact absurd (e ▸ hQ.tgt) fun h'' => Fund.not_tgt_psi0 h''
        · exact h'
      exact hlew hF (lt_transY hF hQ.piF hw (lt_psi_targetY hF) (htgt hQ.piF hQ.tgt hkt))

/-! ### 後者の引数の崩壊の段 -/

/-- 崩壊 `t = Ψ^0_π(X)` の下の段：目標が `t` と `π` の間の節点は部分項以下 -/
theorem top_lowC {π X : Tm} (ht : WNF (.Psi .zero π X)) (P : Option Tm) :
    LowC (.Psi .zero π X) π P := by
  intro x hx hxt htk hkπ
  refine Or.inr ?_
  have hπF := ht.psi.piF
  cases x with
  | Psi s k a =>
    have hP := hx.psi
    rcases below_psi ht hx hxt with h | ⟨w, hw, hle⟩ | ⟨-, -, -, -, hkC⟩
    · exact absurd h (Lt.asymmY ht hP.piF htk)
    · exact subLe_gap ht hw hle
    · exact absurd hkπ (not_lt_of_leY hπF hP.piF (tgt_ge ht hP.piF htk hkC))
  | Xi j b =>
    have hKF := WNF.K' hx.xi.1
    exact absurd hkπ (not_lt_of_leY hπF hKF (tgt_ge ht hKF htk (inC_K _ _ _)))
  | _ => exact absurd htk (not_lt_zero _)

/-- 後者の引数 `X = Y + 1` の崩壊の段の節点：`a < Y` か `a = Y`（添字は `m(π)` 未満）か隙間 -/
theorem top_cls {π X : Tm} (ht : WNF (.Psi .zero π X)) (hs : isSucc X = true) :
    ClsC (.Psi .zero π X) π (pred X) (mi π) := by
  intro s a hx hxt
  have hP := hx.psi
  have hXF := ht.psi.aF
  have hne : Tm.Psi s π a ≠ .Psi .zero π X := fun e => Lt.irrefl _ (e ▸ hxt)
  rcases (lt_psi_psiY rfl hne).mp hxt with h | ⟨-, -, h1 | h2 | h3 | h4⟩
  · exact absurd (lt_psi_targetY ht) h
  · obtain ⟨haX, -, -, -⟩ := h1
    have hle : Le a (pred X) :=
      le_of_lt_succT hP.aF (wnf_pred hXF) (by rw [succT_pred hXF hs]; exact haX)
    rcases hle with e | h
    · exact Or.inr (Or.inl ⟨e, hP.mlt⟩)
    · exact Or.inl h
  · obtain ⟨hle, hn⟩ := h2
    obtain ⟨w, hw, hn'⟩ := wit_c2 ht hx hP.aF (le_of_ne_gtY hXF hP.aF hle) (lt_psi_targetY hx) hn
    have hle' := le_of_not_ltY (by
      rcases hw with hw | hw | hw
      · exact hXF.of_mem_subs (fr_spec hw).1
      · exact ht.psi.piF.of_mem_subs (fr_spec hw).1
      · exact WNF.zero.of_mem_subs (fr_spec hw).1) hx hn'
    rcases hw with hw | hw | hw
    · exact Or.inr (Or.inr (subLe_gap ht (Or.inl hw) hle'))
    · exact Or.inr (Or.inr (subLe_gap ht (Or.inr hw) hle'))
    · simp [fr] at hw
  · obtain ⟨-, -, hs0, -⟩ := h3
    exact absurd hs0 (not_lt_zero _)
  · obtain ⟨-, h⟩ := h4
    rw [inC_zero] at h
    cases h

/-! ### 崩壊の列 -/

/-- 崩壊 `t = Ψ^0_π(X)` の列の共終性 -/
theorem seqC_psi0 {π X : Tm} (ht : WNF (.Psi .zero π X))
    (hIH : ∀ u, u ∈ subs (.Psi .zero π X) → u ≠ .Psi .zero π X → SeqI u (info u).seq)
    (hIC : ∀ u, u ∈ subs (.Psi .zero π X) → u ≠ .Psi .zero π X → SeqC u (info u).seq) :
    SeqI (.Psi .zero π X) (cseq π (info π).fam X (info X).sums) →
      SeqC (.Psi .zero π X) (cseq π (info π).fam X (info X).sums) := by
  have hP := ht.psi
  have hπF := hP.piF
  have hX := hP.aF
  have hsX : ∀ S, S ∈ subs X → S ≠ .Psi .zero π X := fun S hS => ne_of_size_lt (by
    have := size_le_of_mem_subs hS
    simp only [Tm.size]
    omega)
  have hS : ∀ S, S ∈ summands X → S ≠ .one → SeqI S (info S).seq := fun S hm _ =>
    hIH S (subs_psi_a (mem_subs_of_mem_summands hm)) (hsX S (mem_subs_of_mem_summands hm))
  have hSC : ∀ S, S ∈ summands X → S ≠ .one → SeqC S (info S).seq := fun S hm _ =>
    hIC S (subs_psi_a (mem_subs_of_mem_summands hm)) (hsX S (mem_subs_of_mem_summands hm))
  -- `Ω_c` の倍数の列
  have hmul : ∀ c, π = .Om c → ∀ p W, SeedP π X p → WNF (.Psi .zero π W) → Le (.Psi .zero π W) p →
      (∀ v, v ∈ subs (.Psi .zero π X) → v ≠ .Psi .zero π X → Lt v (.Psi .zero π X) → Le v p) →
      LoT (.Psi .zero π X) π p → SeqC (.Psi .zero π X) (famSeq (info π).fam π (some p)) := by
    intro c e p W Sp hw hle hΩ hL
    subst e
    have e' : (info (.Om c)).fam = .om := rfl
    rw [e', famSeq]
    exact leaf_mul ht Sp.hF Sp.prin (om_prin_le ht Sp.hF hw hle hΩ hL)
  unfold cseq
  by_cases hX0 : X = .zero
  · rw [ite_eq_left hX0]
    subst hX0
    cases π with
    | Om c =>
      intro _
      obtain ⟨hB, hBp, -⟩ := mul_base_lt ht
      exact leaf_mul ht hB hBp fun h hF hp hl => prin_le_base ht hF hp hl
    | _ => exact fun _ => True.intro
  rw [ite_eq_right hX0]
  have hd := lastS_dom hX hX0
  by_cases hs : isSucc X = true
  · have hd1 : (lastS (info X).sums).dom = .one := by
      rw [hd]
      exact (dom_eq_one_iff hX).mpr hs
    rw [hd1]
    dsimp only
    by_cases hval : validR π (pred X) = true
    · rw [ite_eq_right (by simp [hval])]
      have C := mctx_succ ht hs hval
      have hμ0 := mi_ne_zero hπF hP.tgt
      obtain ⟨hSμ, hμs⟩ := mi_parts ht hIH
      have hSY : ∀ u, u ∈ summands (pred X) → u ≠ .one → SeqI u (info u).seq := fun u hu h1 =>
        hS u (by
          rw [← succT_pred hX hs, summands_succT]
          exact List.mem_append_left _ hu) h1
      have hSYC : ∀ u, u ∈ summands (pred X) → u ≠ .one → SeqC u (info u).seq := fun u hu h1 =>
        hSC u (by
          rw [← succT_pred hX hs, summands_succT]
          exact List.mem_append_left _ hu) h1
      rw [sums_pred hX, mOfT_tgt hP.tgt, fam_mdl hP.tgt]
      refine mahlo_cof C (mpar_chain ht hIH (.refl _) hP.tgt) hμ0 hSY hSμ hμs hSYC
        (mi_partsC hIC (.refl _) hP.tgt) (mi_partsC hIC (.refl _) hP.tgt) (fun _ e => by cases e)
        (fun _ e => by cases e) (fun u hu => hu) (top_lowC ht _) (top_cls ht hs) (fun _ e => by cases e)
        fun p' Sp hle hL => ?_
      by_cases hn : ∃ c, π = .Om c
      · obtain ⟨c, e⟩ := hn
        exact fun _ => hmul c e p' (pred X) Sp C.hw0 hle (fun v hv hne hl =>
          Or.inr (gp_succ ht hs C.hw0 Sp.hF Sp.prin hle v hv hne hl)) hL
      · exact fam_cof ht hIH hIC π (.refl _) (fun c e => hn ⟨c, e⟩) p' (pred X) Sp C.hw0 hle hL
    · rw [ite_eq_left (Bool.eq_false_iff.mpr hval)]
      cases hr : argR? π with
      | none =>
        unfold validR at hval
        rw [hr] at hval
        exact absurd rfl hval
      | some r =>
        have hrF := wnf_of_argR hπF hr
        have hn : ¬ Lt r (pred X) := fun h' => hval (by
          unfold validR
          rw [hr]
          exact ltB_iff.mpr h')
        have h3 : Le r (pred X) := le_of_lt_succT hrF (wnf_pred hX) (by
          rw [succT_pred hX hs]
          exact arg_lt_of_psi ht hr)
        have h4 : r = pred X := h3.resolve_right hn
        have e' : X = sc r := by
          rw [h4]
          exact (succT_pred hX hs).symm
        subst e'
        cases π with
        | Xi m q =>
          cases hr
          exact floor_cof_xi ht hIH hIC
        | Psi ζ κ γ =>
          cases hr
          exact floor_cof_psi ht hIH hIC
        | _ => cases hr
  · have hd1 : (lastS (info X).sums).dom ≠ .one := by
      rw [hd]
      exact fun h => hs ((dom_eq_one_iff hX).mp h)
    have hlim := seqC_limit (πf := (info π).fam) ht hX0 hs hS hSC fun p W hpm _ _ hw hle hΩ hL => by
      have Sp := seed_of_fr ht hpm
      by_cases hn : ∃ c, π = .Om c
      · obtain ⟨c, e⟩ := hn
        exact fun _ => hmul c e p W Sp hw hle (hΩ c e) hL
      · exact fam_cof ht hIH hIC π (.refl _) (fun c e => hn ⟨c, e⟩) p W Sp hw hle hL
    split
    · rename_i h
      exact absurd h hd1
    · exact hlim

/-! ### 全体の定理 -/

/-- 標準形の項の列の共終性 -/
theorem seqC_all (t : Tm) (ht : WNF t) : SeqC t (info t).seq := by
  induction hn : t.size using Nat.strongRecOn generalizing t with
  | ind n ih =>
    have hIC : ∀ u, u ∈ subs t → u ≠ t → SeqC u (info u).seq := fun u hu hne =>
      ih u.size (hn ▸ size_lt_of_mem_subs_ne hu hne) u (ht.of_mem_subs hu) rfl
    have hIH : ∀ u, u ∈ subs t → u ≠ t → SeqI u (info u).seq := fun u hu _ =>
      seqI_all u (ht.of_mem_subs hu)
    cases t with
    | zero => exact True.intro
    | one => exact True.intro
    | K m => exact seqC_reg (wnf_base_K m)
    | plus a b =>
      have hb : b ∈ subs (.plus a b) := subs_plus_r (self_mem_subs b)
      have hne : b ≠ .plus a b := ne_of_size_lt (by simp only [Tm.size]; omega)
      exact seqC_add ht (hIH b hb hne) (hIC b hb hne)
    | Om c =>
      by_cases hs : isSucc c = true
      · have e : (info (.Om c)).seq = .reg (.Om c) (base (.Om c)) := by simp [info, hs]
        rw [e]
        exact seqC_reg (wnf_base_om ht hs)
      · have e : (info (.Om c)).seq = .om (info c).seq := by simp [info, hs]
        rw [e]
        have hc : c ∈ subs (.Om c) := subs_om (self_mem_subs c)
        have hne : c ≠ .Om c := ne_of_size_lt (by simp only [Tm.size]; omega)
        exact seqC_om ht hs (hIH c hc hne) (hIC c hc hne)
    | Xi m q => exact seqC_reg (wnf_base_xi ht)
    | Psi ζ π X =>
      by_cases hζ : ζ = .zero
      · subst hζ
        exact seqC_psi0 ht hIH hIC (seqI_psi0 ht hIH)
      · have e : (info (.Psi ζ π X)).seq = .reg (.Psi ζ π X) (base (.Psi ζ π X)) := by simp [info, hζ]
        rw [e]
        exact seqC_reg (wnf_base_psi ht hζ)

end RTKA.Fund
