import Compact.FS.Seq

/-! 解析 `info` の基本性質、共終数の分類（後者・0）と、FS の 0・後者・自然数の公理。 -/

namespace RTKA.Fund

open Tm W

/-! ### 解析 `info` の基本性質 -/

/-- 崩壊 `Ψ^0_π(X)` の列の記述 -/
def cs (π X : Tm) : SeqD := cseq π (info π).fam X (info X).sums

theorem info_seq_psi0 (π X : Tm) : (info (Psi zero π X)).seq = cs π X := rfl

theorem info_fam_xi (m : Nat) (q : Tm) : (info (Xi m q)).fam = .xi m q (info q).sums := rfl

theorem info_fam_psi (ζ κ γ : Tm) :
    (info (Psi ζ κ γ)).fam = .psi ζ (info ζ).sums κ (info κ).fam γ (info γ).sums := rfl

theorem info_fam_om (c : Tm) : (info (Om c)).fam = .om := rfl

theorem dom_zero : dom zero = .zero := rfl
theorem dom_one : dom one = .one := rfl
theorem dom_K (m : Nat) : dom (K m) = .big (K m) := rfl
theorem dom_plus (a b : Tm) : dom (plus a b) = dom b := rfl
theorem dom_xi (m : Nat) (q : Tm) : dom (Xi m q) = .big (Xi m q) := rfl

theorem dom_om (c : Tm) : dom (Om c) = if isSucc c then .big (Om c) else dom c := by
  simp only [dom, info]; split <;> rfl

theorem dom_psi (ζ π X : Tm) :
    dom (Psi ζ π X) = if ζ = zero then (cs π X).dom else .big (Psi ζ π X) := by
  simp only [dom, info, cs]; split <;> rfl

theorem dom_psi0 (π X : Tm) : dom (Psi zero π X) = (cs π X).dom := rfl

theorem fundBig_plus (a b ξ : Tm) : fundBig (plus a b) ξ = oadd a (fundBig b ξ) := rfl
theorem fundBig_K (m : Nat) (ξ : Tm) : fundBig (K m) ξ = oadd (base (K m)) ξ := rfl
theorem fundBig_xi (m : Nat) (q ξ : Tm) : fundBig (Xi m q) ξ = oadd (base (Xi m q)) ξ := rfl

theorem fundBig_om (c ξ : Tm) :
    fundBig (Om c) ξ = if isSucc c then oadd (base (Om c)) ξ else Om (sc (fundBig c ξ)) := by
  simp only [fundBig, info]; split <;> rfl

theorem fundBig_psi (ζ π X ξ : Tm) :
    fundBig (Psi ζ π X) ξ = if ζ = zero then (cs π X).big ξ else oadd (base (Psi ζ π X)) ξ := by
  simp only [fundBig, info, cs]; split <;> rfl

theorem fundBig_psi0 (π X ξ : Tm) : fundBig (Psi zero π X) ξ = (cs π X).big ξ := rfl

theorem fundNat_plus (a b : Tm) (n : Nat) : fundNat (plus a b) n = oadd a (fundNat b n) := rfl

theorem fundNat_om {c : Tm} (hc : ¬ isSucc c = true) (n : Nat) :
    fundNat (Om c) n = Om (sc (fundNat c n)) := by
  simp only [fundNat, info, hc, Bool.false_eq_true, ↓reduceIte]; rfl

theorem fundNat_psi0 (π X : Tm) (n : Nat) : fundNat (Psi zero π X) n = (cs π X).nat n := rfl

theorem fund_eq (t ξ : Tm) : fund t ξ =
    match dom t with
    | .zero => zero
    | .one => pred t
    | .omega => fundNat t (natOf ξ)
    | .big σ => fundBig t (if ltB ξ σ then ξ else zero) := rfl

/-- 加数の記述は各加数の記述 -/
def Coh (l : DL) : Prop := ∀ p ∈ l, p.2 = (info p.1).seq

theorem info_sums_fst : ∀ t : Tm, (info t).sums.map Prod.fst = summands t
  | .plus a b => by
    show a :: (info b).sums.map Prod.fst = a :: summands b
    rw [info_sums_fst b]
  | .zero | .one | .K _ | .Om _ | .Xi _ _ | .Psi _ _ _ => rfl

theorem coh_sums : ∀ t : Tm, Coh (info t).sums
  | .plus a b => by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · rfl
    · exact coh_sums b p hp
  | .zero => by intro p hp; cases hp
  | .one | .K _ | .Om _ | .Xi _ _ | .Psi _ _ _ => by
    intro p hp
    rcases List.mem_singleton.mp hp with rfl
    rfl

theorem preT_info (X : Tm) : preT (info X).sums = (summands X).dropLast := by
  rw [preT, List.map_dropLast, info_sums_fst]

theorem lastT_info (X : Tm) : lastT (info X).sums = (summands X).getLast?.getD zero := by
  rw [lastT, ← List.getLast?_map, info_sums_fst]

theorem lastS_coh {l : DL} (h : Coh l) : lastS l = (info (lastT l)).seq := by
  unfold lastS lastT
  cases e : l.getLast? with
  | none => rfl
  | some p => exact h p (List.mem_of_getLast? e)

/-! ### 崩壊の列の記述の形 -/

/-- 崩壊の列の記述の形（`none`・`mul`・`tower`・`app`、一つずらした `app`） -/
def SeqD.isC : SeqD → Bool
  | .none | .mul _ _ | .tower _ | .app _ _ _ _ _ _ _ => true
  | .shift (.app _ _ _ _ _ _ _) => true
  | _ => false

theorem SeqD.app_dom_ne (τ : Tm) (g : Gen) (pre : List Tm) (R : Tm) (r : SeqD) (P c : Tm) :
    (SeqD.app τ g pre R r P c).dom ≠ .one ∧ (SeqD.app τ g pre R r P c).dom ≠ .zero := by
  simp only [SeqD.dom]
  split
  · split <;> simp
  · simp

theorem SeqD.dom_ne_one {s : SeqD} (h : s.isC = true) : s.dom ≠ .one := by
  cases s with
  | app τ g pre R r P c => exact (SeqD.app_dom_ne _ _ _ _ _ _ _).1
  | shift s =>
    cases s with
    | app τ g pre R r P c => exact (SeqD.app_dom_ne τ g pre R r P c).1
    | _ => simp [isC] at h
  | _ => simp_all [isC, SeqD.dom]

theorem SeqD.eq_none_of_dom {s : SeqD} (h : s.isC = true) (hd : s.dom = .zero) : s = .none := by
  cases s with
  | app τ g pre R r P c => exact absurd hd (SeqD.app_dom_ne _ _ _ _ _ _ _).2
  | shift s =>
    cases s with
    | app τ g pre R r P c => exact absurd hd (SeqD.app_dom_ne τ g pre R r P c).2
    | _ => simp [isC] at h
  | _ => simp_all [isC, SeqD.dom]

/-- `mkApp` が作るのは `app`（調整 `c` だけが変わりうる）か、調整なしで一つずらした `app` -/
theorem mkApp_eq_some {ceil : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD} {P c : Tm} {s : SeqD}
    (h : mkApp ceil g pre R r P c = some s) :
    ∃ c', s = .app ceil g pre R r P c' ∨ s = .shift (.app ceil g pre R r P c') := by
  unfold mkApp at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h; exact ⟨_, Or.inl rfl⟩
      · split at h
        · cases h
        · split at h
          · cases h; exact ⟨_, Or.inl rfl⟩
          · split at h
            · cases h; exact ⟨_, Or.inr rfl⟩
            · cases h; exact ⟨_, Or.inl rfl⟩
    · cases h; exact ⟨_, Or.inl rfl⟩

theorem mkApp_isC {ceil : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD} {P c : Tm} {s : SeqD}
    (h : mkApp ceil g pre R r P c = some s) : s.isC = true ∧ s ≠ .none := by
  obtain ⟨c', rfl | rfl⟩ := mkApp_eq_some h
  · exact ⟨rfl, fun e => by cases e⟩
  · exact ⟨rfl, fun e => by cases e⟩

theorem mkApp_ne_none {ceil : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD} {P c : Tm} {s : SeqD}
    (h : mkApp ceil g pre R r P c = some s) : s ≠ .none := (mkApp_isC h).2

theorem getD_isC {o : Option SeqD} (h : ∀ s, o = some s → s.isC = true) : (o.getD .none).isC = true := by
  cases o with
  | none => rfl
  | some s => exact h s rfl

theorem mahloVK_isC (m : Nat) (q : Tm) (qs : DL) (ceil : Tm) (P : Option Tm) :
    (mahloVK m q qs ceil P).isC = true := by
  unfold mahloVK
  dsimp only
  repeat' split
  all_goals first | exact (mkApp_isC (by assumption)).1 | rfl

section
variable {τ : Tm} {τf : Fam} (hf : ∀ c P, (famSeq τf c P).isC = true)
include hf

theorem deadSeqM_isC (c p Y' : Tm) (ys : DL) : (deadSeqM τ τf c p Y' ys).isC = true := by
  unfold deadSeqM
  repeat' split
  all_goals first | exact hf _ _ | exact (mkApp_isC (by assumption)).1 | rfl

theorem insertAtM_isC (c p Y' : Tm) (ys : DL) : (insertAtM τ τf c p Y' ys).isC = true := by
  unfold insertAtM
  repeat' split
  all_goals first | exact hf _ _ | exact deadSeqM_isC hf _ _ _ _ | exact (mkApp_isC (by assumption)).1

theorem mahloSeq_isC (c Y' : Tm) (ys : DL) (μ : Tm) (ms : DL) (P : Option Tm) :
    (mahloSeq τ τf c Y' ys μ ms P).isC = true := by
  unfold mahloSeq
  dsimp only
  repeat' split
  all_goals first
    | exact insertAtM_isC hf _ _ _ _
    | exact (mkApp_isC (by assumption)).1
    | exact getD_isC (fun s hs => (mkApp_isC hs).1)

theorem deadSeq_isC (c p : Tm) (ys : DL) : (deadSeq τ τf c p ys).isC = true := by
  unfold deadSeq
  repeat' split
  all_goals first | exact hf _ _ | exact (mkApp_isC (by assumption)).1

theorem insertAtL_isC (c p : Tm) (ys : DL) : (insertAtL τ τf c p ys).isC = true := by
  unfold insertAtL
  repeat' split
  all_goals first | exact hf _ _ | exact deadSeq_isC hf _ _ _ | exact (mkApp_isC (by assumption)).1

theorem limitSeq_isC (c X : Tm) (xs : DL) (P : Option Tm) : (limitSeq τ τf c X xs P).isC = true := by
  unfold limitSeq
  dsimp only
  repeat' split
  all_goals first
    | exact insertAtL_isC hf _ _ _
    | exact getD_isC (fun s hs => (mkApp_isC hs).1)

end

theorem famSeq_isC : ∀ (πf : Fam) (ceil : Tm) (P : Option Tm), (famSeq πf ceil P).isC = true
  | .om, _, P => by unfold famSeq; cases P <;> rfl
  | .xi m q qs, ceil, P => by unfold famSeq; exact mahloVK_isC _ _ _ _ _
  | .psi ζ ζs κ κf γ γs, ceil, P => by
    unfold famSeq
    exact mahloSeq_isC (famSeq_isC κf) _ _ _ _ _ _
  | .none, _, _ => by unfold famSeq; rfl

theorem cseq_isC (π : Tm) (πf : Fam) (X : Tm) (xs : DL) : (cseq π πf X xs).isC = true := by
  unfold cseq
  repeat' split
  all_goals first
    | rfl
    | exact famSeq_isC _ _ _
    | exact mahloSeq_isC (famSeq_isC πf) _ _ _ _ _ _
    | exact limitSeq_isC (famSeq_isC πf) _ _ _ _

/-! ### 後者 -/

theorem isSucc_principal {x : Tm} (hx : isPrincipal x = true) : isSucc x = (x == one) := by
  simp only [isSucc, summands_principal hx, List.getLast?_singleton, Option.some_beq_some]

theorem isSucc_plus {a b : Tm} (hb : b ≠ zero) : isSucc (plus a b) = isSucc b := by
  obtain ⟨h', t', e⟩ := List.exists_cons_of_ne_nil (summands_ne_nil hb)
  simp only [isSucc, summands_plus, e, List.getLast?_cons_cons]

/-- 標準形の項の共終数が後者 ⟺ 最後の加数が `1` -/
theorem dom_eq_one_iff : ∀ {t : Tm}, WNF t → (dom t = .one ↔ isSucc t = true)
  | .zero, _ => by simp [dom_zero, isSucc, summands]
  | .one, _ => by simp [dom_one, isSucc, summands]
  | .K n, _ => by simp [dom_K, isSucc, summands]
  | .plus a b, h => by
    obtain ⟨-, hb, -, hb0⟩ := h.plus
    rw [isSucc_plus hb0, ← dom_eq_one_iff hb, dom_plus]
  | .Om c, h => by
    have hc := h.om.1
    rw [dom_om]
    split
    · simp [isSucc, summands]
    · rename_i hcs
      rw [dom_eq_one_iff hc]
      constructor
      · intro h'; exact absurd h' hcs
      · intro h'; simp [isSucc, summands] at h'
  | .Xi n a, _ => by simp [dom_xi, isSucc, summands]
  | .Psi ζ π X, _ => by
    rw [dom_psi]
    split
    · simp [SeqD.dom_ne_one (cseq_isC _ _ _ _), cs, isSucc, summands]
    · simp [isSucc, summands]

theorem summands_eq_dropLast_one {a : Tm} (hs : isSucc a = true) :
    summands a = (summands a).dropLast ++ [one] := by
  have h : (summands a).getLast? = some one := by simpa [isSucc] using hs
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp h
  rw [hys, List.dropLast_concat]

theorem wnf_pred {a : Tm} (ha : WNF a) : WNF (pred a) := by
  unfold pred
  apply wnf_ofSummands
  have e : (summands a).dropLast ++ (summands a).drop ((summands a).length - 1) = summands a := by
    rw [List.dropLast_eq_take, List.take_append_drop]
  have h := nfl_summands ha
  rw [← e] at h
  exact nfl_append_left h

/-- 後者 `a` は `pred a + 1` -/
theorem succT_pred {a : Tm} (ha : WNF a) (hs : isSucc a = true) : succT (pred a) = a := by
  have e := summands_eq_dropLast_one hs
  have hp := nfl_principal (nfl_summands ha)
  have h1 : summands (succT (pred a)) = summands a := by
    rw [summands_succT, pred, summands_ofSummands _ (fun x hx => hp x (List.dropLast_subset _ hx))]
    exact e.symm
  calc succT (pred a) = ofSummands (summands (succT (pred a))) :=
        (ofSummands_summands _ (succT_WNF (wnf_pred ha))).symm
    _ = ofSummands (summands a) := by rw [h1]
    _ = a := ofSummands_summands a ha

theorem pred_lt {a : Tm} (ha : WNF a) (hs : isSucc a = true) : Lt (pred a) a := by
  have := lt_succT (pred a)
  rwa [succT_pred ha hs] at this

theorem le_pred {a x : Tm} (ha : WNF a) (hs : isSucc a = true) (hx : WNF x) (h : Lt x a) :
    Le x (pred a) :=
  le_of_lt_succT hx (wnf_pred ha) (by rwa [succT_pred ha hs])

theorem fund_of_dom_one {t : Tm} (ξ : Tm) (h : dom t = .one) : fund t ξ = pred t := by
  rw [fund_eq, h]

theorem fund_zero (ξ : Tm) : fund zero ξ = zero := rfl

theorem wnf_ofNatT (n : Nat) : WNF (ofNatT n) := wnf_mulNat WNF.one rfl n

theorem dom_ofNatT (n : Nat) : dom (ofNatT (n + 1)) = .one := by
  rw [dom_eq_one_iff (wnf_ofNatT _)]
  simp only [isSucc, ofNatT, summands_mulNat (x := one) rfl, List.getLast?_replicate]
  simp

theorem fund_ofNatT (n : Nat) (ξ : Tm) : fund (ofNatT (n + 1)) ξ = ofNatT n := by
  rw [fund_of_dom_one ξ (dom_ofNatT n), pred, ofNatT, summands_mulNat rfl, List.dropLast_replicate]
  rfl

/-! ### 共終数が 0 になるのは 0 だけ -/

theorem cmpList_prefix : ∀ (l m m' : List Tm), cmpList (l ++ m) (l ++ m') = cmpList m m'
  | [], _, _ => rfl
  | x :: xs, m, m' => by
    rw [List.cons_append, List.cons_append, cmpList_cons_cons_eq _ _ (cmpP_self x)]
    exact cmpList_prefix xs m m'

/-- 標準形の `Ψ^0_π(X)` では、目標の引数 `r` は `X` 未満 -/
theorem lt_argR {π X r : Tm} (hP : PsiNF zero π X) (hr : argR? π = some r) : Lt r X := by
  have h := hP.Cpi
  cases π with
  | Xi m q =>
    simp only [argR?, Option.some.injEq] at hr; subst hr
    simp only [inC, cmp_self] at h
    simp at h
    exact h.2
  | Psi ζ κ γ =>
    simp only [argR?, Option.some.injEq] at hr; subst hr
    simp only [inC, cmp_self] at h
    simp at h
    exact h.2
  | _ => simp [argR?] at hr

theorem wnf_argR {π r : Tm} (hπ : WNF π) (hr : argR? π = some r) : WNF r := by
  cases π with
  | Xi m q => simp only [argR?, Option.some.injEq] at hr; subst hr; exact hπ.xi.2.1
  | Psi ζ κ γ => simp only [argR?, Option.some.injEq] at hr; subst hr; exact hπ.psi.aF
  | _ => simp [argR?] at hr

/-- 標準形の `Ψ^0_π(X)`（`X` は 0 でない）では、`X` の最後の加数は `r` の対応する残りより大きい（挿入が塞がらない） -/
theorem lt_tailRaw {π X rt : Tm} (hX : WNF X) (hX0 : X ≠ zero) (hP : PsiNF zero π X)
    (h : tailRaw (argR? π) (summands X).dropLast = some rt) :
    Lt rt ((summands X).getLast?.getD zero) := by
  cases hr : argR? π with
  | none => rw [hr] at h; simp [tailRaw] at h
  | some r =>
    rw [hr] at h
    have hrX := lt_argR hP hr
    have hrW := wnf_argR hP.piF hr
    simp only [tailRaw] at h
    split at h
    · rename_i hpre
      simp only [Option.some.injEq] at h
      subst h
      have hne := summands_ne_nil hX0
      have eX : summands X = (summands X).dropLast ++ [(summands X).getLast hne] :=
        (List.dropLast_concat_getLast hne).symm
      have eL : (summands X).getLast?.getD zero = (summands X).getLast hne := by
        rw [List.getLast?_eq_some_getLast hne]; rfl
      rw [eL]
      have er : summands r = (summands X).dropLast ++ (summands r).drop (summands X).dropLast.length := by
        have := (List.take_append_drop (summands X).dropLast.length (summands r)).symm
        rw [hpre.2] at this
        exact this
      have hRmem : (summands X).getLast hne ∈ summands X := List.getLast_mem hne
      have hRp := nfl_principal (nfl_summands hX) _ hRmem
      have hDp : ∀ x, x ∈ (summands r).drop (summands X).dropLast.length → isPrincipal x = true :=
        fun x hx => nfl_principal (nfl_summands hrW) x (List.mem_of_mem_drop hx)
      show cmp _ _ = .lt
      unfold cmp
      rw [summands_ofSummands _ hDp, summands_principal hRp]
      calc cmpList (List.drop (summands X).dropLast.length (summands r)) [(summands X).getLast hne]
          = cmpList ((summands X).dropLast ++ List.drop (summands X).dropLast.length (summands r))
              ((summands X).dropLast ++ [(summands X).getLast hne]) := (cmpList_prefix _ _ _).symm
        _ = cmpList (summands r) (summands X) := by rw [← er, ← eX]
        _ = .lt := by have := hrX; unfold Lt cmp at this; exact this
    · cases h

theorem wnf_tailRaw {r rt : Tm} {pre : List Tm} (hr : WNF r) (h : tailRaw (some r) pre = some rt) :
    WNF rt := by
  simp only [tailRaw] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    apply wnf_ofSummands
    have e := (List.take_append_drop pre.length (summands r)).symm
    have hn := nfl_summands hr
    rw [e] at hn
    exact nfl_append_right hn
  · cases h

theorem mkApp_idx_zero (ceil κ γ : Tm) (pre : List Tm) (R : Tm) (r : SeqD) (c : Tm) :
    mkApp ceil (.idx κ γ) pre R r zero c = some (.app ceil (.idx κ γ) pre R r zero c) := by
  unfold mkApp
  simp [Gen.tgt?]

/-- 標準形の `Ψ^0_π(X)`（`X ≠ 0`）の素の近似は作れる -/
theorem mkApp_plain_ne_none {π X : Tm} (hX : WNF X) (hX0 : X ≠ zero) (hP : PsiNF zero π X) (ceil : Tm)
    (r : SeqD) : mkApp ceil (.psi0 π) (preT (info X).sums) (lastT (info X).sums) r zero zero ≠ none := by
  rw [preT_info, lastT_info]
  unfold mkApp
  simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, Gen.tgt?]
  split
  · simp
  · rename_i rt hrt
    have hlt := lt_tailRaw hX hX0 hP hrt
    have hne := summands_ne_nil hX0
    have hRW : WNF ((summands X).getLast?.getD zero) := by
      rw [List.getLast?_eq_some_getLast hne]
      exact ((nfl_summands hX).1 _ (List.getLast_mem hne)).1
    cases hr : argR? π with
    | none => rw [hr] at hrt; simp [tailRaw] at hrt
    | some r =>
      rw [hr] at hrt
      have hrtW := wnf_tailRaw (wnf_argR hP.piF hr) hrt
      have hleB : leB ((summands X).getLast?.getD zero) rt = false := by
        cases e : leB ((summands X).getLast?.getD zero) rt with
        | false => rfl
        | true =>
          exfalso
          have : cmp ((summands X).getLast?.getD zero) rt ≠ .gt := by simpa [leB] using e
          exact not_lt_of_leY hRW hrtW (le_of_ne_gtY hRW hrtW this) hlt
      simp only [hleB, Bool.false_eq_true, ↓reduceIte]
      repeat' split
      all_goals simp

theorem mahloVK_ne_none (m : Nat) (q : Tm) (qs : DL) (ceil : Tm) (P : Option Tm) :
    mahloVK m q qs ceil P ≠ .none := by
  unfold mahloVK
  dsimp only
  repeat' split
  all_goals first | (apply mkApp_ne_none; assumption) | simp

section
variable {τ : Tm} {τf : Fam} (hf : ∀ c p, famSeq τf c (some p) ≠ .none)
include hf

theorem deadSeqM_ne_none (ceil p Y' : Tm) (ys : DL) : deadSeqM τ τf ceil p Y' ys ≠ .none := by
  unfold deadSeqM
  repeat' split
  all_goals first | exact hf _ _ | (apply mkApp_ne_none; assumption) | simp

theorem insertAtM_ne_none (ceil p Y' : Tm) (ys : DL) : insertAtM τ τf ceil p Y' ys ≠ .none := by
  unfold insertAtM
  repeat' split
  all_goals first | exact hf _ _ | exact deadSeqM_ne_none hf _ _ _ _ | (apply mkApp_ne_none; assumption) | simp

theorem mahloSeq_ne_none (ceil Y' : Tm) (ys : DL) (μ : Tm) (ms : DL) (P : Option Tm) :
    mahloSeq τ τf ceil Y' ys μ ms P ≠ .none := by
  unfold mahloSeq
  simp only [mkApp_idx_zero, Option.getD_some]
  repeat' split
  all_goals first | exact insertAtM_ne_none hf _ _ _ _ | (apply mkApp_ne_none; assumption) | simp

theorem deadSeq_ne_none (ceil p : Tm) (ys : DL) : deadSeq τ τf ceil p ys ≠ .none := by
  unfold deadSeq
  repeat' split
  all_goals first | exact hf _ _ | (apply mkApp_ne_none; assumption) | simp

theorem insertAtL_ne_none (ceil p : Tm) (ys : DL) : insertAtL τ τf ceil p ys ≠ .none := by
  unfold insertAtL
  repeat' split
  all_goals first | exact hf _ _ | exact deadSeq_ne_none hf _ _ _ | (apply mkApp_ne_none; assumption) | simp

theorem limitSeq_ne_none {ceil X : Tm} {xs : DL} (P : Option Tm)
    (hplain : ∀ r, mkApp ceil (.psi0 τ) (preT xs) (lastT xs) r zero zero ≠ none) :
    limitSeq τ τf ceil X xs P ≠ .none := by
  have key : ∀ r, (mkApp ceil (.psi0 τ) (preT xs) (lastT xs) r zero zero).getD .none ≠ .none := by
    intro r
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp (hplain r)
    rw [hs, Option.getD_some]
    exact mkApp_ne_none hs
  unfold limitSeq
  dsimp only
  repeat' split
  all_goals first | exact key _ | exact insertAtL_ne_none hf _ _ _ | simp

end

theorem famSeq_some_ne_none : ∀ {τ : Tm}, WNF τ → IsTgt τ → ∀ ceil p, famSeq (info τ).fam ceil (some p) ≠ .none
  | .Om c, _, _, ceil, p => by rw [info_fam_om]; unfold famSeq; simp
  | .Xi m q, _, _, ceil, p => by rw [info_fam_xi]; unfold famSeq; exact mahloVK_ne_none _ _ _ _ _
  | .Psi ζ κ γ, hw, _, ceil, p => by
    rw [info_fam_psi]
    unfold famSeq
    have hP := hw.psi
    exact mahloSeq_ne_none (famSeq_some_ne_none hP.piF hP.tgt) _ _ _ _ _ _
  | .zero, _, ht, _, _ | .one, _, ht, _, _ | .K _, _, ht, _, _ | .plus _ _, _, ht, _, _ => by
    exfalso
    rcases ht with ⟨c, h, -⟩ | ⟨n, p, h⟩ | ⟨ζ, κ, b, h, -⟩ <;> cases h

theorem not_lt_zero (q : Tm) : ¬ Lt q zero := by
  intro h
  unfold Lt cmp at h
  have key : ∀ l : List Tm, cmpList l [] ≠ .lt := by
    intro l; cases l <;> simp [cmpList]
  exact key _ (by simpa [summands] using h)

/-- 標準形の崩壊 `Ψ^0_π(X)` の列の記述は空でない -/
theorem cs_ne_none {π X : Tm} (h : WNF (Psi zero π X)) : cs π X ≠ .none := by
  have hP := h.psi
  have hf : ∀ c p, famSeq (info π).fam c (some p) ≠ .none := famSeq_some_ne_none hP.piF hP.tgt
  unfold cs cseq
  split
  · rename_i hX
    subst hX
    rcases hP.tgt with ⟨c, rfl, -⟩ | ⟨n, q, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩
    · simp
    · exact absurd (lt_argR hP (r := q) rfl) (not_lt_zero q)
    · exact absurd (lt_argR hP (r := b) rfl) (not_lt_zero b)
  · rename_i hX0
    split
    · split
      · rename_i hv
        rcases hP.tgt with ⟨c, rfl, -⟩ | ⟨n, q, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩
        · simp [validR, argR?] at hv
        · rw [info_fam_xi]; unfold famSeq; exact mahloVK_ne_none _ _ _ _ _
        · rw [info_fam_psi]
          unfold famSeq
          have hPκ := hP.piF.psi
          exact mahloSeq_ne_none (famSeq_some_ne_none hPκ.piF hPκ.tgt) _ _ _ _ _ _
      · exact mahloSeq_ne_none hf _ _ _ _ _ _
    · exact limitSeq_ne_none hf _ (mkApp_plain_ne_none hP.aF hX0 hP π)

/-- 標準形の項の共終数が 0 ⟺ 項が 0 -/
theorem dom_eq_zero_iff : ∀ {t : Tm}, WNF t → (dom t = .zero ↔ t = zero)
  | .zero, _ => by simp [dom_zero]
  | .one, _ => by simp [dom_one]
  | .K n, _ => by simp [dom_K]
  | .plus a b, h => by
    obtain ⟨-, hb, -, hb0⟩ := h.plus
    simp only [dom_plus, reduceCtorEq, iff_false]
    rw [dom_eq_zero_iff hb]
    exact hb0
  | .Om c, h => by
    obtain ⟨hc, hc0, -⟩ := h.om
    simp only [dom_om, reduceCtorEq, iff_false]
    split
    · simp
    · rw [dom_eq_zero_iff hc]; exact hc0
  | .Xi n a, _ => by simp [dom_xi]
  | .Psi ζ π X, h => by
    simp only [dom_psi, reduceCtorEq, iff_false]
    split
    · rename_i hζ
      subst hζ
      intro e
      exact cs_ne_none h (SeqD.eq_none_of_dom (cseq_isC _ _ _ _) e)
    · simp

end RTKA.Fund
