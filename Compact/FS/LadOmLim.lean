import Compact.FS.LadAll

/-! `Ω_c`（`c` 極限）の下界：`Ω_{c[n]+1}` の区間の元の 0 番目は `Ω_{c[n]+1}` 以上。

* 層の床（`lf_psi_om`）：`Ω_c` への崩壊の 0 番目は `Ω_c` の底 `Ω̂(c-1)` 以上。目標が `Ω_c` の崩壊の列は
  種の倍数か、`Ψ^0_{Ω_c}` の近似（`cs_om_shape`）。
* `Ω` の写し（`lbi_om`）：`LBI x y` で `(x, y]` に `Ω` の不動点がなければ `LBI Ω_{x+1} Ω_{y+1}`。 -/

namespace RTKA.Fund

open Tm W

/-- `Ω_c` への崩壊は `Ω_c` の底より大きい -/
theorem omBase_lt_psi {c β : Tm} (ht : WNF (.Psi .zero (.Om c) β)) : Lt (omBase c) (.Psi .zero (.Om c) β) := by
  have hπ := ht.psi.piF
  have hs : isSucc c = true := (WNF.psiOm ht).2.2.1
  have hb0 := wnf_base_om hπ hs
  have h0 : Lt (omBase c) (.Psi .zero (.Om c) .zero) := (mul_base_lt hb0).2.2
  by_cases hβ : β = .zero
  · subst hβ
    exact h0
  · exact lt_transY (mul_base_lt hb0).1 hb0 ht h0
      (psi_lt_psi_of_arg hb0 ht (zero_lt hβ) (fun w hw => by simp [fr] at hw))

theorem omBase_wnf {c : Tm} (hc : WNF (.Om c)) (hs : isSucc c = true) :
    WNF (omBase c) ∧ isPrincipal (omBase c) = true :=
  ⟨(mul_base_lt (wnf_base_om hc hs)).1, (mul_base_lt (wnf_base_om hc hs)).2.1⟩

/-- 標準形の `0` でない項は `1` 未満でない -/
theorem not_ltB_one {p : Tm} (hp : WNF p) (hp0 : p ≠ .zero) : ltB p .one = false := by
  cases e : ltB p .one with
  | false => rfl
  | true => exact absurd (lt_oneY hp (ltB_iff.mp e)) hp0

/-- 目標が `Ω_c` なら Mahlo 添字に種を持てない -/
theorem idxOK_om {c p : Tm} (hp : WNF p) (hp0 : p ≠ .zero) : idxOK (.Om c) p = false := by
  unfold idxOK mOfT mOf
  simp [not_ltB_one hp hp0]

/-- 目標が `Ω_c` の素の近似は必ず作れる -/
theorem mkApp_om_plain (ceil c : Tm) (pre : List Tm) (R : Tm) (r : SeqD) :
    mkApp ceil (.psi0 (.Om c)) pre R r .zero .zero =
      some (.app ceil (.psi0 (.Om c)) pre R r .zero (kAdj (.Om c) ceil (.psi0 (.Om c)) pre R r)) := by
  unfold mkApp
  simp [Gen.tgt?, argR?, tailRaw]

/-- 極限の引数の素の近似の 0 番目は標準形の崩壊 -/
theorem plain_first_wnf {π X : Tm} (ht : WNF (.Psi .zero π X)) (hX0 : X ≠ .zero)
    (hl : ¬ isSucc X = true) {s0 : SeqD}
    (hs0 : mkApp π (.psi0 π) (preT (info X).sums) (lastT (info X).sums) (lastS (info X).sums) .zero .zero
      = some s0) :
    WNF s0.first ∧ ∃ A, s0.first = .Psi .zero π A := by
  have hP := ht.psi
  have hX := hP.aF
  have hπF := hP.piF
  have hsum := summands_pre_last hX0
  have hlast : lastS (info X).sums = (info (lastT (info X).sums)).seq := lastS_coh (coh_sums X)
  obtain ⟨pre, hpre⟩ : ∃ pre, pre = preT (info X).sums := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = lastT (info X).sums := ⟨_, rfl⟩
  rw [← hpre, ← hR] at hsum hs0
  rw [← hR] at hlast
  rw [hlast] at hs0
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
  have hRI := seqI_all R hRF
  have hlow : ∀ (σ : Tm), IsTgt σ → (info R).seq.dom = .big σ → BigUB R σ (info R).seq →
      Lt σ π → ¬ Lt σ π → WNF (.Psi .zero σ X) := fun _ _ _ _ h h' => absurd h h'
  have hπK : ∀ m, 1 ≤ m → ¬ Lt (.K m) π → Lt π (.K m) := fun m hm h => by
    rcases triY hπF (WNF.K' hm) with h' | h' | h'
    · exact h'
    · exact absurd h' (IsTgt.ne_K hP.tgt m)
    · exact absurd h' h
  have S0 : SeedHyp π X .zero R := seed_zero hP.tgt.ne_zero hR0
  obtain ⟨hx0F, hx0R⟩ := first_good hRI h0 h1
  have hsum0 : summands X = pre ++ R :: [] := hsum
  have pk0 := pack_mkApp (genPsi0 π) ht hsum0 S0 hRne hx0F hx0R hs0 (IdxHyp.zero ht) (zero_le _) hRI h0 h1
    hRp hπF (Or.inl rfl) hlow hπK fun _ hd => dom_ne_succK hd
  obtain ⟨P', x₀, -, hfirst, H₀, -, -⟩ := pk0.form pk0.first_mem
  exact ⟨hfirst ▸ H₀.hnf, _, hfirst⟩

/-- 目標が `Ω_c` の崩壊（引数 `0` でない）の列は、底以上の種の倍数か、`Ψ^0_{Ω_c}` の近似（一つずらしたものを含む） -/
theorem cs_om_shape {c V : Tm} (ht : WNF (.Psi .zero (.Om c) V)) (hV0 : V ≠ .zero) :
    (∃ p, cs (.Om c) V = .mul p 2 ∧ WNF p ∧ isPrincipal p = true ∧ Le (omBase c) p) ∨
    ∃ τ pre R r P k, cs (.Om c) V = .app τ (.psi0 (.Om c)) pre R r P k ∨
      cs (.Om c) V = .shift (.app τ (.psi0 (.Om c)) pre R r P k) := by
  have hV := ht.psi.aF
  have hπ := ht.psi.piF
  have hcs : isSucc c = true := (WNF.psiOm ht).2.2.1
  have happ : ∀ {o : Option SeqD} {s : SeqD}, o = some s → (∃ ceil pre R r P k, o = mkApp ceil (.psi0 (.Om c)) pre R r P k) →
      ∃ τ pre R r P k, s = .app τ (.psi0 (.Om c)) pre R r P k ∨ s = .shift (.app τ (.psi0 (.Om c)) pre R r P k) := by
    intro o s ho ⟨ceil, pre, R, r, P, k, e⟩
    rw [e] at ho
    obtain ⟨c', h | h⟩ := mkApp_eq_some ho
    · exact ⟨_, _, _, _, _, _, Or.inl h⟩
    · exact ⟨_, _, _, _, _, _, Or.inr h⟩
  by_cases hs : isSucc V = true
  · rw [cs_om_succ ht hs]
    have hp := wnf_psi_om_pred ht hs
    have hp0 : Tm.Psi .zero (.Om c) (pred V) ≠ .zero := fun e => by cases e
    have hpb : Le (omBase c) (.Psi .zero (.Om c) (pred V)) := Or.inr (omBase_lt_psi hp)
    have hmul : famSeq .om (.Om c) (some (.Psi .zero (.Om c) (pred V))) = .mul (.Psi .zero (.Om c) (pred V)) 2 := by
      unfold famSeq; rfl
    unfold insertAtM
    cases hsp : splitGtD (.Psi .zero (.Om c) (pred V)) (info V).sums.dropLast with
    | none => exact Or.inl ⟨_, hmul, hp, rfl, hpb⟩
    | some q =>
      obtain ⟨pre, R, r⟩ := q
      dsimp only
      rw [idxOK_om hp hp0, Bool.and_false]
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hm : mkApp (.Om c) (.psi0 (.Om c)) pre R r (.Psi .zero (.Om c) (pred V)) .zero with
      | some s => exact Or.inr (happ hm ⟨_, _, _, _, _, _, rfl⟩)
      | none =>
        dsimp only
        unfold deadSeqM
        rw [idxOK_om hp hp0]
        exact Or.inl ⟨_, hmul, hp, rfl, hpb⟩
  · have hlim : cs (.Om c) V = limitSeq (.Om c) .om (.Om c) V (info V).sums none := by
      unfold cs cseq
      rw [ite_eq_right hV0]
      have hd := lastS_dom hV hV0
      split
      · rename_i h
        rw [hd] at h
        exact absurd ((dom_eq_one_iff hV).mp h) hs
      · rfl
    rw [hlim]
    unfold limitSeq
    dsimp only
    rw [mkApp_om_plain, Option.getD_some]
    obtain ⟨hfw, A, hfA⟩ := plain_first_wnf ht hV0 hs (mkApp_om_plain _ _ _ _ _)
    have hpl : ∃ τ pre R r P k, SeqD.app (.Om c) (.psi0 (.Om c)) (preT (info V).sums) (lastT (info V).sums)
        (lastS (info V).sums) .zero (kAdj (.Om c) (.Om c) (.psi0 (.Om c)) (preT (info V).sums)
          (lastT (info V).sums) (lastS (info V).sums)) = .app τ (.psi0 (.Om c)) pre R r P k ∨
        SeqD.app (.Om c) (.psi0 (.Om c)) (preT (info V).sums) (lastT (info V).sums)
        (lastS (info V).sums) .zero (kAdj (.Om c) (.Om c) (.psi0 (.Om c)) (preT (info V).sums)
          (lastT (info V).sums) (lastS (info V).sums)) = .shift (.app τ (.psi0 (.Om c)) pre R r P k) :=
      ⟨_, _, _, _, _, _, Or.inl rfl⟩
    have hmo : ∀ q : Option Tm, maxOpt none q = q := fun q => by cases q <;> rfl
    rw [hmo]
    cases hm : maxL (frB (.Om c) V) with
    | none => exact Or.inr hpl
    | some p =>
      dsimp only
      have hpm : p ∈ fr (.Om c) V := by
        have := maxL_mem hm
        rwa [frB_eq_fr] at this
      have hpF : WNF p := hV.of_mem_subs (fr_spec hpm).1
      have hpp : isPrincipal p = true := by
        rcases fr_node hpm with ⟨m, a, rfl⟩ | ⟨s, q, a, rfl⟩ <;> rfl
      have hp0 : p ≠ .zero := fun e => by rw [e] at hpp; cases hpp
      split
      · exact Or.inr hpl
      · rename_i h2
        split
        · rw [mkApp_om_plain, Option.getD_some]
          exact Or.inr ⟨_, _, _, _, _, _, Or.inl rfl⟩
        · rename_i h3
          -- 種 `p` は素の近似の 0 番目以上
          have hfw' : WNF (.Psi .zero (.Om c) A) := hfA ▸ hfw
          have hle : Le (omBase c) p := by
            have h4 : ¬ Lt p (.Psi .zero (.Om c) A) := fun h => h2 (by rw [hfA]; exact ltB_iff.mpr h)
            exact le_transY (omBase_wnf hπ hcs).1 hfw' hpF (Or.inr (omBase_lt_psi hfw'))
              (le_of_not_ltY hpF hfw' h4)
          have hmul : famSeq .om (.Om c) (some p) = .mul p 2 := by unfold famSeq; rfl
          unfold insertAtL
          cases hsp : splitGtD p (info V).sums with
          | none => exact Or.inl ⟨p, hmul, hpF, hpp, hle⟩
          | some q =>
            obtain ⟨pre, R, r⟩ := q
            dsimp only
            rw [idxOK_om hpF hp0, Bool.and_false]
            simp only [Bool.false_eq_true, ↓reduceIte]
            cases hm2 : mkApp (.Om c) (.psi0 (.Om c)) pre R r p .zero with
            | some s => exact Or.inr (happ hm2 ⟨_, _, _, _, _, _, rfl⟩)
            | none =>
              dsimp only
              unfold deadSeq
              rw [idxOK_om hpF hp0]
              exact Or.inl ⟨p, hmul, hpF, hpp, hle⟩

/-- 共終数が `0`・後者でなければ、0 番目は列の記述の 0 番目 -/
theorem fund_zero_first {t : Tm} (h0 : dom t ≠ .zero) (h1 : dom t ≠ .one) : fund t .zero = (info t).seq.first := by
  rw [fund_eq]
  unfold SeqD.first
  cases hd : dom t with
  | zero => exact absurd hd h0
  | one => exact absurd hd h1
  | omega =>
    show fundNat t (natOf .zero) = _
    rw [show (info t).seq.dom = dom t from rfl, hd]
    rfl
  | big σ =>
    show fundBig t (if ltB .zero σ = true then .zero else .zero) = _
    have e : (if ltB Tm.zero σ = true then Tm.zero else Tm.zero) = .zero := by split <;> rfl
    rw [e, show (info t).seq.dom = dom t from rfl, hd]
    rfl

/-- `Ψ^0_π` の近似の列の 0 番目は `Ψ^0_π` の崩壊 -/
theorem app_first_psi (τ π : Tm) (pre : List Tm) (R : Tm) (r : SeqD) (P c : Tm) :
    ∃ A, (SeqD.app τ (.psi0 π) pre R r P c).first = .Psi .zero π A := by
  unfold SeqD.first
  cases hd : r.dom with
  | big σ =>
    by_cases hl : ltB σ τ = true
    · have e : (SeqD.app τ (.psi0 π) pre R r P c).dom = .big σ := by simp [SeqD.dom, hd, hl]
      rw [e]
      exact ⟨combine (.psi0 π) pre c P (r.big .zero), rfl⟩
    · have e : (SeqD.app τ (.psi0 π) pre R r P c).dom = .omega := by simp [SeqD.dom, hd, hl]
      rw [e]
      refine ⟨argOf τ σ (.psi0 π) pre R r c P (gam τ σ (.psi0 π) pre R r c P 0), ?_⟩
      show SeqD.nat (.app τ (.psi0 π) pre R r P c) 0 = _
      simp only [SeqD.nat, hd, ite_eq_right hl]
      rfl
  | zero =>
    have e : (SeqD.app τ (.psi0 π) pre R r P c).dom = .omega := by simp [SeqD.dom, hd]
    rw [e]
    refine ⟨combine (.psi0 π) pre c P (r.nat 0), ?_⟩
    show SeqD.nat (.app τ (.psi0 π) pre R r P c) 0 = _
    simp only [SeqD.nat, hd]
    rfl
  | one =>
    have e : (SeqD.app τ (.psi0 π) pre R r P c).dom = .omega := by simp [SeqD.dom, hd]
    rw [e]
    refine ⟨combine (.psi0 π) pre c P (r.nat 0), ?_⟩
    show SeqD.nat (.app τ (.psi0 π) pre R r P c) 0 = _
    simp only [SeqD.nat, hd]
    rfl
  | omega =>
    have e : (SeqD.app τ (.psi0 π) pre R r P c).dom = .omega := by simp [SeqD.dom, hd]
    rw [e]
    refine ⟨combine (.psi0 π) pre c P (r.nat 0), ?_⟩
    show SeqD.nat (.app τ (.psi0 π) pre R r P c) 0 = _
    simp only [SeqD.nat, hd]
    rfl

theorem shift_app_first_psi (τ π : Tm) (pre : List Tm) (R : Tm) (r : SeqD) (P c : Tm) :
    ∃ A, (SeqD.shift (.app τ (.psi0 π) pre R r P c)).first = .Psi .zero π A := by
  unfold SeqD.first
  have hdom : (SeqD.shift (.app τ (.psi0 π) pre R r P c)).dom = (SeqD.app τ (.psi0 π) pre R r P c).dom := rfl
  rw [hdom]
  cases hd : r.dom with
  | big σ =>
    by_cases hl : ltB σ τ = true
    · have e : (SeqD.app τ (.psi0 π) pre R r P c).dom = .big σ := by simp [SeqD.dom, hd, hl]
      rw [e]
      exact ⟨combine (.psi0 π) pre c P (r.big .zero), rfl⟩
    · have e : (SeqD.app τ (.psi0 π) pre R r P c).dom = .omega := by simp [SeqD.dom, hd, hl]
      rw [e]
      refine ⟨argOf τ σ (.psi0 π) pre R r c P (gam τ σ (.psi0 π) pre R r c P 1), ?_⟩
      show SeqD.nat (.app τ (.psi0 π) pre R r P c) 1 = _
      simp only [SeqD.nat, hd, ite_eq_right hl]
      rfl
  | zero =>
    have e : (SeqD.app τ (.psi0 π) pre R r P c).dom = .omega := by simp [SeqD.dom, hd]
    rw [e]
    refine ⟨combine (.psi0 π) pre c P (r.nat 1), ?_⟩
    show SeqD.nat (.app τ (.psi0 π) pre R r P c) 1 = _
    simp only [SeqD.nat, hd]
    rfl
  | one =>
    have e : (SeqD.app τ (.psi0 π) pre R r P c).dom = .omega := by simp [SeqD.dom, hd]
    rw [e]
    refine ⟨combine (.psi0 π) pre c P (r.nat 1), ?_⟩
    show SeqD.nat (.app τ (.psi0 π) pre R r P c) 1 = _
    simp only [SeqD.nat, hd]
    rfl
  | omega =>
    have e : (SeqD.app τ (.psi0 π) pre R r P c).dom = .omega := by simp [SeqD.dom, hd]
    rw [e]
    refine ⟨combine (.psi0 π) pre c P (r.nat 1), ?_⟩
    show SeqD.nat (.app τ (.psi0 π) pre R r P c) 1 = _
    simp only [SeqD.nat, hd]
    rfl

/-- 層の床：`Ω_c` への崩壊の 0 番目は `Ω_c` の底以上 -/
theorem lf_psi_om {c V : Tm} (ht : WNF (.Psi .zero (.Om c) V)) :
    Le (omBase c) (fund (.Psi .zero (.Om c) V) .zero) := by
  have hπ := ht.psi.piF
  have hcs : isSucc c = true := (WNF.psiOm ht).2.2.1
  obtain ⟨hBF, hBp⟩ := omBase_wnf hπ hcs
  by_cases hV0 : V = .zero
  · subst hV0
    rw [fund_psi_om_zero]
    show Le (omBase c) (mulNat (omBase c) 2)
    exact Or.inr (lt_plus_leftY (wnf_mulNat hBF hBp 2))
  have hcsI := cseq_isC (.Om c) (info (.Om c)).fam V (info V).sums
  have hd0 : dom (.Psi .zero (.Om c) V) ≠ .zero := fun e => cs_ne_none ht (SeqD.eq_none_of_dom hcsI e)
  have hd1 : dom (.Psi .zero (.Om c) V) ≠ .one := SeqD.dom_ne_one hcsI
  have hf := fund_wnf ht WNF.zero
  rw [fund_zero_first hd0 hd1] at hf ⊢
  show Le (omBase c) (cs (.Om c) V).first
  change WNF (cs (.Om c) V).first at hf
  rcases cs_om_shape ht hV0 with ⟨p, e, hpF, hpp, hle⟩ | ⟨τ, pre, R, r, P, k, e | e⟩
  · rw [e]
    unfold SeqD.first
    simp only [SeqD.dom, SeqD.nat]
    exact le_transY hBF hpF (wnf_mulNat hpF hpp 2) hle (Or.inr (lt_plus_leftY (wnf_mulNat hpF hpp 2)))
  · rw [e] at hf ⊢
    obtain ⟨A, hA⟩ := app_first_psi τ (.Om c) pre R r P k
    rw [hA] at hf ⊢
    exact Or.inr (omBase_lt_psi hf)
  · rw [e] at hf ⊢
    obtain ⟨A, hA⟩ := shift_app_first_psi τ (.Om c) pre R r P k
    rw [hA] at hf ⊢
    exact Or.inr (omBase_lt_psi hf)

/-! ### `Ω` の写し -/

/-- `K_m` と `Ω` の不動点は `Ω̂` で動かない -/
theorem omHat_fixed {z : Tm} (h : (∃ m, z = .K m) ∨ IsOF z) : omHat z = z := by
  have hz0 : z ≠ .zero := by
    rcases h with ⟨m, rfl⟩ | hO
    · intro e; cases e
    · intro e; rw [e] at hO; rcases hO with ⟨n, a, e'⟩ | ⟨ξ, π, a, e', -, -⟩ <;> cases e'
  have hpf : (isPrincipal z && omegaFixed z) = true := by
    rcases h with ⟨m, rfl⟩ | hO
    · rfl
    · simp [hO.principal, hO.fixed]
  unfold omHat
  rw [ite_eq_right hz0, ite_eq_left hpf]

/-- 不動点のない区間の仮定から、`K_m`・`Ω` の不動点はその区間にない -/
theorem not_fixed_of {z : Tm} (h : (∃ m, z = .K m) ∨ IsOF z) (hz : omHat z = .Om z) : False := by
  rw [omHat_fixed h] at hz
  rcases h with ⟨m, rfl⟩ | hO
  · cases hz
  · rcases hO with ⟨n, a, rfl⟩ | ⟨ξ, π, a, rfl, -, -⟩ <;> cases hz

theorem succT_le_succT {a b : Tm} (ha : WNF a) (hb : WNF b) (h : Le a b) : Le (succT a) (succT b) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (succT_lt_succT ha hb h)

/-- `Ω` の写し：`LBI x y` で `(x, y]` に `Ω` の不動点がなければ `LBI Ω_{x+1} Ω_{y+1}` -/
theorem lbi_om {x y : Tm} (hx : WNF x) (hy : WNF y) (hxy : Lt x y) (hL : LBI x y)
    (hfix : ∀ z, WNF z → Lt x z → Le z y → omHat z = .Om z) :
    LBI (.Om (sc x)) (.Om (sc y)) := by
  intro w hw h1 h2
  have hOx : WNF (.Om (sc x)) := WNF.om_succT hx
  have hOy : WNF (.Om (sc y)) := WNF.om_succT hy
  have hsx := succT_WNF hx
  have hsy := succT_WNF hy
  have hxs : Lt x (sc x) := lt_succT x
  have hxO : Lt x (.Om (sc x)) := lt_transY hx hsx hOx hxs hOx.om.2.2
  have hxw : Lt x w := lt_transY hx hOx hw hxO h1
  have hf0 := fund_wnf hw WNF.zero
  -- 区間の不動点（`K_m`・`Ω` の不動点）は仮定と矛盾する
  have hnofix : (∃ m, w = .K m) ∨ IsOF w → Lt w (sc y) → False := fun hfx hws =>
    not_fixed_of hfx (hfix w hw hxw (le_of_lt_succT hw hy hws))
  rcases h2 with e | h2
  · -- `w = Ω_{y+1}`：0 番目は `Ψ^0_{Ω_{y+1}}(0)`
    subst e
    rw [fund_om_succ (c := sc y) (isSucc_succT y)]
    have hb := wnf_base_om hOy (isSucc_succT y)
    refine le_of_not_ltY hb hOx fun h => ?_
    have h3 := (lt_psi_omY hb hsx).mp h
    exact not_lt_of_leY hsy hsx h3 (succT_lt_succT hx hy hxy)
  -- `w < Ω_{y+1}`
  cases w with
  | zero => exact absurd h1 (not_lt_zero _)
  | one => exact absurd (lt_oneY hOx h1) (by intro e; cases e)
  | plus a b =>
    have hle : Le (.Om (sc x)) a := (lt_prin_plus_iffY hOx rfl hw).mp h1
    rw [fund_plus hw]
    exact le_transY hOx hw.plus.1 (wnf_oadd hw.plus.1 (fund_wnf hw.plus.2.1 WNF.zero)) hle
      (le_oadd_left hw.plus.1 (fund_wnf hw.plus.2.1 WNF.zero))
  | K m =>
    exact (hnofix (Or.inl ⟨m, rfl⟩) ((lt_K_omY hw.k hsy).mp h2)).elim
  | Xi m q =>
    exact (hnofix (Or.inr (Or.inl ⟨m, q, rfl⟩)) ((lt_OF_omG (Or.inl ⟨m, q, rfl⟩) hw hsy).mp h2)).elim
  | Om e =>
    have heF := hw.om.1
    have h3 : Lt (sc x) e := (lt_om_iffY hsx heF).mp h1
    have h4 : Lt e (sc y) := (lt_om_iffY heF hsy).mp h2
    by_cases hs : isSucc e = true
    · rw [fund_om_succ hs]
      have hb := wnf_base_om hw hs
      refine le_of_not_ltY hb hOx fun h => ?_
      exact not_lt_of_leY heF hsx ((lt_psi_omY hb hsx).mp h) h3
    · rw [fund_om_lim hw hs]
      have hxe : Lt x e := lt_transY hx hsx heF hxs h3
      have h5 := hL e heF hxe (le_of_lt_succT heF hy h4)
      have he0 := fund_wnf heF WNF.zero
      exact le_om_of_leY hsx (succT_WNF he0) (succT_le_succT hx he0 h5)
  | Psi ζ ρ V =>
    rcases hw.shape with ⟨c', rfl, rfl⟩ | hsh
    · -- `Ω` への崩壊：層の床
      have hc' := hw.psiOm
      have h3 : Lt (sc x) c' := (lt_om_psiY hw).mp h1
      have h4 : Le c' (sc y) := (lt_psi_omY hw hsy).mp h2
      have hc'F := hc'.1
      have hpF := wnf_pred hc'F
      have hc'e : succT (pred c') = c' := succT_pred hc'F hc'.2.2.1
      have h5 : Lt x (pred c') := by
        have := le_of_lt_succT hsx hpF (by rw [hc'e]; exact h3)
        exact lt_of_lt_of_leY hx hsx hpF hxs this
      have h6 : Le (pred c') y := le_of_lt_succT hpF hy (lt_of_lt_of_leY hpF hc'F hsy (pred_lt hc'F hc'.2.2.1) h4)
      have hfx := hfix (pred c') hpF h5 h6
      have hc1 : c' ≠ .one := fun e => by
        rw [e] at h3
        exact absurd (lt_oneY hsx h3) (succT_ne_zero x)
      have hB : omBase c' = .Om (pred c') := by
        unfold omBase
        rw [ite_eq_right hc1, hfx]
      have hLF := lf_psi_om hw
      rw [hB] at hLF
      refine le_transY hOx (hB ▸ (omBase_wnf hc'.2.1 hc'.2.2.1).1) hf0 ?_ hLF
      exact le_om_of_leY hsx hpF (succT_leY hx hpF h5)
    · have hO : IsOF (.Psi ζ ρ V) := IsOF.psi hw (notOm_of_shape hsh)
      exact (hnofix (Or.inr hO) ((lt_OF_omG hO hw hsy).mp h2)).elim

/-! ### 隣り合う項の間に `Ω` の不動点はない -/

theorem fixed_cases {z : Tm} (hz : WNF z) (hz0 : z ≠ .zero) (h : ¬ omHat z = .Om z) :
    (∃ m, z = .K m) ∨ IsOF z := by
  rcases omHat_cases hz hz0 with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact absurd h1 h
  · exact h2

theorem lt_om_K_iff {a : Tm} {m : Nat} (ha : WNF a) (hm : 1 ≤ m) (hO : WNF (.Om a)) :
    Lt (.Om a) (.K m) ↔ Lt a (.K m) := by
  rw [lt_K_iffY hO hm, lt_K_iffY ha hm]
  simp only [lev]

/-- 不動点 `z` は `Ω_{a+1}` との比較で `a` との比較に移る -/
theorem fixed_om_succ_lt {a z : Tm} (ha : WNF a) (hz : WNF z) (hfx : (∃ m, z = .K m) ∨ IsOF z)
    (h : Lt (.Om (sc a)) z) : Lt a z := by
  have hsa := succT_WNF ha
  have hOa : WNF (.Om (sc a)) := WNF.om_succT ha
  rcases hfx with ⟨m, rfl⟩ | hO
  · exact lt_transY ha hsa hz (lt_succT a) ((lt_om_K_iff hsa hz.k hOa).mp h)
  · exact lt_transY ha hsa hz (lt_succT a) ((lt_om_OFG hO).mp h)

theorem fixed_lt_om_succ {b z : Tm} (hb : WNF b) (hz : WNF z) (hfx : (∃ m, z = .K m) ∨ IsOF z)
    (h : Le z (.Om (sc b))) : Le z b := by
  have hsb := succT_WNF hb
  rcases h with e | h
  · rcases hfx with ⟨m, rfl⟩ | hO
    · cases e
    · rw [e] at hO
      rcases hO with ⟨n, q, e'⟩ | ⟨ξ, π, q, e', -, -⟩ <;> cases e'
  rcases hfx with ⟨m, rfl⟩ | hO
  · exact le_of_lt_succT hz hb ((lt_K_omY hz.k hsb).mp h)
  · exact le_of_lt_succT hz hb ((lt_OF_omG hO hz hsb).mp h)

theorem omHat_of_not_fixed {z : Tm} (hz : WNF z) (hz0 : z ≠ .zero)
    (h : (∃ m, z = .K m) ∨ IsOF z → False) : omHat z = .Om z :=
  Classical.byContradiction fun hn => h (fixed_cases hz hz0 hn)

/-- `ω` 型の `c`（`Ω_c` が標準形）の隣り合う項の間に `Ω` の不動点はない -/
theorem nofix_nat : ∀ (c : Tm), WNF (.Om c) → ¬ isSucc c = true → dom c = .omega →
    ∀ n z, WNF z → Lt ((info c).seq.nat n) z → Le z ((info c).seq.nat (n + 1)) → omHat z = .Om z := by
  intro c
  induction hsz : c.size using Nat.strongRecOn generalizing c with
  | ind N ih =>
  intro hO hs hd n z hz h1 h2
  have hcF := hO.om.1
  have hG := (seqI_dom_nat hcF hd).1.good
  have hz0 : z ≠ .zero := ne_zero_of_lt h1
  refine omHat_of_not_fixed hz hz0 fun hfx => ?_
  have hzp : isPrincipal z = true := by
    rcases hfx with ⟨m, rfl⟩ | hO'
    · rfl
    · exact hO'.principal
  cases c with
  | zero => exact absurd hd (by simp [dom, info, SeqD.dom])
  | one => exact hs rfl
  | K m => exact absurd hd (by simp [dom_K])
  | Xi m q => exact absurd hd (by simp [dom_xi])
  | plus a b =>
    obtain ⟨ha, hb, hap, -⟩ := hcF.plus
    have hd' : dom b = .omega := hd
    have hGb := (seqI_dom_nat hb hd').1
    have hy := hGb.good (n + 1)
    have hy0 : (info b).seq.nat (n + 1) ≠ .zero := hGb.pos (n + 1)
    have hsy := summands_le_of_le ha hap hb hy.1 (summands_le_head_plus hcF) (Or.inr hy.2.1)
    change Lt (oadd a ((info b).seq.nat n)) z at h1
    change Le z (oadd a ((info b).seq.nat (n + 1))) at h2
    rw [oadd_prin_eq hap hy.1 hy0 hsy] at h2
    have hP : WNF (.plus a ((info b).seq.nat (n + 1))) := by
      rw [← oadd_prin_eq hap hy.1 hy0 hsy]; exact wnf_oadd ha hy.1
    have hza : Le z a := by
      rcases h2 with e | h2
      · rw [e] at hzp; cases hzp
      · exact (lt_prin_plus_iffY hz hzp hP).mp h2
    exact not_lt_of_leY hz (wnf_oadd ha (hGb.good n).1)
      (le_transY hz ha (wnf_oadd ha (hGb.good n).1) hza (le_oadd_left ha (hGb.good n).1)) h1
  | Om e =>
    have hes : ¬ isSucc e = true := fun h => by
      have : dom (.Om e) = .big (.Om e) := by rw [dom_om, ite_eq_left h]
      rw [this] at hd; cases hd
    have hd' : dom e = .omega := by rw [dom_om, ite_eq_right hes] at hd; exact hd
    have heO : WNF (.Om e) := hcF
    have heF := heO.om.1
    have hGe := (seqI_dom_nat heF hd').1.good
    have einf : (info (.Om e)).seq = .om (info e).seq := by simp [info, hes]
    rw [einf] at h1 h2
    change Lt (.Om (sc ((info e).seq.nat n))) z at h1
    change Le z (.Om (sc ((info e).seq.nat (n + 1)))) at h2
    have h3 := fixed_om_succ_lt (hGe n).1 hz hfx h1
    have h4 := fixed_lt_om_succ (hGe (n + 1)).1 hz hfx h2
    have hlt : e.size < N := by rw [← hsz]; simp only [Tm.size]; omega
    exact not_fixed_of hfx (ih e.size hlt e rfl heO hes hd' n z hz h3 h4)
  | Psi ζ ρ X =>
    by_cases hζ : ζ = .zero
    · subst hζ
      rcases hcF.shape with ⟨d, rfl, -⟩ | hsh
      · -- `Ω_d` への崩壊：隣り合う項は `(Ω̂(d-1), Ω_d)` にあり、不動点はない
        have hψ := hcF
        have hd1 := (WNF.psiOm hψ).2.2.1
        have hdF := (WNF.psiOm hψ).1
        have hpF := wnf_pred hdF
        have hc2 : Lt ((info (.Psi .zero (.Om d) X)).seq.nat (n + 1)) (.Om d) :=
          lt_transY (hG (n + 1)).1 hcF hψ.psi.piF (hG (n + 1)).2.1 (lt_psi_targetY hψ)
        have hzd : Lt z (.Om d) := lt_of_le_of_ltY hz (hG (n + 1)).1 hψ.psi.piF h2 hc2
        have hzpd : Le z (pred d) := by
          have e := succT_pred hdF hd1
          rcases hfx with ⟨m, rfl⟩ | hO'
          · exact le_of_lt_succT hz hpF (by rw [e]; exact (lt_K_omY hz.k hdF).mp hzd)
          · exact le_of_lt_succT hz hpF (by rw [e]; exact (lt_OF_omG hO' hz hdF).mp hzd)
        -- `c[n] ≥ c[0] ≥ Ω̂(d-1) ≥ d-1`
        have hf0 : Le (omBase d) ((info (.Psi .zero (.Om d) X)).seq.nat 0) := by
          have := lf_psi_om hψ
          rwa [show fund (.Psi .zero (.Om d) X) .zero = fund (.Psi .zero (.Om d) X) (ofNatT 0) from rfl,
            fund_omega hd] at this
        have hBF := (omBase_wnf hψ.psi.piF hd1).1
        have hmono := nat_mono_le hcF hd (Nat.zero_le n)
        have hBn : Le (omBase d) ((info (.Psi .zero (.Om d) X)).seq.nat n) :=
          le_transY hBF (hG 0).1 (hG n).1 hf0 hmono
        by_cases hd1' : d = .one
        · subst hd1'
          have : pred (Tm.one) = .zero := rfl
          rw [this] at hzpd
          rcases hzpd with e | h'
          · exact hz0 e
          · exact not_lt_zero _ h'
        · have hpd0 : pred d ≠ .zero := pred_ne_zero hdF hd1 hd1'
          have hle : Le (pred d) (omBase d) := by
            unfold omBase
            rw [ite_eq_right hd1']
            exact le_omHat hpF hpd0
          have := lt_of_le_of_ltY hpF (hG n).1 hz (le_transY hpF hBF (hG n).1 hle hBn) h1
          exact not_lt_of_leY hz hpF hzpd this
      · -- 不動点の `Ω` は標準形でない
        have hOF : IsOF (.Psi .zero ρ X) := IsOF.psi hcF (notOm_of_shape hsh)
        exact absurd ((lt_OF_omG hOF hcF hcF).mp hO.om.2.2) (Lt.irrefl _)
    · have : dom (.Psi ζ ρ X) = .big (.Psi ζ ρ X) := by
        rw [dom_psi, ite_eq_right hζ]
      rw [this] at hd; cases hd

/-- `Ω_c`（`c` 極限）の場合 -/
theorem omLimCase : OmLimCase := by
  intro c ht hs hL
  refine ladL_of_nat fun hd n => ?_
  have hd' : dom c = .omega := hd
  have hcF := ht.om.1
  have hG := (seqI_dom_nat hcF hd').1.good
  show LBI (.Om (sc ((info c).seq.nat n))) (.Om (sc ((info c).seq.nat (n + 1))))
  exact lbi_om (hG n).1 (hG (n + 1)).1 (hG n).2.2 (hL.nat hd' n) (nofix_nat c ht hs hd' n)

end RTKA.Fund
