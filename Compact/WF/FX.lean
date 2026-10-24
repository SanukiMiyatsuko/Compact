import Compact.WF.F0

/-! 断片 `FX`（`F0` に `Ξ` を加えたもの）の反対称性と相等。

`FX` の項は `0`、`1`、`K_n`、`+`、`Ω`、`Ξ_n`、`Ψ^0_{Ω_c}`（`c` は後者）。`Ψ` の目標は `Ω_c` に限り、
`Ξ` や `Ψ^ξ`（`ξ > 0`）を目標にする `Ψ` は含めない。`ξ > 0` の `Ψ` は目標に `Ξ` が要るので（`m(Ω_c) = 1`）、
`Ψ^ξ` を加える前の段階として、まず `Ξ` だけを加える。

`Ξ` どうしの比較（Lemma 4.14）は `F0` の同じ区間の `Ψ` どうしと同じ形なので、`F0` と同じく
大きさについての帰納法だけで反対称性と相等が示せる（`cmp_swap_FX`・`eq_of_cmp_eq_FX`）。 -/

namespace RTKA

open Tm

/-- 断片 `FX` の項 -/
def isFX : Tm → Bool
  | zero | one | K _ => true
  | plus a b => isFX a && isFX b
  | Om a => isFX a
  | Xi _ a => isFX a
  | Psi xi (Om c) a => xi == zero && isFX c && isFX a
  | Psi _ _ _ => false

/-- `FX` の標準形 -/
def FXNF (t : Tm) : Prop := isNF t = true ∧ isFX t = true

/-! ### 標準形の分解 -/

theorem FXNF.plus {a b : Tm} (h : FXNF (.plus a b)) :
    FXNF a ∧ FXNF b ∧ isPrincipal a = true ∧ b ≠ .zero := by
  obtain ⟨hn, hf⟩ := h
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
  simp only [isFX, Bool.and_eq_true] at hf
  exact ⟨⟨hn.1.1.2, hf.1⟩, ⟨hn.1.2, hf.2⟩, hn.1.1.1.1, hn.1.1.1.2⟩

theorem FXNF.om {a : Tm} (h : FXNF (.Om a)) : FXNF a ∧ a ≠ .zero ∧ cmp a (.Om a) = .lt := by
  obtain ⟨hn, hf⟩ := h
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
  simp only [isFX] at hf
  refine ⟨⟨hn.1.1, hf⟩, hn.1.2, ?_⟩
  have h2 := hn.2
  unfold lt at h2
  simpa using h2

theorem FXNF.xi {n : Nat} {a : Tm} (h : FXNF (.Xi n a)) :
    1 ≤ n ∧ FXNF a ∧ a ≠ .zero ∧ cmp a (succK n) ≠ .gt ∧ inC a a (.K n) = true := by
  obtain ⟨hn, hf⟩ := h
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hn
  simp only [isFX] at hf
  exact ⟨hn.1.1.1.1, ⟨hn.1.1.1.2, hf⟩, hn.1.1.2, hn.1.2, hn.2⟩

/-- `FX` の `Ψ` は `Ψ^0_{Ω_c}(α)`（`c` は後者） -/
theorem FXNF.psi {xi pi a : Tm} (h : FXNF (.Psi xi pi a)) :
    xi = .zero ∧ ∃ c, pi = .Om c ∧ FXNF (.Om c) ∧ isSucc c = true ∧ FXNF a ∧
      inC a a pi = true ∧ inC pi a pi = true := by
  obtain ⟨hn, hf⟩ := h
  simp only [isNF, Bool.and_eq_true] at hn
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, hpin⟩, han⟩, hreg⟩, _⟩, hCa⟩, _⟩, hCpi⟩, _⟩ := hn
  cases pi with
  | Om c =>
    simp only [isFX, Bool.and_eq_true, beq_iff_eq] at hf
    obtain ⟨⟨hxi, hcf⟩, haf⟩ := hf
    subst hxi
    exact ⟨rfl, c, rfl, ⟨hpin, hcf⟩, hreg, ⟨han, haf⟩, hCa, hCpi⟩
  | _ => simp [isFX] at hf

theorem FXNF.k {n : Nat} (h : FXNF (.K n)) : 1 ≤ n := by
  have := h.1
  simp only [isNF, decide_eq_true_eq] at this
  exact this

/-- `Ω_{K_m}` は標準形でない -/
theorem FXNF.om_ne_k {a : Tm} {m : Nat} (h : FXNF (.Om a)) : a ≠ .K m := by
  intro e
  subst e
  have h2 := h.om.2.2
  rw [cmp_principal rfl rfl, cmpP.eq_def] at h2
  simp [lev] at h2

theorem summands_FXNF : ∀ t : Tm, FXNF t → ∀ s, s ∈ summands t → FXNF s ∧ isPrincipal s = true
  | .zero, _, s, hs => by simp [summands] at hs
  | .plus a b, h, s, hs => by
    obtain ⟨ha, hb, hap, _⟩ := h.plus
    rw [summands, List.mem_cons] at hs
    cases hs with
    | inl e => rw [e]; exact ⟨ha, hap⟩
    | inr hs => exact summands_FXNF b hb s hs
  | .one, h, s, hs | .K _, h, s, hs | .Om _, h, s, hs | .Xi _ _, h, s, hs
  | .Psi _ _ _, h, s, hs => by
    simp only [summands, List.mem_singleton] at hs
    rw [hs]
    exact ⟨h, rfl⟩

/-! ### `Ξ` を含む比較の計算 -/

theorem cmpOmX_xi (a b : Tm) (n : Nat) : cmpOmX a (.Xi n b) = cmp a (.Xi n b) := by
  rw [cmpOmX.eq_def]
  simp [omegaFixed]

theorem cmpP_om_xi {a b : Tm} {n : Nat} (h : lev a = n) :
    cmpP (.Om a) (.Xi n b) = cmp a (.Xi n b) := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]
  exact cmpOmX_xi a b n

theorem cmpP_xi_om {a b : Tm} {n : Nat} (h : lev a = n) :
    cmpP (.Xi n b) (.Om a) = (cmp a (.Xi n b)).swap := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]
  rw [cmpOmX_xi]

theorem cmpP_xi_xi (n : Nat) (a b : Tm) :
    cmpP (.Xi n a) (.Xi n b) =
      if a = b then .eq else if xiLtXi (.Xi n a) (.Xi n b) = true then .lt else .gt := by
  rw [cmpP.eq_def]
  simp only [lev, Nat.lt_irrefl, ↓reduceIte, beq_iff_eq]

theorem xiLtXi_eq (n m : Nat) (a b : Tm) :
    xiLtXi (.Xi n a) (.Xi m b) =
      ((cmp a b == .lt && inC a b (.Xi m b)) || (cmp b a == .lt && !inC b a (.Xi n a))) := by
  rw [xiLtXi]

theorem cmpP_psi_xi {xi pi a b : Tm} {m : Nat} (h : lev pi = m) :
    cmpP (.Psi xi pi a) (.Xi m b) =
      if psiLtXi (.Psi xi pi a) (.Xi m b) = true then .lt else .gt := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]

theorem cmpP_xi_psi {xi pi a b : Tm} {m : Nat} (h : lev pi = m) :
    cmpP (.Xi m b) (.Psi xi pi a) =
      if psiLtXi (.Psi xi pi a) (.Xi m b) = true then .gt else .lt := by
  rw [cmpP.eq_def]
  simp only [lev, h, Nat.lt_irrefl, ↓reduceIte]

theorem psiLtXi_eq (xi pi a b : Tm) (m : Nat) :
    psiLtXi (.Psi xi pi a) (.Xi m b) =
      (cmp pi (.Xi m b) != .gt || (cmp b a == .lt && !inC b a (.Psi xi pi a))) := by
  rw [psiLtXi]

/-! ### 反対称性と相等 -/

/-- 大きさの和が `N` 以下の `FX` の標準形の組で、`cmp` は反対称で、`.eq` なら等しい -/
def SEX (N : Nat) : Prop :=
  ∀ a b : Tm, FXNF a → FXNF b → a.size + b.size ≤ N →
    cmp b a = (cmp a b).swap ∧ (cmp a b = .eq → a = b)

/-- `Ξ_n` どうしの反対称性と相等 -/
theorem xi_SE {n : Nat} {a b : Tm}
    (hab : cmp b a = (cmp a b).swap ∧ (cmp a b = .eq → a = b)) :
    cmpP (.Xi n b) (.Xi n a) = (cmpP (.Xi n a) (.Xi n b)).swap ∧
      (cmpP (.Xi n a) (.Xi n b) = .eq → Tm.Xi n a = .Xi n b) := by
  rw [cmpP_xi_xi, cmpP_xi_xi, xiLtXi_eq, xiLtXi_eq]
  cases eab : cmp a b with
  | eq =>
    have := hab.2 eab
    subst this
    simp
  | lt =>
    have eba : cmp b a = .gt := by rw [hab.1, eab]; rfl
    have hne : a ≠ b := by intro e; subst e; rw [cmp_self] at eab; cases eab
    have hne' : b ≠ a := fun e => hne e.symm
    simp only [hne, hne', eba, ↓reduceIte]
    cases inC a b (Tm.Xi n b) <;> simp
  | gt =>
    have eba : cmp b a = .lt := by rw [hab.1, eab]; rfl
    have hne : a ≠ b := by intro e; subst e; rw [cmp_self] at eab; cases eab
    have hne' : b ≠ a := fun e => hne e.symm
    simp only [hne, hne', eba, ↓reduceIte]
    cases inC b a (Tm.Xi n a) <;> simp

/-- 同じ階の主要項どうしの反対称性と相等 -/
theorem cmpP_SEX_same {N : Nat} (ih : SEX N) {x y : Tm} (hx : FXNF x) (hy : FXNF y)
    (hpx : isPrincipal x = true) (hpy : isPrincipal y = true) (hs : x.size + y.size ≤ N + 1)
    (hl : lev x = lev y) : cmpP y x = (cmpP x y).swap ∧ (cmpP x y = .eq → x = y) := by
  cases x <;> cases y
  all_goals first
    | (exfalso; simp [isPrincipal] at hpx hpy; done)
    | skip
  case one.one => rw [cmpP_self]; exact ⟨rfl, fun _ => rfl⟩
  case one.K n =>
    exfalso
    have := hy.k
    simp only [lev] at hl
    omega
  case K.one n =>
    exfalso
    have := hx.k
    simp only [lev] at hl
    omega
  case K.K m n =>
    have : m = n := by simp only [lev] at hl; omega
    subst this
    rw [cmpP_self]
    exact ⟨rfl, fun _ => rfl⟩
  case Om.Om a b =>
    have h := ih a b hx.om.1 hy.om.1 (by simp only [Tm.size] at hs; omega)
    rw [cmpP_om_om (a := a) (b := b) hl, cmpP_om_om (a := b) (b := a) hl.symm]
    exact ⟨h.1, fun e => by rw [h.2 e]⟩
  case K.Om m b =>
    have hne := hy.om_ne_k (m := m)
    rw [cmpP.eq_def, cmpP.eq_def]
    simp [hl, hne]
  case Om.K a m =>
    have hne := hx.om_ne_k (m := m)
    rw [cmpP.eq_def, cmpP.eq_def]
    simp [hl, hne]
  case Om.Xi a n b =>
    have hl' : lev a = n := hl
    rw [cmpP_om_xi hl', cmpP_xi_om hl']
    refine ⟨rfl, fun e => ?_⟩
    have hab := (ih a (.Xi n b) hx.om.1 hy (by simp only [Tm.size] at hs ⊢; omega)).2 e
    subst hab
    have h2 := hx.om.2.2
    rw [cmp_principal rfl rfl, cmpP_xi_om (a := .Xi n b) (b := b) (n := n) rfl, cmp_self] at h2
    cases h2
  case Xi.Om n b a =>
    have hl' : lev a = n := hl.symm
    rw [cmpP_om_xi hl', cmpP_xi_om hl']
    refine ⟨by cases cmp a (Tm.Xi n b) <;> rfl, fun e => ?_⟩
    have e' : cmp a (.Xi n b) = .eq := by
      cases h : cmp a (Tm.Xi n b) <;> rw [h] at e <;> first | rfl | cases e
    have hab := (ih a (.Xi n b) hy.om.1 hx (by simp only [Tm.size] at hs ⊢; omega)).2 e'
    subst hab
    have h2 := hy.om.2.2
    rw [cmp_principal rfl rfl, cmpP_xi_om (a := .Xi n b) (b := b) (n := n) rfl, cmp_self] at h2
    cases h2
  case Xi.Xi n a m b =>
    have : n = m := hl
    subst this
    exact xi_SE (ih a b hx.xi.2.1 hy.xi.2.1 (by simp only [Tm.size] at hs; omega))
  case Psi.Xi xi pi α m b =>
    obtain ⟨-, c, hpi, -⟩ := hx.psi
    subst hpi
    have hl' : lev (Tm.Om c) = m := hl
    rw [cmpP_psi_xi hl', cmpP_xi_psi hl']
    by_cases hp : psiLtXi (Tm.Psi xi (.Om c) α) (.Xi m b) = true
    · simp [hp]
    · simp [hp]
  case Xi.Psi m b xi pi α =>
    obtain ⟨-, c, hpi, -⟩ := hy.psi
    subst hpi
    have hl' : lev (Tm.Om c) = m := hl.symm
    rw [cmpP_psi_xi hl', cmpP_xi_psi hl']
    by_cases hp : psiLtXi (Tm.Psi xi (.Om c) α) (.Xi m b) = true
    · simp [hp]
    · simp [hp]
  case Psi.Psi xi pi α sg ka β =>
    obtain ⟨hxi, c, hpi, hc, -, hα, -, -⟩ := hx.psi
    obtain ⟨hsg, d, hka, hd, -, hβ, -, -⟩ := hy.psi
    subst hxi hpi hsg hka
    have hl' : lev c = lev d := hl
    have hcd := ih c d hc.om.1 hd.om.1 (by simp only [Tm.size] at hs; omega)
    have hab := ih α β hα hβ (by simp only [Tm.size] at hs; omega)
    rw [cmpP_psi_psi (xi := .zero) (pi := .Om c) (a := α) (sg := .zero) (ka := .Om d) (b := β) hl,
      cmpP_psi_psi (xi := .zero) (pi := .Om d) (a := β) (sg := .zero) (ka := .Om c) (b := α) hl.symm]
    exact psi0_SE hl' hcd hab
  case Om.Psi a xi pi β =>
    obtain ⟨hxi, c, hpi, -, -, -, -, -⟩ := hy.psi
    subst hxi hpi
    have h' : lev a = lev c := hl
    rw [cmpP_om_psi0 h', cmpP_psi0_om h']
    by_cases h : cmp a c = .lt <;> simp [h]
  case Psi.Om xi pi β a =>
    obtain ⟨hxi, c, hpi, -, -, -, -, -⟩ := hx.psi
    subst hxi hpi
    have h' : lev a = lev c := hl.symm
    rw [cmpP_om_psi0 h', cmpP_psi0_om h']
    by_cases h : cmp a c = .lt <;> simp [h]
  all_goals
    simp only [cmpP.eq_def]
    simp_all [lev]

theorem cmpP_SEX {N : Nat} (ih : SEX N) {x y : Tm} (hx : FXNF x) (hy : FXNF y)
    (hpx : isPrincipal x = true) (hpy : isPrincipal y = true) (hs : x.size + y.size ≤ N + 1) :
    cmpP y x = (cmpP x y).swap ∧ (cmpP x y = .eq → x = y) := by
  by_cases h1 : lev x < lev y
  · rw [cmpP_of_lev_lt h1, cmpP_of_lev_gt h1]
    exact ⟨rfl, fun h => by cases h⟩
  by_cases h2 : lev y < lev x
  · rw [cmpP_of_lev_gt h2, cmpP_of_lev_lt h2]
    exact ⟨rfl, fun h => by cases h⟩
  exact cmpP_SEX_same ih hx hy hpx hpy hs (by omega)

theorem SEX_succ {N : Nat} (ih : SEX N) : SEX (N + 1) := by
  intro a b ha hb hs
  have hP : ∀ x, x ∈ summands a → ∀ y, y ∈ summands b →
      cmpP y x = (cmpP x y).swap ∧ (cmpP x y = .eq → x = y) := by
    intro x hx y hy
    have sx := summands_FXNF a ha x hx
    have sy := summands_FXNF b hb y hy
    have := size_le_of_mem_summands a x hx
    have := size_le_of_mem_summands b y hy
    exact cmpP_SEX ih sx.1 sy.1 sx.2 sy.2 (by omega)
  rw [cmp_eq a b, cmp_eq b a]
  exact ⟨cmpList_swap _ _ (fun x hx y hy => (hP x hx y hy).1),
    fun h => eq_of_summands_eq ha.1 hb.1
      (eq_of_cmpList_eq _ _ (fun x hx y hy => (hP x hx y hy).2) h)⟩

theorem SEX_all : ∀ N, SEX N
  | 0 => fun a _ _ _ h => absurd h (by have := Tm.size_pos a; omega)
  | N + 1 => SEX_succ (SEX_all N)

/-- `FX` の標準形の上で `cmp` は反対称 -/
theorem cmp_swap_FX {a b : Tm} (ha : FXNF a) (hb : FXNF b) : cmp b a = (cmp a b).swap :=
  (SEX_all _ a b ha hb (Nat.le_refl _)).1

/-- `FX` の標準形の上で `cmp a b = .eq` なら `a = b` -/
theorem eq_of_cmp_eq_FX {a b : Tm} (ha : FXNF a) (hb : FXNF b) (h : cmp a b = .eq) : a = b :=
  (SEX_all _ a b ha hb (Nat.le_refl _)).2 h

end RTKA
