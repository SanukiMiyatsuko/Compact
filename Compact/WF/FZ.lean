import Compact.WF.FXWF

/-! 断片 `FZ`（`FY` に、`Ξ` を目標とする Mahlo 添字つきの崩壊 `Ψ^ξ_{Ξ_n(p)}` を加えたもの）の定義と、
整列性の証明が使う順序の性質。

`FZ` の項は `0`、`1`、`K_n`、`+`、`Ω`、`Ξ_n`、`Ψ^0_{Ω_c}`（`c` は後者）、`Ψ^ξ_{Ξ_n(p)}`（`ξ < p`）。
`Ψ^ξ` を目標とする `Ψ` は含めない。`FY` の証明と同じ形で、整列性の証明は順序の性質の組 `FZOrder` を
仮定して行い、`FZOrder` 自体は別に示す。`FY` から増える順序の性質は、Mahlo 添字 `ξ` の前線（`π` について）が
`Ψ^ξ_π(a)` 未満であること（`k2s`）と、`ξ ∈ C(ξ, Ψ^ξ_π(a))`（`ms`）。 -/

namespace RTKA.Z

open Tm

/-- 断片 `FZ` の項 -/
def isFZ : Tm → Bool
  | zero | one | K _ => true
  | plus a b => isFZ a && isFZ b
  | Om a => isFZ a
  | Xi _ a => isFZ a
  | Psi xi (Om c) a => xi == zero && isFZ c && isFZ a
  | Psi xi (Xi _ p) a => isFZ xi && isFZ p && isFZ a
  | Psi _ _ _ => false

/-- `FZ` の標準形 -/
def FZNF (t : Tm) : Prop := isNF t = true ∧ isFZ t = true

/-- `Ψ` の目標：`Ω_c`（`c` は後者）か `Ξ_n(p)` -/
def IsTgt (π : Tm) : Prop := (∃ c, π = .Om c ∧ isSucc c = true) ∨ ∃ n p, π = .Xi n p

/-! ### 標準形の分解 -/

theorem FZNF.plus {a b : Tm} (h : FZNF (.plus a b)) :
    FZNF a ∧ FZNF b ∧ isPrincipal a = true ∧ b ≠ .zero := by
  obtain ⟨hn, hf⟩ := h
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
  simp only [isFZ, Bool.and_eq_true] at hf
  exact ⟨⟨hn.1.1.2, hf.1⟩, ⟨hn.1.2, hf.2⟩, hn.1.1.1.1, hn.1.1.1.2⟩

theorem FZNF.om {a : Tm} (h : FZNF (.Om a)) : FZNF a ∧ a ≠ .zero ∧ cmp a (.Om a) = .lt := by
  obtain ⟨hn, hf⟩ := h
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
  simp only [isFZ] at hf
  refine ⟨⟨hn.1.1, hf⟩, hn.1.2, ?_⟩
  have h2 := hn.2
  unfold lt at h2
  simpa using h2

theorem FZNF.xi {n : Nat} {a : Tm} (h : FZNF (.Xi n a)) :
    1 ≤ n ∧ FZNF a ∧ a ≠ .zero ∧ cmp a (succK n) ≠ .gt ∧ inC a a (.K n) = true := by
  obtain ⟨hn, hf⟩ := h
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hn
  simp only [isFZ] at hf
  exact ⟨hn.1.1.1.1, ⟨hn.1.1.1.2, hf⟩, hn.1.1.2, hn.1.2, hn.2⟩

/-- `FZ` の `Ψ^ξ_π(a)` の標準形の条件 -/
structure PsiNF (xi pi a : Tm) : Prop where
  tgt : IsTgt pi
  xiF : FZNF xi
  piF : FZNF pi
  aF : FZNF a
  le : cmp xi a ≠ .gt
  Ca : inC a a pi = true
  Cxi : inC xi a pi = true
  Cpi : inC pi a pi = true
  /-- Mahlo 添字：目標が `Ω_c` なら `ξ = 0`、`Ξ_n(p)` なら `ξ < p` で `ξ ∈ C(p, Ξ_n(p))` -/
  m : (∃ c, pi = .Om c ∧ xi = .zero) ∨ ∃ n p, pi = .Xi n p ∧ Lt xi p ∧ inC xi p pi = true

theorem FZNF.psi {xi pi a : Tm} (h : FZNF (.Psi xi pi a)) : PsiNF xi pi a := by
  obtain ⟨hn, hf⟩ := h
  simp only [isNF, Bool.and_eq_true] at hn
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hxin, hpin⟩, han⟩, hreg⟩, hle⟩, hCa⟩, hCxi⟩, hCpi⟩, hm⟩ := hn
  have hle' : cmp xi a ≠ .gt := by simpa using hle
  cases pi with
  | Om c =>
    simp only [isFZ, Bool.and_eq_true, beq_iff_eq] at hf
    obtain ⟨⟨hxi, hcf⟩, haf⟩ := hf
    subst hxi
    exact ⟨Or.inl ⟨c, rfl, hreg⟩, ⟨hxin, rfl⟩, ⟨hpin, hcf⟩, ⟨han, haf⟩, hle', hCa, hCxi, hCpi,
      Or.inl ⟨c, rfl, rfl⟩⟩
  | Xi n p =>
    simp only [isFZ, Bool.and_eq_true] at hf
    obtain ⟨⟨hxf, hpf⟩, haf⟩ := hf
    simp only [mOf, Bool.and_eq_true] at hm
    refine ⟨Or.inr ⟨n, p, rfl⟩, ⟨hxin, hxf⟩, ⟨hpin, hpf⟩, ⟨han, haf⟩, hle', hCa, hCxi, hCpi,
      Or.inr ⟨n, p, rfl, ?_, hm.2⟩⟩
    have := hm.1
    unfold lt at this
    show cmp xi p = .lt
    simpa using this
  | _ => simp [isFZ] at hf

theorem FZNF.k {n : Nat} (h : FZNF (.K n)) : 1 ≤ n := by
  have := h.1
  simp only [isNF, decide_eq_true_eq] at this
  exact this

theorem FZNF.zero : FZNF .zero := ⟨rfl, rfl⟩

theorem FZNF.one : FZNF .one := ⟨rfl, rfl⟩

theorem FZNF.K' {n : Nat} (h : 1 ≤ n) : FZNF (.K n) := by
  refine ⟨?_, rfl⟩
  simp only [isNF, decide_eq_true_eq]
  exact h

/-- `Ω_{K_m}` は標準形でない -/
theorem FZNF.om_ne_k {a : Tm} {m : Nat} (h : FZNF (.Om a)) : a ≠ .K m := by
  intro e
  subst e
  have h2 := h.om.2.2
  rw [cmp_principal rfl rfl, cmpP.eq_def] at h2
  simp [lev] at h2

theorem summands_FZNF : ∀ t : Tm, FZNF t → ∀ s, s ∈ summands t → FZNF s ∧ isPrincipal s = true
  | .zero, _, s, hs => by simp [summands] at hs
  | .plus a b, h, s, hs => by
    obtain ⟨ha, hb, hap, _⟩ := h.plus
    rw [summands, List.mem_cons] at hs
    cases hs with
    | inl e => rw [e]; exact ⟨ha, hap⟩
    | inr hs => exact summands_FZNF b hb s hs
  | .one, h, s, hs | .K _, h, s, hs | .Om _, h, s, hs | .Xi _ _, h, s, hs
  | .Psi _ _ _, h, s, hs => by
    simp only [summands, List.mem_singleton] at hs
    rw [hs]
    exact ⟨h, rfl⟩

theorem FZNF.of_mem_subs : ∀ {t s : Tm}, FZNF t → s ∈ subs t → FZNF s
  | .zero, s, ht, h | .one, s, ht, h | .K _, s, ht, h => by
    simp only [subs, List.mem_singleton] at h
    rw [h]
    exact ht
  | .plus a b, s, ht, h => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    obtain ⟨ha, hb, -, -⟩ := ht.plus
    rcases h with h | h | h
    · rw [h]; exact ht
    · exact FZNF.of_mem_subs ha h
    · exact FZNF.of_mem_subs hb h
  | .Om a, s, ht, h => by
    simp only [subs, List.mem_cons] at h
    rcases h with h | h
    · rw [h]; exact ht
    · exact FZNF.of_mem_subs ht.om.1 h
  | .Xi _ a, s, ht, h => by
    simp only [subs, List.mem_cons] at h
    rcases h with h | h
    · rw [h]; exact ht
    · exact FZNF.of_mem_subs ht.xi.2.1 h
  | .Psi x p a, s, ht, h => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    have hP := ht.psi
    rcases h with h | (h | h) | h
    · rw [h]; exact ht
    · exact FZNF.of_mem_subs hP.xiF h
    · exact FZNF.of_mem_subs hP.piF h
    · exact FZNF.of_mem_subs hP.aF h

/-! ### 順序についての仮定 -/

/-- 整列性の証明が使う順序の性質：`FZ` の標準形の上で `cmp` は反対称で `.eq` なら等しく、`<` は推移的。
    さらに `Ψ^ξ_π(a)` の引数 `a`・目標 `π`・Mahlo 添字 `ξ` の前線（`π` について）は `Ψ^ξ_π(a)` 未満（K2）、
    `ξ ∈ C(ξ, Ψ^ξ_π(a))`、`Ξ_n(a)` の引数の前線（`K_n` について）は `Ξ_n(a)` 未満、`c < Ψ^0_{Ω_c}(a)`。 -/
class FZOrder : Prop where
  swap : ∀ {a b : Tm}, FZNF a → FZNF b → cmp b a = (cmp a b).swap
  eq : ∀ {a b : Tm}, FZNF a → FZNF b → cmp a b = .eq → a = b
  trans : ∀ {a b c : Tm}, FZNF a → FZNF b → FZNF c → Lt a b → Lt b c → Lt a c
  k2 : ∀ {ξ π a : Tm}, FZNF (.Psi ξ π a) → ∀ w, w ∈ fr π a → Lt w (.Psi ξ π a)
  k2t : ∀ {ξ π a : Tm}, FZNF (.Psi ξ π a) → ∀ w, w ∈ fr π π → Lt w (.Psi ξ π a)
  k2s : ∀ {ξ π a : Tm}, FZNF (.Psi ξ π a) → ∀ w, w ∈ fr π ξ → Lt w (.Psi ξ π a)
  ms : ∀ {ξ π a : Tm}, FZNF (.Psi ξ π a) → inC ξ ξ (.Psi ξ π a) = true
  k2x : ∀ {n : Nat} {a : Tm}, FZNF (.Xi n a) → ∀ w, w ∈ fr (.K n) a → Lt w (.Xi n a)
  cx : ∀ {c a : Tm}, FZNF (.Psi .zero (.Om c) a) → Lt c (.Psi .zero (.Om c) a)

section Order

variable [FZOrder]

theorem lt_transY {a b c : Tm} (ha : FZNF a) (hb : FZNF b) (hc : FZNF c)
    (h1 : Lt a b) (h2 : Lt b c) : Lt a c :=
  FZOrder.trans ha hb hc h1 h2

theorem Lt.asymmY {a b : Tm} (ha : FZNF a) (hb : FZNF b) (h : Lt a b) : ¬ Lt b a := by
  unfold Lt at *
  rw [FZOrder.swap ha hb, h]
  decide

theorem lt_of_gtY {a b : Tm} (ha : FZNF a) (hb : FZNF b) (h : cmp a b = .gt) : Lt b a := by
  unfold Lt
  rw [FZOrder.swap ha hb, h]
  rfl

theorem triY {a b : Tm} (ha : FZNF a) (hb : FZNF b) : Lt a b ∨ a = b ∨ Lt b a := by
  cases e : cmp a b with
  | lt => exact Or.inl e
  | eq => exact Or.inr (Or.inl (FZOrder.eq ha hb e))
  | gt => exact Or.inr (Or.inr (lt_of_gtY ha hb e))

/-- `¬ a < b` なら `b ≤ a` -/
theorem le_of_not_ltY {a b : Tm} (ha : FZNF a) (hb : FZNF b) (h : ¬ Lt a b) : Le b a := by
  rcases triY ha hb with h' | h' | h'
  · exact absurd h' h
  · exact Or.inl h'.symm
  · exact Or.inr h'

/-- `cmp a b ≠ .gt` なら `a ≤ b` -/
theorem le_of_ne_gtY {a b : Tm} (ha : FZNF a) (hb : FZNF b) (h : cmp a b ≠ .gt) : Le a b := by
  cases e : cmp a b with
  | lt => exact Or.inr e
  | eq => exact Or.inl (FZOrder.eq ha hb e)
  | gt => exact absurd e h

theorem not_lt_of_leY {a b : Tm} (ha : FZNF a) (hb : FZNF b) (h : Le a b) : ¬ Lt b a := by
  rcases h with rfl | h
  · exact Lt.irrefl _
  · exact Lt.asymmY ha hb h

theorem lt_of_lt_of_leY {a b c : Tm} (ha : FZNF a) (hb : FZNF b) (hc : FZNF c)
    (h1 : Lt a b) (h2 : Le b c) : Lt a c := by
  rcases h2 with rfl | h2
  · exact h1
  · exact lt_transY ha hb hc h1 h2

theorem lt_of_le_of_ltY {a b c : Tm} (ha : FZNF a) (hb : FZNF b) (hc : FZNF c)
    (h1 : Le a b) (h2 : Lt b c) : Lt a c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact lt_transY ha hb hc h1 h2

theorem le_transY {a b c : Tm} (ha : FZNF a) (hb : FZNF b) (hc : FZNF c)
    (h1 : Le a b) (h2 : Le b c) : Le a c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact Or.inr (lt_of_lt_of_leY ha hb hc h1 h2)

theorem le_antisymmY {a b : Tm} (ha : FZNF a) (hb : FZNF b) (h1 : Le a b) (h2 : Le b a) :
    a = b := by
  rcases h1 with e | h1
  · exact e
  · exact absurd h1 (not_lt_of_leY hb ha h2)

theorem eq_of_cmpP_eqY {x y : Tm} (hx : FZNF x) (hy : FZNF y) (hpx : isPrincipal x = true)
    (hpy : isPrincipal y = true) (h : cmpP x y = .eq) : x = y := by
  apply FZOrder.eq hx hy
  rw [cmp_principal hpx hpy, h]

end Order

end RTKA.Z
