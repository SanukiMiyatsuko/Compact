import Compact.WF.FXWF

/-! 体系全体（`isNF` の標準形全て）の定義と、整列性の証明が使う順序の性質。

`FZ` との違いは、`Ψ^ξ_π(a)` の目標 `π` に Mahlo 添字が `0` でない崩壊 `Ψ^ζ_κ(b)` も入ること。目標をたどる
列（`Ψ^ξ_π(a)`、`π`、`π` の目標、…）の上で Mahlo 添字は真に減る。`FZ` と同じく、整列性の証明は順序の性質の組
`FWOrder` を仮定して行い、`FWOrder` 自体は別に示す。 -/

namespace RTKA.W

open Tm

/-- 体系全体の標準形 -/
def WNF (t : Tm) : Prop := isNF t = true

/-- `Ψ` の目標：`Ω_c`（`c` は後者）、`Ξ_n(p)`、Mahlo 添字が `0` でない `Ψ^ζ_κ(b)` -/
def IsTgt (π : Tm) : Prop :=
  (∃ c, π = .Om c ∧ isSucc c = true) ∨ (∃ n p, π = .Xi n p) ∨
    ∃ ζ κ b, π = .Psi ζ κ b ∧ ζ ≠ .zero

/-- 目標の Mahlo 添字 `m(π)`（`Ω_c` は `1`、`Ξ_n(p)` は `p`、`Ψ^ζ_κ(b)` は `ζ`） -/
def mi : Tm → Tm
  | .Om _ => .one
  | .Xi _ p => p
  | .Psi ζ _ _ => ζ
  | _ => .zero

/-! ### 標準形の分解 -/

theorem WNF.plus {a b : Tm} (h : WNF (.plus a b)) :
    WNF a ∧ WNF b ∧ isPrincipal a = true ∧ b ≠ .zero := by
  have hn : isNF (.plus a b) = true := h
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
  exact ⟨hn.1.1.2, hn.1.2, hn.1.1.1.1, hn.1.1.1.2⟩

theorem WNF.om {a : Tm} (h : WNF (.Om a)) : WNF a ∧ a ≠ .zero ∧ cmp a (.Om a) = .lt := by
  have hn : isNF (.Om a) = true := h
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
  refine ⟨hn.1.1, hn.1.2, ?_⟩
  have h2 := hn.2
  unfold lt at h2
  simpa using h2

theorem WNF.xi {n : Nat} {a : Tm} (h : WNF (.Xi n a)) :
    1 ≤ n ∧ WNF a ∧ a ≠ .zero ∧ cmp a (succK n) ≠ .gt ∧ inC a a (.K n) = true := by
  have hn : isNF (.Xi n a) = true := h
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hn
  exact ⟨hn.1.1.1.1, hn.1.1.1.2, hn.1.1.2, hn.1.2, hn.2⟩

/-- `Ψ^ξ_π(a)` の標準形の条件 -/
structure PsiNF (xi pi a : Tm) : Prop where
  tgt : IsTgt pi
  xiF : WNF xi
  piF : WNF pi
  aF : WNF a
  le : cmp xi a ≠ .gt
  Ca : inC a a pi = true
  Cxi : inC xi a pi = true
  Cpi : inC pi a pi = true
  /-- Mahlo 添字は目標の Mahlo 添字未満で、`ξ ∈ C(m(π), π)` -/
  mlt : Lt xi (mi pi)
  mC : inC xi (mi pi) pi = true

theorem WNF.psi {xi pi a : Tm} (h : WNF (.Psi xi pi a)) : PsiNF xi pi a := by
  have hn : isNF (.Psi xi pi a) = true := h
  simp only [isNF, Bool.and_eq_true] at hn
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hxin, hpin⟩, han⟩, hreg⟩, hle⟩, hCa⟩, hCxi⟩, hCpi⟩, hm⟩ := hn
  have hle' : cmp xi a ≠ .gt := by simpa using hle
  have key : ∀ m, mOf pi = some m → mi pi = m ∧ IsTgt pi := by
    intro m hm'
    cases pi with
    | Om c =>
      simp only [mOf, Option.some.injEq] at hm'; subst hm'; exact ⟨rfl, Or.inl ⟨c, rfl, hreg⟩⟩
    | Xi n p =>
      simp only [mOf, Option.some.injEq] at hm'; subst hm'; exact ⟨rfl, Or.inr (Or.inl ⟨n, p, rfl⟩)⟩
    | Psi ζ κ b =>
      simp only [mOf, Option.some.injEq] at hm'; subst hm'
      refine ⟨rfl, Or.inr (Or.inr ⟨ζ, κ, b, rfl, ?_⟩)⟩
      simpa [isRegTerm] using hreg
    | _ => simp [mOf] at hm'
  cases e : mOf pi with
  | none => rw [e] at hm; simp at hm
  | some m =>
    rw [e] at hm
    simp only [Bool.and_eq_true] at hm
    obtain ⟨hmi, ht⟩ := key m e
    refine ⟨ht, hxin, hpin, han, hle', hCa, hCxi, hCpi, ?_, ?_⟩
    · rw [hmi]
      have := hm.1
      unfold lt at this
      show cmp xi m = .lt
      simpa using this
    · rw [hmi]; exact hm.2

theorem WNF.k {n : Nat} (h : WNF (.K n)) : 1 ≤ n := by
  have hn : isNF (.K n) = true := h
  simp only [isNF, decide_eq_true_eq] at hn
  exact hn

theorem WNF.zero : WNF .zero := rfl

theorem WNF.one : WNF .one := rfl

theorem WNF.K' {n : Nat} (h : 1 ≤ n) : WNF (.K n) := by
  show isNF (.K n) = true
  simp only [isNF, decide_eq_true_eq]
  exact h

/-- `Ω_{K_m}` は標準形でない -/
theorem WNF.om_ne_k {a : Tm} {m : Nat} (h : WNF (.Om a)) : a ≠ .K m := by
  intro e
  subst e
  have h2 := h.om.2.2
  rw [cmp_principal rfl rfl, cmpP.eq_def] at h2
  simp [lev] at h2

theorem summands_WNF : ∀ t : Tm, WNF t → ∀ s, s ∈ summands t → WNF s ∧ isPrincipal s = true
  | .zero, _, s, hs => by simp [summands] at hs
  | .plus a b, h, s, hs => by
    obtain ⟨ha, hb, hap, _⟩ := h.plus
    rw [summands, List.mem_cons] at hs
    cases hs with
    | inl e => rw [e]; exact ⟨ha, hap⟩
    | inr hs => exact summands_WNF b hb s hs
  | .one, h, s, hs | .K _, h, s, hs | .Om _, h, s, hs | .Xi _ _, h, s, hs
  | .Psi _ _ _, h, s, hs => by
    simp only [summands, List.mem_singleton] at hs
    rw [hs]
    exact ⟨h, rfl⟩

theorem WNF.of_mem_subs : ∀ {t s : Tm}, WNF t → s ∈ subs t → WNF s
  | .zero, s, ht, h | .one, s, ht, h | .K _, s, ht, h => by
    simp only [subs, List.mem_singleton] at h
    rw [h]
    exact ht
  | .plus a b, s, ht, h => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    obtain ⟨ha, hb, -, -⟩ := ht.plus
    rcases h with h | h | h
    · rw [h]; exact ht
    · exact WNF.of_mem_subs ha h
    · exact WNF.of_mem_subs hb h
  | .Om a, s, ht, h => by
    simp only [subs, List.mem_cons] at h
    rcases h with h | h
    · rw [h]; exact ht
    · exact WNF.of_mem_subs ht.om.1 h
  | .Xi _ a, s, ht, h => by
    simp only [subs, List.mem_cons] at h
    rcases h with h | h
    · rw [h]; exact ht
    · exact WNF.of_mem_subs ht.xi.2.1 h
  | .Psi x p a, s, ht, h => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    have hP := ht.psi
    rcases h with h | (h | h) | h
    · rw [h]; exact ht
    · exact WNF.of_mem_subs hP.xiF h
    · exact WNF.of_mem_subs hP.piF h
    · exact WNF.of_mem_subs hP.aF h

/-! ### 順序についての仮定 -/

/-- 整列性の証明が使う順序の性質：標準形の上で `cmp` は反対称で `.eq` なら等しく、`<` は推移的。
    さらに `Ψ^ξ_π(a)` の引数 `a`・目標 `π`・Mahlo 添字 `ξ` の前線（`π` について）は `Ψ^ξ_π(a)` 未満（K2）、
    `ξ ∈ C(ξ, Ψ^ξ_π(a))`、`Ξ_n(a)` の引数の前線（`K_n` について）は `Ξ_n(a)` 未満、`c < Ψ^0_{Ω_c}(a)`。 -/
class FWOrder : Prop where
  swap : ∀ {a b : Tm}, WNF a → WNF b → cmp b a = (cmp a b).swap
  eq : ∀ {a b : Tm}, WNF a → WNF b → cmp a b = .eq → a = b
  trans : ∀ {a b c : Tm}, WNF a → WNF b → WNF c → Lt a b → Lt b c → Lt a c
  k2 : ∀ {ξ π a : Tm}, WNF (.Psi ξ π a) → ∀ w, w ∈ fr π a → Lt w (.Psi ξ π a)
  k2t : ∀ {ξ π a : Tm}, WNF (.Psi ξ π a) → ∀ w, w ∈ fr π π → Lt w (.Psi ξ π a)
  k2s : ∀ {ξ π a : Tm}, WNF (.Psi ξ π a) → ∀ w, w ∈ fr π ξ → Lt w (.Psi ξ π a)
  ms : ∀ {ξ π a : Tm}, WNF (.Psi ξ π a) → inC ξ ξ (.Psi ξ π a) = true
  k2x : ∀ {n : Nat} {a : Tm}, WNF (.Xi n a) → ∀ w, w ∈ fr (.K n) a → Lt w (.Xi n a)
  cx : ∀ {c a : Tm}, WNF (.Psi .zero (.Om c) a) → Lt c (.Psi .zero (.Om c) a)

section Order

variable [FWOrder]

theorem lt_transY {a b c : Tm} (ha : WNF a) (hb : WNF b) (hc : WNF c)
    (h1 : Lt a b) (h2 : Lt b c) : Lt a c :=
  FWOrder.trans ha hb hc h1 h2

theorem Lt.asymmY {a b : Tm} (ha : WNF a) (hb : WNF b) (h : Lt a b) : ¬ Lt b a := by
  unfold Lt at *
  rw [FWOrder.swap ha hb, h]
  decide

theorem lt_of_gtY {a b : Tm} (ha : WNF a) (hb : WNF b) (h : cmp a b = .gt) : Lt b a := by
  unfold Lt
  rw [FWOrder.swap ha hb, h]
  rfl

theorem triY {a b : Tm} (ha : WNF a) (hb : WNF b) : Lt a b ∨ a = b ∨ Lt b a := by
  cases e : cmp a b with
  | lt => exact Or.inl e
  | eq => exact Or.inr (Or.inl (FWOrder.eq ha hb e))
  | gt => exact Or.inr (Or.inr (lt_of_gtY ha hb e))

/-- `¬ a < b` なら `b ≤ a` -/
theorem le_of_not_ltY {a b : Tm} (ha : WNF a) (hb : WNF b) (h : ¬ Lt a b) : Le b a := by
  rcases triY ha hb with h' | h' | h'
  · exact absurd h' h
  · exact Or.inl h'.symm
  · exact Or.inr h'

/-- `cmp a b ≠ .gt` なら `a ≤ b` -/
theorem le_of_ne_gtY {a b : Tm} (ha : WNF a) (hb : WNF b) (h : cmp a b ≠ .gt) : Le a b := by
  cases e : cmp a b with
  | lt => exact Or.inr e
  | eq => exact Or.inl (FWOrder.eq ha hb e)
  | gt => exact absurd e h

theorem not_lt_of_leY {a b : Tm} (ha : WNF a) (hb : WNF b) (h : Le a b) : ¬ Lt b a := by
  rcases h with rfl | h
  · exact Lt.irrefl _
  · exact Lt.asymmY ha hb h

theorem lt_of_lt_of_leY {a b c : Tm} (ha : WNF a) (hb : WNF b) (hc : WNF c)
    (h1 : Lt a b) (h2 : Le b c) : Lt a c := by
  rcases h2 with rfl | h2
  · exact h1
  · exact lt_transY ha hb hc h1 h2

theorem lt_of_le_of_ltY {a b c : Tm} (ha : WNF a) (hb : WNF b) (hc : WNF c)
    (h1 : Le a b) (h2 : Lt b c) : Lt a c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact lt_transY ha hb hc h1 h2

theorem le_transY {a b c : Tm} (ha : WNF a) (hb : WNF b) (hc : WNF c)
    (h1 : Le a b) (h2 : Le b c) : Le a c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact Or.inr (lt_of_lt_of_leY ha hb hc h1 h2)

theorem le_antisymmY {a b : Tm} (ha : WNF a) (hb : WNF b) (h1 : Le a b) (h2 : Le b a) :
    a = b := by
  rcases h1 with e | h1
  · exact e
  · exact absurd h1 (not_lt_of_leY hb ha h2)

theorem eq_of_cmpP_eqY {x y : Tm} (hx : WNF x) (hy : WNF y) (hpx : isPrincipal x = true)
    (hpy : isPrincipal y = true) (h : cmpP x y = .eq) : x = y := by
  apply FWOrder.eq hx hy
  rw [cmp_principal hpx hpy, h]

end Order

end RTKA.W
