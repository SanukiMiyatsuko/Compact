import Compact.WF.FXWF

/-! 断片 `FY`（`FX` に `Ξ` を目標とする `Ψ^0` を加えたもの）の定義と、整列性の証明が使う順序の性質。

`FY` の項は `0`、`1`、`K_n`、`+`、`Ω`、`Ξ_n`、`Ψ^0_{Ω_c}`（`c` は後者）、`Ψ^0_{Ξ_n(p)}`。`Ψ^0_{Ξ_n(p)}(a)` は
`Ω` の不動点で（`Ω_X = X`）、正則ではない。`ξ > 0` の `Ψ^ξ` と、`Ψ^ξ` を目標とする `Ψ` は含めない。

`FY` では反対称性の証明に推移性が要る（`Ψ^0_{Ξ}(a)` と `Ψ^0_{Ω_d}(b)` の比較など）。そこで整列性の証明は、
順序についての性質の組 `FYOrder`（反対称性・相等・推移性と K2 型の性質）を仮定して行い、`FYOrder` 自体は
別に示す。 -/

namespace RTKA

open Tm

/-- 断片 `FY` の項 -/
def isFY : Tm → Bool
  | zero | one | K _ => true
  | plus a b => isFY a && isFY b
  | Om a => isFY a
  | Xi _ a => isFY a
  | Psi xi (Om c) a => xi == zero && isFY c && isFY a
  | Psi xi (Xi _ p) a => xi == zero && isFY p && isFY a
  | Psi _ _ _ => false

/-- `FY` の標準形 -/
def FYNF (t : Tm) : Prop := isNF t = true ∧ isFY t = true

/-- `Ψ` の目標：`Ω_c`（`c` は後者）か `Ξ_n(p)` -/
def IsTgt (π : Tm) : Prop := (∃ c, π = .Om c ∧ isSucc c = true) ∨ ∃ n p, π = .Xi n p

/-! ### 標準形の分解 -/

theorem FYNF.plus {a b : Tm} (h : FYNF (.plus a b)) :
    FYNF a ∧ FYNF b ∧ isPrincipal a = true ∧ b ≠ .zero := by
  obtain ⟨hn, hf⟩ := h
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
  simp only [isFY, Bool.and_eq_true] at hf
  exact ⟨⟨hn.1.1.2, hf.1⟩, ⟨hn.1.2, hf.2⟩, hn.1.1.1.1, hn.1.1.1.2⟩

theorem FYNF.om {a : Tm} (h : FYNF (.Om a)) : FYNF a ∧ a ≠ .zero ∧ cmp a (.Om a) = .lt := by
  obtain ⟨hn, hf⟩ := h
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
  simp only [isFY] at hf
  refine ⟨⟨hn.1.1, hf⟩, hn.1.2, ?_⟩
  have h2 := hn.2
  unfold lt at h2
  simpa using h2

theorem FYNF.xi {n : Nat} {a : Tm} (h : FYNF (.Xi n a)) :
    1 ≤ n ∧ FYNF a ∧ a ≠ .zero ∧ cmp a (succK n) ≠ .gt ∧ inC a a (.K n) = true := by
  obtain ⟨hn, hf⟩ := h
  simp only [isNF, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hn
  simp only [isFY] at hf
  exact ⟨hn.1.1.1.1, ⟨hn.1.1.1.2, hf⟩, hn.1.1.2, hn.1.2, hn.2⟩

/-- `FY` の `Ψ` は `Ψ^0_π(α)`（`π` は `Ω_c`（`c` は後者）か `Ξ_n(p)`） -/
theorem FYNF.psi {xi pi a : Tm} (h : FYNF (.Psi xi pi a)) :
    xi = .zero ∧ IsTgt pi ∧ FYNF pi ∧ FYNF a ∧ inC a a pi = true ∧ inC pi a pi = true := by
  obtain ⟨hn, hf⟩ := h
  simp only [isNF, Bool.and_eq_true] at hn
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, hpin⟩, han⟩, hreg⟩, _⟩, hCa⟩, _⟩, hCpi⟩, _⟩ := hn
  cases pi with
  | Om c =>
    simp only [isFY, Bool.and_eq_true, beq_iff_eq] at hf
    obtain ⟨⟨hxi, hcf⟩, haf⟩ := hf
    subst hxi
    exact ⟨rfl, Or.inl ⟨c, rfl, hreg⟩, ⟨hpin, hcf⟩, ⟨han, haf⟩, hCa, hCpi⟩
  | Xi n p =>
    simp only [isFY, Bool.and_eq_true, beq_iff_eq] at hf
    obtain ⟨⟨hxi, hpf⟩, haf⟩ := hf
    subst hxi
    exact ⟨rfl, Or.inr ⟨n, p, rfl⟩, ⟨hpin, hpf⟩, ⟨han, haf⟩, hCa, hCpi⟩
  | _ => simp [isFY] at hf

theorem FYNF.k {n : Nat} (h : FYNF (.K n)) : 1 ≤ n := by
  have := h.1
  simp only [isNF, decide_eq_true_eq] at this
  exact this

theorem FYNF.zero : FYNF .zero := ⟨rfl, rfl⟩

theorem FYNF.one : FYNF .one := ⟨rfl, rfl⟩

theorem FYNF.K' {n : Nat} (h : 1 ≤ n) : FYNF (.K n) := by
  refine ⟨?_, rfl⟩
  simp only [isNF, decide_eq_true_eq]
  exact h

/-- `Ω_{K_m}` は標準形でない -/
theorem FYNF.om_ne_k {a : Tm} {m : Nat} (h : FYNF (.Om a)) : a ≠ .K m := by
  intro e
  subst e
  have h2 := h.om.2.2
  rw [cmp_principal rfl rfl, cmpP.eq_def] at h2
  simp [lev] at h2

theorem summands_FYNF : ∀ t : Tm, FYNF t → ∀ s, s ∈ summands t → FYNF s ∧ isPrincipal s = true
  | .zero, _, s, hs => by simp [summands] at hs
  | .plus a b, h, s, hs => by
    obtain ⟨ha, hb, hap, _⟩ := h.plus
    rw [summands, List.mem_cons] at hs
    cases hs with
    | inl e => rw [e]; exact ⟨ha, hap⟩
    | inr hs => exact summands_FYNF b hb s hs
  | .one, h, s, hs | .K _, h, s, hs | .Om _, h, s, hs | .Xi _ _, h, s, hs
  | .Psi _ _ _, h, s, hs => by
    simp only [summands, List.mem_singleton] at hs
    rw [hs]
    exact ⟨h, rfl⟩

theorem FYNF.of_mem_subs : ∀ {t s : Tm}, FYNF t → s ∈ subs t → FYNF s
  | .zero, s, ht, h | .one, s, ht, h | .K _, s, ht, h => by
    simp only [subs, List.mem_singleton] at h
    rw [h]
    exact ht
  | .plus a b, s, ht, h => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    obtain ⟨ha, hb, -, -⟩ := ht.plus
    rcases h with h | h | h
    · rw [h]; exact ht
    · exact FYNF.of_mem_subs ha h
    · exact FYNF.of_mem_subs hb h
  | .Om a, s, ht, h => by
    simp only [subs, List.mem_cons] at h
    rcases h with h | h
    · rw [h]; exact ht
    · exact FYNF.of_mem_subs ht.om.1 h
  | .Xi _ a, s, ht, h => by
    simp only [subs, List.mem_cons] at h
    rcases h with h | h
    · rw [h]; exact ht
    · exact FYNF.of_mem_subs ht.xi.2.1 h
  | .Psi x p a, s, ht, h => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    obtain ⟨hx, -, hp, ha, -, -⟩ := ht.psi
    subst hx
    rcases h with h | (h | h) | h
    · rw [h]; exact ht
    · simp only [subs, List.mem_singleton] at h
      rw [h]
      exact FYNF.zero
    · exact FYNF.of_mem_subs hp h
    · exact FYNF.of_mem_subs ha h

/-! ### 順序についての仮定 -/

/-- 整列性の証明が使う順序の性質：`FY` の標準形の上で `cmp` は反対称で `.eq` なら等しく、`<` は推移的。
    さらに `Ψ^0_π(a)` の引数 `a` と目標 `π` の前線（`π` について）は `Ψ^0_π(a)` 未満（K2）、`Ξ_n(a)` の引数の
    前線（`K_n` について）は `Ξ_n(a)` 未満、`c < Ψ^0_{Ω_c}(a)`。 -/
class FYOrder : Prop where
  swap : ∀ {a b : Tm}, FYNF a → FYNF b → cmp b a = (cmp a b).swap
  eq : ∀ {a b : Tm}, FYNF a → FYNF b → cmp a b = .eq → a = b
  trans : ∀ {a b c : Tm}, FYNF a → FYNF b → FYNF c → Lt a b → Lt b c → Lt a c
  k2 : ∀ {π a : Tm}, FYNF (.Psi .zero π a) → ∀ w, w ∈ fr π a → Lt w (.Psi .zero π a)
  k2t : ∀ {π a : Tm}, FYNF (.Psi .zero π a) → ∀ w, w ∈ fr π π → Lt w (.Psi .zero π a)
  k2x : ∀ {n : Nat} {a : Tm}, FYNF (.Xi n a) → ∀ w, w ∈ fr (.K n) a → Lt w (.Xi n a)
  cx : ∀ {c a : Tm}, FYNF (.Psi .zero (.Om c) a) → Lt c (.Psi .zero (.Om c) a)

section Order

variable [FYOrder]

theorem lt_transY {a b c : Tm} (ha : FYNF a) (hb : FYNF b) (hc : FYNF c)
    (h1 : Lt a b) (h2 : Lt b c) : Lt a c :=
  FYOrder.trans ha hb hc h1 h2

theorem Lt.asymmY {a b : Tm} (ha : FYNF a) (hb : FYNF b) (h : Lt a b) : ¬ Lt b a := by
  unfold Lt at *
  rw [FYOrder.swap ha hb, h]
  decide

theorem lt_of_gtY {a b : Tm} (ha : FYNF a) (hb : FYNF b) (h : cmp a b = .gt) : Lt b a := by
  unfold Lt
  rw [FYOrder.swap ha hb, h]
  rfl

theorem triY {a b : Tm} (ha : FYNF a) (hb : FYNF b) : Lt a b ∨ a = b ∨ Lt b a := by
  cases e : cmp a b with
  | lt => exact Or.inl e
  | eq => exact Or.inr (Or.inl (FYOrder.eq ha hb e))
  | gt => exact Or.inr (Or.inr (lt_of_gtY ha hb e))

/-- `¬ a < b` なら `b ≤ a` -/
theorem le_of_not_ltY {a b : Tm} (ha : FYNF a) (hb : FYNF b) (h : ¬ Lt a b) : Le b a := by
  rcases triY ha hb with h' | h' | h'
  · exact absurd h' h
  · exact Or.inl h'.symm
  · exact Or.inr h'

/-- `cmp a b ≠ .gt` なら `a ≤ b` -/
theorem le_of_ne_gtY {a b : Tm} (ha : FYNF a) (hb : FYNF b) (h : cmp a b ≠ .gt) : Le a b := by
  cases e : cmp a b with
  | lt => exact Or.inr e
  | eq => exact Or.inl (FYOrder.eq ha hb e)
  | gt => exact absurd e h

theorem not_lt_of_leY {a b : Tm} (ha : FYNF a) (hb : FYNF b) (h : Le a b) : ¬ Lt b a := by
  rcases h with rfl | h
  · exact Lt.irrefl _
  · exact Lt.asymmY ha hb h

theorem lt_of_lt_of_leY {a b c : Tm} (ha : FYNF a) (hb : FYNF b) (hc : FYNF c)
    (h1 : Lt a b) (h2 : Le b c) : Lt a c := by
  rcases h2 with rfl | h2
  · exact h1
  · exact lt_transY ha hb hc h1 h2

theorem lt_of_le_of_ltY {a b c : Tm} (ha : FYNF a) (hb : FYNF b) (hc : FYNF c)
    (h1 : Le a b) (h2 : Lt b c) : Lt a c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact lt_transY ha hb hc h1 h2

theorem le_transY {a b c : Tm} (ha : FYNF a) (hb : FYNF b) (hc : FYNF c)
    (h1 : Le a b) (h2 : Le b c) : Le a c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact Or.inr (lt_of_lt_of_leY ha hb hc h1 h2)

theorem le_antisymmY {a b : Tm} (ha : FYNF a) (hb : FYNF b) (h1 : Le a b) (h2 : Le b a) :
    a = b := by
  rcases h1 with e | h1
  · exact e
  · exact absurd h1 (not_lt_of_leY hb ha h2)

theorem eq_of_cmpP_eqY {x y : Tm} (hx : FYNF x) (hy : FYNF y) (hpx : isPrincipal x = true)
    (hpy : isPrincipal y = true) (h : cmpP x y = .eq) : x = y := by
  apply FYOrder.eq hx hy
  rw [cmp_principal hpx hpy, h]

end Order

end RTKA
