import Compact.WF.FYCmp

/-! 断片 `FY` の順序の性質（`FYOrder`）の証明の下準備。

`FX` の推移性の証明（`FXGood.lean` など）と同じく、部分項で閉じた有限集合 `S` の要素数についての帰納法で
不変条件 `GoodY S` を示す。`FY` では反対称性の証明に推移性が要るので、`FX` と違い反対称性（`AntiOn`）も
不変条件に入れ、新しい項 `t` との反対称性は、`t` の切断性などを示した後で導く。

不変条件：
* `LinOn S`・`AntiOn S`：`S` の上で `<` は推移的、`cmp` は反対称で `.eq` なら等しい。
* `K2YOn S`・`K2TOn S`：`Ψ^0_π(γ) ∈ S` の引数と目標の前線（`π` について）は `Ψ^0_π(γ)` 未満。
* `K2XYOn S`：`Ξ_n(γ) ∈ S` の引数の前線（`K_n` について）は `Ξ_n(γ)` 未満。
* `CXYOn S`：`Ψ^0_{Ω_c}(γ) ∈ S` について `c < Ψ^0_{Ω_c}(γ)`。 -/

namespace RTKA

open Tm

/-- `S` の上の反対称性と相等 -/
def AntiOn (S : List Tm) : Prop :=
  ∀ a, a ∈ S → ∀ b, b ∈ S → cmp b a = (cmp a b).swap ∧ (cmp a b = .eq → a = b)

def K2YOn (S : List Tm) : Prop :=
  ∀ π γ, Tm.Psi .zero π γ ∈ S → ∀ w, w ∈ fr π γ → Lt w (.Psi .zero π γ)

def K2TOn (S : List Tm) : Prop :=
  ∀ π γ, Tm.Psi .zero π γ ∈ S → ∀ w, w ∈ fr π π → Lt w (.Psi .zero π γ)

def K2XYOn (S : List Tm) : Prop :=
  ∀ n γ, Tm.Xi n γ ∈ S → ∀ w, w ∈ fr (.K n) γ → Lt w (.Xi n γ)

def CXYOn (S : List Tm) : Prop :=
  ∀ c γ, Tm.Psi .zero (.Om c) γ ∈ S → Lt c (.Psi .zero (.Om c) γ)

/-- `FY` の順序の性質の証明の不変条件 -/
structure GoodY (S : List Tm) : Prop where
  lin : LinOn S
  anti : AntiOn S
  nf : ∀ s, s ∈ S → FYNF s
  cl : ∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S
  k2 : K2YOn S
  k2t : K2TOn S
  k2x : K2XYOn S
  cx : CXYOn S

namespace GoodY

variable {S : List Tm} (G : GoodY S)
include G

theorem sub {s r : Tm} (hs : s ∈ S) (hr : r ∈ subs s) : r ∈ S := G.cl s hs r hr

theorem trans {a b c : Tm} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (h1 : Lt a b) (h2 : Lt b c) :
    Lt a c :=
  G.lin a ha b hb c hc h1 h2

theorem swap {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) : cmp b a = (cmp a b).swap :=
  (G.anti a ha b hb).1

theorem eq {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) (h : cmp a b = .eq) : a = b :=
  (G.anti a ha b hb).2 h

theorem asymm {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) (h : Lt a b) : ¬ Lt b a := by
  unfold Lt at *
  rw [G.swap ha hb, h]
  decide

theorem lt_of_gt {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) (h : cmp a b = .gt) : Lt b a := by
  unfold Lt
  rw [G.swap ha hb, h]
  rfl

theorem tri {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) : Lt a b ∨ a = b ∨ Lt b a := by
  cases e : cmp a b with
  | lt => exact Or.inl e
  | eq => exact Or.inr (Or.inl (G.eq ha hb e))
  | gt => exact Or.inr (Or.inr (G.lt_of_gt ha hb e))

/-- `¬ a < b` なら `b ≤ a` -/
theorem le_of_not_lt {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) (h : ¬ Lt a b) : Le b a := by
  rcases G.tri ha hb with h' | h' | h'
  · exact absurd h' h
  · exact Or.inl h'.symm
  · exact Or.inr h'

theorem le_of_ne_gt {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) (h : cmp a b ≠ .gt) : Le a b := by
  cases e : cmp a b with
  | lt => exact Or.inr e
  | eq => exact Or.inl (G.eq ha hb e)
  | gt => exact absurd e h

theorem not_lt_of_le {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) (h : Le a b) : ¬ Lt b a := by
  rcases h with rfl | h
  · exact Lt.irrefl _
  · exact G.asymm ha hb h

theorem lt_of_lt_of_le {a b c : Tm} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (h1 : Lt a b)
    (h2 : Le b c) : Lt a c := by
  rcases h2 with rfl | h2
  · exact h1
  · exact G.trans ha hb hc h1 h2

theorem lt_of_le_of_lt {a b c : Tm} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (h1 : Le a b)
    (h2 : Lt b c) : Lt a c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact G.trans ha hb hc h1 h2

theorem le_trans {a b c : Tm} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (h1 : Le a b)
    (h2 : Le b c) : Le a c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact Or.inr (G.lt_of_lt_of_le ha hb hc h1 h2)

theorem eq_of_cmpP_eq {x y : Tm} (hx : x ∈ S) (hy : y ∈ S) (hpx : isPrincipal x = true)
    (hpy : isPrincipal y = true) (h : cmpP x y = .eq) : x = y := by
  apply G.eq hx hy
  rw [cmp_principal hpx hpy, h]

/-- 引数の大小の推移性（前線による比較の仮定の形） -/
theorem argTrans {α β : Tm} (hα : α ∈ S) (hβ : β ∈ S) :
    Lt α β → ∀ v, v ∈ subs α → Lt v α → Lt v β :=
  fun h _ hv hvα => G.trans (G.sub hα hv) hα hβ hvα h

end GoodY

end RTKA
