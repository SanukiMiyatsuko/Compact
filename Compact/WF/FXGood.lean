import Compact.WF.FXFF

/-! 断片 `FX` の推移性の証明の不変条件（部分項で閉じた有限集合 `S` の上の性質）。

* `LinOn S`：`<` が推移的。
* `K2fOn S`：`Ψ_c(γ) ∈ S` の前線（`Ω_c` について）は全て `Ψ_c(γ)` 未満（K2 の前線による形）。
* `K2XOn S`：`Ξ_n(γ) ∈ S` の前線（`K_n` について）は全て `Ξ_n(γ)` 未満。
* `CXOn S`：`Ψ_c(γ) ∈ S` について `c < Ψ_c(γ)`。
* `KLOn S`：`Ψ_c(β), Ξ_n(ξ) ∈ S`（同じ階）について `Ψ_c(β) < Ξ_n(ξ) ⟺ c ≤ Ξ_n(ξ)`。
* `ICOn S`：`Ψ_c(γ) ∈ S` について `Ω_c ∈ C(g, Ψ_c(γ))`。 -/

namespace RTKA

open Tm

def K2fOn (S : List Tm) : Prop :=
  ∀ c γ, Tm.Psi .zero (.Om c) γ ∈ S → ∀ w, w ∈ fr (.Om c) γ → Lt w (.Psi .zero (.Om c) γ)

def K2XOn (S : List Tm) : Prop :=
  ∀ n γ, Tm.Xi n γ ∈ S → ∀ w, w ∈ fr (.K n) γ → Lt w (.Xi n γ)

def CXOn (S : List Tm) : Prop :=
  ∀ c γ, Tm.Psi .zero (.Om c) γ ∈ S → Lt c (.Psi .zero (.Om c) γ)

def KLOn (S : List Tm) : Prop :=
  ∀ c β n ξ, Tm.Psi .zero (.Om c) β ∈ S → Tm.Xi n ξ ∈ S → lev c = n →
    (Lt (.Psi .zero (.Om c) β) (.Xi n ξ) ↔ cmp c (.Xi n ξ) ≠ .gt)

/-- 推移性の証明の不変条件 -/
structure GoodX (S : List Tm) : Prop where
  lin : LinOn S
  nf : ∀ s, s ∈ S → FXNF s
  cl : ∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S
  k2 : K2fOn S
  k2x : K2XOn S
  cx : CXOn S
  kl : KLOn S
  ic : ICOn S

namespace GoodX

variable {S : List Tm} (G : GoodX S)
include G

theorem trans {a b c : Tm} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (h1 : Lt a b) (h2 : Lt b c) :
    Lt a c :=
  G.lin a ha b hb c hc h1 h2

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

theorem sub {s r : Tm} (hs : s ∈ S) (hr : r ∈ subs s) : r ∈ S := G.cl s hs r hr

/-- 引数の大小の推移性（前線による比較の仮定 `H3`・`H4` の形） -/
theorem argTrans {α β : Tm} (hα : α ∈ S) (hβ : β ∈ S) :
    Lt α β → ∀ v, v ∈ subs α → Lt v α → Lt v β :=
  fun h _ hv hvα => G.trans (G.sub hα hv) hα hβ hvα h

/-! ### 前線による比較（`S` の元どうし） -/

theorem ff_psi {c α β : Tm} (hx : Tm.Psi .zero (.Om c) α ∈ S) (hy : Tm.Psi .zero (.Om c) β ∈ S)
    (hne : α ≠ β) :
    Lt (.Psi .zero (.Om c) α) (.Psi .zero (.Om c) β) ↔
      (Lt α β ∧ ∀ w, w ∈ fr (.Om c) α → Lt w (.Psi .zero (.Om c) β)) ∨
        (Lt β α ∧ ∃ w, w ∈ fr (.Om c) β ∧ ¬ Lt w (.Psi .zero (.Om c) α)) := by
  have hαS := G.sub hx (mem_subs_psi_a _ _ α)
  have hβS := G.sub hy (mem_subs_psi_a _ _ β)
  have hOm := G.sub hx (show Tm.Om c ∈ subs (.Psi .zero (.Om c) α) by simp [subs])
  have below : ∀ {δ}, Tm.Psi .zero (.Om c) δ ∈ S → ∀ w, w ∈ S → ¬ Lt w (.Om c) →
      ¬ Lt w (.Psi .zero (.Om c) δ) := fun hz w hw h h' =>
    h (G.trans hw hz hOm h' (lt_psi_om_self c _))
  exact RTKA.ff_psi (G.nf _ hx) (G.nf _ hy) hne (fun g => G.ic c α g hx) (fun g => G.ic c β g hy)
    (fun w hw => below hy w (G.sub hαS hw)) (fun w hw => below hx w (G.sub hβS hw))
    (G.argTrans hαS hβS) (G.argTrans hβS hαS)

theorem ff_xi {n : Nat} {α β : Tm} (hx : Tm.Xi n α ∈ S) (hy : Tm.Xi n β ∈ S) (hne : α ≠ β) :
    Lt (.Xi n α) (.Xi n β) ↔
      (Lt α β ∧ ∀ w, w ∈ fr (.K n) α → Lt w (.Xi n β)) ∨
        (Lt β α ∧ ∃ w, w ∈ fr (.K n) β ∧ ¬ Lt w (.Xi n α)) := by
  have hαS := G.sub hx (mem_subs_xi n α)
  have hβS := G.sub hy (mem_subs_xi n β)
  exact RTKA.ff_xi (G.nf _ hx) (G.nf _ hy) hne (G.argTrans hαS hβS) (G.argTrans hβS hαS)

/-- `S` の `Ξ` と `Ψ` の比較：`Ξ < Ψ_c(β)` ⟺ `Ξ < c` -/
theorem xi_lt_psi {c β ξ : Tm} {n : Nat} (hψ : Tm.Psi .zero (.Om c) β ∈ S) (hX : Tm.Xi n ξ ∈ S)
    (hl : lev c = n) : Lt (.Xi n ξ) (.Psi .zero (.Om c) β) ↔ Lt (.Xi n ξ) c := by
  have hcS := G.sub hψ (show c ∈ subs (.Psi .zero (.Om c) β) from mem_subs_psi_c _ c β)
  have hcF := G.nf _ hcS
  have hXF := G.nf _ hX
  rw [lt_xi_psi hl, G.kl c β n ξ hψ hX hl]
  constructor
  · intro h
    cases e : cmp c (Tm.Xi n ξ) with
    | lt => exact absurd (by rw [e]; decide) h
    | eq => exact absurd (by rw [e]; decide) h
    | gt => exact lt_of_gtX hcF hXF e
  · intro h e
    apply e
    unfold Lt at h
    rw [cmp_swap_FX hXF hcF, h]
    rfl

end GoodX

end RTKA
