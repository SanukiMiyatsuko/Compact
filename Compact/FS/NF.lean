import Compact.FS.Dom

/-! 基本列が標準形を保つこと（の土台）：`Ψ` の項の組み立て、正則項の列の始点 `base σ` の標準形。 -/

namespace RTKA.Fund

open Tm W

/-- `PsiNF` から `Ψ` の項の標準形を組み立てる（`WNF.psi` の逆） -/
theorem WNF.mk_psi {xi pi a : Tm} (h : PsiNF xi pi a) : WNF (.Psi xi pi a) := by
  show isNF (.Psi xi pi a) = true
  have hreg : isRegTerm pi = true := by
    rcases h.tgt with ⟨c, rfl, hc⟩ | ⟨n, p, rfl⟩ | ⟨ζ, κ, b, rfl, hζ⟩
    · simpa [isRegTerm] using hc
    · rfl
    · simp [isRegTerm, hζ]
  have hmOf : mOf pi = some (mi pi) := by
    rcases h.tgt with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩ <;> rfl
  have hle : (cmp xi a != .gt) = true := by simpa using h.le
  have hlt : lt xi (mi pi) = true := by
    have := h.mlt
    unfold Lt at this
    simp [lt, this]
  have hx : isNF xi = true := h.xiF
  have hp : isNF pi = true := h.piF
  have ha : isNF a = true := h.aF
  simp only [isNF, hmOf, hx, hp, ha, hreg, hle, h.Ca, h.Cxi, h.Cpi, hlt, h.mC, Bool.and_self]

/-- `Ω_c` 未満の標準形の項は `C(g, Ω_c)` に入る -/
theorem inC_of_lt_om {c g : Tm} (hc : WNF (.Om c)) : ∀ x, WNF x → Lt x (.Om c) → inC x g (.Om c) = true
  | .zero, _, _ => inC_zero _ _
  | .one, _, _ => inC_one _ _
  | .K n, _, _ => inC_K _ _ _
  | .plus a b, hx, hlt => by
    obtain ⟨ha, hb, -, -⟩ := hx.plus
    rw [inC_plus, Bool.and_eq_true]
    exact ⟨inC_of_lt_om hc a ha (lt_transY ha hx hc (lt_plus_leftY hx) hlt),
      inC_of_lt_om hc b hb (lt_transY hb hx hc (lt_plus_rightY hx) hlt)⟩
  | .Om y, hx, hlt => by
    rw [inC_om]
    obtain ⟨hy, -, hyo⟩ := hx.om
    exact inC_of_lt_om hc y hy (lt_transY hy hx hc hyo hlt)
  | .Xi m a, _, hlt => inC_of_lt_node (Or.inl ⟨m, a, rfl⟩) hlt
  | .Psi s p a, _, hlt => inC_of_lt_node (Or.inr ⟨s, p, a, rfl⟩) hlt

/-- `Ψ^0_{Ω_c}(0)`（`c` は後者）は標準形 -/
theorem wnf_base_om {c : Tm} (hc : WNF (.Om c)) (hs : isSucc c = true) :
    WNF (.Psi .zero (.Om c) .zero) := by
  obtain ⟨hcF, -, hco⟩ := hc.om
  apply WNF.mk_psi
  exact {
    tgt := Or.inl ⟨c, rfl, hs⟩
    xiF := WNF.zero
    piF := hc
    aF := WNF.zero
    le := by simp [cmp_self]
    Ca := inC_zero _ _
    Cxi := inC_zero _ _
    Cpi := by rw [inC_om]; exact inC_of_lt_om hc c hcF hco
    mlt := by show Lt .zero .one; exact zero_lt (by intro e; cases e)
    mC := inC_zero _ _ }

/-- `C(g0, R)` に入る `x` は、`R` についての前線が全て `d` 未満なら、`g0 ≤ g` で `C(g, d)` に入る -/
theorem inC_lift {R g0 g d x : Tm} (hx : WNF x) (hg0 : WNF g0) (hg : WNF g) (h0 : inC x g0 R = true)
    (hle : Le g0 g) (hfr : ∀ w, w ∈ fr R x → Lt w d) : inC x g d = true :=
  inC_of_fr x h0 (fun _ hv hvg => lt_of_lt_of_leY (hx.of_mem_subs hv) hg0 hg hvg hle)
    (fun w hw => inC_of_lt_node (fr_node hw) (hfr w hw))

theorem cmp_zero_ne_gt (x : Tm) : cmp .zero x ≠ .gt := by
  unfold cmp
  cases summands x <;> simp [summands, cmpList]

/-- `Ψ^0_{Ξ_m(q)}(q+1)` は標準形 -/
theorem wnf_base_xi {m : Nat} {q : Tm} (h : WNF (.Xi m q)) : WNF (.Psi .zero (.Xi m q) (sc q)) := by
  obtain ⟨-, hq, hq0, -, hqC⟩ := h.xi
  have hsq : WNF (sc q) := succT_WNF hq
  have hC : inC q (sc q) (.Xi m q) = true :=
    inC_lift hq hq hsq hqC (Or.inr (lt_succT q)) (fun w hw => FWOrder.k2x h w hw)
  apply WNF.mk_psi
  exact {
    tgt := Or.inr (Or.inl ⟨m, q, rfl⟩)
    xiF := WNF.zero
    piF := h
    aF := hsq
    le := cmp_zero_ne_gt _
    Ca := inC_succT hC
    Cxi := inC_zero _ _
    Cpi := by
      rw [inC_xi_iff]
      exact Or.inr ⟨hC, lt_succT q⟩
    mlt := zero_lt hq0
    mC := inC_zero _ _ }

/-- `Ψ^0_{Ψ^ζ_κ(γ)}(γ+1)`（`ζ ≠ 0`）は標準形 -/
theorem wnf_base_psi {ζ κ γ : Tm} (h : WNF (.Psi ζ κ γ)) (hζ : ζ ≠ .zero) :
    WNF (.Psi .zero (.Psi ζ κ γ) (sc γ)) := by
  have hP := h.psi
  have hsγ : WNF (sc γ) := succT_WNF hP.aF
  have hle : Le γ (sc γ) := Or.inr (lt_succT γ)
  have hCγ : inC γ (sc γ) (.Psi ζ κ γ) = true :=
    inC_lift hP.aF hP.aF hsγ hP.Ca hle (fun w hw => FWOrder.k2 h w hw)
  have hCκ : inC κ (sc γ) (.Psi ζ κ γ) = true :=
    inC_lift hP.piF hP.aF hsγ hP.Cpi hle (fun w hw => FWOrder.k2t h w hw)
  have hCζ : inC ζ (sc γ) (.Psi ζ κ γ) = true :=
    inC_lift hP.xiF hP.aF hsγ hP.Cxi hle (fun w hw => FWOrder.k2s h w hw)
  apply WNF.mk_psi
  exact {
    tgt := Or.inr (Or.inr ⟨ζ, κ, γ, rfl, hζ⟩)
    xiF := WNF.zero
    piF := h
    aF := hsγ
    le := cmp_zero_ne_gt _
    Ca := inC_succT hCγ
    Cxi := inC_zero _ _
    Cpi := by
      rw [inC_psi_iff]
      exact Or.inr ⟨hCκ, hCζ, hCγ, lt_succT γ⟩
    mlt := zero_lt hζ
    mC := inC_zero _ _ }

/-- `K_n` の列の始点 `K_{n-1}`（`n ≤ 1` なら 0）は標準形 -/
theorem wnf_base_K (n : Nat) : WNF (base (.K n)) := by
  simp only [base]
  split
  · exact WNF.zero
  · show isNF (.K (n - 1)) = true; simp [isNF]; omega

/-! ### 構造的な部分：和・Ω・正則項（崩壊 `Ψ^0_π(X)` の列は仮定として） -/

theorem wnf_tower {G : Tm} (hG : WNF G) : ∀ n, WNF (tower G n)
  | 0 => hG
  | n + 1 => WNF.om_succT (wnf_tower hG n)

/-- 崩壊 `Ψ^0_π(X)` の、共終数が正則項の場合の列が標準形を保つこと -/
def PsiBigNF : Prop :=
  ∀ π X ξ σ, WNF (.Psi .zero π X) → WNF ξ → dom (.Psi .zero π X) = .big σ → Lt ξ σ →
    WNF (fundBig (.Psi .zero π X) ξ)

/-- 崩壊 `Ψ^0_π(X)` の、共終数が `ω` の場合の列が標準形を保つこと -/
def PsiNatNF : Prop :=
  ∀ π X n, WNF (.Psi .zero π X) → dom (.Psi .zero π X) = .omega → WNF (fundNat (.Psi .zero π X) n)

theorem wnf_fundBig_of (hψ : PsiBigNF) :
    ∀ (t ξ σ : Tm), WNF t → WNF ξ → dom t = .big σ → Lt ξ σ → WNF (fundBig t ξ)
  | .plus a b, ξ, σ, ht, hξ, hd, hlt => by
    obtain ⟨ha, hb, -, -⟩ := ht.plus
    rw [dom_plus] at hd
    rw [fundBig_plus]
    exact wnf_oadd ha (wnf_fundBig_of hψ b ξ σ hb hξ hd hlt)
  | .K n, ξ, _, _, hξ, _, _ => by
    rw [fundBig_K]
    exact wnf_oadd (wnf_base_K n) hξ
  | .Xi m q, ξ, _, ht, hξ, _, _ => by
    rw [fundBig_xi]
    exact wnf_oadd (wnf_base_xi ht) hξ
  | .Om c, ξ, σ, ht, hξ, hd, hlt => by
    rw [fundBig_om]
    split
    · rename_i hs
      exact wnf_oadd (wnf_base_om ht hs) hξ
    · rename_i hs
      rw [dom_om, ite_eq_right hs] at hd
      exact WNF.om_succT (wnf_fundBig_of hψ c ξ σ ht.om.1 hξ hd hlt)
  | .Psi ζ κ γ, ξ, σ, ht, hξ, hd, hlt => by
    by_cases hζ : ζ = .zero
    · subst hζ
      exact hψ κ γ ξ σ ht hξ hd hlt
    · rw [fundBig_psi, ite_eq_right hζ]
      exact wnf_oadd (wnf_base_psi ht hζ) hξ
  | .zero, _, _, _, _, hd, _ | .one, _, _, _, _, hd, _ => by cases hd

theorem wnf_fundNat_of (hψ : PsiNatNF) :
    ∀ (t : Tm) (n : Nat), WNF t → dom t = .omega → WNF (fundNat t n)
  | .plus a b, n, ht, hd => by
    obtain ⟨ha, hb, -, -⟩ := ht.plus
    rw [dom_plus] at hd
    rw [fundNat_plus]
    exact wnf_oadd ha (wnf_fundNat_of hψ b n hb hd)
  | .Om c, n, ht, hd => by
    rw [dom_om] at hd
    split at hd
    · cases hd
    · rename_i hs
      rw [fundNat_om hs]
      exact WNF.om_succT (wnf_fundNat_of hψ c n ht.om.1 hd)
  | .Psi ζ κ γ, n, ht, hd => by
    by_cases hζ : ζ = .zero
    · subst hζ
      exact hψ κ γ n ht hd
    · rw [dom_psi, ite_eq_right hζ] at hd
      cases hd
  | .zero, _, _, hd | .one, _, _, hd | .K _, _, _, hd | .Xi _ _, _, _, hd => by cases hd

/-! ### `Ψ^0_π(A)` の標準形 -/

/-- 目標 `π` は、その引数 `r` が `A` 未満なら `C(A, π)` に入る -/
theorem inC_tgt {π A : Tm} (hπ : WNF π) (ht : IsTgt π) (hA : WNF A)
    (hr : ∀ r, argR? π = some r → Lt r A) : inC π A π = true := by
  rcases ht with ⟨c, rfl, -⟩ | ⟨n, q, rfl⟩ | ⟨ζ, κ, γ, rfl, -⟩
  · obtain ⟨hc, -, hco⟩ := hπ.om
    rw [inC_om]
    exact inC_of_lt_om hπ c hc hco
  · obtain ⟨-, hq, -, -, hqC⟩ := hπ.xi
    have hqA := hr q rfl
    rw [inC_xi_iff]
    exact Or.inr ⟨inC_lift hq hq hA hqC (Or.inr hqA) (fun w hw => FWOrder.k2x hπ w hw), hqA⟩
  · have hP := hπ.psi
    have hγA := hr γ rfl
    have hle : Le γ A := Or.inr hγA
    rw [inC_psi_iff]
    exact Or.inr ⟨inC_lift hP.piF hP.aF hA hP.Cpi hle (fun w hw => FWOrder.k2t hπ w hw),
      inC_lift hP.xiF hP.aF hA hP.Cxi hle (fun w hw => FWOrder.k2s hπ w hw),
      inC_lift hP.aF hP.aF hA hP.Ca hle (fun w hw => FWOrder.k2 hπ w hw), hγA⟩

theorem mi_pos {π : Tm} (hπ : WNF π) (ht : IsTgt π) : Lt .zero (mi π) := by
  rcases ht with ⟨c, rfl, -⟩ | ⟨n, q, rfl⟩ | ⟨ζ, κ, γ, rfl, hζ⟩
  · exact zero_lt (by intro e; cases e)
  · exact zero_lt hπ.xi.2.2.1
  · exact zero_lt hζ

/-- `A` が標準形で `A ∈ C(A, π)`、目標の引数が `A` 未満なら `Ψ^0_π(A)` は標準形 -/
theorem wnf_psi0 {π A : Tm} (hπ : WNF π) (ht : IsTgt π) (hA : WNF A) (hC : inC A A π = true)
    (hr : ∀ r, argR? π = some r → Lt r A) : WNF (.Psi .zero π A) :=
  WNF.mk_psi {
    tgt := ht
    xiF := WNF.zero
    piF := hπ
    aF := hA
    le := cmp_zero_ne_gt _
    Ca := hC
    Cxi := inC_zero _ _
    Cpi := inC_tgt hπ ht hA hr
    mlt := mi_pos hπ ht
    mC := inC_zero _ _ }

end RTKA.Fund
