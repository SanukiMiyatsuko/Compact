import Compact.WF.FXFront

/-! 崩壊の性質と、前線による比較の言い換え（断片 `FX`）。

* `coll_psi`・`coll_xi`：崩壊の性質 `C(γ, t) ∩ R ⊆ t`。推移性を使わず、項についての帰納法で示す。
* `ff_psi`・`ff_xi`：同じ正則項の崩壊項どうしの比較を前線で書き直したもの（再帰的経路順序の形）。
* `ff_kl`：`Ψ_c(β)` と `Ξ_n(ξ)` の比較を前線で書き直したもの。 -/

namespace RTKA

open Tm

/-- 前線の元は `Ξ` か `Ψ` の節点 -/
theorem fr_node {R : Tm} : ∀ {x w : Tm}, w ∈ fr R x →
    (∃ m a, w = .Xi m a) ∨ (∃ s p a, w = .Psi s p a)
  | .zero, _, h | .one, _, h | .K _, _, h => by simp [fr] at h
  | .plus a b, w, h => by
    rw [fr, List.mem_append] at h
    rcases h with h | h
    · exact fr_node h
    · exact fr_node h
  | .Om a, w, h => by rw [fr] at h; exact fr_node h
  | .Xi m a, w, h => by
    rw [fr] at h
    by_cases hR : Lt (.Xi m a) R
    · simp only [hR, ↓reduceIte, List.mem_singleton] at h
      exact Or.inl ⟨m, a, h⟩
    · simp only [hR, ↓reduceIte] at h
      exact fr_node h
  | .Psi s p a, w, h => by
    rw [fr] at h
    by_cases hR : Lt (.Psi s p a) R
    · simp only [hR, ↓reduceIte, List.mem_singleton] at h
      exact Or.inr ⟨s, p, a, h⟩
    · simp only [hR, ↓reduceIte, List.mem_append] at h
      rcases h with (h | h) | h
      · exact fr_node h
      · exact fr_node h
      · exact fr_node h

theorem inC_of_lt_node {w g d : Tm} (hw : (∃ m a, w = .Xi m a) ∨ (∃ s p a, w = .Psi s p a))
    (h : Lt w d) : inC w g d = true := by
  rcases hw with ⟨m, a, rfl⟩ | ⟨s, p, a, rfl⟩
  · exact inC_xi_iff.mpr (Or.inl h)
  · exact inC_psi_iff.mpr (Or.inl h)

/-! ### 崩壊の性質 -/

theorem FXNF.K' {n : Nat} (h : 1 ≤ n) : FXNF (.K n) := by
  refine ⟨?_, rfl⟩
  simp only [isNF, decide_eq_true_eq]
  exact h

theorem lev_le_of_lt_K {z : Tm} {n : Nat} (hn : 1 ≤ n) (hz : FXNF z) (h : Lt z (.K n)) :
    lev z ≤ n := by
  cases hs : summands z with
  | nil =>
    have : z = .zero := by cases z <;> simp_all [summands]
    subst this
    simp [lev]
  | cons x xs =>
    have hx := summands_FXNF z hz x (by rw [hs]; exact List.mem_cons_self)
    unfold Lt at h
    rw [cmp_eq, hs, show summands (Tm.K n) = [.K n] from rfl] at h
    have hl := lev_head hs
    rcases cmpList_lt_cases h with e | ⟨-, e'⟩
    · have := lev_le_of_cmpP_lt e
      simp only [lev] at this
      rcases Nat.lt_or_eq_of_le this with h1 | h1
      · rw [← hl]; omega
      · exact absurd e (not_lt_isBotX (by simp only [lev]; exact h1) rfl hx.1 (FXNF.K' hn))
    · cases xs with
      | nil => rw [cmpList_nil_nil] at e'; cases e'
      | cons _ _ => rw [cmpList_cons_nil] at e'; cases e'

/-- `Ψ_c(γ)` の崩壊の性質：`z ∈ C(γ, Ψ_c(γ))` で `z < Ω_c` なら `z < Ψ_c(γ)` -/
theorem coll_psi {c γ : Tm} (ht : FXNF (.Psi .zero (.Om c) γ)) :
    ∀ z, FXNF z → inC z γ (.Psi .zero (.Om c) γ) = true → Lt z (.Om c) →
      Lt z (.Psi .zero (.Om c) γ) := by
  obtain ⟨-, c', hc', hcF, -, hγF, -, -⟩ := ht.psi
  cases hc'
  have hc := hcF.om.1
  have bot : ∀ z, isBot z = true → lev z ≤ lev c → Lt z (.Psi .zero (.Om c) γ) := by
    intro z hb hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · cases z <;> simp [isBot] at hb
      all_goals exact (lt_principal_iff rfl rfl).mpr (lt_of_isBotX hl rfl rfl rfl ht)
  intro z
  induction z with
  | zero => intros; exact zero_lt (by intro e; cases e)
  | one =>
    intro hz _ hlt
    have hl := lev_le_of_ltX hz hcF hlt
    simp only [lev] at hl
    exact bot _ rfl hl
  | K m =>
    intro hz _ hlt
    have hl := lev_le_of_ltX hz hcF hlt
    simp only [lev] at hl
    exact bot _ rfl hl
  | plus a b iha _ =>
    intro hz hin hlt
    rw [inC_plus, Bool.and_eq_true] at hin
    obtain ⟨haF, -, hap, -⟩ := hz.plus
    have hao : Lt a (.Om c) := (lt_principal_iff hap rfl).mpr (lt_head_of_lt_plus rfl hlt)
    have := iha haF hin.1 hao
    exact lt_of_head_lt rfl (summands_plus a b) ((lt_principal_iff hap rfl).mp this)
  | Om g _ =>
    intro hz _ hlt
    have hgF := hz.om.1
    have hgc := (lt_om_iffX hgF hc).mp hlt
    have hl := lev_le_of_ltX hz hcF hlt
    simp only [lev] at hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · exact (lt_om_psi g c γ hl).mpr hgc
  | Xi m f _ =>
    intro hz hin hlt
    rcases inC_xi_iff.mp hin with h | ⟨hf, _⟩
    · exact h
    have hl := lev_le_of_ltX hz hcF hlt
    simp only [lev] at hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · have hXc : Lt (.Xi m f) c := (lt_xi_om hl.symm hc hz).mp hlt
      have hcX : cmp c (.Xi m f) = .gt := by
        unfold Lt at hXc
        rw [cmp_swap_FX hz hc, hXc]
        rfl
      rw [lt_xi_psi hl.symm, lt_psi_xi hl.symm]
      rintro (h | ⟨-, h⟩)
      · exact h hcX
      · rw [hf] at h; cases h
  | Psi s p β _ _ _ =>
    intro hz hin hlt
    obtain ⟨rfl, d, rfl, hdF, -, hβF, -⟩ := hz.psi
    rcases inC_psi_iff.mp hin with h | ⟨hp, -, hβ, hβγ⟩
    · exact h
    have hl := lev_le_of_ltX hz hcF hlt
    simp only [lev] at hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · have hcd : ¬ Lt c d := (lt_psi_om c d β hl.symm).mp hlt
      rcases triX hdF.om.1 hc with h | h | h
      · exact lt_psi_psi_of_lt d c β γ hl h
      · subst h
        have hne : β ≠ γ := fun e => by subst e; exact Lt.irrefl _ hβγ
        exact (lt_psi_psi_same hne).mpr (Or.inl ⟨hβγ, hβ, hp⟩)
      · exact absurd h hcd

/-- `Ξ_n(γ)` の崩壊の性質：`z ∈ C(γ, Ξ_n(γ))` で `z < K_n` なら `z < Ξ_n(γ)` -/
theorem coll_xi {n : Nat} {γ : Tm} (ht : FXNF (.Xi n γ)) :
    ∀ z, FXNF z → inC z γ (.Xi n γ) = true → Lt z (.K n) → Lt z (.Xi n γ) := by
  obtain ⟨hn, hγF, -, -, -⟩ := ht.xi
  have bot : ∀ z, isBot z = true → lev z ≤ n → Lt z (.Xi n γ) := by
    intro z hb hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · cases z <;> simp [isBot] at hb
      all_goals exact (lt_principal_iff rfl rfl).mpr (lt_of_isBotX hl rfl rfl rfl ht)
  intro z
  induction z with
  | zero => intros; exact zero_lt (by intro e; cases e)
  | one => intro hz _ hlt; exact bot _ rfl (lev_le_of_lt_K hn hz hlt)
  | K m => intro hz _ hlt; exact bot _ rfl (lev_le_of_lt_K hn hz hlt)
  | plus a b iha _ =>
    intro hz hin hlt
    rw [inC_plus, Bool.and_eq_true] at hin
    obtain ⟨haF, -, hap, -⟩ := hz.plus
    have hao : Lt a (.K n) := (lt_principal_iff hap rfl).mpr (lt_head_of_lt_plus rfl hlt)
    have := iha haF hin.1 hao
    exact lt_of_head_lt rfl (summands_plus a b) ((lt_principal_iff hap rfl).mp this)
  | Om g ihg =>
    intro hz hin hlt
    rw [inC_om] at hin
    have hgF := hz.om.1
    have hl := lev_le_of_lt_K hn hz hlt
    simp only [lev] at hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · have := ihg hgF hin (lt_of_lev_lt' (by simp only [lev]; omega))
      exact (lt_om_xi g γ n hl).mpr this
  | Xi m f _ =>
    intro hz hin hlt
    rcases inC_xi_iff.mp hin with h | ⟨hf, hfγ⟩
    · exact h
    have hl := lev_le_of_lt_K hn hz hlt
    simp only [lev] at hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · subst hl
      have hne : f ≠ γ := fun e => by subst e; exact Lt.irrefl _ hfγ
      exact (lt_xi_xi_same hz.xi.2.1 hγF hne).mpr (Or.inl ⟨hfγ, hf⟩)
  | Psi s p β _ ihp _ =>
    intro hz hin hlt
    obtain ⟨rfl, d, rfl, hdF, -, -, -⟩ := hz.psi
    rcases inC_psi_iff.mp hin with h | ⟨hp, -, -, -⟩
    · exact h
    have hl := lev_le_of_lt_K hn hz hlt
    simp only [lev] at hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · have hdo := ihp hdF hp (lt_of_lev_lt' (by simp only [lev]; omega))
      have hd : Lt d (.Xi n γ) := (lt_om_xi d γ n hl).mp hdo
      refine (lt_psi_xi hl).mpr (Or.inl ?_)
      unfold Lt at hd
      rw [hd]
      decide

end RTKA
