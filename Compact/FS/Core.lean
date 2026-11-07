import Compact.FS.Lt

/-! 崩壊 `Ψ^0_π(X)` の列の各分岐（標準形・減少・単調）。 -/

namespace RTKA.Fund

open Tm W

/-! ### `X = 0`：`Ψ^0_{Ω_c}(0)` の列 `B·(n+2)` -/

theorem cs_om_zero (c : Tm) :
    cs (.Om c) .zero = .mul (if c = one then one else omHat (pred c)) 2 := by
  unfold cs cseq; simp

theorem omHat_wnf {x : Tm} (hx : WNF x) (hx0 : x ≠ .zero) :
    WNF (omHat x) ∧ isPrincipal (omHat x) = true := by
  unfold omHat
  simp only [hx0, ↓reduceIte]
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    exact ⟨hx, h.1⟩
  · rename_i h
    refine ⟨WNF.om_ofY hx hx0 ?_ ?_, rfl⟩
    · intro m e; subst e; simp [isPrincipal, omegaFixed] at h
    · intro hOF; exact h (by simp [hOF.principal, hOF.fixed])

/-- `Ψ^0_{Ω_c}(0)` の列の底 `B` -/
theorem mul_base_lt {c : Tm} (ht : WNF (.Psi .zero (.Om c) .zero)) :
    WNF (if c = one then one else omHat (pred c)) ∧
    isPrincipal (if c = one then one else omHat (pred c)) = true ∧
    Lt (if c = one then one else omHat (pred c)) (.Psi .zero (.Om c) .zero) := by
  have hP := ht.psi
  have hc : WNF c := hP.piF.om.1
  have hs : isSucc c = true := by
    rcases hP.tgt with ⟨d, e, hd⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, -⟩
    · cases e; exact hd
    · cases e
    · cases e
  split
  · rename_i h1
    subst h1
    refine ⟨WNF.one, rfl, ?_⟩
    unfold Lt cmp
    simp [summands, cmpList, cmpP, lev]
  · rename_i h1
    have hpc : WNF (pred c) := wnf_pred hc
    have hpc0 : pred c ≠ .zero := by
      intro e
      apply h1
      rw [← succT_pred hc hs, e]
      rfl
    obtain ⟨hw, hp⟩ := omHat_wnf hpc hpc0
    refine ⟨hw, hp, ?_⟩
    have hlt : Lt (pred c) c := pred_lt hc hs
    unfold omHat
    simp only [hpc0, ↓reduceIte]
    split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      -- `pred c` は `K_m` か `Ω` の不動点
      by_cases hK : ∃ m, pred c = .K m
      · obtain ⟨m, hm⟩ := hK
        have hcm : c = .plus (.K m) .one := by
          rw [← succT_pred hc hs, hm]; rfl
        rw [hm]
        subst hcm
        unfold Lt cmp
        simp [summands, cmpList, cmpP, lev]
      · have hOF : IsOF (pred c) := by
          cases hq : pred c with
          | Xi n a => exact Or.inl ⟨n, a, rfl⟩
          | Psi ξ π a =>
            refine Or.inr ⟨ξ, π, a, rfl, hq ▸ hpc, ?_⟩
            intro d e
            subst e
            have h2 := h.2
            rw [hq] at h2
            have hξ : ξ = .zero := by
              have hP' := (hq ▸ hpc : WNF (.Psi ξ (.Om d) a)).psi
              have := hP'.mlt
              simp only [mi] at this
              exact lt_oneY hP'.xiF this
            subst hξ
            simp [omegaFixed, isInacc] at h2
          | K m => exact absurd ⟨m, hq⟩ hK
          | _ => rw [hq] at h; simp [isPrincipal, omegaFixed] at h
        exact (lt_OF_psiOm hOF hpc ht).mpr hlt
    · exact (lt_om_psiY ht).mpr hlt

/-- `Ψ^0_{Ω_c}(0)` の列：標準形・元の項未満・単調 -/
theorem psi_om_zero_seq {c : Tm} (ht : WNF (.Psi .zero (.Om c) .zero)) (n : Nat) :
    WNF (fundNat (.Psi .zero (.Om c) .zero) n) ∧
    Lt (fundNat (.Psi .zero (.Om c) .zero) n) (.Psi .zero (.Om c) .zero) ∧
    Lt (fundNat (.Psi .zero (.Om c) .zero) n) (fundNat (.Psi .zero (.Om c) .zero) (n + 1)) := by
  obtain ⟨hB, hBp, hBt⟩ := mul_base_lt ht
  rw [fundNat_psi0, fundNat_psi0, cs_om_zero]
  simp only [SeqD.nat]
  exact ⟨wnf_mulNat hB hBp _, mulNat_lt_prin hBp rfl hBt _,
    mulNat_lt_mulNat hB hBp (by omega)⟩

/-! ### Ω の塔 -/

theorem not_succ_OF {X : Tm} (hX : IsOF X) : ¬ isSucc X = true := by
  rw [isSucc_principal hX.principal]
  rcases hX with ⟨n, a, rfl⟩ | ⟨ξ, π, a, rfl, -, -⟩ <;> simp

/-- Ω の不動点 `X` 未満の `G` からの Ω の塔は `X` 未満 -/
theorem tower_lt_OF {G X : Tm} (hX : IsOF X) (hXF : WNF X) (hG : WNF G) (hGX : Lt G X) :
    ∀ n, Lt (tower G n) X
  | 0 => hGX
  | n + 1 => by
    show Lt (.Om (succT (tower G n))) X
    rw [lt_om_OFG hX]
    exact succT_lt_of_not_succ (wnf_tower hG n) hXF (not_succ_OF hX) (tower_lt_OF hX hXF hG hGX n)

theorem tower_mono {G : Tm} (hG : WNF G) (n : Nat) : Lt (tower G n) (tower G (n + 1)) := by
  have hw := wnf_tower hG n
  show Lt (tower G n) (.Om (succT (tower G n)))
  exact lt_transY hw (succT_WNF hw) (WNF.om_succT hw) (lt_succT _) (WNF.om_succT hw).om.2.2

end RTKA.Fund
