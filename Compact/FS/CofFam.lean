import Compact.FS.CofVK

/-! 目標の族の閉包の共終性：`t = Ψ^0_π(X)` の鎖の上の `famSeq`（`fam_cof`）。

`fam_rec`（不変量）と同じく鎖をたどる。段 `ρ = Ψ^ζ_κ(γ)` では `mahlo_cof`（段の分類は `chain_low`・`chain_cls`・
`chain_hW`、下の段 `κ` へは再帰）、鎖の端 `ρ = Ξ_m(q)` では `vk_cof`。 -/

namespace RTKA.Fund

open Tm W

/-- 鎖の上の `Ψ^ζ_κ(γ)` の成分の加数の共終性 -/
theorem psi_partsC {π X ζ κ γ : Tm}
    (hIC : ∀ u, u ∈ subs (.Psi .zero π X) → u ≠ .Psi .zero π X → SeqC u (info u).seq)
    (hc : Chain π (.Psi ζ κ γ)) :
    (∀ u, u ∈ summands γ → u ≠ .one → SeqC u (info u).seq) ∧
      (∀ u, u ∈ summands ζ → u ≠ .one → SeqC u (info u).seq) := by
  have hne0 : ∀ {u : Tm}, u ∈ subs ζ → u ≠ .Psi ζ κ γ := fun hu =>
    ne_of_size_lt (by
      have := size_le_of_mem_subs hu
      simp only [Tm.size]
      omega)
  have hne1 : ∀ {u : Tm}, u ∈ subs γ → u ≠ .Psi ζ κ γ := fun hu =>
    ne_of_size_lt (by
      have := size_le_of_mem_subs hu
      simp only [Tm.size]
      omega)
  refine ⟨fun u hu _ => ?_, fun u hu _ => ?_⟩
  · obtain ⟨h1, -, h3⟩ := chain_sub (X := X) hc (subs_psi_a (mem_subs_of_mem_summands hu))
      (hne1 (mem_subs_of_mem_summands hu))
    exact hIC u h1 h3
  · obtain ⟨h1, -, h3⟩ := chain_sub (X := X) hc (subs_psi_s (mem_subs_of_mem_summands hu))
      (hne0 (mem_subs_of_mem_summands hu))
    exact hIC u h1 h3

/-- 鎖の上の `Ξ_m(q)` の添字の加数の共終性 -/
theorem xi_partsC {π X q : Tm} {m : Nat}
    (hIC : ∀ u, u ∈ subs (.Psi .zero π X) → u ≠ .Psi .zero π X → SeqC u (info u).seq)
    (hc : Chain π (.Xi m q)) : ∀ u, u ∈ summands q → u ≠ .one → SeqC u (info u).seq := fun u hu _ => by
  have hne0 : u ≠ .Xi m q := ne_of_size_lt (by
    have := size_le_of_mem_subs (mem_subs_of_mem_summands hu)
    simp only [Tm.size]
    omega)
  obtain ⟨h1, -, h3⟩ := chain_sub (X := X) hc (subs_xi (mem_subs_of_mem_summands hu)) hne0
  exact hIC u h1 h3

/-- 鎖の上の目標の Mahlo 添字の上限の加数の共終性 -/
theorem mi_partsC {π X τ : Tm}
    (hIC : ∀ u, u ∈ subs (.Psi .zero π X) → u ≠ .Psi .zero π X → SeqC u (info u).seq)
    (hc : Chain π τ) (hτt : IsTgt τ) : ∀ u, u ∈ summands (mi τ) → u ≠ .one → SeqC u (info u).seq := by
  rcases hτt with ⟨c, rfl, -⟩ | ⟨n, q, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩
  · intro u hu h1
    simp only [mi, summands, List.mem_singleton] at hu
    exact absurd hu h1
  · exact xi_partsC hIC hc
  · exact (psi_partsC hIC hc).2

/-- 目標の族の閉包の共終性（鎖の再帰） -/
theorem fam_cof {π X : Tm} (ht : WNF (.Psi .zero π X))
    (hIH : ∀ u, u ∈ subs (.Psi .zero π X) → u ≠ .Psi .zero π X → SeqI u (info u).seq)
    (hIC : ∀ u, u ∈ subs (.Psi .zero π X) → u ≠ .Psi .zero π X → SeqC u (info u).seq) :
    ∀ ρ, Chain π ρ → (∀ c, ρ ≠ .Om c) → ∀ p W, SeedP π X p → WNF (.Psi .zero ρ W) →
      Le (.Psi .zero ρ W) p → LoT (.Psi .zero π X) ρ p →
      SeqI (.Psi .zero π X) (famSeq (info ρ).fam π (some p)) →
        SeqC (.Psi .zero π X) (famSeq (info ρ).fam π (some p))
  | .Xi m q, hc, _, p, W, Sp, hw, hle, hL => by
    have hπF := ht.psi.piF
    have hρ : WNF (.Xi m q) := hc.wnf hπF
    have hqF := hρ.xi.2.1
    have hq0 := hρ.xi.2.2.1
    have hpρ : Lt p (.Xi m q) := lt_of_lt_of_leY Sp.hF hπF hρ (Sp.hπ ht) (hc.le hπF)
    have e : (info (.Xi m q)).fam = .xi m q (info q).sums := rfl
    rw [e, famSeq]
    obtain ⟨hS, hqs, hqσ⟩ := xi_parts ht hIH hc
    refine vk_cof ht hc hS hqs hqσ (xi_partsC hIC hc) (fun p' e' => ?_) (fun p' e' _ _ o => ?_)
      (xi_low ht hc hL) (fun p' e' _ _ _ => ?_)
    · cases e'
      exact Sp
    · cases e'
      intro ef
      have hWF := hw.psi.aF
      have hwρ : Lt (.Psi .zero (.Xi m q) W) (.Xi m q) := lt_psi_targetY hw
      have hC0 : inC (.Xi m q) W (.Psi .zero (.Xi m q) W) = true :=
        inC_tgt_of_k2t hw fun v hv => FWOrder.k2t hw v hv
      rcases inC_xi_iff.mp hC0 with h' | ⟨h2, h3⟩
      · exact absurd h' (Lt.asymmY hw hρ hwρ)
      have h0 : Lt .zero W := lt_transY WNF.zero hqF hWF (zero_lt hq0) h3
      have hπρ := hc.le hπF
      have hC := o.ubF W _ hWF hw h0 (fun v hv hvπ hvC =>
        coll_psiY hw v (hqF.of_mem_subs hv) hvC (lt_of_lt_of_leY (hqF.of_mem_subs hv) hπF hρ hvπ hπρ)) h2 h3
        (inC_zero _ _)
      obtain ⟨P₀, x₀, -, -, hfF, -⟩ := o.form _ o.mem
      have hf := coll_psiY hw _ hfF hC (lt_of_lt_of_leY hfF hπF hρ o.ltπ hπρ)
      rw [ef] at hf
      exact not_lt_of_leY hw Sp.hF hle hf
    · cases e'
      exact xi_hW ht hc hw hle Sp.hF hpρ
  | .Psi ζ κ γ, hc, _, p, W, Sp, hw, hle, hL => by
    have hπF := ht.psi.piF
    have hρ : WNF (.Psi ζ κ γ) := hc.wnf hπF
    have hP := hρ.psi
    have hζ0 : ζ ≠ .zero := by
      rcases hw.psi.tgt with ⟨c, e, -⟩ | ⟨n, p', e⟩ | ⟨ζ', κ', b, e, h⟩
      · cases e
      · cases e
      · cases e
        exact h
    have hpρ : Lt p (.Psi ζ κ γ) := lt_of_lt_of_leY Sp.hF hπF hρ (Sp.hπ ht) (hc.le hπF)
    have C := mctx_chain (X := X) ht hc
    have e : (info (.Psi ζ κ γ)).fam = .psi ζ (info ζ).sums κ (info κ).fam γ (info γ).sums := rfl
    rw [e, famSeq]
    obtain ⟨hSY, hSμ, hμs⟩ := psi_parts hIH hc
    obtain ⟨hSYC, hSμC⟩ := psi_partsC hIC hc
    have M := mpar_chain ht hIH (hc.snoc rfl) hP.tgt
    refine mahlo_cof C M hζ0 hSY hSμ hμs hSYC hSμC (mi_partsC hIC (hc.snoc rfl) hP.tgt) (fun p' e' => ?_)
      (fun p' e' _ _ o => ?_) (fun u hu => (hc.snoc rfl).fr_mem hπF hu) (chain_low ht hc hL) (chain_cls ht hc)
      (fun p' e' _ _ _ => ?_) fun p' S' hle' hL' =>
        fam_cof ht hIH hIC κ (hc.snoc rfl) (tgt_not_om hρ hζ0) p' γ S' C.hw0 hle' hL'
    · cases e'
      exact Sp
    · cases e'
      intro ef
      have hWF := hw.psi.aF
      have hwρ : Lt (.Psi .zero (.Psi ζ κ γ) W) (.Psi ζ κ γ) := lt_psi_targetY hw
      have hC0 : inC (.Psi ζ κ γ) W (.Psi .zero (.Psi ζ κ γ) W) = true :=
        inC_tgt_of_k2t hw fun v hv => FWOrder.k2t hw v hv
      rcases inC_psi_iff.mp hC0 with h' | ⟨h1, h2, h3, h4⟩
      · exact absurd h' (Lt.asymmY hw hρ hwρ)
      have hγ0 : Lt .zero γ := by
        have h5 : Lt .zero ζ := zero_lt hζ0
        exact lt_of_lt_of_leY WNF.zero hP.xiF hP.aF h5 (le_of_ne_gtY hP.xiF hP.aF hP.le)
      have h0 : Lt .zero W := lt_transY WNF.zero hP.aF hWF hγ0 h4
      have hπρ := hc.le hπF
      have hC := o.ubF W _ hWF hw h0 (fun v hv hvπ hvC =>
        coll_psiY hw v (hP.xiF.of_mem_subs hv) hvC (lt_of_lt_of_leY (hP.xiF.of_mem_subs hv) hπF hρ hvπ hπρ))
        h1 h3 h4 h2 (inC_zero _ _)
      obtain ⟨P₀, x₀, -, -, hfF, -⟩ := o.form _ o.mem
      have hf := coll_psiY hw _ hfF hC (lt_of_lt_of_leY hfF hπF hρ o.ltπ hπρ)
      rw [ef] at hf
      exact not_lt_of_leY hw Sp.hF hle hf
    · cases e'
      exact chain_hW ht hc hw hle Sp.hF hpρ
  | .Om c, _, h, _, _, _, _, _, _ => absurd rfl (h c)
  | .zero, _, _, _, _, _, hw, _, _ => (not_tgt_zero hw.psi.tgt).elim
  | .one, _, _, _, _, _, hw, _, _ => (not_tgt_one hw.psi.tgt).elim
  | .K _, _, _, _, _, _, hw, _, _ => (not_tgt_K hw.psi.tgt).elim
  | .plus _ _, _, _, _, _, _, hw, _, _ => (not_tgt_plus hw.psi.tgt).elim

end RTKA.Fund
