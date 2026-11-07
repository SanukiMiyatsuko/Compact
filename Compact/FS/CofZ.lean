import Compact.FS.CofLimit

/-! 族の閉包の共終性の準備。

* 補題 Z：Mahlo 添字を持てる目標 `τ`（`lev τ = L`）について、`C(m(τ), τ)` の `τ` 以上の元は `K_L` 以上。
  `τ = Ξ_L(q)` なら `C(q, τ) ∩ K_L ⊂ τ`、`τ = Ψ^z_κ(b)` なら `κ` に帰着する。
* 補題 W：`K_L` より大きく `K_L⁺` 以下の目標は `K_L⁺`。
* `leaf_natG`・`leaf_bigG`：段 `τ` の列の共終性の一歩（添字は項ごとに違ってよい。段の節点の扱いは仮定）。 -/

namespace RTKA.Fund

open Tm W

/-- Mahlo 添字を持てる目標は `Ω` の不動点 -/
theorem tgt_isOF {τ : Tm} (hτF : WNF τ) (hτt : IsTgt τ) (hτΩ : ∀ c, τ ≠ .Om c) : IsOF τ := by
  rcases hτt with ⟨c, rfl, -⟩ | ⟨n, q, rfl⟩ | ⟨ζ, κ, b, rfl, hζ⟩
  · exact absurd rfl (hτΩ c)
  · exact Or.inl ⟨n, q, rfl⟩
  · exact IsOF.psi hτF (tgt_not_om hτF hζ)

/-- 補題 Z：`C(m(τ), τ)` の `τ` 以上の元は `K_{lev τ}` 未満にならない -/
theorem not_lt_K_of_inC_mi {τ : Tm} (hτF : WNF τ) (hτt : IsTgt τ) (hτΩ : ∀ c, τ ≠ .Om c) :
    ∀ u, WNF u → inC u (mi τ) τ = true → Le τ u → ¬ Lt u (.K (lev τ)) := by
  have hOF := tgt_isOF hτF hτt hτΩ
  have hτp := IsOF.principal hOF
  have hL : 1 ≤ lev τ := lev_posY hτF (IsTgt.ne_zero hτt)
  have hbot : isBot τ = false := by
    rcases hOF with ⟨n, a, rfl⟩ | ⟨ξ, π, a, rfl, -, -⟩ <;> rfl
  have hτ1 : τ ≠ .one := by
    rcases hOF with ⟨n, a, rfl⟩ | ⟨ξ, π, a, rfl, -, -⟩ <;> intro e <;> cases e
  have hKτ : ∀ j, j + 1 ≤ lev τ → Lt (.K j) τ := fun j h => K_lt_of_lev hτF hτp hbot h
  intro u
  induction hn : u.size using Nat.strongRecOn generalizing u with
  | ind n ih =>
    intro hu hC hτu huK
    have hnu : ¬ Lt u τ := not_lt_of_leY hτF hu hτu
    cases u with
    | zero =>
      rcases hτu with e | h
      · exact IsTgt.ne_zero hτt e
      · exact not_lt_zero _ h
    | one =>
      rcases hτu with e | h
      · exact hτ1 e
      · exact IsTgt.ne_zero hτt (lt_oneY hτF h)
    | K j =>
      have hj := (lt_K_iffY hu hL).mp huK
      simp only [lev] at hj
      exact hnu (hKτ j hj)
    | plus a b =>
      obtain ⟨ha, hb, -, -⟩ := hu.plus
      rw [inC_plus, Bool.and_eq_true] at hC
      have hτa : Le τ a := le_of_not_ltY ha hτF fun h => hnu ((lt_plus_prin_iffY hu hτp).mpr h)
      have haK : Lt a (.K (lev τ)) := lt_transY ha hu (WNF.K' hL) (lt_plus_leftY hu) huK
      exact ih a.size (by rw [← hn]; simp only [Tm.size]; omega) a rfl ha hC.1 hτa haK
    | Om e =>
      have heF := hu.om.1
      rw [inC_om] at hC
      have hτe : Le τ e := le_of_not_ltY heF hτF fun h => hnu ((lt_om_OFG hOF).mpr h)
      have heK : Lt e (.K (lev τ)) := lt_transY heF hu (WNF.K' hL) hu.om.2.2 huK
      exact ih e.size (by rw [← hn]; simp only [Tm.size]; omega) e rfl heF hC hτe heK
    | Xi j a =>
      obtain ⟨hj, haF, -, -, -⟩ := hu.xi
      have hjL : j ≤ lev τ := (lt_K_iffY hu hL).mp huK
      by_cases hjl : j = lev τ
      · rcases inC_xi_iff.mp hC with h | ⟨h1, h2⟩
        · exact hnu h
        · exact hnu (xi_lt_tgt hu τ hτF hτt hjl.symm h2 h1)
      · have h1 : Lt (.Xi j a) (.K j) := (lt_K_iffY hu hj).mpr (Nat.le_refl _)
        exact hnu (lt_transY hu (WNF.K' hj) hτF h1 (hKτ j (by omega)))
    | Psi z k a =>
      have hP := hu.psi
      rcases inC_psi_iff.mp hC with h | ⟨h1, -, -, -⟩
      · exact hnu h
      · have hτk : Le τ k := le_transY hτF hu hP.piF hτu (Or.inr (lt_psi_targetY hu))
        have hkK : Lt k (.K (lev τ)) := (lt_K_iffY hP.piF hL).mpr (by
          have := (lt_K_iffY hu hL).mp huK
          simpa only [lev] using this)
        exact ih k.size (by rw [← hn]; simp only [Tm.size]; omega) k rfl hP.piF h1 hτk hkK

/-- 補題 W：`K_L` より大きく `K_L⁺` 以下の目標は `K_L⁺` -/
theorem tgt_eq_succK {σ : Tm} {L : Nat} (hσF : WNF σ) (hσt : IsTgt σ) (hL : 1 ≤ L)
    (h1 : Lt (.K L) σ) (h2 : Le σ (succK L)) : σ = succK L := by
  have hS := WNF.succK hL
  have hKF := WNF.K' hL
  rcases hσt with ⟨c, rfl, -⟩ | ⟨n, q, rfl⟩ | ⟨ζ, κ, b, rfl, hζ⟩
  · have hcF := hσF.om.1
    have hKc : Lt (.K L) c := (lt_K_omY hL hcF).mp h1
    have hle : Le (succT (.K L)) c := succT_leY hKF hcF hKc
    have h3 : Le (succK L) (.Om c) := le_om_of_leY (succT_WNF hKF) hcF hle
    exact le_antisymmY hσF hS h2 h3
  · exact absurd (succK_lt_of_OF hL (Or.inl ⟨n, q, rfl⟩) hσF h1) (not_lt_of_leY hσF hS h2)
  · exact absurd (succK_lt_of_OF hL (IsOF.psi hσF (tgt_not_om hσF hζ)) hσF h1) (not_lt_of_leY hσF hS h2)

/-! ### 段の列の一歩（添字は項ごと） -/

/-- `ω` 型：段の節点は仮定 `hL`、下の段は `hlow` -/
theorem leaf_natG {π X τ : Tm} {s : SeqD} (ht : WNF (.Psi .zero π X)) (hτt : IsTgt τ) (hπτ : Le π τ)
    (hτfr : ∀ u, u ∈ fr τ τ → u ∈ fr π π) (hI : NatInv (.Psi .zero π X) s)
    (hform : ∀ n, ∃ ξ A, s.nat n = .Psi ξ τ A)
    (hlow : ∀ x N, WNF x → Lt x (.Psi .zero π X) →
      (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w (s.nat N)) →
      Lt (.Psi .zero π X) (tgtN x) → Lt (tgtN x) τ → Le π (tgtN x) → ∃ n, Lt x (s.nat n))
    (hL : ∀ x N, WNF x → Lt x (.Psi .zero π X) →
      (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w (s.nat N)) →
      ∀ s' a, x = .Psi s' τ a → Lt a X → inC a a (.Psi .zero π X) = true →
      (∀ u, u ∈ fr (.Psi .zero π X) a → Lt u (s.nat N)) → ∃ n, Lt x (s.nat n)) :
    ∀ x, WNF x → Lt x (.Psi .zero π X) → ∃ n, Lt x (s.nat n) := by
  have hyF : ∀ n, WNF (s.nat n) := fun n => (hI.1.good n).1
  have hm : ∀ n, Lt (s.nat n) (s.nat (n + 1)) := fun n => (hI.1.good n).2.2
  refine cof_nat hyF hm fun x hx hxt N hpar => ?_
  obtain ⟨ξ, A, hA⟩ := hform N
  rcases leaf_one ht hτt hπτ hτfr (hyF N) hA (fun v hv hne hl => hI.2 N v hv hne hl) hx hxt hpar with
    h | ⟨a, harg, haX, haC, hafr, htk, hπk, hkτ | ⟨s', rfl⟩⟩
  · exact ⟨N, h⟩
  · exact hlow x N hx hxt hpar htk hkτ hπk
  · exact hL _ N hx hxt hpar s' a rfl haX haC hafr

/-- 共終数が大きい型：段の節点は仮定 `hL`、下の段は `hlow` -/
theorem leaf_bigG {π X τ σ : Tm} {s : SeqD} (ht : WNF (.Psi .zero π X)) (hτt : IsTgt τ) (hπτ : Le π τ)
    (hτfr : ∀ u, u ∈ fr τ τ → u ∈ fr π π) (hσF : WNF σ)
    (hU : BigUB (.Psi .zero π X) σ s) (hG : BigGap (.Psi .zero π X) σ s)
    (hform : ∀ β, WNF β → Lt β σ → ∃ ξ A, s.big β = .Psi ξ τ A)
    (hlow : ∀ x β, WNF x → Lt x (.Psi .zero π X) → WNF β → Lt β σ → Cl σ β →
      (∀ f, f ∈ fr σ x → Lt f β) → (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w (s.big β)) →
      Lt (.Psi .zero π X) (tgtN x) → Lt (tgtN x) τ → Le π (tgtN x) → Lt x (s.big β))
    (hL : ∀ x β, WNF x → Lt x (.Psi .zero π X) → WNF β → Lt β σ → Cl σ β →
      (∀ f, f ∈ fr σ x → Lt f β) → (∀ w, w ∈ parL x → Lt w (.Psi .zero π X) → Lt w (s.big β)) →
      Le σ x → ∀ s' a, x = .Psi s' τ a → Lt a X → Lt x (s.big β)) :
    ∀ x β, WNF x → Lt x (.Psi .zero π X) → WNF β → Lt β σ → Cl σ β → (∀ f, f ∈ fr σ x → Lt f β) →
      Lt x (s.big β) := by
  have hYF : ∀ β, WNF β → Lt β σ → WNF (s.big β) := fun β hβ hβσ => (hU.good.1 β hβ hβσ).1
  refine cof_big hσF (fun β hβ hβσ hCl => Cl.le_big hCl hU hβ hβσ) hYF
    fun x β hx hxt hβ hβσ hCl hfr hσx hpar => ?_
  obtain ⟨ξ, A, hA⟩ := hform β hβ hβσ
  rcases leaf_one ht hτt hπτ hτfr (hYF β hβ hβσ) hA (fun v hv hne hl => hG β hβ hβσ v hv hne hl) hx hxt
    hpar with h | ⟨a, harg, haX, -, -, htk, hπk, hkτ | ⟨s', rfl⟩⟩
  · exact h
  · exact hlow x β hx hxt hβ hβσ hCl hfr hpar htk hkτ hπk
  · exact hL _ β hx hxt hβ hβσ hCl hfr hpar hσx s' a rfl haX

end RTKA.Fund
