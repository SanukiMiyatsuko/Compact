import Compact.WF.FYDist

/-! 断片 `FY` の `Good α → α ∈ Wmax`（`FXHyp.lean` と同じ構成。順序の仮定 `FYOrder` の下で）。

`FX` との違いは二つある。

* `(18)` の証明の場合 2（`case_two`）：添字 `π ≤ β` の崩壊 `α < γ` で `γ` が `Ψ_κ(b)`（`κ > β`）や `Ξ_j(b)` の
  とき、`FX` では矛盾になったが、`FY` では `α < γ` になりうる。このとき `γ` の引数や目標の前線に `α` 以上の
  元 `w < γ` があり（`wit_psi_psi`・`wit_psi_xi`）、`w ∈ Wmax` で `α` を上から押さえる（Arai の Claim 6.39 の
  場合 2）。
* 崩壊の再帰は二段まで：`K_n` の崩壊 `Ξ_n(p)` はそれ自身が `Ψ` の目標になる。そこで `h15` は `η` の崩壊と
  崩壊の崩壊（`K_n` に対する `Ψ_{Ξ_n(p)}(a)`）を扱い、崩壊の深さ `cdepth` についての帰納法で
  `wmax_of_good` を示す。 -/

namespace RTKA.WFY

open Tm
open WFX (fr_mem_plus_l fr_mem_plus_r fr_mem_om fr_mem_xi fr_mem_xi_self fr_mem_psi_p
  fr_mem_psi_a fr_mem_psi_self)

variable [FYOrder]

/-! ### 生成集合の間の移し替えと係数についての帰納法 -/

/-- 前線（`R` について）が `θ` 未満の `C^θ(Wmax)` の元は、`ν < R` なら `C^ν(Wmax)` に入る -/
theorem hull_transfer {θ ν R : Tm} (wν : FYNF ν) (wR : FYNF R) (hνR : Lt ν R) (S : Nat)
    (good : ∀ x, Hull θ Wmax x → Lt x θ → x.size < S → Wmax x) :
    ∀ x, Hull θ Wmax x → x.size < S → (∀ w, w ∈ fr R x → Lt w θ) → Hull ν Wmax x := by
  intro x
  induction x using size_induction with
  | h x ih =>
    intro hx hs hfr
    by_cases hxθ : Lt x θ
    · exact wmax_hull (good x hx hxθ hs) wν
    · cases hx with
      | zero => exact Hull.zero
      | one => exact Hull.one
      | K hn => exact Hull.K hn
      | mem _ _ hlt => exact absurd hlt hxθ
      | plus hw ha hb =>
        exact Hull.plus hw
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_plus_l h)))
          (ih _ (by size_omega) hb (by size_omega) (fun w h => hfr w (fr_mem_plus_r h)))
      | om hw ha =>
        exact Hull.om hw
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_om h)))
      | @xi n a hw _ ha =>
        have hnR : ¬ Lt (.Xi n a) R := fun hl => hxθ (hfr _ (fr_mem_xi_self hl))
        have wK := FYNF.K' hw.xi.1
        have hνK : Lt ν (.K n) := lt_of_lt_of_leY wν wR wK hνR
          (le_transY wR hw wK (le_of_not_ltY hw wR hnR)
            (Or.inr ((lt_K_iffY hw hw.xi.1).mpr (Nat.le_refl _))))
        exact Hull.xi hw hνK (ih _ (by size_omega) ha (by size_omega)
          (fun w h => hfr w (fr_mem_xi hnR h)))
      | @psi π a hw _ hσ ha =>
        have hnR : ¬ Lt (.Psi .zero π a) R := fun hl => hxθ (hfr _ (fr_mem_psi_self hl))
        have wπ := hw.psi.2.2.1
        have hνσ : Lt ν π := lt_of_lt_of_leY wν wR wπ hνR
          (le_transY wR hw wπ (le_of_not_ltY hw wR hnR) (Or.inr (lt_psi_targetY hw)))
        exact Hull.psi hw hνσ
          (ih _ (by size_omega) hσ (by size_omega) (fun w h => hfr w (fr_mem_psi_p hnR h)))
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_psi_a hnR h)))

omit [FYOrder] in
/-- `C^θ(Wmax)` の元で、前線（`R` について）が `θ` 未満、`R` 以上の節点の引数が `g` 未満のものに
    ついての帰納法 -/
theorem coeff_induction {θ R g : Tm} (P : Tm → Prop) (S : Nat)
    (good : ∀ x, Hull θ Wmax x → Lt x θ → x.size < S → P x)
    (hzero : P .zero) (hone : P .one) (hK : ∀ {n : Nat}, 1 ≤ n → P (.K n))
    (hplus : ∀ {a b : Tm}, FYNF (.plus a b) → P a → P b → P (.plus a b))
    (hom : ∀ {a : Tm}, FYNF (.Om a) → P a → P (.Om a))
    (hxi : ∀ {n : Nat} {a : Tm}, FYNF (.Xi n a) → Lt a g → P a → P (.Xi n a))
    (hpsi : ∀ {π a : Tm}, FYNF (.Psi .zero π a) → Lt a g → P π → P a →
      P (.Psi .zero π a)) :
    ∀ x, Hull θ Wmax x → x.size < S → (∀ w, w ∈ fr R x → Lt w θ) → inC x g R = true →
      P x := by
  intro x
  induction x using size_induction with
  | h x ih =>
    intro hx hs hfr hC
    by_cases hxθ : Lt x θ
    · exact good x hx hxθ hs
    · cases hx with
      | zero => exact hzero
      | one => exact hone
      | K hn => exact hK hn
      | mem _ _ hlt => exact absurd hlt hxθ
      | plus hw ha hb =>
        rw [inC_plus, Bool.and_eq_true] at hC
        exact hplus hw
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_plus_l h)) hC.1)
          (ih _ (by size_omega) hb (by size_omega) (fun w h => hfr w (fr_mem_plus_r h)) hC.2)
      | om hw ha =>
        rw [inC_om] at hC
        exact hom hw
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_om h)) hC)
      | @xi n a hw _ ha =>
        have hnR : ¬ Lt (.Xi n a) R := fun hl => hxθ (hfr _ (fr_mem_xi_self hl))
        have hC' := (inC_xi_iff.mp hC).resolve_left hnR
        exact hxi hw hC'.2 (ih _ (by size_omega) ha (by size_omega)
          (fun w h => hfr w (fr_mem_xi hnR h)) hC'.1)
      | @psi π a hw _ hσ ha =>
        have hnR : ¬ Lt (.Psi .zero π a) R := fun hl => hxθ (hfr _ (fr_mem_psi_self hl))
        have hC' := (inC_psi_iff.mp hC).resolve_left hnR
        exact hpsi hw hC'.2.2.2
          (ih _ (by size_omega) hσ (by size_omega) (fun w h => hfr w (fr_mem_psi_p hnR h))
            hC'.1)
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_psi_a hnR h))
            hC'.2.2.1)

/-! ### `Wmax` の元の部分 -/

theorem wmax_om_arg {c : Tm} (h : Wmax (.Om c)) : Wmax c := by
  cases (wmax_good h).1 with
  | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
  | om hw hc => exact (wmax_good h).2 c hc hw.om.2.2

omit [FYOrder] in
theorem fr_hull_wmax {θ R : Tm}
    (IH : ∀ m, Wmax m → Lt m θ → ∀ w, w ∈ fr R m → Wmax w) :
    ∀ y, Hull θ Wmax y → ∀ w, w ∈ fr R y → Wmax w ∨ Hull θ Wmax w := by
  intro y hy
  induction hy with
  | zero => intro w h; simp [fr] at h
  | one => intro w h; simp [fr] at h
  | K _ => intro w h; simp [fr] at h
  | mem hX _ hlt => intro w h; exact Or.inl (IH _ hX hlt w h)
  | plus _ _ _ iha ihb =>
    intro w h
    rw [fr, List.mem_append] at h
    rcases h with h | h
    · exact iha w h
    · exact ihb w h
  | om _ _ iha => intro w h; rw [fr] at h; exact iha w h
  | @xi n a hw hα ha iha =>
    intro w h
    rw [fr] at h
    by_cases hl : Lt (.Xi n a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact Or.inr (Hull.xi hw hα ha)
    · simp only [hl, ↓reduceIte] at h
      exact iha w h
  | @psi π a hw hα hσ ha ihσ iha =>
    intro w h
    rw [fr] at h
    by_cases hl : Lt (.Psi .zero π a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact Or.inr (Hull.psi hw hα hσ ha)
    · simp only [hl, ↓reduceIte, List.mem_append] at h
      rcases h with (h | h) | h
      · simp [fr] at h
      · exact ihσ w h
      · exact iha w h

/-- `Wmax` の元の前線の元は `Wmax` に入る -/
theorem fr_wmax {R : Tm} (wR : FYNF R) : ∀ x, Wmax x → ∀ w, w ∈ fr R x → Wmax w := by
  have key : ∀ x, Acc (Rel Wmax) x → Wmax x → ∀ w, w ∈ fr R x → Wmax w := by
    intro x hacc
    induction hacc with
    | intro x _ ih =>
      intro hx w hw
      have hG := wmax_good hx
      rcases fr_hull_wmax (fun m hm hmx => ih m ⟨hm, hmx⟩ hm) x hG.1 w hw with h | h
      · exact h
      · rcases fr_leY wR (wmax_wf hx) hw with e | hlt
        · rw [e]; exact hx
        · exact hG.2 w h hlt
  intro x hx
  exact key x (wmax_acc hx) hx

/-- `C^β(Wmax)` の元の前線の元で `γ` 未満のものは、`γ` 未満の `C^β(Wmax)` の元が `Wmax` に入るなら
    `Wmax` に入る -/
theorem fr_hull_below {β γ R y : Tm} (wR : FYNF R) (hy : Hull β Wmax y)
    (MIH : ∀ ζ, Hull β Wmax ζ → Lt ζ γ → Wmax ζ) {w : Tm} (hw : w ∈ fr R y) (hwγ : Lt w γ) :
    Wmax w := by
  rcases fr_hull_wmax (fun m hm _ => fr_wmax wR m hm) y hy w hw with h | h
  · exact h
  · exact MIH w h hwγ

/-! ### Lemma 3.26 -/

/-- `(18)` の証明の場合 2（Arai の Claim 6.39 の場合 2）：添字 `π ≤ β` の崩壊 `α < γ`（`γ < π`）は、
    `γ` の作り方で場合を分けて、`Wmax` の元で上から押さえる -/
theorem case_two {β γ α : Tm} (wβ : FYNF β) (hγH : Hull β Wmax γ)
    (MIH : ∀ ζ, Hull β Wmax ζ → Lt ζ γ → Wmax ζ)
    (hshape : (∃ n a, α = .Xi n a ∧ Lt γ (.K n) ∧ Le (.K n) β) ∨
      (∃ π a, α = .Psi .zero π a ∧ Lt γ π ∧ Le π β))
    (hα : Hull γ Wmax α) (hαγ : Lt α γ) : Wmax α := by
  have wγ := hγH.wf_of
  have wα := hα.wf_of
  have hnγ := nr_specY γ wγ
  have hαp : isPrincipal α = true := by
    rcases hshape with ⟨n, a, rfl, -⟩ | ⟨π, a, rfl, -⟩ <;> rfl
  -- `γ` 未満の `Wmax` の元 `w ≥ α` で押さえる
  have bound : ∀ w, Wmax w → Lt w γ → ¬ Lt w α → Wmax α := fun w hW hwγ hn =>
    wmax_bounded wγ hα hW (le_of_not_ltY (wmax_wf hW) wα hn)
      (lt_transY (wmax_wf hW) wγ hnγ.1 hwγ hnγ.2.2)
  cases hγH with
  | zero => exact absurd hαγ (not_lt_zero _)
  | one =>
    have := lt_oneY wα hαγ
    subst this
    simp [isPrincipal] at hαp
  | K hj =>
    exfalso
    rcases hshape with ⟨n, a, rfl, hγK, -⟩ | ⟨π, a, rfl, hγσ, -⟩
    · have h1 := (lt_K_iffY wα hj).mp hαγ
      have h2 := (lt_K_iffY (FYNF.K' hj) wα.xi.1).mp hγK
      simp only [lev] at h1 h2
      omega
    · have h1 := (lt_K_iffY wα hj).mp hαγ
      have h2 := lev_le_of_lt_gen hγσ
      simp only [lev] at h1 h2
      omega
  | mem hX _ _ => exact (wmax_good hX).2 _ hα hαγ
  | @plus g₁ g₂ hw hg₁ _ =>
    exact wmax_bounded wγ hα (MIH g₁ hg₁ (lt_plus_leftY hw))
      ((lt_prin_plus_iffY wα hαp hw).mp hαγ)
      (lt_transY hw.plus.1 hw hnγ.1 (lt_plus_leftY hw) hnγ.2.2)
  | @om e hw he =>
    have heW := MIH e he hw.om.2.2
    have hb : Lt e (nrY (.Om e)) := lt_transY hw.om.1 hw hnγ.1 hw.om.2.2 hnγ.2.2
    rcases hshape with ⟨n, a, rfl, -, -⟩ | ⟨π, a, rfl, hγσ, -⟩
    · exact wmax_bounded wγ hα heW
        (Or.inr ((lt_OF_omG (Or.inl ⟨n, a, rfl⟩) wα hw.om.1).mp hαγ)) hb
    · rcases wα.psi.2.1 with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
      · exfalso
        have h1 := (lt_psi_omY wα hw.om.1).mp hαγ
        exact not_lt_of_leY wα.psiOm.2.1 hw (le_om_of_leY wα.psiOm.1 hw.om.1 h1) hγσ
      · exact wmax_bounded wγ hα heW
          (Or.inr ((lt_OF_omG (Or.inr ⟨n, p, a, rfl⟩) wα hw.om.1).mp hαγ)) hb
  | @xi j b hw hβK hb =>
    rcases hshape with ⟨n, a, rfl, hγK, hKβ⟩ | ⟨π, a, rfl, hγσ, hσβ⟩
    · exfalso
      have h1 := (lt_K_iffY hw wα.xi.1).mp hγK
      have h2 := (lt_K_iffY (FYNF.K' wα.xi.1) hw.xi.1).mp
        (lt_of_le_of_ltY (FYNF.K' wα.xi.1) wβ (FYNF.K' hw.xi.1) hKβ hβK)
      simp only [lev] at h1 h2
      omega
    · have wπ := wα.psi.2.2.1
      rcases wα.psi.2.1 with ⟨c, rfl, -⟩ | ⟨m, q, rfl⟩
      · exfalso
        exact Lt.asymmY wα hw hαγ ((lt_OF_psiOm (Or.inl ⟨j, b, rfl⟩) hw wα).mpr
          ((lt_OF_omG (Or.inl ⟨j, b, rfl⟩) hw wα.psiOm.1).mp hγσ))
      · have hmj : m = j := by
          have h1 := lev_le_of_lt_gen hγσ
          have h2 := (lt_K_iffY wπ hw.xi.1).mp (lt_of_le_of_ltY wπ wβ (FYNF.K' hw.xi.1) hσβ hβK)
          simp only [lev] at h1 h2
          omega
        subst hmj
        obtain ⟨-, w, hwfr, hwn⟩ := wit_psi_xi wα hw rfl hαγ hγσ
        have hwγ := FYOrder.k2x hw w hwfr
        exact bound w (fr_hull_below (FYNF.K' hw.xi.1) hb MIH hwfr hwγ) hwγ hwn
  | @psi κ b hw hβκ hκ hb =>
    have wκ := hw.psi.2.2.1
    rcases hshape with ⟨n, a, rfl, hγK, hKβ⟩ | ⟨π, a, rfl, hγσ, hσβ⟩
    · exfalso
      have h1 := (lt_K_iffY hw wα.xi.1).mp hγK
      have h2 := lev_le_of_lt_gen (lt_of_le_of_ltY (FYNF.K' wα.xi.1) wβ wκ hKβ hβκ)
      simp only [lev] at h1 h2
      omega
    · have wπ := wα.psi.2.2.1
      have hπκ : Lt π κ := lt_of_le_of_ltY wπ wβ wκ hσβ hβκ
      have hl : lev π = lev κ := by
        have h1 := lev_le_of_lt_gen hπκ
        have h2 := lev_le_of_lt_gen hγσ
        simp only [lev] at h2
        omega
      obtain ⟨w, hwfr, hwn⟩ := wit_psi_psi wα hw hl hαγ hγσ hπκ
      rcases hwfr with hwfr | hwfr
      · have hwγ := FYOrder.k2 hw w hwfr
        exact bound w (fr_hull_below wκ hb MIH hwfr hwγ) hwγ hwn
      · have hwγ := FYOrder.k2t hw w hwfr
        exact bound w (fr_hull_below wκ hκ MIH hwfr hwγ) hwγ hwn

/-- `γ` は `η` を添字とする崩壊（`η = K_n` の `Ξ_n(b)`、または `η` を目標とする `Ψ^0_η(b)`） -/
def IsColl (η γ : Tm) : Prop := (∃ n b, η = .K n ∧ γ = .Xi n b) ∨ ∃ b, γ = .Psi .zero η b

/-- `η` の崩壊か、`η` の崩壊の崩壊 -/
def IsColl2 (η γ : Tm) : Prop := IsColl η γ ∨ ∃ ρ, IsColl η ρ ∧ IsColl ρ γ

/-- 崩壊の深さ：`K_n` は 2、`Ξ_n(p)` と `Ω_c` は 1、それ以外は 0 -/
def cdepth : Tm → Nat
  | .K _ => 2
  | .Xi _ _ => 1
  | .Om _ => 1
  | _ => 0

omit [FYOrder] in
theorem cdepth_coll {η γ : Tm} (h : IsColl η γ) (hγ : FYNF γ) : cdepth γ < cdepth η := by
  rcases h with ⟨n, b, rfl, rfl⟩ | ⟨b, rfl⟩
  · simp [cdepth]
  · rcases hγ.psi.2.1 with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ <;> simp [cdepth]

omit [FYOrder] in
theorem cdepth_coll2 {η γ : Tm} (h : IsColl2 η γ) (hγ : FYNF γ) : cdepth γ < cdepth η := by
  rcases h with h | ⟨ρ, h1, h2⟩
  · exact cdepth_coll h hγ
  · have hρ : FYNF ρ := by
      rcases h2 with ⟨n, b, rfl, rfl⟩ | ⟨b, rfl⟩
      · exact FYNF.K' hγ.xi.1
      · exact hγ.psi.2.2.1
    have := cdepth_coll h1 hρ
    have := cdepth_coll h2 hγ
    omega

/-- Lemma 3.26 の証明の段階 3：`η` 未満の `Good` な項は `Wmax` に入る -/
theorem step_three {η γ : Tm} (hG : Good η) (h15 : ∀ γ, IsColl2 η γ → Good γ → Wmax γ)
    (hγ : Good γ) (hγη : Lt γ η) (Obs : ∀ δ, Wmax δ → Le γ δ → Wmax γ) : Wmax γ := by
  have wη := hG.1.wf_of
  have wγ := hγ.1.wf_of
  cases γ with
  | zero => exact hG.2 _ Hull.zero hγη
  | one => exact hG.2 _ Hull.one hγη
  | K n => exact hG.2 _ (Hull.K wγ.k) hγη
  | plus g₁ g₂ =>
    cases hγ.1 with
    | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
    | plus hw hg₁ hg₂ =>
      exact hG.2 _ (Hull.plus hw (wmax_hull (hγ.2 _ hg₁ (lt_plus_leftY hw)) wη)
        (wmax_hull (hγ.2 _ hg₂ (lt_plus_rightY hw)) wη)) hγη
  | Om e =>
    cases hγ.1 with
    | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
    | om hw he => exact hG.2 _ (Hull.om hw (wmax_hull (hγ.2 e he hw.om.2.2) wη)) hγη
  | Xi n b =>
    cases hγ.1 with
    | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
    | xi hw hγK hb =>
      have wK := FYNF.K' hw.xi.1
      rcases triY wK wη with hKη | e | hηK
      · exact Obs _ (hG.2 _ (Hull.K hw.xi.1) hKη) (Or.inr hγK)
      · exact h15 _ (Or.inl (Or.inl ⟨n, b, e.symm, rfl⟩)) hγ
      · exact hG.2 _ (Hull.xi hw hηK (hull_transfer wη wK hηK (b.size + 1)
          (fun x hx hxγ _ => hγ.2 x hx hxγ) b hb (Nat.lt_succ_self _) (FYOrder.k2x hw))) hγη
  | Psi s ρ a =>
    obtain ⟨rfl, hT, wρ, -⟩ := wγ.psi
    cases hγ.1 with
    | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
    | psi hw hγρ hρ ha =>
      -- `ρ` 自身の前線は `γ` 未満
      have hρfr : ∀ w, w ∈ fr ρ ρ → Lt w (.Psi .zero ρ a) := FYOrder.k2t hw
      rcases triY wρ wη with hρη | e | hηρ
      · -- `ρ < η`：`ρ`（または `K_n`）が `Wmax` に入れば `Obs`
        rcases hT with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
        · have hc : Wmax c := by
            cases hρ with
            | mem hX _ _ => exact wmax_om_arg hX
            | om _ hc => exact hγ.2 c hc (FYOrder.cx hw)
          exact Obs _ (hG.2 _ (Hull.om wρ (wmax_hull hc wη)) hρη) (Or.inr hγρ)
        · have wK := FYNF.K' wρ.xi.1
          have hρK : Lt (.Xi n p) (.K n) := (lt_K_iffY wρ wρ.xi.1).mpr (Nat.le_refl _)
          rcases triY wK wη with hKη | e | hηK
          · exact Obs _ (hG.2 _ (Hull.K wρ.xi.1) hKη)
              (Or.inr (lt_transY wγ wρ wK hγρ hρK))
          · exact h15 _ (Or.inr ⟨.Xi n p, Or.inl ⟨n, p, e.symm, rfl⟩, Or.inr ⟨a, rfl⟩⟩) hγ
          · -- `η < K_n`：`ρ = Ξ_n(p)` を `C^η(Wmax)` に移す
            have hρη' : Hull η Wmax (.Xi n p) := by
              cases hρ with
              | mem hX _ _ => exact wmax_hull hX wη
              | xi hwρ _ hp =>
                refine Hull.xi hwρ hηK (hull_transfer wη wK hηK (p.size + 1)
                  (fun x hx hxγ _ => hγ.2 x hx hxγ) p hp (Nat.lt_succ_self _) ?_)
                intro w hw'
                have hwF : FYNF w := wρ.xi.2.1.of_mem_subs (fr_spec hw').1
                have hwρ := FYOrder.k2x wρ w hw'
                have hw'' : w ∈ fr (.Xi n p) (.Xi n p) := by
                  rw [fr]
                  simp only [Lt.irrefl, ↓reduceIte]
                  exact fr_sub wK wρ (Or.inr hρK) wρ.xi.2.1 hw' hwρ
                exact hρfr w hw''
            exact Obs _ (hG.2 _ hρη' hρη) (Or.inr hγρ)
      · exact h15 _ (Or.inl (Or.inr ⟨a, by rw [e]⟩)) hγ
      · -- `η < ρ`：`γ` の引数と目標を `C^η(Wmax)` に移す
        have hρη' := hull_transfer wη wρ hηρ (ρ.size + 1) (fun x hx hxγ _ => hγ.2 x hx hxγ)
          ρ hρ (Nat.lt_succ_self _) hρfr
        have haη := hull_transfer wη wρ hηρ (a.size + 1) (fun x hx hxγ _ => hγ.2 x hx hxγ)
          a ha (Nat.lt_succ_self _) (FYOrder.k2 hw)
        exact hG.2 _ (Hull.psi hw hηρ hρη' haη) hγη

/-- Arai の Lemma 3.26：`η` の崩壊と崩壊の崩壊が `Good` なら `Wmax` に入るとき、`Good η` から拡張の
    仮定が成り立つ -/
theorem hyp_of_good {η : Tm} (hG : Good η) (h15 : ∀ γ, IsColl2 η γ → Good γ → Wmax γ) :
    Hyp η := by
  have wη := hG.1.wf_of
  intro β wβ hle γ hW hγ
  have hnβ := nr_specY β wβ
  have key : ∀ γ, Acc (Rel (Hull β Wmax)) γ → Hull β Wmax γ → Lt γ (nrY β) → Wmax γ := by
    intro γ hacc
    induction hacc with
    | intro γ hacc' MIH0 =>
      intro hγH hγ
      have wγ := hγH.wf_of
      have MIH : ∀ ζ, Hull β Wmax ζ → Lt ζ γ → Wmax ζ := fun ζ hζ hζγ =>
        MIH0 ζ ⟨hζ, hζγ⟩ hζ (lt_transY hζ.wf_of wγ hnβ.1 hζγ hγ)
      have Obs : ∀ δ, Wmax δ → Le γ δ → Wmax γ := by
        intro δ hδ hγδ
        have wδ := wmax_wf hδ
        by_cases hδβ : Lt δ β
        · exact wmax_bounded wδ (Hull.lower HW wδ wβ (Or.inr hδβ) hγH) hδ hγδ
            (nr_specY δ wδ).2.2
        · exact ((wmax_dist.2 β wβ ⟨δ, hδ, le_of_not_ltY wδ wβ hδβ⟩ γ).mp
            ⟨⟨hγH, Acc.intro γ hacc'⟩, hγ⟩).1
      have G2 : ∀ α, Hull γ Wmax α → Lt α γ → Wmax α := by
        intro α
        induction α using size_induction with
        | h α ihα =>
          intro hα hαγ
          by_cases hβnγ : Lt β (nrY γ)
          · exact MIH α (Hull.sub_of_lt_nr HW wγ wβ hβnγ hα) hαγ
          · have below : ∀ x, FYNF x → Lt x α → Lt x γ :=
              fun x wx h => lt_transY wx hα.wf_of wγ h hαγ
            cases hα with
            | zero => exact MIH _ Hull.zero hαγ
            | one => exact MIH _ Hull.one hαγ
            | K hn => exact MIH _ (Hull.K hn) hαγ
            | mem hX _ _ => exact hX
            | plus hw ha hb =>
              exact MIH _ (Hull.plus hw
                (wmax_hull (ihα _ (by size_omega) ha (below _ hw.plus.1 (lt_plus_leftY hw))) wβ)
                (wmax_hull (ihα _ (by size_omega) hb
                  (below _ hw.plus.2.1 (lt_plus_rightY hw))) wβ)) hαγ
            | om hw ha =>
              exact MIH _ (Hull.om hw (wmax_hull (ihα _ (by size_omega) ha
                (below _ hw.om.1 hw.om.2.2)) wβ)) hαγ
            | @xi n a hw hγK ha =>
              have wK := FYNF.K' hw.xi.1
              by_cases hβK : Lt β (.K n)
              · exact MIH _ (Hull.xi hw hβK (hull_transfer wβ wK hβK _
                  (fun x hx hxγ hs => ihα x hs hx hxγ) a ha (by size_omega)
                  (fun w hw' => lt_transY (hw.of_mem_subs (subs_xi (fr_spec hw').1)) hw wγ
                    (FYOrder.k2x hw w hw') hαγ))) hαγ
              · exact case_two wβ hγH MIH (Or.inl ⟨n, a, rfl, hγK, le_of_not_ltY wβ wK hβK⟩)
                  (Hull.xi hw hγK ha) hαγ
            | @psi π a hw hγσ hσ ha =>
              have wπ := hw.psi.2.2.1
              by_cases hβσ : Lt β π
              · have hσ' := hull_transfer wβ wπ hβσ _ (fun x hx hxγ hs => ihα x hs hx hxγ)
                  π hσ (by size_omega)
                  (fun w hw' => lt_transY (wπ.of_mem_subs (fr_spec hw').1) hw wγ
                    (FYOrder.k2t hw w hw') hαγ)
                exact MIH _ (Hull.psi hw hβσ hσ' (hull_transfer wβ wπ hβσ _
                  (fun x hx hxγ hs => ihα x hs hx hxγ) a ha (by size_omega)
                  (fun w hw' => lt_transY (hw.of_mem_subs (subs_psi_a (fr_spec hw').1)) hw wγ
                    (FYOrder.k2 hw w hw') hαγ))) hαγ
              · exact case_two wβ hγH MIH (Or.inr ⟨π, a, rfl, hγσ, le_of_not_ltY wβ wπ hβσ⟩)
                  (Hull.psi hw hγσ hσ ha) hαγ
      exact step_three hG h15 ⟨Hull.sub_of_lt_nr HW wβ wγ hγ hγH, G2⟩
        (lt_of_lt_of_leY wγ hnβ.1 wη hγ hle) Obs
  exact key γ hW.2 hW.1 hγ

theorem wmax_of_good_aux : ∀ d, ∀ η, cdepth η ≤ d → Good η → Wmax η
  | 0, _, hd, hG => wmax_of_good_hyp hG (hyp_of_good hG (fun γ hc hγ =>
      absurd (Nat.lt_of_lt_of_le (cdepth_coll2 hc hγ.1.wf_of) hd) (Nat.not_lt_zero _)))
  | d + 1, _, hd, hG => wmax_of_good_hyp hG (hyp_of_good hG (fun γ hc hγ =>
      wmax_of_good_aux d γ (by have := cdepth_coll2 hc hγ.1.wf_of; omega) hγ))

/-- `Good` な項は最大区別集合に入る -/
theorem wmax_of_good {η : Tm} (hG : Good η) : Wmax η :=
  wmax_of_good_aux _ η (Nat.le_refl _) hG

end RTKA.WFY
