import Compact.WF.FZDist

/-! 断片 `FZ` の `Good α → α ∈ Wmax`（`FYHyp.lean` と同じ構成。順序の仮定 `FZOrder` の下で）。

`FY` との違いは、崩壊 `Ψ^ξ_π(a)` が Mahlo 添字 `ξ` を持つこと。

* 生成集合 `C^θ(Wmax)` の移し替え・係数についての帰納法・前線は `ξ` も含めて扱う（`ξ` の前線は K2S）。
* `(18)` の証明の場合 2（`case_two`）：`α = Ψ^ξ_π(a) < γ = Ψ^σ_κ(b)`（`γ < π ≤ β < κ`）の比較を
  Prop. 4.20 の (1)〜(4) で分ける。(1) と (3) は起こらず、(2) は `γ` の引数・目標・Mahlo 添字の前線
  （`κ` について、`wit_c2`）、(4) は `σ ∈ C(σ, γ)` から `σ` の前線（`γ` について、`wit_c4`）に
  `α` 以上の元 `w < γ` がある。
* `Ψ^ξ`（`ξ > 0`）は `FZ` では崩壊の目標にならないので、崩壊の再帰は `FY` と同じく二段まで。 -/

namespace RTKA.Z.WFY

open Tm
open WFX (fr_mem_plus_l fr_mem_plus_r fr_mem_om fr_mem_xi fr_mem_xi_self fr_mem_psi_p
  fr_mem_psi_a fr_mem_psi_self)

theorem fr_mem_psi_s {R s p a w : Tm} (hn : ¬ Lt (.Psi s p a) R) (h : w ∈ fr R s) :
    w ∈ fr R (.Psi s p a) := by
  rw [fr]; simp only [hn, ↓reduceIte, List.mem_append]; exact Or.inl (Or.inl h)

variable [FZOrder]

/-! ### 生成集合の間の移し替えと係数についての帰納法 -/

/-- 前線（`R` について）が `θ` 未満の `C^θ(Wmax)` の元は、`ν < R` なら `C^ν(Wmax)` に入る -/
theorem hull_transfer {θ ν R : Tm} (wν : FZNF ν) (wR : FZNF R) (hνR : Lt ν R) (S : Nat)
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
        have wK := FZNF.K' hw.xi.1
        have hνK : Lt ν (.K n) := lt_of_lt_of_leY wν wR wK hνR
          (le_transY wR hw wK (le_of_not_ltY hw wR hnR)
            (Or.inr ((lt_K_iffY hw hw.xi.1).mpr (Nat.le_refl _))))
        exact Hull.xi hw hνK (ih _ (by size_omega) ha (by size_omega)
          (fun w h => hfr w (fr_mem_xi hnR h)))
      | @psi ξ π a hw _ hξ hσ ha =>
        have hnR : ¬ Lt (.Psi ξ π a) R := fun hl => hxθ (hfr _ (fr_mem_psi_self hl))
        have wπ := hw.psi.piF
        have hνσ : Lt ν π := lt_of_lt_of_leY wν wR wπ hνR
          (le_transY wR hw wπ (le_of_not_ltY hw wR hnR) (Or.inr (lt_psi_targetY hw)))
        exact Hull.psi hw hνσ
          (ih _ (by size_omega) hξ (by size_omega) (fun w h => hfr w (fr_mem_psi_s hnR h)))
          (ih _ (by size_omega) hσ (by size_omega) (fun w h => hfr w (fr_mem_psi_p hnR h)))
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_psi_a hnR h)))

omit [FZOrder] in
/-- `C^θ(Wmax)` の元で、前線（`R` について）が `θ` 未満、`R` 以上の節点の引数が `g` 未満のものに
    ついての帰納法 -/
theorem coeff_induction {θ R g : Tm} (P : Tm → Prop) (S : Nat)
    (good : ∀ x, Hull θ Wmax x → Lt x θ → x.size < S → P x)
    (hzero : P .zero) (hone : P .one) (hK : ∀ {n : Nat}, 1 ≤ n → P (.K n))
    (hplus : ∀ {a b : Tm}, FZNF (.plus a b) → P a → P b → P (.plus a b))
    (hom : ∀ {a : Tm}, FZNF (.Om a) → P a → P (.Om a))
    (hxi : ∀ {n : Nat} {a : Tm}, FZNF (.Xi n a) → Lt a g → P a → P (.Xi n a))
    (hpsi : ∀ {ξ π a : Tm}, FZNF (.Psi ξ π a) → Lt a g → P ξ → P π → P a →
      P (.Psi ξ π a)) :
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
      | @psi ξ π a hw _ hξ hσ ha =>
        have hnR : ¬ Lt (.Psi ξ π a) R := fun hl => hxθ (hfr _ (fr_mem_psi_self hl))
        have hC' := (inC_psi_iff.mp hC).resolve_left hnR
        exact hpsi hw hC'.2.2.2
          (ih _ (by size_omega) hξ (by size_omega) (fun w h => hfr w (fr_mem_psi_s hnR h))
            hC'.2.1)
          (ih _ (by size_omega) hσ (by size_omega) (fun w h => hfr w (fr_mem_psi_p hnR h))
            hC'.1)
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_psi_a hnR h))
            hC'.2.2.1)

/-! ### `Wmax` の元の部分 -/

theorem wmax_om_arg {c : Tm} (h : Wmax (.Om c)) : Wmax c := by
  cases (wmax_good h).1 with
  | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
  | om hw hc => exact (wmax_good h).2 c hc hw.om.2.2

omit [FZOrder] in
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
  | @psi ξ π a hw hα hξ hσ ha ihξ ihσ iha =>
    intro w h
    rw [fr] at h
    by_cases hl : Lt (.Psi ξ π a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact Or.inr (Hull.psi hw hα hξ hσ ha)
    · simp only [hl, ↓reduceIte, List.mem_append] at h
      rcases h with (h | h) | h
      · exact ihξ w h
      · exact ihσ w h
      · exact iha w h

/-- `Wmax` の元の前線の元は `Wmax` に入る -/
theorem fr_wmax {R : Tm} (wR : FZNF R) : ∀ x, Wmax x → ∀ w, w ∈ fr R x → Wmax w := by
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
theorem fr_hull_below {β γ R y : Tm} (wR : FZNF R) (hy : Hull β Wmax y)
    (MIH : ∀ ζ, Hull β Wmax ζ → Lt ζ γ → Wmax ζ) {w : Tm} (hw : w ∈ fr R y) (hwγ : Lt w γ) :
    Wmax w := by
  rcases fr_hull_wmax (fun m hm _ => fr_wmax wR m hm) y hy w hw with h | h
  · exact h
  · exact MIH w h hwγ

/-! ### Lemma 3.26 -/

/-- `(18)` の証明の場合 2（Arai の Claim 6.39 の場合 2）：添字 `π ≤ β` の崩壊 `α < γ`（`γ < π`）は、
    `γ` の作り方で場合を分けて、`Wmax` の元で上から押さえる -/
theorem case_two {β γ α : Tm} (wβ : FZNF β) (hγH : Hull β Wmax γ)
    (MIH : ∀ ζ, Hull β Wmax ζ → Lt ζ γ → Wmax ζ)
    (hshape : (∃ n a, α = .Xi n a ∧ Lt γ (.K n) ∧ Le (.K n) β) ∨
      (∃ ξ π a, α = .Psi ξ π a ∧ Lt γ π ∧ Le π β))
    (hα : Hull γ Wmax α) (hαγ : Lt α γ) : Wmax α := by
  have wγ := hγH.wf_of
  have wα := hα.wf_of
  have hnγ := nr_specY γ wγ
  have hαp : isPrincipal α = true := by
    rcases hshape with ⟨n, a, rfl, -⟩ | ⟨ξ, π, a, rfl, -⟩ <;> rfl
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
    rcases hshape with ⟨n, a, rfl, hγK, -⟩ | ⟨ξ, π, a, rfl, hγσ, -⟩
    · have h1 := (lt_K_iffY wα hj).mp hαγ
      have h2 := (lt_K_iffY (FZNF.K' hj) wα.xi.1).mp hγK
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
    rcases hshape with ⟨n, a, rfl, -, -⟩ | ⟨ξ, π, a, rfl, hγσ, -⟩
    · exact wmax_bounded wγ hα heW
        (Or.inr ((lt_OF_omG (Or.inl ⟨n, a, rfl⟩) wα hw.om.1).mp hαγ)) hb
    · rcases wα.psi.m with ⟨c, rfl, rfl⟩ | ⟨n, p, rfl, -, -⟩
      · exfalso
        have h1 := (lt_psi_omY wα hw.om.1).mp hαγ
        exact not_lt_of_leY wα.psiOm.2.1 hw (le_om_of_leY wα.psiOm.1 hw.om.1 h1) hγσ
      · exact wmax_bounded wγ hα heW
          (Or.inr ((lt_OF_omG (Or.inr ⟨ξ, n, p, a, rfl⟩) wα hw.om.1).mp hαγ)) hb
  | @xi j b hw hβK hb =>
    rcases hshape with ⟨n, a, rfl, hγK, hKβ⟩ | ⟨ξ, π, a, rfl, hγσ, hσβ⟩
    · exfalso
      have h1 := (lt_K_iffY hw wα.xi.1).mp hγK
      have h2 := (lt_K_iffY (FZNF.K' wα.xi.1) hw.xi.1).mp
        (lt_of_le_of_ltY (FZNF.K' wα.xi.1) wβ (FZNF.K' hw.xi.1) hKβ hβK)
      simp only [lev] at h1 h2
      omega
    · have wπ := wα.psi.piF
      rcases wα.psi.m with ⟨c, rfl, rfl⟩ | ⟨m, q, rfl, -, -⟩
      · exfalso
        exact Lt.asymmY wα hw hαγ ((lt_OF_psiOm (Or.inl ⟨j, b, rfl⟩) hw wα).mpr
          ((lt_OF_omG (Or.inl ⟨j, b, rfl⟩) hw wα.psiOm.1).mp hγσ))
      · have hmj : m = j := by
          have h1 := lev_le_of_lt_gen hγσ
          have h2 := (lt_K_iffY wπ hw.xi.1).mp (lt_of_le_of_ltY wπ wβ (FZNF.K' hw.xi.1) hσβ hβK)
          simp only [lev] at h1 h2
          omega
        subst hmj
        obtain ⟨-, w, hwfr, hwn⟩ := wit_psi_xi wα hw rfl hαγ hγσ
        have hwγ := FZOrder.k2x hw w hwfr
        exact bound w (fr_hull_below (FZNF.K' hw.xi.1) hb MIH hwfr hwγ) hwγ hwn
  | @psi σ κ b hw hβκ hσH hκ hb =>
    have wκ := hw.psi.piF
    rcases hshape with ⟨n, a, rfl, hγK, hKβ⟩ | ⟨ξ, π, a, rfl, hγσ, hσβ⟩
    · exfalso
      have h1 := (lt_K_iffY hw wα.xi.1).mp hγK
      have h2 := lev_le_of_lt_gen (lt_of_le_of_ltY (FZNF.K' wα.xi.1) wβ wκ hKβ hβκ)
      simp only [lev] at h1 h2
      omega
    · have wπ := wα.psi.piF
      have hπκ : Lt π κ := lt_of_le_of_ltY wπ wβ wκ hσβ hβκ
      have hl : lev π = lev κ := by
        have h1 := lev_le_of_lt_gen hπκ
        have h2 := lev_le_of_lt_gen hγσ
        simp only [lev] at h2
        omega
      rcases (lt_psi_psiY hl hαγ.ne).mp hαγ with
        h1 | ⟨-, hακ, (⟨-, -, -, hπC⟩ | ⟨hba, hn⟩ | ⟨-, e, -⟩ | ⟨hσξ, hn⟩)⟩
      · exact absurd hγσ h1
      · exact absurd (coll_psiY hw π wπ hπC hπκ) (Lt.asymmY hw wπ hγσ)
      · obtain ⟨w, hwfr, hwn⟩ := wit_c2 hw wα wα.psi.aF (le_of_ne_gtY hw.psi.aF wα.psi.aF hba)
          hακ hn
        rcases hwfr with hwfr | hwfr | hwfr
        · have hwγ := FZOrder.k2 hw w hwfr
          exact bound w (fr_hull_below wκ hb MIH hwfr hwγ) hwγ hwn
        · have hwγ := FZOrder.k2t hw w hwfr
          exact bound w (fr_hull_below wκ hκ MIH hwfr hwγ) hwγ hwn
        · have hwγ := FZOrder.k2s hw w hwfr
          exact bound w (fr_hull_below wκ hσH MIH hwfr hwγ) hwγ hwn
      · subst e
        exact absurd hπκ (Lt.irrefl _)
      · obtain ⟨w, hwfr, hwn⟩ := wit_c4 hw wα wα.psi.xiF hαγ hσξ hn
        have hwγ := (fr_spec hwfr).2
        exact bound w (fr_hull_below hw hσH MIH hwfr hwγ) hwγ hwn

/-- `γ` は `η` を添字とする崩壊（`η = K_n` の `Ξ_n(b)`、または `η` を目標とする `Ψ^ξ_η(b)`） -/
def IsColl (η γ : Tm) : Prop := (∃ n b, η = .K n ∧ γ = .Xi n b) ∨ ∃ ξ b, γ = .Psi ξ η b

/-- `η` の崩壊か、`η` の崩壊の崩壊 -/
def IsColl2 (η γ : Tm) : Prop := IsColl η γ ∨ ∃ ρ, IsColl η ρ ∧ IsColl ρ γ

/-- 崩壊の深さ：`K_n` は 2、`Ξ_n(p)` と `Ω_c` は 1、それ以外は 0 -/
def cdepth : Tm → Nat
  | .K _ => 2
  | .Xi _ _ => 1
  | .Om _ => 1
  | _ => 0

omit [FZOrder] in
theorem cdepth_coll {η γ : Tm} (h : IsColl η γ) (hγ : FZNF γ) : cdepth γ < cdepth η := by
  rcases h with ⟨n, b, rfl, rfl⟩ | ⟨ξ, b, rfl⟩
  · simp [cdepth]
  · rcases hγ.psi.tgt with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ <;> simp [cdepth]

omit [FZOrder] in
theorem cdepth_coll2 {η γ : Tm} (h : IsColl2 η γ) (hγ : FZNF γ) : cdepth γ < cdepth η := by
  rcases h with h | ⟨ρ, h1, h2⟩
  · exact cdepth_coll h hγ
  · have hρ : FZNF ρ := by
      rcases h2 with ⟨n, b, rfl, rfl⟩ | ⟨ξ, b, rfl⟩
      · exact FZNF.K' hγ.xi.1
      · exact hγ.psi.piF
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
      have wK := FZNF.K' hw.xi.1
      rcases triY wK wη with hKη | e | hηK
      · exact Obs _ (hG.2 _ (Hull.K hw.xi.1) hKη) (Or.inr hγK)
      · exact h15 _ (Or.inl (Or.inl ⟨n, b, e.symm, rfl⟩)) hγ
      · exact hG.2 _ (Hull.xi hw hηK (hull_transfer wη wK hηK (b.size + 1)
          (fun x hx hxγ _ => hγ.2 x hx hxγ) b hb (Nat.lt_succ_self _) (FZOrder.k2x hw))) hγη
  | Psi s ρ a =>
    have wρ := wγ.psi.piF
    have hT := wγ.psi.tgt
    cases hγ.1 with
    | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
    | psi hw hγρ hs hρ ha =>
      -- `ρ` 自身の前線は `γ` 未満
      have hρfr : ∀ w, w ∈ fr ρ ρ → Lt w (.Psi s ρ a) := FZOrder.k2t hw
      rcases triY wρ wη with hρη | e | hηρ
      · -- `ρ < η`：`ρ`（または `K_n`）が `Wmax` に入れば `Obs`
        rcases hT with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
        · have hs0 := hw.psiOm.2.2.2.2.2
          subst hs0
          have hc : Wmax c := by
            cases hρ with
            | mem hX _ _ => exact wmax_om_arg hX
            | om _ hc => exact hγ.2 c hc (FZOrder.cx hw)
          exact Obs _ (hG.2 _ (Hull.om wρ (wmax_hull hc wη)) hρη) (Or.inr hγρ)
        · have wK := FZNF.K' wρ.xi.1
          have hρK : Lt (.Xi n p) (.K n) := (lt_K_iffY wρ wρ.xi.1).mpr (Nat.le_refl _)
          rcases triY wK wη with hKη | e | hηK
          · exact Obs _ (hG.2 _ (Hull.K wρ.xi.1) hKη)
              (Or.inr (lt_transY wγ wρ wK hγρ hρK))
          · exact h15 _ (Or.inr ⟨.Xi n p, Or.inl ⟨n, p, e.symm, rfl⟩, Or.inr ⟨s, a, rfl⟩⟩) hγ
          · -- `η < K_n`：`ρ = Ξ_n(p)` を `C^η(Wmax)` に移す
            have hρη' : Hull η Wmax (.Xi n p) := by
              cases hρ with
              | mem hX _ _ => exact wmax_hull hX wη
              | xi hwρ _ hp =>
                refine Hull.xi hwρ hηK (hull_transfer wη wK hηK (p.size + 1)
                  (fun x hx hxγ _ => hγ.2 x hx hxγ) p hp (Nat.lt_succ_self _) ?_)
                intro w hw'
                have hwF : FZNF w := wρ.xi.2.1.of_mem_subs (fr_spec hw').1
                have hwρ := FZOrder.k2x wρ w hw'
                have hw'' : w ∈ fr (.Xi n p) (.Xi n p) := by
                  rw [fr]
                  simp only [Lt.irrefl, ↓reduceIte]
                  exact fr_sub wK wρ (Or.inr hρK) wρ.xi.2.1 hw' hwρ
                exact hρfr w hw''
            exact Obs _ (hG.2 _ hρη' hρη) (Or.inr hγρ)
      · exact h15 _ (Or.inl (Or.inr ⟨s, a, by rw [e]⟩)) hγ
      · -- `η < ρ`：`γ` の Mahlo 添字・引数・目標を `C^η(Wmax)` に移す
        have hsη := hull_transfer wη wρ hηρ (s.size + 1) (fun x hx hxγ _ => hγ.2 x hx hxγ)
          s hs (Nat.lt_succ_self _) (FZOrder.k2s hw)
        have hρη' := hull_transfer wη wρ hηρ (ρ.size + 1) (fun x hx hxγ _ => hγ.2 x hx hxγ)
          ρ hρ (Nat.lt_succ_self _) hρfr
        have haη := hull_transfer wη wρ hηρ (a.size + 1) (fun x hx hxγ _ => hγ.2 x hx hxγ)
          a ha (Nat.lt_succ_self _) (FZOrder.k2 hw)
        exact hG.2 _ (Hull.psi hw hηρ hsη hρη' haη) hγη

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
          · have below : ∀ x, FZNF x → Lt x α → Lt x γ :=
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
              have wK := FZNF.K' hw.xi.1
              by_cases hβK : Lt β (.K n)
              · exact MIH _ (Hull.xi hw hβK (hull_transfer wβ wK hβK _
                  (fun x hx hxγ hs => ihα x hs hx hxγ) a ha (by size_omega)
                  (fun w hw' => lt_transY (hw.of_mem_subs (subs_xi (fr_spec hw').1)) hw wγ
                    (FZOrder.k2x hw w hw') hαγ))) hαγ
              · exact case_two wβ hγH MIH (Or.inl ⟨n, a, rfl, hγK, le_of_not_ltY wβ wK hβK⟩)
                  (Hull.xi hw hγK ha) hαγ
            | @psi ξ π a hw hγσ hξ hσ ha =>
              have wπ := hw.psi.piF
              by_cases hβσ : Lt β π
              · have hξ' := hull_transfer wβ wπ hβσ _ (fun x hx hxγ hs => ihα x hs hx hxγ)
                  ξ hξ (by size_omega)
                  (fun w hw' => lt_transY (hw.of_mem_subs (subs_psi_s (fr_spec hw').1)) hw wγ
                    (FZOrder.k2s hw w hw') hαγ)
                have hσ' := hull_transfer wβ wπ hβσ _ (fun x hx hxγ hs => ihα x hs hx hxγ)
                  π hσ (by size_omega)
                  (fun w hw' => lt_transY (wπ.of_mem_subs (fr_spec hw').1) hw wγ
                    (FZOrder.k2t hw w hw') hαγ)
                exact MIH _ (Hull.psi hw hβσ hξ' hσ' (hull_transfer wβ wπ hβσ _
                  (fun x hx hxγ hs => ihα x hs hx hxγ) a ha (by size_omega)
                  (fun w hw' => lt_transY (hw.of_mem_subs (subs_psi_a (fr_spec hw').1)) hw wγ
                    (FZOrder.k2 hw w hw') hαγ))) hαγ
              · exact case_two wβ hγH MIH (Or.inr ⟨ξ, π, a, rfl, hγσ, le_of_not_ltY wβ wπ hβσ⟩)
                  (Hull.psi hw hγσ hξ hσ ha) hαγ
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

end RTKA.Z.WFY
