import Compact.WF.FWDist

/-! 体系全体の `Good α → α ∈ Wmax` の枠組み（`FZHyp.lean` の一般化。順序の仮定 `FWOrder` の下で）。

* 生成集合 `C^θ(Wmax)` の移し替え（`ν ≤ R` に一般化）・係数についての帰納法・前線は Mahlo 添字も含めて扱う。
* `(18)` の証明の場合 2（`case_two`）：`α = Ψ^ξ_π(a) < γ = Ψ^σ_κ(b)`（`γ < π ≤ β < κ`）の比較を
  Prop. 4.20 の (1)〜(4) で分ける（`FZ` と同じ）。
* `FZ` と違って `Ψ^ξ`（`ξ > 0`）も崩壊の目標になるので、目標をたどる列 `Ch` は任意の長さになる。段階 3
  （`step_three`）は列をたどり（`chain_walk`、Arai の Lemma 6.38 の段階 3）、目標が `η` より大きい元に
  着けばそれを `C^η(Wmax)` に移して `Wmax` に入れ、列の行き着く先が `η` の崩壊になる場合だけを仮定
  `H15 η` に任せる。`H15` は `FWWF.lean` で `η` の形ごとに示す。 -/

namespace RTKA.W.WFY

open Tm
open WFX (fr_mem_plus_l fr_mem_plus_r fr_mem_om fr_mem_xi fr_mem_xi_self fr_mem_psi_p
  fr_mem_psi_a fr_mem_psi_self)

theorem fr_mem_psi_s {R s p a w : Tm} (hn : ¬ Lt (.Psi s p a) R) (h : w ∈ fr R s) :
    w ∈ fr R (.Psi s p a) := by
  rw [fr]; simp only [hn, ↓reduceIte, List.mem_append]; exact Or.inl (Or.inl h)

variable [FWOrder]

/-! ### 生成集合の間の移し替えと係数についての帰納法 -/

/-- 前線（`R` について）が `θ` 未満の `C^θ(Wmax)` の元は、`ν ≤ R` なら `C^ν(Wmax)` に入る -/
theorem hull_transfer {θ ν R : Tm} (wν : WNF ν) (wR : WNF R) (hνR : Le ν R) (S : Nat)
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
        have wK := WNF.K' hw.xi.1
        have hνK : Lt ν (.K n) := lt_of_le_of_ltY wν wR wK hνR
          (lt_of_le_of_ltY wR hw wK (le_of_not_ltY hw wR hnR)
            ((lt_K_iffY hw hw.xi.1).mpr (Nat.le_refl _)))
        exact Hull.xi hw hνK (ih _ (by size_omega) ha (by size_omega)
          (fun w h => hfr w (fr_mem_xi hnR h)))
      | @psi ξ π a hw _ hξ hσ ha =>
        have hnR : ¬ Lt (.Psi ξ π a) R := fun hl => hxθ (hfr _ (fr_mem_psi_self hl))
        have wπ := hw.psi.piF
        have hνσ : Lt ν π := lt_of_le_of_ltY wν wR wπ hνR
          (lt_of_le_of_ltY wR hw wπ (le_of_not_ltY hw wR hnR) (lt_psi_targetY hw))
        exact Hull.psi hw hνσ
          (ih _ (by size_omega) hξ (by size_omega) (fun w h => hfr w (fr_mem_psi_s hnR h)))
          (ih _ (by size_omega) hσ (by size_omega) (fun w h => hfr w (fr_mem_psi_p hnR h)))
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_psi_a hnR h)))

omit [FWOrder] in
/-- `C^θ(Wmax)` の元で、前線（`R` について）が `θ` 未満、`R` 以上の節点の引数が `g` 未満のものに
    ついての帰納法 -/
theorem coeff_induction {θ R g : Tm} (P : Tm → Prop) (S : Nat)
    (good : ∀ x, Hull θ Wmax x → Lt x θ → x.size < S → P x)
    (hzero : P .zero) (hone : P .one) (hK : ∀ {n : Nat}, 1 ≤ n → P (.K n))
    (hplus : ∀ {a b : Tm}, WNF (.plus a b) → P a → P b → P (.plus a b))
    (hom : ∀ {a : Tm}, WNF (.Om a) → P a → P (.Om a))
    (hxi : ∀ {n : Nat} {a : Tm}, WNF (.Xi n a) → Lt a g → P a → P (.Xi n a))
    (hpsi : ∀ {ξ π a : Tm}, WNF (.Psi ξ π a) → Lt a g → P ξ → P π → P a →
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

omit [FWOrder] in
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
theorem fr_wmax {R : Tm} (wR : WNF R) : ∀ x, Wmax x → ∀ w, w ∈ fr R x → Wmax w := by
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
theorem fr_hull_below {β γ R y : Tm} (wR : WNF R) (hy : Hull β Wmax y)
    (MIH : ∀ ζ, Hull β Wmax ζ → Lt ζ γ → Wmax ζ) {w : Tm} (hw : w ∈ fr R y) (hwγ : Lt w γ) :
    Wmax w := by
  rcases fr_hull_wmax (fun m hm _ => fr_wmax wR m hm) y hy w hw with h | h
  · exact h
  · exact MIH w h hwγ

/-! ### Lemma 3.26 -/

/-- `(18)` の証明の場合 2（Arai の Claim 6.39 の場合 2）：添字 `π ≤ β` の崩壊 `α < γ`（`γ < π`）は、
    `γ` の作り方で場合を分けて、`Wmax` の元で上から押さえる -/
theorem case_two {β γ α : Tm} (wβ : WNF β) (hγH : Hull β Wmax γ)
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
      have h2 := (lt_K_iffY (WNF.K' hj) wα.xi.1).mp hγK
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
    · rcases wα.shape with ⟨c, rfl, rfl⟩ | hsh
      · exfalso
        have h1 := (lt_psi_omY wα hw.om.1).mp hαγ
        exact not_lt_of_leY wα.psiOm.2.1 hw (le_om_of_leY wα.psiOm.1 hw.om.1 h1) hγσ
      · exact wmax_bounded wγ hα heW
          (Or.inr ((lt_OF_omG (IsOF.psi wα (notOm_of_shape hsh)) wα hw.om.1).mp hαγ)) hb
  | @xi j b hw hβK hb =>
    rcases hshape with ⟨n, a, rfl, hγK, hKβ⟩ | ⟨ξ, π, a, rfl, hγσ, hσβ⟩
    · exfalso
      have h1 := (lt_K_iffY hw wα.xi.1).mp hγK
      have h2 := (lt_K_iffY (WNF.K' wα.xi.1) hw.xi.1).mp
        (lt_of_le_of_ltY (WNF.K' wα.xi.1) wβ (WNF.K' hw.xi.1) hKβ hβK)
      simp only [lev] at h1 h2
      omega
    · have wπ := wα.psi.piF
      rcases wα.shape with ⟨c, rfl, rfl⟩ | -
      · exfalso
        exact Lt.asymmY wα hw hαγ ((lt_OF_psiOm (Or.inl ⟨j, b, rfl⟩) hw wα).mpr
          ((lt_OF_omG (Or.inl ⟨j, b, rfl⟩) hw wα.psiOm.1).mp hγσ))
      · have hmj : lev π = j := by
          have h1 := lev_le_of_lt_gen hγσ
          have h2 := (lt_K_iffY wπ hw.xi.1).mp (lt_of_le_of_ltY wπ wβ (WNF.K' hw.xi.1) hσβ hβK)
          simp only [lev] at h1 h2
          omega
        obtain ⟨-, w, hwfr, hwn⟩ := wit_psi_xi wα hw hmj hαγ hγσ
        have hwγ := FWOrder.k2x hw w hwfr
        exact bound w (fr_hull_below (WNF.K' hw.xi.1) hb MIH hwfr hwγ) hwγ hwn
  | @psi σ κ b hw hβκ hσH hκ hb =>
    have wκ := hw.psi.piF
    rcases hshape with ⟨n, a, rfl, hγK, hKβ⟩ | ⟨ξ, π, a, rfl, hγσ, hσβ⟩
    · exfalso
      have h1 := (lt_K_iffY hw wα.xi.1).mp hγK
      have h2 := lev_le_of_lt_gen (lt_of_le_of_ltY (WNF.K' wα.xi.1) wβ wκ hKβ hβκ)
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
        · have hwγ := FWOrder.k2 hw w hwfr
          exact bound w (fr_hull_below wκ hb MIH hwfr hwγ) hwγ hwn
        · have hwγ := FWOrder.k2t hw w hwfr
          exact bound w (fr_hull_below wκ hκ MIH hwfr hwγ) hwγ hwn
        · have hwγ := FWOrder.k2s hw w hwfr
          exact bound w (fr_hull_below wκ hσH MIH hwfr hwγ) hwγ hwn
      · subst e
        exact absurd hπκ (Lt.irrefl _)
      · obtain ⟨w, hwfr, hwn⟩ := wit_c4 hw wα wα.psi.xiF hαγ hσξ hn
        have hwγ := (fr_spec hwfr).2
        exact bound w (fr_hull_below hw hσH MIH hwfr hwγ) hwγ hwn

/-! ### 目標をたどる列 -/

/-- `γ` は `η` を添字とする崩壊（`η = K_n` の `Ξ_n(b)`、または `η` を目標とする `Ψ^ξ_η(b)`） -/
def IsColl (η γ : Tm) : Prop := (∃ n b, η = .K n ∧ γ = .Xi n b) ∨ ∃ ξ b, γ = .Psi ξ η b

/-- `Ch γ τ`：`τ` は `γ` から目標を 0 回以上たどって得られる（`Ψ^ξ_ρ(b)` の次は `ρ`） -/
inductive Ch : Tm → Tm → Prop
  | refl (x : Tm) : Ch x x
  | step {x ξ ρ b : Tm} : Ch x (.Psi ξ ρ b) → Ch x ρ

omit [FWOrder] in
theorem Ch.wnf {x y : Tm} (h : Ch x y) (hx : WNF x) : WNF y := by
  induction h with
  | refl => exact hx
  | step _ ih => exact ih.psi.piF

theorem Ch.le {x y : Tm} (h : Ch x y) (hx : WNF x) : Le x y := by
  induction h with
  | refl => exact Or.inl rfl
  | step h' ih =>
    have w := h'.wnf hx
    exact le_transY hx w w.psi.piF ih (Or.inr (lt_psi_targetY w))

omit [FWOrder] in
/-- 目標でない項に至る列は長さ 0 -/
theorem Ch.eq_of_not_tgt {x y : Tm} (h : Ch x y) (hx : WNF x) (hy : ¬ IsTgt y) : x = y := by
  cases h with
  | refl => rfl
  | step h' => exact absurd (h'.wnf hx).psi.tgt hy

omit [FWOrder] in
theorem not_tgt_psi0 {c a : Tm} : ¬ IsTgt (.Psi .zero (.Om c) a) := by
  rintro (⟨c', e', -⟩ | ⟨n, p, e'⟩ | ⟨ζ, κ, b', e', hζ⟩) <;> cases e'
  exact hζ rfl

/-- 列の行き着く先が `η` の崩壊になるときの仮定（Arai の Lemma 6.38 の (44)） -/
def H15 (η : Tm) : Prop := ∀ γ τ, Good γ → Lt γ η → (∀ δ, Wmax δ → Le γ δ → Wmax γ) →
  IsColl η τ → Ch γ τ → Hull γ Wmax τ → (∀ w, w ∈ fr τ τ → Lt w γ) → Wmax γ

/-- `η` 未満の `Good` な崩壊 `γ` から目標をたどる：たどった先 `τ` の目標が `η` より大きければ `τ` を
    `C^η(Wmax)` に移して `τ ∈ Wmax`、`η` なら `H15`、`η` より小さければさらにたどる -/
theorem chain_walk {η γ : Tm} (hG : Good η) (h15 : H15 η) (hγ : Good γ) (hγη : Lt γ η)
    (Obs : ∀ δ, Wmax δ → Le γ δ → Wmax γ) :
    ∀ τ, Ch γ τ → Hull γ Wmax τ → Lt τ η → (∀ w, w ∈ fr τ τ → Lt w γ) →
      (τ = γ ∨ IsTgt τ) → ((∃ n b, τ = .Xi n b) ∨ ∃ s ρ a, τ = .Psi s ρ a) → Wmax γ := by
  have wη := hG.1.wf_of
  have wγ := hγ.1.wf_of
  intro τ
  induction τ using size_induction with
  | h τ ih =>
  intro hch hτH hτη hfr hτt hsh
  have wτ := hch.wnf wγ
  have hγτ := hch.le wγ
  have fin : Hull η Wmax τ → Wmax γ := fun h => Obs τ (hG.2 τ h hτη) hγτ
  rcases hsh with ⟨n, b, rfl⟩ | ⟨s, ρ, a, rfl⟩
  · cases hτH with
    | mem hX _ _ => exact Obs _ hX hγτ
    | xi hw hγK hb =>
      have wK := WNF.K' hw.xi.1
      have hτK : Lt (.Xi n b) (.K n) := (lt_K_iffY hw hw.xi.1).mpr (Nat.le_refl _)
      rcases triY wK wη with hKη | e | hηK
      · exact Obs _ (hG.2 _ (Hull.K hw.xi.1) hKη) (le_transY wγ hw wK hγτ (Or.inr hτK))
      · exact h15 γ _ hγ hγη Obs (Or.inl ⟨n, b, e.symm, rfl⟩) hch (Hull.xi hw hγK hb) hfr
      · apply fin
        refine Hull.xi hw hηK (hull_transfer wη wK (Or.inr hηK) (b.size + 1)
          (fun x hx hxγ _ => hγ.2 x hx hxγ) b hb (Nat.lt_succ_self _) ?_)
        intro w hw'
        apply hfr w
        rw [fr]
        simp only [Lt.irrefl, ↓reduceIte]
        exact fr_sub wK hw (Or.inr hτK) hw.xi.2.1 hw' (FWOrder.k2x hw w hw')
  · cases hτH with
    | mem hX _ _ => exact Obs _ hX hγτ
    | psi hw hγρ hs hρ ha =>
      have wρ := hw.psi.piF
      have hττ : ¬ Lt (.Psi s ρ a) (.Psi s ρ a) := Lt.irrefl _
      have hτρ : Le (.Psi s ρ a) ρ := Or.inr (lt_psi_targetY hw)
      have frs : ∀ w, w ∈ fr ρ s → Lt w γ := fun w h =>
        hfr w (fr_mem_psi_s hττ (fr_sub wρ hw hτρ hw.psi.xiF h (FWOrder.k2s hw w h)))
      have frp : ∀ w, w ∈ fr ρ ρ → Lt w γ := fun w h =>
        hfr w (fr_mem_psi_p hττ (fr_sub wρ hw hτρ wρ h (FWOrder.k2t hw w h)))
      have fra : ∀ w, w ∈ fr ρ a → Lt w γ := fun w h =>
        hfr w (fr_mem_psi_a hττ (fr_sub wρ hw hτρ hw.psi.aF h (FWOrder.k2 hw w h)))
      rcases triY wρ wη with hρη | e | hηρ
      · rcases hw.shape with ⟨c, rfl, rfl⟩ | ⟨n, p, rfl⟩ | ⟨ζ, κ, b, rfl, hζ⟩
        · -- `Ω_c`：`τ = γ`
          have hτγ : Tm.Psi .zero (.Om c) a = γ := by
            rcases hτt with e | ht
            · exact e
            · exact absurd ht not_tgt_psi0
          have hc : Wmax c := by
            cases hρ with
            | mem hX _ _ => exact wmax_om_arg hX
            | om _ hc => exact hγ.2 c hc (by rw [← hτγ]; exact FWOrder.cx hw)
          exact Obs _ (hG.2 _ (Hull.om wρ (wmax_hull hc wη)) hρη) (le_transY wγ hw wρ hγτ hτρ)
        · exact ih _ (by size_omega) (Ch.step hch) hρ hρη frp
            (Or.inr (Or.inr (Or.inl ⟨n, p, rfl⟩))) (Or.inl ⟨n, p, rfl⟩)
        · exact ih _ (by size_omega) (Ch.step hch) hρ hρη frp
            (Or.inr (Or.inr (Or.inr ⟨ζ, κ, b, rfl, hζ⟩))) (Or.inr ⟨ζ, κ, b, rfl⟩)
      · exact h15 γ _ hγ hγη Obs (Or.inr ⟨s, a, by rw [e]⟩) hch (Hull.psi hw hγρ hs hρ ha) hfr
      · exact fin (Hull.psi hw hηρ
          (hull_transfer wη wρ (Or.inr hηρ) (s.size + 1) (fun x hx hxγ _ => hγ.2 x hx hxγ)
            s hs (Nat.lt_succ_self _) frs)
          (hull_transfer wη wρ (Or.inr hηρ) (ρ.size + 1) (fun x hx hxγ _ => hγ.2 x hx hxγ)
            ρ hρ (Nat.lt_succ_self _) frp)
          (hull_transfer wη wρ (Or.inr hηρ) (a.size + 1) (fun x hx hxγ _ => hγ.2 x hx hxγ)
            a ha (Nat.lt_succ_self _) fra))

/-- Lemma 3.26 の証明の段階 3：`η` 未満の `Good` な項は `Wmax` に入る -/
theorem step_three {η γ : Tm} (hG : Good η) (h15 : H15 η)
    (hγ : Good γ) (hγη : Lt γ η) (Obs : ∀ δ, Wmax δ → Le γ δ → Wmax γ) : Wmax γ := by
  have wη := hG.1.wf_of
  have wγ := hγ.1.wf_of
  have frγ : ∀ w, w ∈ fr γ γ → Lt w γ := fun w h => (fr_spec h).2
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
    exact chain_walk hG h15 hγ hγη Obs _ (Ch.refl _) hγ.1 hγη frγ (Or.inl rfl)
      (Or.inl ⟨n, b, rfl⟩)
  | Psi s ρ a =>
    exact chain_walk hG h15 hγ hγη Obs _ (Ch.refl _) hγ.1 hγη frγ (Or.inl rfl)
      (Or.inr ⟨s, ρ, a, rfl⟩)

/-- Arai の Lemma 3.26：列の行き着く先が `η` の崩壊になる場合の仮定 `H15 η` の下で、`Good η` から拡張の
    仮定が成り立つ -/
theorem hyp_of_good {η : Tm} (hG : Good η) (h15 : H15 η) :
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
          · have below : ∀ x, WNF x → Lt x α → Lt x γ :=
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
              have wK := WNF.K' hw.xi.1
              by_cases hβK : Lt β (.K n)
              · exact MIH _ (Hull.xi hw hβK (hull_transfer wβ wK (Or.inr hβK) _
                  (fun x hx hxγ hs => ihα x hs hx hxγ) a ha (by size_omega)
                  (fun w hw' => lt_transY (hw.of_mem_subs (subs_xi (fr_spec hw').1)) hw wγ
                    (FWOrder.k2x hw w hw') hαγ))) hαγ
              · exact case_two wβ hγH MIH (Or.inl ⟨n, a, rfl, hγK, le_of_not_ltY wβ wK hβK⟩)
                  (Hull.xi hw hγK ha) hαγ
            | @psi ξ π a hw hγσ hξ hσ ha =>
              have wπ := hw.psi.piF
              by_cases hβσ : Lt β π
              · have hξ' := hull_transfer wβ wπ (Or.inr hβσ) _ (fun x hx hxγ hs => ihα x hs hx hxγ)
                  ξ hξ (by size_omega)
                  (fun w hw' => lt_transY (hw.of_mem_subs (subs_psi_s (fr_spec hw').1)) hw wγ
                    (FWOrder.k2s hw w hw') hαγ)
                have hσ' := hull_transfer wβ wπ (Or.inr hβσ) _ (fun x hx hxγ hs => ihα x hs hx hxγ)
                  π hσ (by size_omega)
                  (fun w hw' => lt_transY (wπ.of_mem_subs (fr_spec hw').1) hw wγ
                    (FWOrder.k2t hw w hw') hαγ)
                exact MIH _ (Hull.psi hw hβσ hξ' hσ' (hull_transfer wβ wπ (Or.inr hβσ) _
                  (fun x hx hxγ hs => ihα x hs hx hxγ) a ha (by size_omega)
                  (fun w hw' => lt_transY (hw.of_mem_subs (subs_psi_a (fr_spec hw').1)) hw wγ
                    (FWOrder.k2 hw w hw') hαγ))) hαγ
              · exact case_two wβ hγH MIH (Or.inr ⟨ξ, π, a, rfl, hγσ, le_of_not_ltY wβ wπ hβσ⟩)
                  (Hull.psi hw hγσ hξ hσ ha) hαγ
      exact step_three hG h15 ⟨Hull.sub_of_lt_nr HW wβ wγ hγ hγH, G2⟩
        (lt_of_lt_of_leY wγ hnβ.1 wη hγ hle) Obs
  exact key γ hW.2 hW.1 hγ

omit [FWOrder] in
theorem h15_nt {η : Tm} (hT : ¬ IsTgt η) (hK : ∀ n, η ≠ .K n) : H15 η := by
  intro γ τ hγ _ _ hc hch _ _
  have wτ := hch.wnf hγ.1.wf_of
  rcases hc with ⟨n, b, e, -⟩ | ⟨ξ, b, rfl⟩
  · exact absurd e (hK n)
  · exact absurd wτ.psi.tgt hT

/-- 目標にも `K_n` にもならない `Good` な項は `Wmax` に入る -/
theorem wmax_of_good_nt {η : Tm} (hG : Good η) (hT : ¬ IsTgt η) (hK : ∀ n, η ≠ .K n) :
    Wmax η :=
  wmax_of_good_hyp hG (hyp_of_good hG (h15_nt hT hK))

theorem h15_om (c : Tm) : H15 (.Om c) := by
  intro γ τ hγ _ _ hc hch _ _
  have wγ := hγ.1.wf_of
  have wτ := hch.wnf wγ
  rcases hc with ⟨n, b, e, -⟩ | ⟨ξ, b, rfl⟩
  · cases e
  · have hξ := wτ.psiOm.2.2.2.2.2
    subst hξ
    have e := hch.eq_of_not_tgt wγ not_tgt_psi0
    subst e
    exact wmax_of_good_nt hγ not_tgt_psi0 (fun n e => by cases e)

end RTKA.W.WFY
