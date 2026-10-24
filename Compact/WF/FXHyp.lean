import Compact.WF.FXDist

/-! 断片 `FX` の `Good α → α ∈ Wmax`（Arai の Lemma 3.26 にあたる。Subsp の
`OCF/Jaeger/Constructive/WellOrder.lean` の `wmax_of_good` と同じ構成）。

拡張の仮定 `Hyp η` は、`Good η` から、`C^β(Wmax)` の整礎部分の `Acc` に沿った帰納法で導く
（`hyp_of_good`）。そこで `η` 自身を添字とする崩壊（`η = K_n` の `Ξ_n(b)`、`η = Ω_c` の `Ψ_{Ω_c}(b)`）が
現れたときだけ、同じ議論を一段下の崩壊に使う（`h15`）。`FX` では崩壊の値（`Ξ`・`Ψ`）は崩壊の添字
（`K_n`・`Ω_c`）にならないので、再帰は二段で止まる（`wmax_of_good`）。

Jäger の系では `Ψ` は引数について単調だが、`FX` の `Ξ`・`Ψ` は単調でない。そのため、生成集合の間の
移し替え（`hull_transfer`）と係数についての帰納法（`coeff_induction`）は、前線（`fr`）と K2・K2x を使って
示す。 -/

namespace RTKA.WFX

open Tm

/-! ### 前線の所属 -/

theorem fr_mem_plus_l {R a b w : Tm} (h : w ∈ fr R a) : w ∈ fr R (.plus a b) := by
  rw [fr, List.mem_append]; exact Or.inl h

theorem fr_mem_plus_r {R a b w : Tm} (h : w ∈ fr R b) : w ∈ fr R (.plus a b) := by
  rw [fr, List.mem_append]; exact Or.inr h

theorem fr_mem_om {R a w : Tm} (h : w ∈ fr R a) : w ∈ fr R (.Om a) := by
  rw [fr]; exact h

theorem fr_mem_xi {R a w : Tm} {n : Nat} (hn : ¬ Lt (.Xi n a) R) (h : w ∈ fr R a) :
    w ∈ fr R (.Xi n a) := by
  rw [fr]; simp only [hn, ↓reduceIte]; exact h

theorem fr_mem_xi_self {R a : Tm} {n : Nat} (hl : Lt (.Xi n a) R) :
    Tm.Xi n a ∈ fr R (.Xi n a) := by
  rw [fr]; simp only [hl, ↓reduceIte, List.mem_singleton]

theorem fr_mem_psi_p {R s p a w : Tm} (hn : ¬ Lt (.Psi s p a) R) (h : w ∈ fr R p) :
    w ∈ fr R (.Psi s p a) := by
  rw [fr]; simp only [hn, ↓reduceIte, List.mem_append]; exact Or.inl (Or.inr h)

theorem fr_mem_psi_a {R s p a w : Tm} (hn : ¬ Lt (.Psi s p a) R) (h : w ∈ fr R a) :
    w ∈ fr R (.Psi s p a) := by
  rw [fr]; simp only [hn, ↓reduceIte, List.mem_append]; exact Or.inr h

theorem fr_mem_psi_self {R s p a : Tm} (hl : Lt (.Psi s p a) R) :
    Tm.Psi s p a ∈ fr R (.Psi s p a) := by
  rw [fr]; simp only [hl, ↓reduceIte, List.mem_singleton]

/-! ### 生成集合の間の移し替えと係数についての帰納法 -/

/-- 前線（`R` について）が `θ` 未満の `C^θ(Wmax)` の元は、`ν < R` なら `C^ν(Wmax)` に入る
    （`θ` 未満の部分は `good` で `Wmax` に入れ、残りは `R` 以上の節点として作り直す） -/
theorem hull_transfer {θ ν R : Tm} (wν : FXNF ν) (wR : FXNF R) (hνR : Lt ν R) (S : Nat)
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
        have wK := FXNF.K' hw.xi.1
        have hνK : Lt ν (.K n) := lt_of_lt_of_leX wν wR wK hνR
          (le_transX wR hw wK (le_of_not_ltX hw wR hnR)
            (Or.inr ((lt_K_iff hw hw.xi.1).mpr (Nat.le_refl _))))
        exact Hull.xi hw hνK (ih _ (by size_omega) ha (by size_omega)
          (fun w h => hfr w (fr_mem_xi hnR h)))
      | @psi c a hw _ hσ ha =>
        have hnR : ¬ Lt (.Psi .zero (.Om c) a) R := fun hl => hxθ (hfr _ (fr_mem_psi_self hl))
        have hνσ : Lt ν (.Om c) := lt_of_lt_of_leX wν wR hw.psi'.2.1 hνR
          (le_transX wR hw hw.psi'.2.1 (le_of_not_ltX hw wR hnR) (Or.inr (lt_psi_om_self c a)))
        exact Hull.psi hw hνσ
          (ih _ (by size_omega) hσ (by size_omega) (fun w h => hfr w (fr_mem_psi_p hnR h)))
          (ih _ (by size_omega) ha (by size_omega) (fun w h => hfr w (fr_mem_psi_a hnR h)))

/-- `C^θ(Wmax)` の元で、前線（`R` について）が `θ` 未満、`R` 以上の節点の引数が `g` 未満のものに
    ついての帰納法 -/
theorem coeff_induction {θ R g : Tm} (P : Tm → Prop) (S : Nat)
    (good : ∀ x, Hull θ Wmax x → Lt x θ → x.size < S → P x)
    (hzero : P .zero) (hone : P .one) (hK : ∀ {n : Nat}, 1 ≤ n → P (.K n))
    (hplus : ∀ {a b : Tm}, FXNF (.plus a b) → P a → P b → P (.plus a b))
    (hom : ∀ {a : Tm}, FXNF (.Om a) → P a → P (.Om a))
    (hxi : ∀ {n : Nat} {a : Tm}, FXNF (.Xi n a) → Lt a g → P a → P (.Xi n a))
    (hpsi : ∀ {c a : Tm}, FXNF (.Psi .zero (.Om c) a) → Lt a g → P (.Om c) → P a →
      P (.Psi .zero (.Om c) a)) :
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
      | @psi c a hw _ hσ ha =>
        have hnR : ¬ Lt (.Psi .zero (.Om c) a) R := fun hl => hxθ (hfr _ (fr_mem_psi_self hl))
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
  | @psi c a hw hα hσ ha ihσ iha =>
    intro w h
    rw [fr] at h
    by_cases hl : Lt (.Psi .zero (.Om c) a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact Or.inr (Hull.psi hw hα hσ ha)
    · simp only [hl, ↓reduceIte, List.mem_append] at h
      rcases h with (h | h) | h
      · simp [fr] at h
      · exact ihσ w h
      · exact iha w h

/-- `Wmax` の元の前線の元は `Wmax` に入る -/
theorem fr_wmax {R : Tm} (wR : FXNF R) : ∀ x, Wmax x → ∀ w, w ∈ fr R x → Wmax w := by
  have key : ∀ x, Acc (Rel Wmax) x → Wmax x → ∀ w, w ∈ fr R x → Wmax w := by
    intro x hacc
    induction hacc with
    | intro x _ ih =>
      intro hx w hw
      have hG := wmax_good hx
      rcases fr_hull_wmax (fun m hm hmx => ih m ⟨hm, hmx⟩ hm) x hG.1 w hw with h | h
      · exact h
      · rcases fr_le wR (wmax_wf hx) hw with e | hlt
        · rw [e]; exact hx
        · exact hG.2 w h hlt
  intro x hx
  exact key x (wmax_acc hx) hx

/-! ### Lemma 3.26 -/

/-- `(18)` の証明の場合 2：添字 `π ≤ β` の崩壊 `α < γ`（`γ < π`） -/
theorem case_two {β γ α : Tm} (wβ : FXNF β) (hγH : Hull β Wmax γ)
    (MIH : ∀ ζ, Hull β Wmax ζ → Lt ζ γ → Wmax ζ)
    (hshape : (∃ n a, α = .Xi n a ∧ Lt γ (.K n) ∧ Le (.K n) β) ∨
      (∃ c a, α = .Psi .zero (.Om c) a ∧ Lt γ (.Om c) ∧ Le (.Om c) β))
    (hα : Hull γ Wmax α) (hαγ : Lt α γ) : Wmax α := by
  have wγ := hγH.wf_of
  have wα := hα.wf_of
  have hnγ := nr_spec γ wγ
  have hαp : isPrincipal α = true := by
    rcases hshape with ⟨n, a, rfl, -⟩ | ⟨c, a, rfl, -⟩ <;> rfl
  cases hγH with
  | zero => exact absurd hαγ (not_lt_zero _)
  | one =>
    have := lt_oneX wα hαγ
    subst this
    simp [isPrincipal] at hαp
  | K hj =>
    exfalso
    rcases hshape with ⟨n, a, rfl, hγK, -⟩ | ⟨c, a, rfl, hγσ, -⟩
    · have h1 := (lt_K_iff wα hj).mp hαγ
      have h2 := (lt_K_iff (FXNF.K' hj) wα.xi.1).mp hγK
      simp only [lev] at h1 h2
      omega
    · have h1 := (lt_K_iff wα hj).mp hαγ
      have h2 := lev_le_of_lt_gen hγσ
      simp only [lev] at h1 h2
      omega
  | mem hX _ _ => exact (wmax_good hX).2 _ hα hαγ
  | @plus g₁ g₂ hw hg₁ _ =>
    exact wmax_bounded wγ hα (MIH g₁ hg₁ (lt_plus_leftX hw))
      ((lt_prin_plus_iff wα hαp hw).mp hαγ)
      (lt_trans_FX hw.plus.1 hw hnγ.1 (lt_plus_leftX hw) hnγ.2.2)
  | @om e hw he =>
    rcases hshape with ⟨n, a, rfl, -, -⟩ | ⟨c, a, rfl, hγσ, -⟩
    · exact wmax_bounded wγ hα (MIH e he hw.om.2.2) (Or.inr ((lt_xi_omG wα hw.om.1).mp hαγ))
        (lt_trans_FX hw.om.1 hw hnγ.1 hw.om.2.2 hnγ.2.2)
    · exfalso
      have h1 := (lt_psi_omG wα hw.om.1).mp hαγ
      exact not_lt_of_leX wα.psi'.2.1 hw (le_om_of_leX wα.psi'.1 hw.om.1 h1) hγσ
  | @xi j b hw hβK _ =>
    exfalso
    rcases hshape with ⟨n, a, rfl, hγK, hKβ⟩ | ⟨c, a, rfl, hγσ, -⟩
    · have h1 := (lt_K_iff hw wα.xi.1).mp hγK
      have h2 := (lt_K_iff (FXNF.K' wα.xi.1) hw.xi.1).mp
        (lt_of_le_of_ltX (FXNF.K' wα.xi.1) wβ (FXNF.K' hw.xi.1) hKβ hβK)
      simp only [lev] at h1 h2
      omega
    · exact Lt.asymmX wα hw hαγ ((xi_lt_psiG hw wα).mpr ((lt_xi_omG hw wα.psi'.1).mp hγσ))
  | @psi c' b hw hβσ _ _ =>
    exfalso
    rcases hshape with ⟨n, a, rfl, hγK, hKβ⟩ | ⟨c, a, rfl, hγσ, hσβ⟩
    · have h1 := (lt_K_iff hw wα.xi.1).mp hγK
      have h2 := lev_le_of_lt_gen (lt_of_le_of_ltX (FXNF.K' wα.xi.1) wβ hw.psi'.2.1 hKβ hβσ)
      simp only [lev] at h1 h2
      omega
    · have h1 := (lt_om_iffX wα.psi'.1 hw.psi'.1).mp
        (lt_of_le_of_ltX wα.psi'.2.1 wβ hw.psi'.2.1 hσβ hβσ)
      have h2 := (lt_psi_omG hw wα.psi'.1).mp hγσ
      exact not_lt_of_leX hw.psi'.1 wα.psi'.1 h2 h1

/-- `γ` は `η` を添字とする崩壊（`η = K_n` の `Ξ_n(b)`、または `η = Ω_c` の `Ψ_{Ω_c}(b)`） -/
def IsColl (η γ : Tm) : Prop :=
  (∃ n b, η = .K n ∧ γ = .Xi n b) ∨ (∃ c b, η = .Om c ∧ γ = .Psi .zero (.Om c) b)

/-- 崩壊の値は崩壊の添字にならない -/
theorem not_isColl_of_isColl {η γ δ : Tm} (h : IsColl η γ) : ¬ IsColl γ δ := by
  rintro (⟨n, b, e, -⟩ | ⟨c, b, e, -⟩) <;>
    rcases h with ⟨_, _, -, rfl⟩ | ⟨_, _, -, rfl⟩ <;> cases e

/-- Lemma 3.26 の証明の段階 3：`η` 未満の `Good` な項は `Wmax` に入る -/
theorem step_three {η γ : Tm} (hG : Good η) (h15 : ∀ γ, IsColl η γ → Good γ → Wmax γ)
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
      exact hG.2 _ (Hull.plus hw (wmax_hull (hγ.2 _ hg₁ (lt_plus_leftX hw)) wη)
        (wmax_hull (hγ.2 _ hg₂ (lt_plus_rightX hw)) wη)) hγη
  | Om e =>
    cases hγ.1 with
    | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
    | om hw he => exact hG.2 _ (Hull.om hw (wmax_hull (hγ.2 e he hw.om.2.2) wη)) hγη
  | Xi n b =>
    cases hγ.1 with
    | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
    | xi hw hγK hb =>
      have wK := FXNF.K' hw.xi.1
      rcases triX wK wη with hKη | e | hηK
      · exact Obs _ (hG.2 _ (Hull.K hw.xi.1) hKη) (Or.inr hγK)
      · exact h15 _ (Or.inl ⟨n, b, e.symm, rfl⟩) hγ
      · exact hG.2 _ (Hull.xi hw hηK (hull_transfer wη wK hηK (b.size + 1)
          (fun x hx hxγ _ => hγ.2 x hx hxγ) b hb (Nat.lt_succ_self _) (k2x_FX hw))) hγη
  | Psi s p a =>
    obtain ⟨rfl, c, rfl, -⟩ := wγ.psi
    cases hγ.1 with
    | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
    | psi hw hγσ hσ ha =>
      have wσ := hw.psi'.2.1
      have hc : Wmax c := by
        cases hσ with
        | mem hX _ _ => exact wmax_om_arg hX
        | om _ hc => exact hγ.2 c hc (cx_FX hw)
      have hση : Hull η Wmax (.Om c) := Hull.om wσ (wmax_hull hc wη)
      rcases triX wσ wη with hσlt | e | hησ
      · exact Obs _ (hG.2 _ hση hσlt) (Or.inr hγσ)
      · exact h15 _ (Or.inr ⟨c, a, e.symm, rfl⟩) hγ
      · exact hG.2 _ (Hull.psi hw hησ hση (hull_transfer wη wσ hησ (a.size + 1)
          (fun x hx hxγ _ => hγ.2 x hx hxγ) a ha (Nat.lt_succ_self _) (k2_FX hw))) hγη

/-- Arai の Lemma 3.26：`η` を添字とする崩壊が `Good` なら `Wmax` に入るとき、`Good η` から拡張の仮定が
    成り立つ -/
theorem hyp_of_good {η : Tm} (hG : Good η) (h15 : ∀ γ, IsColl η γ → Good γ → Wmax γ) :
    Hyp η := by
  have wη := hG.1.wf_of
  intro β wβ hle γ hW hγ
  have hnβ := nr_spec β wβ
  have key : ∀ γ, Acc (Rel (Hull β Wmax)) γ → Hull β Wmax γ → Lt γ (nr β) → Wmax γ := by
    intro γ hacc
    induction hacc with
    | intro γ hacc' MIH0 =>
      intro hγH hγ
      have wγ := hγH.wf_of
      have MIH : ∀ ζ, Hull β Wmax ζ → Lt ζ γ → Wmax ζ := fun ζ hζ hζγ =>
        MIH0 ζ ⟨hζ, hζγ⟩ hζ (lt_trans_FX hζ.wf_of wγ hnβ.1 hζγ hγ)
      have Obs : ∀ δ, Wmax δ → Le γ δ → Wmax γ := by
        intro δ hδ hγδ
        have wδ := wmax_wf hδ
        by_cases hδβ : Lt δ β
        · exact wmax_bounded wδ (Hull.lower HW wδ wβ (Or.inr hδβ) hγH) hδ hγδ
            (nr_spec δ wδ).2.2
        · exact ((wmax_dist.2 β wβ ⟨δ, hδ, le_of_not_ltX wδ wβ hδβ⟩ γ).mp
            ⟨⟨hγH, Acc.intro γ hacc'⟩, hγ⟩).1
      have G2 : ∀ α, Hull γ Wmax α → Lt α γ → Wmax α := by
        intro α
        induction α using size_induction with
        | h α ihα =>
          intro hα hαγ
          by_cases hβnγ : Lt β (nr γ)
          · exact MIH α (Hull.sub_of_lt_nr HW wγ wβ hβnγ hα) hαγ
          · have below : ∀ x, FXNF x → Lt x α → Lt x γ :=
              fun x wx h => lt_trans_FX wx hα.wf_of wγ h hαγ
            cases hα with
            | zero => exact MIH _ Hull.zero hαγ
            | one => exact MIH _ Hull.one hαγ
            | K hn => exact MIH _ (Hull.K hn) hαγ
            | mem hX _ _ => exact hX
            | plus hw ha hb =>
              exact MIH _ (Hull.plus hw
                (wmax_hull (ihα _ (by size_omega) ha (below _ hw.plus.1 (lt_plus_leftX hw))) wβ)
                (wmax_hull (ihα _ (by size_omega) hb
                  (below _ hw.plus.2.1 (lt_plus_rightX hw))) wβ)) hαγ
            | om hw ha =>
              exact MIH _ (Hull.om hw (wmax_hull (ihα _ (by size_omega) ha
                (below _ hw.om.1 hw.om.2.2)) wβ)) hαγ
            | @xi n a hw hγK ha =>
              have wK := FXNF.K' hw.xi.1
              by_cases hβK : Lt β (.K n)
              · exact MIH _ (Hull.xi hw hβK (hull_transfer wβ wK hβK _
                  (fun x hx hxγ hs => ihα x hs hx hxγ) a ha (by size_omega)
                  (fun w hw' => lt_trans_FX (hw.of_mem_subs (subs_xi (fr_spec hw').1)) hw wγ
                    (k2x_FX hw w hw') hαγ))) hαγ
              · exact case_two wβ hγH MIH (Or.inl ⟨n, a, rfl, hγK, le_of_not_ltX wβ wK hβK⟩)
                  (Hull.xi hw hγK ha) hαγ
            | @psi c a hw hγσ hσ ha =>
              have wσ := hw.psi'.2.1
              by_cases hβσ : Lt β (.Om c)
              · have hσ' : Hull β Wmax (.Om c) := by
                  cases hσ with
                  | mem hX _ _ => exact wmax_hull hX wβ
                  | om hwσ hc =>
                    exact Hull.om hwσ (wmax_hull (ihα c (by size_omega) hc
                      (below c hw.psi'.1 (cx_FX hw))) wβ)
                exact MIH _ (Hull.psi hw hβσ hσ' (hull_transfer wβ wσ hβσ _
                  (fun x hx hxγ hs => ihα x hs hx hxγ) a ha (by size_omega)
                  (fun w hw' => lt_trans_FX (hw.of_mem_subs (subs_psi_a (fr_spec hw').1)) hw wγ
                    (k2_FX hw w hw') hαγ))) hαγ
              · exact case_two wβ hγH MIH (Or.inr ⟨c, a, rfl, hγσ, le_of_not_ltX wβ wσ hβσ⟩)
                  (Hull.psi hw hγσ hσ ha) hαγ
      exact step_three hG h15 ⟨Hull.sub_of_lt_nr HW wβ wγ hγ hγH, G2⟩
        (lt_of_lt_of_leX wγ hnβ.1 wη hγ hle) Obs
  exact key γ hW.2 hW.1 hγ

/-- `Good` な項は最大区別集合に入る -/
theorem wmax_of_good {η : Tm} (hG : Good η) : Wmax η :=
  wmax_of_good_hyp hG (hyp_of_good hG (fun _ hc hgγ => wmax_of_good_hyp hgγ
    (hyp_of_good hgγ (fun _ hc' _ => absurd hc' (not_isColl_of_isColl hc)))))

end RTKA.WFX
