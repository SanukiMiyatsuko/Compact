import Compact.FS.FamRec

/-! 底：`t = Ψ^0_ρ(r + 1)`（`r` は目標 `ρ` の引数）の隙間。

`ρ = Ψ^ζ_κ(γ)`・`y = Ψ^ξ_κ(A)`（`A ≤ γ`）について、`ρ` の前線が `y` の下にあれば `C(γ, ρ)` の元は `C(A, y)` に入る
（`hull_tr`）。`t` の部分項の比較は `ρ` の部分項の比較に帰着する（`gp_floor`）。`Ξ_m(q)` も同じ（`hull_trx`）。 -/

namespace RTKA.Fund

open Tm W

/-- 前線の元は、より大きい基準の前線の元が全て基準の未満なら、より大きい基準の前線の元 -/
theorem fr_up {R' R : Tm} (hR' : WNF R') (hR : WNF R) (hle : Lt R' R) :
    ∀ {x w : Tm}, WNF x → (∀ u, u ∈ fr R x → Lt u R') → w ∈ fr R' x → w ∈ fr R x
  | .zero, _, _, _, h | .one, _, _, _, h | .K _, _, _, _, h => by simp [fr] at h
  | .plus a b, w, hx, hu, h => by
    obtain ⟨ha, hb, -, -⟩ := hx.plus
    rw [fr, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (fr_up hR' hR hle ha (fun u hu' => hu u (by rw [fr, List.mem_append]; exact Or.inl hu')) h)
    · exact Or.inr (fr_up hR' hR hle hb (fun u hu' => hu u (by rw [fr, List.mem_append]; exact Or.inr hu')) h)
  | .Om a, w, hx, hu, h => by
    rw [fr] at h ⊢
    exact fr_up hR' hR hle hx.om.1 (fun u hu' => hu u (by rw [fr]; exact hu')) h
  | .Xi m a, w, hx, hu, h => by
    rw [fr] at h ⊢
    by_cases h1 : Lt (.Xi m a) R'
    · simp only [h1, ↓reduceIte, List.mem_singleton] at h
      subst h
      simp [lt_transY hx hR' hR h1 hle]
    · simp only [h1, ↓reduceIte] at h
      have h2 : ¬ Lt (.Xi m a) R := fun h' => h1 (hu _ (by
        rw [fr]
        simp [h']))
      simp only [h2, ↓reduceIte]
      refine fr_up hR' hR hle hx.xi.2.1 (fun u hu' => hu u ?_) h
      rw [fr]
      simp only [h2, ↓reduceIte]
      exact hu'
  | .Psi s p a, w, hx, hu, h => by
    have hP := hx.psi
    rw [fr] at h ⊢
    by_cases h1 : Lt (.Psi s p a) R'
    · simp only [h1, ↓reduceIte, List.mem_singleton] at h
      subst h
      simp [lt_transY hx hR' hR h1 hle]
    · simp only [h1, ↓reduceIte, List.mem_append] at h
      have h2 : ¬ Lt (.Psi s p a) R := fun h' => h1 (hu _ (by
        rw [fr]
        simp [h']))
      simp only [h2, ↓reduceIte, List.mem_append]
      have hu2 : ∀ u, (u ∈ fr R s ∨ u ∈ fr R p) ∨ u ∈ fr R a → Lt u R' := fun u hu' => hu u (by
        rw [fr]
        simp only [h2, ↓reduceIte, List.mem_append]
        exact hu')
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (fr_up hR' hR hle hP.xiF (fun u hu' => hu2 u (Or.inl (Or.inl hu'))) h))
      · exact Or.inl (Or.inr (fr_up hR' hR hle hP.piF (fun u hu' => hu2 u (Or.inl (Or.inr hu'))) h))
      · exact Or.inr (fr_up hR' hR hle hP.aF (fun u hu' => hu2 u (Or.inr hu')) h)

/-- `κ` についての成分の前線は `ρ = Ψ^ζ_κ(γ)` の前線 -/
theorem fr_comp_mem {ζ κ γ w : Tm} (hρ : WNF (.Psi ζ κ γ)) (h : w ∈ fr κ γ ∨ w ∈ fr κ κ ∨ w ∈ fr κ ζ) :
    w ∈ fr (.Psi ζ κ γ) (.Psi ζ κ γ) := by
  have hP := hρ.psi
  have hle : Le (.Psi ζ κ γ) κ := Or.inr (lt_psi_targetY hρ)
  rcases h with h | h | h
  · exact fr_psi_self (Or.inr (Or.inr rfl)) (fr_of_fr hP.piF hρ hle hP.aF h (FWOrder.k2 hρ w h))
  · exact fr_psi_self (Or.inr (Or.inl rfl)) (fr_of_fr hP.piF hρ hle hP.piF h (FWOrder.k2t hρ w h))
  · exact fr_psi_self (Or.inl rfl) (fr_of_fr hP.piF hρ hle hP.xiF h (FWOrder.k2s hρ w h))

/-- `ρ = Ψ^ζ_κ(γ)` の前線は `κ` についての成分の前線 -/
theorem fr_cover {ζ κ γ w : Tm} (hρ : WNF (.Psi ζ κ γ)) (h : w ∈ fr (.Psi ζ κ γ) (.Psi ζ κ γ)) :
    w ∈ fr κ ζ ∨ w ∈ fr κ κ ∨ w ∈ fr κ γ := by
  have hP := hρ.psi
  have hne : ¬ Lt (Tm.Psi ζ κ γ) (.Psi ζ κ γ) := Lt.irrefl _
  have hlt : Lt (.Psi ζ κ γ) κ := lt_psi_targetY hρ
  rw [fr] at h
  simp only [hne, ↓reduceIte, List.mem_append] at h
  rcases h with (h | h) | h
  · exact Or.inl (fr_up hρ hP.piF hlt hP.xiF (fun u hu => FWOrder.k2s hρ u hu) h)
  · exact Or.inr (Or.inl (fr_up hρ hP.piF hlt hP.piF (fun u hu => FWOrder.k2t hρ u hu) h))
  · exact Or.inr (Or.inr (fr_up hρ hP.piF hlt hP.aF (fun u hu => FWOrder.k2 hρ u hu) h))

/-- `ρ = Ξ_m(q)` の前線は `K_m` についての `q` の前線 -/
theorem fr_cover_xi {m : Nat} {q w : Tm} (hρ : WNF (.Xi m q)) (h : w ∈ fr (.Xi m q) (.Xi m q)) :
    w ∈ fr (.K m) q := by
  have hn := hρ.xi.1
  have hne : ¬ Lt (Tm.Xi m q) (.Xi m q) := Lt.irrefl _
  rw [fr] at h
  simp only [hne, ↓reduceIte] at h
  exact fr_up hρ (WNF.K' hn) ((lt_K_iffY hρ hn).mpr (Nat.le_refl _)) hρ.xi.2.1
    (fun u hu => FWOrder.k2x hρ u hu) h

/-- `C(γ, ρ)` から `C(A, y)` への移し替え -/
theorem hull_tr {ζ κ γ ξ A E : Tm} (hρ : WNF (.Psi ζ κ γ)) (hy : WNF (.Psi ξ κ A)) (hAγ : Le A γ)
    (hsz : E.size < (Tm.Psi ζ κ γ).size)
    (hlow : ∀ n, n ∈ subs E → WNF n → ¬ Lt n (.Psi ξ κ A) →
      ∀ f, f ∈ fr (.Psi ζ κ γ) (.Psi ζ κ γ) → Lt f n)
    (hc1 : ∀ s k a, Tm.Psi s k a ∈ subs E → Lt a γ → Lt a A)
    (hc1x : ∀ m b, Tm.Xi m b ∈ subs E → Lt b γ → Lt b A)
    (hc3 : ∀ s, Tm.Psi s κ γ ∈ subs E → Lt s ζ → inC s A (.Psi ξ κ A) = true →
      Lt (.Psi s κ γ) (.Psi ξ κ A)) :
    ∀ {e : Tm}, WNF e → e ∈ subs E → inC e γ (.Psi ζ κ γ) = true → inC e A (.Psi ξ κ A) = true
  | .zero, _, _, _ => inC_zero _ _
  | .one, _, _, _ => inC_one _ _
  | .K _, _, _, _ => inC_K _ _ _
  | .plus a b, he, hE, h => by
    obtain ⟨ha, hb, -, -⟩ := he.plus
    rw [inC_plus, Bool.and_eq_true] at h ⊢
    exact ⟨hull_tr hρ hy hAγ hsz hlow hc1 hc1x hc3 ha (subs_trans hE (subs_plus_l (self_mem_subs a))) h.1,
      hull_tr hρ hy hAγ hsz hlow hc1 hc1x hc3 hb (subs_trans hE (subs_plus_r (self_mem_subs b))) h.2⟩
  | .Om a, he, hE, h => by
    rw [inC_om] at h ⊢
    exact hull_tr hρ hy hAγ hsz hlow hc1 hc1x hc3 he.om.1 (subs_trans hE (mem_subs_om a)) h
  | .Xi m b, he, hE, h => by
    have hbF := he.xi.2.1
    have hS := hull_tr hρ hy hAγ hsz hlow hc1 hc1x hc3 hbF (subs_trans hE (mem_subs_xi m b))
    have hγF := hρ.psi.aF
    have hAF := hy.psi.aF
    by_cases h1 : Lt (.Xi m b) (.Psi ζ κ γ)
    · by_cases hl : lev κ = m
      · have e1 := (lt_xi_psiY hl).mp h1
        rw [lt_psi_xiY hl] at e1
        refine inC_xi_iff.mpr (Or.inl ((lt_xi_psiY hl).mpr ?_))
        rw [lt_psi_xiY hl]
        rintro (h3 | ⟨h3, h4⟩)
        · exact e1 (Or.inl h3)
        · by_cases h5 : inC b γ (.Psi ζ κ γ) = true
          · rw [hS h5] at h4
            cases h4
          · exact e1 (Or.inr ⟨lt_of_lt_of_leY hbF hAF hγF h3 hAγ, by simpa using h5⟩)
      · have h0 : lev (.Xi m b) ≤ lev (.Psi ζ κ γ) := lev_le_of_lt_gen h1
        have h0' : m < lev κ := by
          simp only [lev] at h0
          omega
        exact inC_xi_iff.mpr (Or.inl ((lt_principal_iff rfl rfl).mpr
          (cmpP_of_lev_lt (y := .Psi ξ κ A) h0')))
    · rcases inC_xi_iff.mp h with h2 | ⟨h2, h3⟩
      · exact absurd h2 h1
      · exact inC_xi_iff.mpr (Or.inr ⟨hS h2, hc1x m b hE h3⟩)
  | .Psi s k a, he, hE, h => by
    have hP := he.psi
    have hκF := hρ.psi.piF
    have hS_k := hull_tr hρ hy hAγ hsz hlow hc1 hc1x hc3 hP.piF
      (subs_trans hE (subs_psi_p (self_mem_subs k)))
    have hS_s := hull_tr hρ hy hAγ hsz hlow hc1 hc1x hc3 hP.xiF
      (subs_trans hE (subs_psi_s (self_mem_subs s)))
    have hS_a := hull_tr hρ hy hAγ hsz hlow hc1 hc1x hc3 hP.aF
      (subs_trans hE (subs_psi_a (self_mem_subs a)))
    have parts : inC k γ (.Psi ζ κ γ) = true → inC s γ (.Psi ζ κ γ) = true →
        inC a γ (.Psi ζ κ γ) = true → Lt a γ → inC (.Psi s k a) A (.Psi ξ κ A) = true := fun h0 h2 h3 h4 =>
      inC_psi_iff.mpr (Or.inr ⟨hS_k h0, hS_s h2, hS_a h3, hc1 s k a hE h4⟩)
    by_cases h1 : Lt (.Psi s k a) (.Psi ζ κ γ)
    · by_cases hny : Lt (.Psi s k a) (.Psi ξ κ A)
      · exact inC_psi_iff.mpr (Or.inl hny)
      by_cases hl : lev k = lev κ
      · rcases (lt_psi_psiY hl h1.ne).mp h1 with hA' | ⟨-, hB2, hc1' | hc2 | hc3' | hc4⟩
        · have hkρ : Le k (.Psi ζ κ γ) := le_of_not_ltY hρ hP.piF hA'
          have hkne : k ≠ .Psi ζ κ γ := ne_of_size_lt (by
            have h3 := size_le_of_mem_subs hE
            simp only [Tm.size] at h3 hsz ⊢
            omega)
          have hkρ' : Lt k (.Psi ζ κ γ) := hkρ.resolve_left hkne
          have hkκ : Lt k κ := lt_transY hP.piF hρ hκF hkρ' (lt_psi_targetY hρ)
          have hky := coll_psiY hy k hP.piF (hS_k (WFY.inC_of_ltY _ hP.piF hρ hkρ')) hkκ
          exact inC_psi_iff.mpr (Or.inl (lt_transY he hP.piF hy (lt_psi_targetY he) hky))
        · obtain ⟨h4, h3, h2, h0⟩ := hc1'
          exact parts h0 h2 h3 h4
        · exfalso
          obtain ⟨w, hw, hw'⟩ := wit_c2 hρ he hP.aF (le_of_ne_gtY hρ.psi.aF hP.aF hc2.1) hB2 hc2.2
          have hw2 : w ∈ fr (.Psi ζ κ γ) (.Psi ζ κ γ) := fr_comp_mem hρ (by
            rcases hw with h3 | h3 | h3
            · exact Or.inl h3
            · exact Or.inr (Or.inl h3)
            · exact Or.inr (Or.inr h3))
          exact hw' (hlow _ hE he hny w hw2)
        · obtain ⟨h5, h6, h7, h8⟩ := hc3'
          have e1 : a = γ := FWOrder.eq hP.aF hρ.psi.aF h5
          subst e1
          subst h6
          exact inC_psi_iff.mpr (Or.inl (hc3 s hE h7 (hS_s h8)))
        · exfalso
          obtain ⟨w, hw, hw'⟩ := wit_c4 hρ he hP.xiF h1 hc4.1 hc4.2
          exact hw' (hlow _ hE he hny w (fr_psi_self (Or.inl rfl) hw))
      · have h0 : lev (.Psi s k a) ≤ lev (.Psi ζ κ γ) := lev_le_of_lt_gen h1
        have h0' : lev k < lev κ := by
          simp only [lev] at h0
          omega
        exact inC_psi_iff.mpr (Or.inl ((lt_principal_iff rfl rfl).mpr (cmpP_of_lev_lt h0')))
    · rcases inC_psi_iff.mp h with h2 | ⟨h2, h3, h4, h5⟩
      · exact absurd h2 h1
      · exact parts h2 h3 h4 h5

/-- `C(γ, ρ)` の元で `κ` 未満のものは `y` 未満 -/
theorem hull_lt {ζ κ γ ξ A v : Tm} (hρ : WNF (.Psi ζ κ γ)) (hy : WNF (.Psi ξ κ A)) (hAγ : Le A γ)
    (hsz : v.size < (Tm.Psi ζ κ γ).size)
    (hlow : ∀ n, n ∈ subs v → WNF n → ¬ Lt n (.Psi ξ κ A) →
      ∀ f, f ∈ fr (.Psi ζ κ γ) (.Psi ζ κ γ) → Lt f n)
    (hc1 : ∀ s k a, Tm.Psi s k a ∈ subs v → Lt a γ → Lt a A)
    (hc1x : ∀ m b, Tm.Xi m b ∈ subs v → Lt b γ → Lt b A)
    (hc3 : ∀ s, Tm.Psi s κ γ ∈ subs v → Lt s ζ → inC s A (.Psi ξ κ A) = true →
      Lt (.Psi s κ γ) (.Psi ξ κ A))
    (hv : WNF v) (hvκ : Lt v κ) (hC : inC v γ (.Psi ζ κ γ) = true) : Lt v (.Psi ξ κ A) :=
  coll_psiY hy v hv (hull_tr hρ hy hAγ hsz hlow hc1 hc1x hc3 hv (self_mem_subs v) hC) hvκ

/-- 同じ目標・同じ引数の崩壊の比較 -/
theorem lt_same_arg {s z κ γ : Tm} (hn : WNF (.Psi s κ γ)) (hy : WNF (.Psi z κ γ)) (hsz : Lt s z)
    (hC : inC s γ (.Psi z κ γ) = true) : Lt (.Psi s κ γ) (.Psi z κ γ) := by
  have hne : Tm.Psi s κ γ ≠ .Psi z κ γ := fun e => hsz.ne (Tm.Psi.inj e).1
  exact (lt_psi_psiY rfl hne).mpr (Or.inr ⟨lt_psi_targetY hy, lt_psi_targetY hn, Or.inr (Or.inr (Or.inl
    ⟨cmp_self _, rfl, hsz, hC⟩))⟩)

/-- `C(q, ρ)` から `C(A, y)` への移し替え（`ρ = Ξ_m(q)`、`y = Ξ_m(A)`） -/
theorem hull_trx {m : Nat} {q A E : Tm} (hρ : WNF (.Xi m q)) (hy : WNF (.Xi m A))
    (hsz : E.size < (Tm.Xi m q).size)
    (hlow : ∀ n, n ∈ subs E → WNF n → ¬ Lt n (.Xi m A) → ∀ f, f ∈ fr (.Xi m q) (.Xi m q) → Lt f n)
    (hc1 : ∀ s k a, Tm.Psi s k a ∈ subs E → Lt a q → Lt a A)
    (hc1x : ∀ m' b, Tm.Xi m' b ∈ subs E → Lt b q → Lt b A) :
    ∀ {e : Tm}, WNF e → e ∈ subs E → inC e q (.Xi m q) = true → inC e A (.Xi m A) = true
  | .zero, _, _, _ => inC_zero _ _
  | .one, _, _, _ => inC_one _ _
  | .K _, _, _, _ => inC_K _ _ _
  | .plus a b, he, hE, h => by
    obtain ⟨ha, hb, -, -⟩ := he.plus
    rw [inC_plus, Bool.and_eq_true] at h ⊢
    exact ⟨hull_trx hρ hy hsz hlow hc1 hc1x ha (subs_trans hE (subs_plus_l (self_mem_subs a))) h.1,
      hull_trx hρ hy hsz hlow hc1 hc1x hb (subs_trans hE (subs_plus_r (self_mem_subs b))) h.2⟩
  | .Om a, he, hE, h => by
    rw [inC_om] at h ⊢
    exact hull_trx hρ hy hsz hlow hc1 hc1x he.om.1 (subs_trans hE (mem_subs_om a)) h
  | .Xi m' b, he, hE, h => by
    have hbF := he.xi.2.1
    have hS := hull_trx hρ hy hsz hlow hc1 hc1x hbF (subs_trans hE (mem_subs_xi m' b))
    have hqF := hρ.xi.2.1
    by_cases h1 : Lt (.Xi m' b) (.Xi m q)
    · by_cases hny : Lt (.Xi m' b) (.Xi m A)
      · exact inC_xi_iff.mpr (Or.inl hny)
      by_cases hl : m' = m
      · subst hl
        have hne : b ≠ q := fun e => h1.ne (by rw [e])
        rcases (lt_xi_xi0 hne).mp h1 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · have h5 := hc1x m' b hE h3
          exact inC_xi_iff.mpr (Or.inl ((lt_xi_xi0 h5.ne).mpr (Or.inl ⟨h5, hS h4⟩)))
        · exfalso
          have hn := hρ.xi.1
          have hK := WNF.K' hn
          have hxK : Lt (.Xi m' b) (.K m') := (lt_K_iffY he hn).mpr (Nat.le_refl _)
          have h5 := (inC_frY hqF hK he hqF hbF hρ.xi.2.2.2.2 (Or.inr hxK) (Or.inr h3)).mpr
            fun w hw => inC_of_lt_node (fr_node hw) (hlow _ hE he hny w (fr_xi_self hρ hw))
          rw [h5] at h4
          cases h4
      · have h0 : lev (.Xi m' b) ≤ lev (.Xi m q) := lev_le_of_lt_gen h1
        have h0' : m' < m := by
          simp only [lev] at h0
          omega
        exact inC_xi_iff.mpr (Or.inl ((lt_principal_iff rfl rfl).mpr
          (cmpP_of_lev_lt (y := .Xi m A) h0')))
    · rcases inC_xi_iff.mp h with h2 | ⟨h2, h3⟩
      · exact absurd h2 h1
      · exact inC_xi_iff.mpr (Or.inr ⟨hS h2, hc1x m' b hE h3⟩)
  | .Psi s k a, he, hE, h => by
    have hP := he.psi
    have hqF := hρ.xi.2.1
    have hn := hρ.xi.1
    have hK := WNF.K' hn
    have hS_k := hull_trx hρ hy hsz hlow hc1 hc1x hP.piF (subs_trans hE (subs_psi_p (self_mem_subs k)))
    have hS_s := hull_trx hρ hy hsz hlow hc1 hc1x hP.xiF (subs_trans hE (subs_psi_s (self_mem_subs s)))
    have hS_a := hull_trx hρ hy hsz hlow hc1 hc1x hP.aF (subs_trans hE (subs_psi_a (self_mem_subs a)))
    have parts : inC k q (.Xi m q) = true → inC s q (.Xi m q) = true → inC a q (.Xi m q) = true → Lt a q →
        inC (.Psi s k a) A (.Xi m A) = true := fun h0 h2 h3 h4 =>
      inC_psi_iff.mpr (Or.inr ⟨hS_k h0, hS_s h2, hS_a h3, hc1 s k a hE h4⟩)
    by_cases h1 : Lt (.Psi s k a) (.Xi m q)
    · by_cases hny : Lt (.Psi s k a) (.Xi m A)
      · exact inC_psi_iff.mpr (Or.inl hny)
      by_cases hl : lev k = m
      · by_cases hρk : Lt (.Xi m q) k
        · exfalso
          obtain ⟨-, w, hw, hw'⟩ := wit_psi_xi he hρ hl h1 hρk
          exact hw' (hlow _ hE he hny w (fr_xi_self hρ hw))
        · have hkρ : Le k (.Xi m q) := le_of_not_ltY hρ hP.piF hρk
          have hkne : k ≠ .Xi m q := ne_of_size_lt (by
            have h3 := size_le_of_mem_subs hE
            simp only [Tm.size] at h3 hsz ⊢
            omega)
          have hkρ' : Lt k (.Xi m q) := hkρ.resolve_left hkne
          have hρK : Lt (.Xi m q) (.K m) := (lt_K_iffY hρ hn).mpr (Nat.le_refl _)
          have hky := coll_xi0 hy k hP.piF (hS_k (WFY.inC_of_ltY _ hP.piF hρ hkρ'))
            (lt_transY hP.piF hρ hK hkρ' hρK)
          exact inC_psi_iff.mpr (Or.inl (lt_transY he hP.piF hy (lt_psi_targetY he) hky))
      · have h0 : lev (.Psi s k a) ≤ lev (.Xi m q) := lev_le_of_lt_gen h1
        have h0' : lev k < m := by
          simp only [lev] at h0
          omega
        exact inC_psi_iff.mpr (Or.inl ((lt_principal_iff rfl rfl).mpr
          (cmpP_of_lev_lt (y := .Xi m A) h0')))
    · rcases inC_psi_iff.mp h with h2 | ⟨h2, h3, h4, h5⟩
      · exact absurd h2 h1
      · exact parts h2 h3 h4 h5

/-- `C(q, ρ)` の元で `K_m` 未満のものは `y = Ξ_m(A)` 未満 -/
theorem hull_ltx {m : Nat} {q A v : Tm} (hρ : WNF (.Xi m q)) (hy : WNF (.Xi m A))
    (hsz : v.size < (Tm.Xi m q).size)
    (hlow : ∀ n, n ∈ subs v → WNF n → ¬ Lt n (.Xi m A) → ∀ f, f ∈ fr (.Xi m q) (.Xi m q) → Lt f n)
    (hc1 : ∀ s k a, Tm.Psi s k a ∈ subs v → Lt a q → Lt a A)
    (hc1x : ∀ m' b, Tm.Xi m' b ∈ subs v → Lt b q → Lt b A)
    (hv : WNF v) (hvK : Lt v (.K m)) (hC : inC v q (.Xi m q) = true) : Lt v (.Xi m A) :=
  coll_xi0 hy v hv (hull_trx hρ hy hsz hlow hc1 hc1x hv (self_mem_subs v) hC) hvK

/-! ### `t` の部分項と `ρ` の部分項 -/

theorem one_lt_of_prin {y : Tm} (hy : WNF y) (hyp : isPrincipal y = true) (hy1 : y ≠ .one) : Lt .one y := by
  rcases triY WNF.one hy with h | h | h
  · exact h
  · exact absurd h.symm hy1
  · have e := lt_oneY hy h
    rw [e] at hyp
    cases hyp

/-- `t = Ψ^0_ρ(r + 1)` の部分項の比較は `ρ` の部分項の比較に帰着する -/
theorem gp_floor {ρ r y : Tm} (ht : WNF (.Psi .zero ρ (sc r))) (hr : r ∈ subs ρ) (hyF : WNF y)
    (hyp : isPrincipal y = true) (hy1 : y ≠ .one)
    (h : ∀ v, v ∈ subs ρ → v ≠ ρ → Lt v ρ → Lt v y) : Gp (.Psi .zero ρ (sc r)) y := by
  intro v hv hne hvt
  have hρ := ht.psi.piF
  have hX := ht.psi.aF
  have hy0 : y ≠ .zero := fun e => by
    rw [e] at hyp
    cases hyp
  have hρy : ∀ w, w ∈ subs ρ → Lt w (.Psi .zero ρ (sc r)) → Lt w y := fun w hw hl => by
    have hwF := hρ.of_mem_subs hw
    have hl' : Lt w ρ := lt_transY hwF ht hρ hl (lt_psi_targetY ht)
    exact h w hw hl'.ne hl'
  simp only [subs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
  rcases hv with e | (e | h') | h'
  · exact absurd e hne
  · rw [e]
    exact zero_lt hy0
  · exact hρy v h' hvt
  · refine lt_of_summands_sub hX ht hyp hy0 (fun s hs w hw hl => ?_) h' hvt
    have e' : summands (sc r) = summands r ++ [.one] := summands_succT r
    rw [e'] at hs
    rcases List.mem_append.mp hs with hs' | hs'
    · exact hρy w (subs_trans hr (subs_trans (mem_subs_of_mem_summands hs') hw)) hl
    · rw [List.mem_singleton.mp hs'] at hw
      simp only [subs, List.mem_singleton] at hw
      rw [hw]
      exact one_lt_of_prin hyF hyp hy1

/-- 前線の元が全て `y` 未満で、添字の条件があれば、`ρ` の真の部分項は `y` 未満 -/
theorem floor_low {ζ κ γ z : Tm} (hρ : WNF (.Psi ζ κ γ)) (hy : WNF (.Psi z κ γ))
    (hF : ∀ f, f ∈ fr (.Psi ζ κ γ) (.Psi ζ κ γ) → Lt f (.Psi z κ γ))
    (hI : ∀ s, Tm.Psi s κ γ ∈ subs ζ → Lt s ζ → Lt s z) :
    ∀ v, v ∈ subs (.Psi ζ κ γ) → v ≠ .Psi ζ κ γ → Lt v (.Psi ζ κ γ) → Lt v (.Psi z κ γ) := by
  intro v hv hne hl
  have hP := hρ.psi
  have hvF := hρ.of_mem_subs hv
  have hvκ : Lt v κ := lt_transY hvF hρ hP.piF hl (lt_psi_targetY hρ)
  have hlow : ∀ n, n ∈ subs v → WNF n → ¬ Lt n (.Psi z κ γ) →
      ∀ f, f ∈ fr (.Psi ζ κ γ) (.Psi ζ κ γ) → Lt f n := fun n _ hnF hn f hf =>
    lt_of_lt_of_leY (hρ.of_mem_subs (fr_spec hf).1) hy hnF (hF f hf) (le_of_not_ltY hnF hy hn)
  have hCv := WFY.inC_of_ltY γ hvF hρ hl
  have hsz := size_lt_of_mem_subs_ne hv hne
  simp only [subs, List.mem_cons, List.mem_append] at hv
  rcases hv with e | (h | h) | h
  · exact absurd e hne
  · exact hull_lt hρ hy (Or.inl rfl) hsz hlow (fun _ _ _ _ h' => h') (fun _ _ _ h' => h')
      (fun s hs hsζ hC => lt_same_arg (hvF.of_mem_subs hs) hy (hI s (subs_trans h hs) hsζ) hC) hvF hvκ hCv
  · exact lt_of_mem_tgt hy h hvκ
  · refine hull_lt hρ hy (Or.inl rfl) hsz hlow (fun _ _ _ _ h' => h') (fun _ _ _ h' => h')
      (fun s hs _ _ => ?_) hvF hvκ hCv
    exfalso
    have h1 := size_le_of_mem_subs (subs_trans h hs)
    simp only [Tm.size] at h1
    omega

/-- 目標の前線の元は種 -/
theorem seed_of_frt {π X p : Tm} (ht : WNF (.Psi .zero π X)) (hp : p ∈ fr π π) : SeedP π X p := by
  have hπF := ht.psi.piF
  have hpF := hπF.of_mem_subs (fr_spec hp).1
  have hpt := FWOrder.k2t ht p hp
  refine ⟨hpF, hpt, fun g d _ hd h => ?_, fr_node hp⟩
  by_cases hdt : Lt (.Psi .zero π X) d
  · exact WFY.inC_of_ltY _ hpF hd (lt_transY hpF ht hd hpt hdt)
  · rcases inC_psi_iff.mp h with h' | ⟨h1, -, -, -⟩
    · exact absurd h' hdt
    · refine fr_of_inC π (fun u hu hn hud => hn ?_) h1 p hp
      exact lt_of_lt_of_leY (hπF.of_mem_subs hu) hd hπF hud
        (le_transY hd ht hπF (le_of_not_ltY ht hd hdt) (Or.inr (lt_psi_targetY ht)))

/-- 目標の前線の最大の元 -/
theorem maxL_frt {π X p : Tm} (ht : WNF (.Psi .zero π X)) (hm : maxL (frB π π) = some p) :
    SeedP π X p ∧ p ∈ fr π π ∧ ∀ f, f ∈ fr π π → Le f p := by
  have hπF := ht.psi.piF
  have hpm : p ∈ fr π π := by
    have := maxL_mem hm
    rwa [frB_eq_fr] at this
  refine ⟨seed_of_frt ht hpm, hpm, fun f hf => le_maxL (fun x hx => ?_) hm (by rw [frB_eq_fr]; exact hf)⟩
  rw [frB_eq_fr] at hx
  exact hπF.of_mem_subs (fr_spec hx).1

/-- 添字が極限のときの最初の列 -/
theorem s0_out {π X τ Y μ : Tm} {T : Tm → Tm → Prop} (C : MCtx π X τ Y μ T)
    (hSμ : ∀ u, u ∈ summands μ → u ≠ .one → SeqI u (info u).seq)
    (hμs : ∀ u, u ∈ summands μ → u ≠ .one → u ∈ subs (.Psi .zero π X) ∧ u.size < π.size)
    (hμ0 : μ ≠ .zero) (hs : ¬ isSucc μ = true) :
    ∃ pre R, summands μ = pre ++ [R] ∧ R ≠ .one ∧ preT (info μ).sums = pre ∧ lastT (info μ).sums = R ∧
      s0Of π τ Y μ = .app π (.idx τ Y) pre R (info R).seq .zero .zero ∧
      IdxOut π X τ Y μ .zero pre R (s0Of π τ Y μ) := by
  have hμF := C.hμF
  have hsum := summands_pre_last hμ0
  have hlast : lastS (info μ).sums = (info (lastT (info μ).sums)).seq := lastS_coh (coh_sums μ)
  obtain ⟨pre, hpr⟩ : ∃ pre, pre = preT (info μ).sums := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = lastT (info μ).sums := ⟨_, rfl⟩
  rw [← hpr, ← hR] at hsum
  rw [← hR] at hlast
  have hRm : R ∈ summands μ := by
    rw [hsum]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hR1 : R ≠ .one := by
    intro e
    apply hs
    show (summands μ).getLast? == some one
    rw [hsum, e]
    simp
  have hRp := nfl_principal (nfl_summands hμF) R hRm
  have hR0 : R ≠ .zero := by
    intro e
    rw [e] at hRp
    cases hRp
  have hs0 : s0Of π τ Y μ = .app π (.idx τ Y) pre R (info R).seq .zero .zero := by
    unfold s0Of
    rw [← hpr, ← hR, hlast, mkApp_idx (Or.inl rfl)]
    rfl
  have o0 := mahlo_out C hSμ hμs .zero pre [] R hsum hR1 (zero_lt hR0) (fun h => absurd rfl h) WNF.zero
  rw [← hs0] at o0
  exact ⟨pre, R, hsum, hR1, hpr.symm, hR.symm, hs0, o0⟩

/-- 底の例外：素の 0 番目が種 `p` 未満のとき -/
theorem tail_floor {ζ κ γ p : Tm} (ht : WNF (.Psi .zero (.Psi ζ κ γ) (sc γ)))
    (hIH : ∀ u, u ∈ subs (.Psi .zero (.Psi ζ κ γ) (sc γ)) → u ≠ .Psi .zero (.Psi ζ κ γ) (sc γ) →
      SeqI u (info u).seq)
    (hζ0 : ζ ≠ .zero) (hs : ¬ isSucc ζ = true)
    (Sp : SeedP (.Psi ζ κ γ) (sc γ) p) (hpm : p ∈ fr (.Psi ζ κ γ) (.Psi ζ κ γ))
    (hmax : ∀ f, f ∈ fr (.Psi ζ κ γ) (.Psi ζ κ γ) → Le f p)
    (hlt : Lt (s0Of (.Psi ζ κ γ) κ γ ζ).first p) (hyp : Le (.Psi .zero κ γ) p) :
    SeqI (.Psi .zero (.Psi ζ κ γ) (sc γ)) (mTail (.Psi ζ κ γ) κ (info κ).fam γ ζ p) := by
  have hρ := ht.psi.piF
  have hP := hρ.psi
  have hκF := hP.piF
  have hγF := hP.aF
  have hζF := hP.xiF
  have hρκ : Lt (.Psi ζ κ γ) κ := lt_psi_targetY hρ
  have hc : Chain (.Psi ζ κ γ) (.Psi ζ κ γ) := .refl _
  have C := mctx_chain (X := sc γ) ht hc
  obtain ⟨hSY, hSμ, hμs⟩ := psi_parts hIH hc
  obtain ⟨pre, R, hsum, hR1, -, -, -, o0⟩ := s0_out C hSμ hμs hζ0 hs
  obtain ⟨P₀, x₀, hP₀, hz₀, hfF, hx₀F, hyR, hz₀μ, -, -, hx₀0, hx₀g⟩ := o0.form _ o0.mem
  have e0 : P₀ = .zero := by
    rcases hP₀ with h | h <;> exact h
  subst e0
  rw [hz₀] at hlt hfF
  have hN : NFL (pre ++ R :: []) := hsum ▸ nfl_summands hζF
  have hζe : ζ = ofSummands (pre ++ R :: []) := by rw [← hsum, ofSummands_summands ζ hζF]
  have hRN := hN.1 R (List.mem_append_right _ List.mem_cons_self)
  have hRF := hRN.1
  have hpreN := nfl_append_left hN
  have hpreF := wnf_ofSummands hpreN
  have hz₀F := hfF.psi.xiF
  have hpκ : Lt p κ := lt_transY Sp.hF hρ hκF (fr_spec hpm).2 hρκ
  have hp0 : p ≠ .zero := by
    rcases Sp.hn with ⟨m', a, e'⟩ | ⟨s, q'', a, e'⟩ <;> rw [e'] <;> simp
  have hy₀p : ∀ {y : Tm}, WNF y → Lt p y → Lt (.Psi (approx pre .zero x₀) κ γ) y := fun hyF h =>
    lt_transY hfF Sp.hF hyF hlt h
  have hfrpre : ∀ w, w ∈ fr κ (ofSummands pre) → Lt w (.Psi (approx pre .zero x₀) κ γ) := fun w hw =>
    FWOrder.k2s hfF w (fr_oadd_of_left hpreF (wnf_nsum hx₀F WNF.zero) (fun s hd r' hs' e => by
      rw [summands_ofSummands _ (nfl_principal hpreN)] at hs'
      exact head_le_pre hN (wnf_nsum hx₀F WNF.zero) hyR s hd r' hs' e) hw)
  have hpR : p ∈ fr κ R := by
    rcases fr_cover hρ hpm with h | h | h
    · obtain ⟨s, hs', hp'⟩ := (mem_fr_iff hζF).mp h
      rw [hsum] at hs'
      rcases List.mem_append.mp hs' with h2 | h2
      · exfalso
        have h3 : p ∈ fr κ (ofSummands pre) := (mem_fr_iff hpreF).mpr
          ⟨s, by rw [summands_ofSummands _ (nfl_principal hpreN)]; exact h2, hp'⟩
        exact Lt.asymmY Sp.hF hfF (hfrpre p h3) hlt
      · rw [List.mem_singleton.mp h2] at hp'
        exact hp'
    · exact absurd (FWOrder.k2t hfF p h) (Lt.asymmY hfF Sp.hF hlt)
    · exact absurd (FWOrder.k2 hfF p h) (Lt.asymmY hfF Sp.hF hlt)
  have hpleR : Le p R := fr_leY hκF hRF hpR
  -- 種が最後の加数なら、その真の部分項は素の 0 番目未満
  have hS' : R = p → ∀ v, v ∈ subs p → v ≠ p → Lt v (.Psi ζ κ γ) →
      Lt v (.Psi (approx pre .zero x₀) κ γ) := by
    intro hRe v hv hne hl
    have hx₀R : Lt x₀ R := lt_of_le_of_ltY hx₀F (wnf_nsum hx₀F WNF.zero) hRF (le_nsum_left hx₀F WNF.zero) hyR
    have hx₀κ : Lt x₀ κ := lt_transY hx₀F hRF hκF hx₀R (by rw [hRe]; exact hpκ)
    have hzC := inC_of_fr_lt hz₀F hκF hfF hγF hγF hfF.psi.Cxi (Or.inr (lt_psi_targetY hfF)) (Or.inl rfl)
      fun w hw => FWOrder.k2s hfF w hw
    have hxC := (inC_approx_parts hN hx₀F WNF.zero hyR hzC).2.1
    have hxy := coll_psiY hfF x₀ hx₀F hxC hx₀κ
    have hG0 : ∀ u, u ∈ subs p → u ≠ p → Lt u p → Lt u (.Psi (approx pre .zero x₀) κ γ) :=
      fun u hu hne' hl' => by
        have hu' := hx₀g u (by rw [hRe]; exact hu) (by rw [hRe]; exact hne') (by rw [hRe]; exact hl')
        exact lt_transY (Sp.hF.of_mem_subs hu) hx₀F hfF hu' hxy
    have hvF := Sp.hF.of_mem_subs hv
    have hvκ : Lt v κ := lt_transY hvF hρ hκF hl hρκ
    have hsv := size_lt_of_mem_subs_ne hv hne
    have hsp := size_le_of_mem_subs (fr_spec hpm).1
    have hsz : v.size < (Tm.Psi ζ κ γ).size := by omega
    refine hull_lt hρ hfF (Or.inl rfl) hsz (fun n hn hnF hny f hf => ?_) (fun _ _ _ _ h' => h')
      (fun _ _ _ h' => h') (fun s hs hsζ hC => ?_) hvF hvκ (WFY.inC_of_ltY γ hvF hρ hl)
    · have hnp : n ∈ subs p := subs_trans hv hn
      have hnne : n ≠ p := ne_of_size_lt (Nat.lt_of_le_of_lt (size_le_of_mem_subs hn) hsv)
      have h1 : ¬ Lt n p := fun h' => hny (hG0 n hnp hnne h')
      have h2 : Lt p n := (le_of_not_ltY hnF Sp.hF h1).resolve_left (Ne.symm hnne)
      exact lt_of_le_of_ltY (hρ.of_mem_subs (fr_spec hf).1) Sp.hF hnF (hmax f hf) h2
    · have hs1 : s ∈ subs R := by
        rw [hRe]
        exact subs_trans hv (subs_trans hs (subs_psi_s (self_mem_subs s)))
      have hsne : s ≠ R := by
        rw [hRe]
        refine ne_of_size_lt ?_
        have h3 := size_le_of_mem_subs hs
        simp only [Tm.size] at h3
        omega
      have hS : R ∈ pre ++ [R] := List.mem_append_right _ (List.mem_singleton.mpr rfl)
      exact lt_same_arg (hvF.of_mem_subs hs) hfF
        (lt_approx_summand hN hx₀F WNF.zero hyR hx₀0 hx₀g hS hs1 hsne (by rw [← hζe]; exact hsζ)) hC
  unfold mTail
  cases hsp : splitGtD p (info ζ).sums with
  | some q =>
    obtain ⟨pre₂, R₂, r₂⟩ := q
    obtain ⟨L, rest, hys, hL, hpR₂, -, hhd⟩ := splitGtD_spec hsp
    have hpR' : Lt p R₂ := ltB_iff.mp hpR₂
    have hsum₂ : summands ζ = pre₂ ++ R₂ :: rest.map Prod.fst := by
      rw [← info_sums_fst, hys, List.map_append, hL, List.map_cons]
    have hrc : r₂ = (info R₂).seq := by
      have hm' : (R₂, r₂) ∈ (info ζ).sums := by
        rw [hys]
        simp
      exact coh_sums ζ (R₂, r₂) hm'
    subst hrc
    have hR₂1 : R₂ ≠ .one := by
      intro e
      rw [e] at hpR'
      exact hp0 (lt_oneY Sp.hF hpR')
    dsimp only
    rw [mkApp_idx (Or.inr hpR₂)]
    simp only
    have o := mahlo_out C hSμ hμs p pre₂ _ R₂ hsum₂ hR₂1 hpR' (fun _ => Sp) Sp.hF
    have hhd' : ∀ a l, rest.map Prod.fst = a :: l → ¬ Lt p a := by
      intro a l e h
      cases hr : rest with
      | nil =>
        rw [hr] at e
        cases e
      | cons q tl =>
        rw [hr] at e
        simp only [List.map_cons, List.cons.injEq] at e
        have := hhd q tl hr
        rw [e.1, ltB_iff.mpr h] at this
        cases this
    have hrs := rest_eq_seed hζF hsum hsum₂ Sp.hF hpleR hhd'
    have hN₂ : NFL (pre₂ ++ R₂ :: rest.map Prod.fst) := hsum₂ ▸ nfl_summands hζF
    have hζe₂ : ζ = ofSummands (pre₂ ++ R₂ :: rest.map Prod.fst) := by
      rw [← hsum₂, ofSummands_summands ζ hζF]
    refine o.inv fun y hy => ?_
    obtain ⟨P', x, hP', rfl, hyF, hxF, hyR', -, -, hPy, hx0, hxg⟩ := o.form y hy
    have hpy := hPy hp0
    have hP'F : WNF P' := by
      rcases hP' with rfl | rfl
      · exact Sp.hF
      · exact WNF.zero
    refine gp_floor ht (subs_psi_a (self_mem_subs γ)) hyF rfl (fun e => by cases e) fun v hv hne hl => ?_
    have hlow : ∀ (w n : Tm), WNF n → ¬ Lt n (.Psi (approx pre₂ P' x) κ γ) →
        ∀ f, f ∈ fr (.Psi ζ κ γ) (.Psi ζ κ γ) → Lt f n := fun _ n hnF hn f hf =>
      lt_of_le_of_ltY (hρ.of_mem_subs (fr_spec hf).1) Sp.hF hnF (hmax f hf)
        (lt_of_lt_of_leY Sp.hF hyF hnF hpy (le_of_not_ltY hnF hyF hn))
    have hvF := hρ.of_mem_subs hv
    have hvκ : Lt v κ := lt_transY hvF hρ hκF hl hρκ
    have hsz := size_lt_of_mem_subs_ne hv hne
    simp only [subs, List.mem_cons, List.mem_append] at hv
    rcases hv with e | (h | h) | h
    · exact absurd e hne
    · refine lt_of_summands_sub hζF hρ rfl (by intro e; cases e) (fun s hs' w hw hl' => ?_) h hl
      have hwF := (hζF.of_mem_subs (mem_subs_of_mem_summands hs')).of_mem_subs hw
      have hhull : s ∈ pre₂ ++ [R₂] → Lt w (.Psi (approx pre₂ P' x) κ γ) := by
        intro hmem
        have hsw : w.size < (Tm.Psi ζ κ γ).size := by
          have h1 := size_le_of_mem_subs (subs_trans (mem_subs_of_mem_summands hs') hw)
          simp only [Tm.size] at h1 ⊢
          omega
        refine hull_lt hρ hyF (Or.inl rfl) hsw (fun n _ hnF hn f hf => hlow w n hnF hn f hf)
          (fun _ _ _ _ h' => h') (fun _ _ _ h' => h') (fun s' hs2 hsζ hC => ?_) hwF
          (lt_transY hwF hρ hκF hl' hρκ) (WFY.inC_of_ltY γ hwF hρ hl')
        have hsne : s' ≠ s := by
          refine ne_of_size_lt ?_
          have h3 := size_le_of_mem_subs (subs_trans hw hs2)
          simp only [Tm.size] at h3
          omega
        exact lt_same_arg (hwF.of_mem_subs hs2) hyF
          (lt_approx_summand hN₂ hxF hP'F hyR' hx0 hxg hmem
            (subs_trans hw (subs_trans hs2 (subs_psi_s (self_mem_subs s')))) hsne
            (by rw [← hζe₂]; exact hsζ)) hC
      rw [hsum₂] at hs'
      rcases List.mem_append.mp hs' with hs1 | hs1
      · exact hhull (List.mem_append_left _ hs1)
      · rcases List.mem_cons.mp hs1 with e | hs2
        · exact hhull (by
            rw [e]
            exact List.mem_append_right _ (List.mem_singleton.mpr rfl))
        · obtain ⟨hRe, hall⟩ := hrs (fun e => by rw [e] at hs2; cases hs2)
          have e1 := hall s hs2
          subst e1
          by_cases hwp : w = s
          · rw [hwp]
            exact hpy
          · exact lt_transY hwF hfF hyF (hS' hRe w hw hwp hl') (hy₀p hyF hpy)
    · exact lt_of_mem_tgt hyF h hvκ
    · refine hull_lt hρ hyF (Or.inl rfl) hsz (fun n _ hnF hn f hf => hlow v n hnF hn f hf)
        (fun _ _ _ _ h' => h') (fun _ _ _ h' => h') (fun s hs _ _ => ?_) hvF hvκ (WFY.inC_of_ltY γ hvF hρ hl)
      exfalso
      have h1 := size_le_of_mem_subs (subs_trans h hs)
      simp only [Tm.size] at h1
      omega
  | none =>
    -- `ζ` の加数は全て `p` 以下：`ζ = p`
    have hhead : ∀ a l, summands ζ = a :: l → ¬ Lt p a := by
      intro a l e h
      have e' : (info ζ).sums.map Prod.fst = a :: l := by
        rw [info_sums_fst]
        exact e
      cases hxs : (info ζ).sums with
      | nil =>
        rw [hxs] at e'
        cases e'
      | cons q ys =>
        rw [hxs] at e' hsp
        simp only [List.map_cons, List.cons.injEq] at e'
        have h0' := splitGtD_none_head hsp
        rw [e'.1, ltB_iff.mpr h] at h0'
        cases h0'
    have hnil : pre = [] := by
      cases hpe : pre with
      | nil => rfl
      | cons a l =>
        exfalso
        subst hpe
        have haN := hN.1 a (List.mem_cons_self)
        have h3 : Le a p := le_of_not_ltY Sp.hF haN.1 (hhead a _ (by rw [hsum]; rfl))
        have h4 : Le R a := le_of_ne_gtY hRF haN.1 (le_of_nfl_append (rest := []) hN a List.mem_cons_self)
        have h5 : a = p := le_antisymmY haN.1 Sp.hF h3 (le_transY Sp.hF hRF haN.1 hpleR h4)
        have h6 : p ∈ fr κ (ofSummands (a :: l)) := (mem_fr_iff hpreF).mpr
          ⟨a, by rw [summands_ofSummands _ (nfl_principal hpreN)]; exact List.mem_cons_self, by
            rw [h5]
            exact Sp.self_fr hpκ⟩
        exact Lt.asymmY Sp.hF hfF (hfrpre p h6) hlt
    subst hnil
    have hRe : R = p := le_antisymmY hRF Sp.hF (le_of_not_ltY Sp.hF hRF (hhead R [] hsum)) hpleR
    have hζp : ζ = p := by
      rw [← hRe, hζe]
      rfl
    have hidx : idxOK κ p = true := by
      unfold idxOK
      rw [mOfT_tgt hP.tgt, ← hζp, ltB_iff.mpr hP.mlt, hP.mC]
      rfl
    have hS2 : ∀ v, v ∈ subs p → v ≠ p → Lt v (.Psi ζ κ γ) → Lt v p := fun v hv hne hl =>
      lt_transY (Sp.hF.of_mem_subs hv) hfF Sp.hF (hS' hRe v hv hne hl) hlt
    have hparts : ∀ (y : Tm), WNF y → isPrincipal y = true → Lt p y →
        (∀ v, v ∈ subs γ → v ≠ .Psi ζ κ γ → Lt v (.Psi ζ κ γ) → Lt v y) →
        (∀ v, v ∈ subs κ → v ≠ .Psi ζ κ γ → Lt v (.Psi ζ κ γ) → Lt v y) → Gp (.Psi .zero (.Psi ζ κ γ) (sc γ)) y := by
      intro y hyF hyp' hpy h1 h2
      refine gp_floor ht (subs_psi_a (self_mem_subs γ)) hyF hyp' (fun e => ?_) fun v hv hne hl => ?_
      · rw [e] at hpy
        exact hp0 (lt_oneY Sp.hF hpy)
      · simp only [subs, List.mem_cons, List.mem_append] at hv
        rcases hv with e | (h | h) | h
        · exact absurd e hne
        · rw [hζp] at h
          by_cases hvp : v = p
          · rw [hvp]
            exact hpy
          · exact lt_transY (Sp.hF.of_mem_subs h) Sp.hF hyF (hS2 v h hvp hl) hpy
        · exact h2 v h hne hl
        · exact h1 v h hne hl
    refine insert_specG C (mpar_chain ht hIH (hc.snoc rfl) hP.tgt) hSY Sp hyp ?_ (fun h => by rw [hidx] at h; cases h)
      (fun hn => ?_) (fun _ hs' hval => ?_)
      (fun h => by rw [hidx] at h; cases h)
    · rintro y hyF hyp' hpy ⟨ξ, A, rfl, hAγ, harg⟩
      refine hparts _ hyF hyp' hpy (fun v h hne hl => ?_) fun v h _ hl =>
        lt_of_mem_tgt hyF h (lt_transY (hκF.of_mem_subs h) hρ hκF hl hρκ)
      have hvF := hγF.of_mem_subs h
      have hsz : v.size < (Tm.Psi ζ κ γ).size := by
        have h1 := size_le_of_mem_subs h
        simp only [Tm.size] at h1 ⊢
        omega
      have hA' : ∀ a n, n ∈ subs v → a ∈ subs n → a ≠ n → isPrincipal n = true → n ≠ .one → Lt a γ → Lt a A := by
        intro a n hn ha hne' hnp hn1 hlt'
        obtain ⟨S, hSm, hnS⟩ := mem_subs_summand hnp (subs_trans h hn)
        have hSF := hγF.of_mem_subs (mem_subs_of_mem_summands hSm)
        have hne2 : a ≠ S := ne_of_size_lt (Nat.lt_of_lt_of_le (size_lt_of_mem_subs_ne ha hne')
          (size_le_of_mem_subs hnS))
        exact harg S hSm a (subs_trans hnS ha) hne2
          (lt_transY (hSF.of_mem_subs (subs_trans hnS ha)) hγF (succT_WNF hγF) hlt' (lt_succT γ))
      refine hull_lt hρ hyF hAγ hsz (fun n _ hnF hn f hf => ?_) (fun s k a hn hlt' => ?_)
        (fun m b hn hlt' => ?_) (fun s hs _ _ => ?_) hvF (lt_transY hvF hρ hκF hl hρκ)
        (WFY.inC_of_ltY γ hvF hρ hl)
      · exact lt_of_le_of_ltY (hρ.of_mem_subs (fr_spec hf).1) Sp.hF hnF (hmax f hf)
          (lt_of_lt_of_leY Sp.hF hyF hnF hpy (le_of_not_ltY hnF hyF hn))
      · exact hA' a _ hn (subs_psi_a (self_mem_subs a))
          (ne_of_size_lt (by simp only [Tm.size]; omega)) rfl (by intro e; cases e) hlt'
      · exact hA' b _ hn (subs_xi (self_mem_subs b))
          (ne_of_size_lt (by simp only [Tm.size]; omega)) rfl (by intro e; cases e) hlt'
      · exfalso
        have h1 := size_le_of_mem_subs (subs_trans h hs)
        simp only [Tm.size] at h1
        omega
    · -- `γ` の加数に `p` より大きいものがある
      exfalso
      have hγp : Le p γ := by
        rw [← hζp]
        exact le_of_ne_gtY hζF hγF hP.le
      cases hsγ : summands γ with
      | nil =>
        have e := eq_zero_of_summands_nil hsγ
        rw [e] at hγp
        rcases hγp with h | h
        · exact hp0 h
        · exact not_lt_zero _ h
      | cons a l =>
        have ham : a ∈ summands γ := by
          rw [hsγ]
          exact List.mem_cons_self
        have hm := (nfl_summands hγF).1 a ham
        have h1 : ¬ Lt p a := by
          intro h
          have e' : (info γ).sums.map Prod.fst = a :: l := by
            rw [info_sums_fst]
            exact hsγ
          cases hxs : (info γ).sums with
          | nil =>
            rw [hxs] at e'
            cases e'
          | cons q ys =>
            rw [hxs] at e' hn
            simp only [List.map_cons, List.cons.injEq] at e'
            have h0' := splitGtD_none_head hn
            rw [e'.1, ltB_iff.mpr h] at h0'
            cases h0'
        have h2 : Le p a := by
          rcases hγp with e | h
          · rw [← e, summands_principal Sp.prin] at hsγ
            simp only [List.cons.injEq] at hsγ
            exact Or.inl hsγ.1
          · exact le_head_of_prin_lt Sp.hF Sp.prin hγF hsγ h
        have h3 : a = p := le_antisymmY hm.1 Sp.hF (le_of_not_ltY Sp.hF hm.1 h1) h2
        have h4 : p ∈ fr κ γ := (mem_fr_iff hγF).mpr ⟨a, ham, by
          rw [h3]
          exact Sp.self_fr hpκ⟩
        exact Lt.asymmY Sp.hF hfF (FWOrder.k2 hfF p h4) hlt
    · -- 底の引数：`Dom`
      have hD : Dom (.Psi .zero (.Psi ζ κ γ) (sc γ)) p := by
        intro v hv hne hl y hyF hyp' hpy
        refine hparts y hyF hyp' hpy (fun v' h _ hl' => ?_) (fun v' h _ hl' => ?_) v hv hne hl
        · have hy0 : y ≠ .zero := fun e => by
            rw [e] at hyp'
            cases hyp'
          have hy1 : y ≠ .one := fun e => by
            rw [e] at hpy
            exact hp0 (lt_oneY Sp.hF hpy)
          cases hr : argR? κ with
          | none =>
            unfold validR at hval
            rw [hr] at hval
            cases hval
          | some r =>
            have hrγ : Lt r γ := arg_lt_of_psi hρ hr
            have hrF := wnf_of_argR hκF hr
            have hn : ¬ Lt r (pred γ) := fun h' => by
              unfold validR at hval
              rw [hr] at hval
              have h5 : ltB r (pred γ) = false := hval
              rw [ltB_iff.mpr h'] at h5
              cases h5
            have h3 : Le r (pred γ) := le_of_lt_succT hrF (wnf_pred hγF) (by
              rw [succT_pred hγF hs']
              exact hrγ)
            have h4 : r = pred γ := h3.resolve_right hn
            have e' : summands γ = summands r ++ [.one] := by
              rw [h4, ← summands_succT, succT_pred hγF hs']
            refine lt_of_summands_sub hγF hρ hyp' hy0 (fun s hs w hw hl2 => ?_) h hl'
            rw [e'] at hs
            rcases List.mem_append.mp hs with hs1 | hs1
            · have hwκ : w ∈ subs κ := subs_trans (mem_subs_arg hr)
                (subs_trans (mem_subs_of_mem_summands hs1) hw)
              have hwF := hκF.of_mem_subs hwκ
              exact lt_transY hwF hfF hyF (lt_of_mem_tgt hfF hwκ (lt_transY hwF hρ hκF hl2 hρκ))
                (hy₀p hyF hpy)
            · rw [List.mem_singleton.mp hs1] at hw
              simp only [subs, List.mem_singleton] at hw
              rw [hw]
              exact one_lt_of_prin hyF hyp' hy1
        · have hv'F := hκF.of_mem_subs h
          exact lt_transY hv'F hfF hyF (lt_of_mem_tgt hfF h (lt_transY hv'F hρ hκF hl' hρκ)) (hy₀p hyF hpy)
      exact fam_rec ht hIH κ (hc.snoc rfl) (tgt_not_om hρ hζ0) p γ Sp hD C.hw0 hyp

/-- 目標 `Ψ^ζ_κ(γ)` の底 -/
theorem floor_psi {ζ κ γ : Tm} (ht : WNF (.Psi .zero (.Psi ζ κ γ) (sc γ)))
    (hIH : ∀ u, u ∈ subs (.Psi .zero (.Psi ζ κ γ) (sc γ)) → u ≠ .Psi .zero (.Psi ζ κ γ) (sc γ) →
      SeqI u (info u).seq) :
    SeqI (.Psi .zero (.Psi ζ κ γ) (sc γ))
      (famSeq (info (.Psi ζ κ γ)).fam (.Psi ζ κ γ) (maxL (frB (.Psi ζ κ γ) (.Psi ζ κ γ)))) := by
  have hρ := ht.psi.piF
  have hP := hρ.psi
  have hκF := hP.piF
  have hγF := hP.aF
  have hζF := hP.xiF
  have hζ0 : ζ ≠ .zero := by
    rcases ht.psi.tgt with ⟨c, e, -⟩ | ⟨n, p', e⟩ | ⟨ζ', κ', b, e, h⟩
    · cases e
    · cases e
    · cases e
      exact h
  have hc : Chain (.Psi ζ κ γ) (.Psi ζ κ γ) := .refl _
  have C := mctx_chain (X := sc γ) ht hc
  have M := mpar_chain ht hIH (hc.snoc rfl) hP.tgt
  obtain ⟨hSY, hSμ, hμs⟩ := psi_parts hIH hc
  have hfam : ∀ p', SeedP (.Psi ζ κ γ) (sc γ) p' → Dom (.Psi .zero (.Psi ζ κ γ) (sc γ)) p' →
      Le (.Psi .zero κ γ) p' →
      SeqI (.Psi .zero (.Psi ζ κ γ) (sc γ)) (famSeq (info κ).fam (.Psi ζ κ γ) (some p')) :=
    fun p' S' D' hle' => fam_rec ht hIH κ (hc.snoc rfl) (tgt_not_om hρ hζ0) p' γ S' D' C.hw0 hle'
  have e : (info (.Psi ζ κ γ)).fam = .psi ζ (info ζ).sums κ (info κ).fam γ (info γ).sums := rfl
  rw [e, famSeq]
  have hr : γ ∈ subs (.Psi ζ κ γ) := subs_psi_a (self_mem_subs γ)
  have hGL : ∀ z, WNF (.Psi z κ γ) →
      (∀ v, v ∈ subs (.Psi ζ κ γ) → v ≠ .Psi ζ κ γ → Lt v (.Psi ζ κ γ) → Lt v (.Psi z κ γ)) →
      ∀ y, WNF y → isPrincipal y = true → Le (.Psi z κ γ) y →
        Gp (.Psi .zero (.Psi ζ κ γ) (sc γ)) y := fun z hy₀ hl y hyF hyp hle =>
    gp_floor ht hr hyF hyp (fun e' => by
      rw [e'] at hle
      exact not_lt_of_leY hy₀ WNF.one hle (one_lt_of_prin hy₀ rfl (by intro e''; cases e'')))
      fun v hv hne hl' => lt_of_lt_of_leY (hρ.of_mem_subs hv) hy₀ hyF (hl v hv hne hl') hle
  by_cases h1 : ζ = .one
  · have hc' : mcanon (.Psi ζ κ γ) κ γ ζ = .Psi .zero κ γ := by
      unfold mcanon
      rw [ite_eq_left h1]
    have hw0 := C.hw0
    have hF : ∀ f, f ∈ fr (.Psi ζ κ γ) (.Psi ζ κ γ) → Lt f (.Psi .zero κ γ) := fun f hf => by
      rcases fr_cover hρ hf with h | h | h
      · rw [h1] at h
        simp [fr] at h
      · exact FWOrder.k2t hw0 f h
      · exact FWOrder.k2 hw0 f h
    have hI : ∀ s, Tm.Psi s κ γ ∈ subs ζ → Lt s ζ → Lt s .zero := fun s h _ => by
      rw [h1] at h
      simp [subs] at h
    have hl := floor_low hρ hw0 hF hI
    refine mahlo_spec C M hζ0 hSY hSμ hμs (fun p hm => (maxL_frt ht hm).1) (fun _ _ _ h' => absurd h1 h')
      (fun y hyF hyp _ hle _ => ?_) hfam (fun _ _ _ h' => absurd h1 h')
    rw [hc'] at hle
    exact hGL _ hw0 hl y hyF hyp hle
  by_cases hs : isSucc ζ = true
  · have hc' : mcanon (.Psi ζ κ γ) κ γ ζ = .Psi (pred ζ) κ γ := by
      unfold mcanon
      rw [ite_eq_right h1, ite_eq_left hs]
    have hpμ : Lt (pred ζ) ζ := pred_lt hζF hs
    have hpF := wnf_pred hζF
    have hy₁ : WNF (.Psi (pred ζ) κ γ) := C.nfI hpF hpμ h1 (inC_pred_of hζF C.hμ1) (inC_pred_of hζF C.hμ2)
    have hF : ∀ f, f ∈ fr (.Psi ζ κ γ) (.Psi ζ κ γ) → Lt f (.Psi (pred ζ) κ γ) := fun f hf => by
      rcases fr_cover hρ hf with h | h | h
      · have e' : fr κ ζ = fr κ (pred ζ) := by
          have := fr_succT κ (pred ζ)
          rwa [succT_pred hζF hs] at this
        rw [e'] at h
        exact FWOrder.k2s hy₁ f h
      · exact FWOrder.k2t hy₁ f h
      · exact FWOrder.k2 hy₁ f h
    have hI : ∀ s, Tm.Psi s κ γ ∈ subs ζ → Lt s ζ → Lt s (pred ζ) := fun s hn hsζ => by
      have hn' := node_mem_subs_pred hζF hs rfl (by intro e; cases e) hn
      have hsF := hpF.of_mem_subs (subs_trans hn' (subs_psi_s (self_mem_subs s)))
      rcases le_of_lt_succT hsF hpF (by rw [succT_pred hζF hs]; exact hsζ) with e' | e'
      · exfalso
        have e1 := size_le_of_mem_subs hn'
        rw [← e'] at e1
        simp only [Tm.size] at e1
        omega
      · exact e'
    have hl := floor_low hρ hy₁ hF hI
    refine mahlo_spec C M hζ0 hSY hSμ hμs (fun p hm => (maxL_frt ht hm).1) (fun _ _ h' _ => absurd hs h')
      (fun y hyF hyp _ hle _ => ?_) hfam (fun _ _ h' _ => absurd hs h')
    rw [hc'] at hle
    exact hGL _ hy₁ hl y hyF hyp hle
  -- 極限
  obtain ⟨pre, R, hsum, hR1, -, -, -, o0⟩ := s0_out C hSμ hμs hζ0 hs
  obtain ⟨P₀, x₀, hP₀, hz₀, hfF, hx₀F, hyR, hz₀μ, -, -, hx₀0, hx₀g⟩ := o0.form _ o0.mem
  have e0 : P₀ = .zero := by
    rcases hP₀ with h | h <;> exact h
  subst e0
  have hc' : mcanon (.Psi ζ κ γ) κ γ ζ = (s0Of (.Psi ζ κ γ) κ γ ζ).first := by
    unfold mcanon
    rw [ite_eq_right h1, ite_eq_right hs]
  have hN : NFL (pre ++ R :: []) := hsum ▸ nfl_summands hζF
  have hζe : ζ = ofSummands (pre ++ R :: []) := by rw [← hsum, ofSummands_summands ζ hζF]
  have hI : ∀ s, Tm.Psi s κ γ ∈ subs ζ → Lt s ζ → Lt s (approx pre .zero x₀) := fun s hn hsζ => by
    obtain ⟨S, hSm, hnS⟩ := mem_subs_summand rfl hn
    rw [hsum] at hSm
    have hsne : s ≠ S := by
      refine ne_of_size_lt ?_
      have h3 := size_le_of_mem_subs hnS
      simp only [Tm.size] at h3
      omega
    exact lt_approx_summand hN hx₀F WNF.zero hyR hx₀0 hx₀g hSm
      (subs_trans hnS (subs_psi_s (self_mem_subs s))) hsne (by rw [← hζe]; exact hsζ)
  have hnefirst : ∀ p, p ∈ fr (.Psi ζ κ γ) (.Psi ζ κ γ) → (s0Of (.Psi ζ κ γ) κ γ ζ).first ≠ p := by
    intro p hp e'
    rw [hz₀] at e'
    subst e'
    have hps := (fr_spec hp).1
    have hsz := size_lt_of_mem_subs_ne hps (fr_spec hp).2.ne
    simp only [subs, List.mem_cons, List.mem_append] at hps
    rcases hps with e' | (h | h) | h
    · exact (fr_spec hp).2.ne e'
    · exact Lt.irrefl _ (hI _ h hz₀μ)
    · have h3 := size_le_of_mem_subs h
      simp only [Tm.size] at h3
      omega
    · have h3 := size_le_of_mem_subs h
      simp only [Tm.size] at h3
      omega
  by_cases hE : ∃ p, maxL (frB (.Psi ζ κ γ) (.Psi ζ κ γ)) = some p ∧ Lt (s0Of (.Psi ζ κ γ) κ γ ζ).first p
  · obtain ⟨p, hm, hlt⟩ := hE
    refine mahlo_spec C M hζ0 hSY hSμ hμs (fun p' hm' => (maxL_frt ht hm').1)
      (fun p' hm' _ _ _ e' => hnefirst p' (maxL_frt ht hm').2.1 e') (fun y hyF hyp _ hle hq => ?_) hfam
      (fun p' hm' _ _ hlt' hyp' => ?_)
    · exfalso
      rcases hq with h | h | h
      · exact h1 h
      · exact hs h
      · exact h p hm (by rw [hc']; exact hlt)
    · obtain ⟨S', hpm, hmax⟩ := maxL_frt ht hm'
      exact tail_floor ht hIH hζ0 hs S' hpm hmax hlt' hyp'
  · have hfF' := hfF
    rw [hz₀] at hfF'
    have hF : ∀ f, f ∈ fr (.Psi ζ κ γ) (.Psi ζ κ γ) → Lt f (.Psi (approx pre .zero x₀) κ γ) := by
      intro f hf
      rw [← hz₀]
      cases hm : maxL (frB (.Psi ζ κ γ) (.Psi ζ κ γ)) with
      | none =>
        have h3 := maxL_none hm
        rw [frB_eq_fr] at h3
        rw [h3] at hf
        cases hf
      | some p =>
        obtain ⟨S', hpm, hmax⟩ := maxL_frt ht hm
        have hpf : Lt p (s0Of (.Psi ζ κ γ) κ γ ζ).first := by
          rcases triY S'.hF hfF with h | h | h
          · exact h
          · exact absurd h.symm (hnefirst p hpm)
          · exact absurd ⟨p, hm, h⟩ hE
        exact lt_of_le_of_ltY (hρ.of_mem_subs (fr_spec hf).1) S'.hF hfF (hmax f hf) hpf
    have hl := floor_low hρ hfF' hF hI
    refine mahlo_spec C M hζ0 hSY hSμ hμs (fun p' hm' => (maxL_frt ht hm').1)
      (fun p' hm' _ _ _ e' => hnefirst p' (maxL_frt ht hm').2.1 e') (fun y hyF hyp _ hle _ => ?_) hfam
      (fun p' hm' _ _ hlt' _ => absurd ⟨p', hm', hlt'⟩ hE)
    rw [hc', hz₀] at hle
    exact hGL _ hfF' hl y hyF hyp hle

/-! ### `Ξ_m(q)` の底 -/

/-- 前線の元が全て `y` 未満で、引数の条件があれば、`ρ = Ξ_m(q)` の真の部分項は `y` 未満 -/
theorem floor_lowx {m : Nat} {q A : Tm} (hρ : WNF (.Xi m q)) (hy : WNF (.Xi m A))
    (hF : ∀ f, f ∈ fr (.Xi m q) (.Xi m q) → Lt f (.Xi m A))
    (hc1 : ∀ s k a, Tm.Psi s k a ∈ subs q → Lt a q → Lt a A)
    (hc1x : ∀ m' b, Tm.Xi m' b ∈ subs q → Lt b q → Lt b A) :
    ∀ v, v ∈ subs (.Xi m q) → v ≠ .Xi m q → Lt v (.Xi m q) → Lt v (.Xi m A) := by
  intro v hv hne hl
  have hn := hρ.xi.1
  have hK := WNF.K' hn
  have hvF := hρ.of_mem_subs hv
  have hvK : Lt v (.K m) := lt_transY hvF hρ hK hl ((lt_K_iffY hρ hn).mpr (Nat.le_refl _))
  have hsz := size_lt_of_mem_subs_ne hv hne
  simp only [subs, List.mem_cons] at hv
  rcases hv with e | h
  · exact absurd e hne
  · exact hull_ltx hρ hy hsz (fun n _ hnF hn' f hf => lt_of_lt_of_leY (hρ.of_mem_subs (fr_spec hf).1) hy hnF
      (hF f hf) (le_of_not_ltY hnF hy hn')) (fun s k a hz hlt => hc1 s k a (subs_trans h hz) hlt)
      (fun m' b hz hlt => hc1x m' b (subs_trans h hz) hlt) hvF hvK (WFY.inC_of_ltY q hvF hρ hl)

/-- `Ξ_m` の添字が極限のときの最初の列 -/
theorem s0x_out {π X q : Tm} {m : Nat} (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Xi m q))
    (hS : ∀ u, u ∈ summands q → u ≠ .one → SeqI u (info u).seq)
    (hqs : ∀ u, u ∈ summands q → u ≠ .one → u ∈ subs (.Psi .zero π X) ∧ u.size < π.size)
    (hqσ : ∀ σ, WNF σ → Le π σ → inC q q σ = true) (hq0 : q ≠ .zero) (hs : ¬ isSucc q = true) :
    ∃ pre R, summands q = pre ++ [R] ∧ R ≠ .one ∧ preT (info q).sums = pre ∧ lastT (info q).sums = R ∧
      s0X π m q = .app π (.xi m) pre R (info R).seq .zero .one ∧
      XiOut π X m q .zero .one pre R (s0X π m q) := by
  have hρ : WNF (.Xi m q) := hc.wnf ht.psi.piF
  have hqF := hρ.xi.2.1
  have hsum := summands_pre_last hq0
  have hlast : lastS (info q).sums = (info (lastT (info q).sums)).seq := lastS_coh (coh_sums q)
  obtain ⟨pre, hpr⟩ : ∃ pre, pre = preT (info q).sums := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = lastT (info q).sums := ⟨_, rfl⟩
  rw [← hpr, ← hR] at hsum
  rw [← hR] at hlast
  have hRm : R ∈ summands q := by
    rw [hsum]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hR1 : R ≠ .one := by
    intro e
    apply hs
    show (summands q).getLast? == some one
    rw [hsum, e]
    simp
  have hRp := nfl_principal (nfl_summands hqF) R hRm
  have hR0 : R ≠ .zero := by
    intro e
    rw [e] at hRp
    cases hRp
  have hs0 : s0X π m q = .app π (.xi m) pre R (info R).seq .zero .one := by
    unfold s0X
    rw [← hpr, ← hR, hlast]
  have o0 := vk_out ht hc hS hqs hqσ .zero .one pre [] R hsum hR1 (zero_lt hR0) (fun h => absurd rfl h) WNF.zero
    (Or.inr rfl) (fun e => by cases e)
  rw [← hs0] at o0
  exact ⟨pre, R, hsum, hR1, hpr.symm, hR.symm, hs0, o0⟩

/-- 底の例外（`Ξ_m(q)`） -/
theorem vtail_floor {m : Nat} {q p : Tm} (ht : WNF (.Psi .zero (.Xi m q) (sc q)))
    (hS : ∀ u, u ∈ summands q → u ≠ .one → SeqI u (info u).seq)
    (hqs : ∀ u, u ∈ summands q → u ≠ .one → u ∈ subs (.Psi .zero (.Xi m q) (sc q)) ∧ u.size < (Tm.Xi m q).size)
    (hqσ : ∀ σ, WNF σ → Le (.Xi m q) σ → inC q q σ = true)
    (hs : ¬ isSucc q = true)
    (Sp : SeedP (.Xi m q) (sc q) p) (hpm : p ∈ fr (.Xi m q) (.Xi m q))
    (hmax : ∀ f, f ∈ fr (.Xi m q) (.Xi m q) → Le f p)
    (hlt : Lt (s0X (.Xi m q) m q).first p) :
    SeqI (.Psi .zero (.Xi m q) (sc q)) (vTail (.Xi m q) m q p) := by
  have hρ := ht.psi.piF
  have hm := hρ.xi.1
  have hqF := hρ.xi.2.1
  have hq0 := hρ.xi.2.2.1
  have hKF : WNF (.K m) := WNF.K' hm
  have hρK : Lt (.Xi m q) (.K m) := (lt_K_iffY hρ hm).mpr (Nat.le_refl _)
  have hc : Chain (.Xi m q) (.Xi m q) := .refl _
  have hr : q ∈ subs (.Xi m q) := subs_xi (self_mem_subs q)
  obtain ⟨pre, R, hsum, hR1, -, -, -, o0⟩ := s0x_out ht hc hS hqs hqσ hq0 hs
  obtain ⟨P₀, x₀, hP₀, hz₀, hfF, hx₀F, hx₀R, hz₀q, -, -, hx₀0, hx₀g⟩ := o0.form _ o0.mem
  have e0 : P₀ = .zero := by
    rcases hP₀ with h | h <;> exact h
  subst e0
  rw [hz₀] at hlt hfF
  have hRm : R ∈ summands q := by
    rw [hsum]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hRp := nfl_principal (nfl_summands hqF) R hRm
  have hR0 : R ≠ .zero := by
    intro e
    rw [e] at hRp
    cases hRp
  have G : XiG m q .zero .one pre [] R :=
    ⟨hρ, hsum, WNF.zero, zero_lt hR0, zero_lt (by intro e; cases e), Or.inr rfl, hR1⟩
  have hRF := G.hRF
  have hN := G.hN
  have hpreF := G.hpreF
  have hpreN := nfl_append_left hN
  have hp0 : p ≠ .zero := by
    rcases Sp.hn with ⟨m', a, e'⟩ | ⟨s, q'', a, e'⟩ <;> rw [e'] <;> simp
  have hpK : Lt p (.K m) := lt_transY Sp.hF hρ hKF (fr_spec hpm).2 hρK
  have hy₀p : ∀ {y : Tm}, WNF y → Lt p y → Lt (.Xi m (xA .one pre .zero x₀)) y := fun hyF h =>
    lt_transY hfF Sp.hF hyF hlt h
  have hfrpre : ∀ w, w ∈ fr (.K m) (ofSummands pre) → Lt w (.Xi m (xA .one pre .zero x₀)) := fun w hw =>
    FWOrder.k2x hfF w (fr_oadd_of_left hpreF (G.hEF hx₀F) (fun s hd r' hs' e => by
      rw [summands_ofSummands _ (nfl_principal hpreN)] at hs'
      exact head_le_pre hN (G.hEF hx₀F) (G.hER hx₀F hx₀R) s hd r' hs' e) hw)
  have hpR : p ∈ fr (.K m) R := by
    obtain ⟨s, hs', hp'⟩ := (mem_fr_iff hqF).mp (fr_cover_xi hρ hpm)
    rw [hsum] at hs'
    rcases List.mem_append.mp hs' with h2 | h2
    · exfalso
      have h3 : p ∈ fr (.K m) (ofSummands pre) := (mem_fr_iff hpreF).mpr
        ⟨s, by rw [summands_ofSummands _ (nfl_principal hpreN)]; exact h2, hp'⟩
      exact Lt.asymmY Sp.hF hfF (hfrpre p h3) hlt
    · rw [List.mem_singleton.mp h2] at hp'
      exact hp'
  have hpleR : Le p R := fr_leY hKF hRF hpR
  have hS' : R = p → ∀ v, v ∈ subs p → v ≠ p → Lt v (.Xi m q) → Lt v (.Xi m (xA .one pre .zero x₀)) := by
    intro hRe v hv hne hl
    have hx₀K : Lt x₀ (.K m) := lt_transY hx₀F hRF hKF hx₀R (by rw [hRe]; exact hpK)
    have hAF := G.hAF hx₀F
    have hyK : Lt (.Xi m (xA .one pre .zero x₀)) (.K m) := (lt_K_iffY hfF hm).mpr (Nat.le_refl _)
    have hAC : inC (xA .one pre .zero x₀) (xA .one pre .zero x₀) (.Xi m (xA .one pre .zero x₀)) = true :=
      inC_of_fr_lt hAF hKF hfF hAF hAF hfF.xi.2.2.2.2 (Or.inr hyK) (Or.inl rfl)
        fun w hw => FWOrder.k2x hfF w hw
    have hxy := coll_xi0 hfF x₀ hx₀F (G.parts hx₀F hx₀R hAC).2.1 hx₀K
    have hG0 : ∀ u, u ∈ subs p → u ≠ p → Lt u p → Lt u (.Xi m (xA .one pre .zero x₀)) :=
      fun u hu hne' hl' => by
        have hu' := hx₀g u (by rw [hRe]; exact hu) (by rw [hRe]; exact hne') (by rw [hRe]; exact hl')
        exact lt_transY (Sp.hF.of_mem_subs hu) hx₀F hfF hu' hxy
    have hvF := Sp.hF.of_mem_subs hv
    have hvK : Lt v (.K m) := lt_transY hvF hρ hKF hl hρK
    have hsv := size_lt_of_mem_subs_ne hv hne
    have hsp := size_le_of_mem_subs (fr_spec hpm).1
    have hsz : v.size < (Tm.Xi m q).size := by omega
    have hmem : R ∈ pre ++ [R] := List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have hsubR : ∀ {u n : Tm}, n ∈ subs v → u ∈ subs n → u ∈ subs R := fun hn hu => by
      rw [hRe]
      exact subs_trans hv (subs_trans hn hu)
    have hneR : ∀ {u n : Tm}, n ∈ subs v → u.size < n.size → u ≠ R := fun hn hu => by
      rw [hRe]
      exact ne_of_size_lt (by
        have := size_le_of_mem_subs hn
        omega)
    refine hull_ltx hρ hfF hsz (fun n hn hnF hny f hf => ?_) (fun s k a hn hlt' => ?_)
      (fun m' b hn hlt' => ?_) hvF hvK (WFY.inC_of_ltY q hvF hρ hl)
    · have hnp : n ∈ subs p := subs_trans hv hn
      have hnne : n ≠ p := ne_of_size_lt (Nat.lt_of_le_of_lt (size_le_of_mem_subs hn) hsv)
      have h1 : ¬ Lt n p := fun h' => hny (hG0 n hnp hnne h')
      have h2 : Lt p n := (le_of_not_ltY hnF Sp.hF h1).resolve_left (Ne.symm hnne)
      exact lt_of_le_of_ltY (hρ.of_mem_subs (fr_spec hf).1) Sp.hF hnF (hmax f hf) h2
    · exact G.lt_xA hx₀F hx₀R hx₀0 hx₀g hmem (hsubR hn (subs_psi_a (self_mem_subs a)))
        (hneR hn (by simp only [Tm.size]; omega)) hlt'
    · exact G.lt_xA hx₀F hx₀R hx₀0 hx₀g hmem (hsubR hn (subs_xi (self_mem_subs b)))
        (hneR hn (by simp only [Tm.size]; omega)) hlt'
  unfold vTail
  cases hsp : splitGtD p (info q).sums with
  | some q' =>
    obtain ⟨pre₂, R₂, r₂⟩ := q'
    obtain ⟨L, rest, hys, hL, hpR₂, -, hhd⟩ := splitGtD_spec hsp
    have hpR' : Lt p R₂ := ltB_iff.mp hpR₂
    have hsum₂ : summands q = pre₂ ++ R₂ :: rest.map Prod.fst := by
      rw [← info_sums_fst, hys, List.map_append, hL, List.map_cons]
    have hrc : r₂ = (info R₂).seq := by
      have hm' : (R₂, r₂) ∈ (info q).sums := by
        rw [hys]
        simp
      exact coh_sums q (R₂, r₂) hm'
    subst hrc
    have hR₂1 : R₂ ≠ .one := by
      intro e
      rw [e] at hpR'
      exact hp0 (lt_oneY Sp.hF hpR')
    dsimp only
    rw [mkApp_xi (Or.inr hpR₂)]
    simp only
    have o := vk_out ht hc hS hqs hqσ p .zero pre₂ _ R₂ hsum₂ hR₂1 hpR' (fun _ => Sp) Sp.hF (Or.inl rfl)
      fun _ => hp0
    have hhd' : ∀ a l, rest.map Prod.fst = a :: l → ¬ Lt p a := by
      intro a l e h
      cases hr' : rest with
      | nil =>
        rw [hr'] at e
        cases e
      | cons q' tl =>
        rw [hr'] at e
        simp only [List.map_cons, List.cons.injEq] at e
        have := hhd q' tl hr'
        rw [e.1, ltB_iff.mpr h] at this
        cases this
    have hrs := rest_eq_seed hqF hsum hsum₂ Sp.hF hpleR hhd'
    have hN₂ : NFL (pre₂ ++ R₂ :: rest.map Prod.fst) := hsum₂ ▸ nfl_summands hqF
    refine o.inv fun y hy => ?_
    obtain ⟨P', x, hP', rfl, hyF, hxF, hxR, -, -, hPy, hx0, hxg⟩ := o.form y hy
    have hpy := hPy hp0
    have hP'F : WNF P' := by
      rcases hP' with rfl | rfl
      · exact Sp.hF
      · exact WNF.zero
    have hPR : Lt P' R₂ := by
      rcases hP' with rfl | rfl
      · exact hpR'
      · exact zero_lt fun e => not_lt_zero _ (e ▸ hpR')
    have hPK : Lt P' (.K m) := by
      rcases hP' with rfl | rfl
      · exact hpK
      · exact zero_lt (by intro e; cases e)
    have G₂ : XiG m q P' .zero pre₂ (rest.map Prod.fst) R₂ := ⟨hρ, hsum₂, hP'F, hPR, hPK, Or.inl rfl, hR₂1⟩
    refine gp_floor ht hr hyF rfl (fun e => by cases e) fun v hv hne hl => ?_
    have hlow : ∀ n : Tm, WNF n → ¬ Lt n (.Xi m (xA .zero pre₂ P' x)) →
        ∀ f, f ∈ fr (.Xi m q) (.Xi m q) → Lt f n := fun n hnF hn f hf =>
      lt_of_le_of_ltY (hρ.of_mem_subs (fr_spec hf).1) Sp.hF hnF (hmax f hf)
        (lt_of_lt_of_leY Sp.hF hyF hnF hpy (le_of_not_ltY hnF hyF hn))
    simp only [subs, List.mem_cons] at hv
    rcases hv with e | h
    · exact absurd e hne
    refine lt_of_summands_sub hqF hρ rfl (by intro e; cases e) (fun s hs' w hw hl' => ?_) h hl
    have hwF := (hqF.of_mem_subs (mem_subs_of_mem_summands hs')).of_mem_subs hw
    have hhull : s ∈ pre₂ ++ [R₂] → Lt w (.Xi m (xA .zero pre₂ P' x)) := by
      intro hmem
      have hsw : w.size < (Tm.Xi m q).size := by
        have h1 := size_le_of_mem_subs (subs_trans (mem_subs_of_mem_summands hs') hw)
        simp only [Tm.size] at h1 ⊢
        omega
      have hsiz : ∀ {u n : Tm}, n ∈ subs w → u.size < n.size → u ≠ s := fun hn hu =>
        ne_of_size_lt (by
          have h1 := size_le_of_mem_subs (subs_trans hw hn)
          omega)
      refine hull_ltx hρ hyF hsw (fun n _ hnF hn f hf => hlow n hnF hn f hf) (fun s' k a hn hlt' => ?_)
        (fun m' b hn hlt' => ?_) hwF (lt_transY hwF hρ hKF hl' hρK) (WFY.inC_of_ltY q hwF hρ hl')
      · exact G₂.lt_xA hxF hxR hx0 hxg hmem (subs_trans hw (subs_trans hn (subs_psi_a (self_mem_subs a))))
          (hsiz hn (by simp only [Tm.size]; omega)) hlt'
      · exact G₂.lt_xA hxF hxR hx0 hxg hmem (subs_trans hw (subs_trans hn (subs_xi (self_mem_subs b))))
          (hsiz hn (by simp only [Tm.size]; omega)) hlt'
    rw [hsum₂] at hs'
    rcases List.mem_append.mp hs' with hs1 | hs1
    · exact hhull (List.mem_append_left _ hs1)
    · rcases List.mem_cons.mp hs1 with e | hs2
      · exact hhull (by
          rw [e]
          exact List.mem_append_right _ (List.mem_singleton.mpr rfl))
      · obtain ⟨hRe, hall⟩ := hrs (fun e => by rw [e] at hs2; cases hs2)
        have e1 := hall s hs2
        subst e1
        by_cases hwp : w = s
        · rw [hwp]
          exact hpy
        · exact lt_transY hwF hfF hyF (hS' hRe w hw hwp hl') (hy₀p hyF hpy)
  | none =>
    -- `q` の加数は全て `p` 以下：`q = p`
    have hhead : ∀ a l, summands q = a :: l → ¬ Lt p a := by
      intro a l e h
      have e' : (info q).sums.map Prod.fst = a :: l := by
        rw [info_sums_fst]
        exact e
      cases hxs : (info q).sums with
      | nil =>
        rw [hxs] at e'
        cases e'
      | cons q' ys =>
        rw [hxs] at e' hsp
        simp only [List.map_cons, List.cons.injEq] at e'
        have h0' := splitGtD_none_head hsp
        rw [e'.1, ltB_iff.mpr h] at h0'
        cases h0'
    have hnil : pre = [] := by
      cases hpe : pre with
      | nil => rfl
      | cons a l =>
        exfalso
        subst hpe
        have haN := hN.1 a (List.mem_cons_self)
        have h3 : Le a p := le_of_not_ltY Sp.hF haN.1 (hhead a _ (by rw [hsum]; rfl))
        have h4 : Le R a := le_of_ne_gtY hRF haN.1 (le_of_nfl_append (rest := []) hN a List.mem_cons_self)
        have h5 : a = p := le_antisymmY haN.1 Sp.hF h3 (le_transY Sp.hF hRF haN.1 hpleR h4)
        have h6 : p ∈ fr (.K m) (ofSummands (a :: l)) := (mem_fr_iff hpreF).mpr
          ⟨a, by rw [summands_ofSummands _ (nfl_principal hpreN)]; exact List.mem_cons_self, by
            rw [h5]
            exact Sp.self_fr hpK⟩
        exact Lt.asymmY Sp.hF hfF (hfrpre p h6) hlt
    subst hnil
    have hRe : R = p := le_antisymmY hRF Sp.hF (le_of_not_ltY Sp.hF hRF (hhead R [] hsum)) hpleR
    have hqp : q = p := by
      rw [← hRe, G.hqe]
      rfl
    have hS2 : ∀ v, v ∈ subs p → v ≠ p → Lt v (.Xi m q) → Lt v p := fun v hv hne hl =>
      lt_transY (Sp.hF.of_mem_subs hv) hfF Sp.hF (hS' hRe v hv hne hl) hlt
    refine tower_seq ht (chain_not_om hc) Sp.hF Sp.hlt Sp.hC fun y hyF hyp hy1 hpy => ?_
    refine gp_floor ht hr hyF hyp hy1 fun v hv hne hl => ?_
    simp only [subs, List.mem_cons] at hv
    rcases hv with e | h
    · exact absurd e hne
    rw [hqp] at h
    by_cases hvp : v = p
    · rw [hvp]
      exact hpy
    · exact lt_transY (Sp.hF.of_mem_subs h) Sp.hF hyF (hS2 v h hvp hl) hpy

/-- 目標 `Ξ_m(q)` の底 -/
theorem floor_xi {m : Nat} {q : Tm} (ht : WNF (.Psi .zero (.Xi m q) (sc q)))
    (hIH : ∀ u, u ∈ subs (.Psi .zero (.Xi m q) (sc q)) → u ≠ .Psi .zero (.Xi m q) (sc q) →
      SeqI u (info u).seq) :
    SeqI (.Psi .zero (.Xi m q) (sc q))
      (famSeq (info (.Xi m q)).fam (.Xi m q) (maxL (frB (.Xi m q) (.Xi m q)))) := by
  have hρ := ht.psi.piF
  have hm := hρ.xi.1
  have hqF := hρ.xi.2.1
  have hq0 := hρ.xi.2.2.1
  have hc : Chain (.Xi m q) (.Xi m q) := .refl _
  obtain ⟨hS, hqs, hqσ⟩ := xi_parts ht hIH hc
  have e : (info (.Xi m q)).fam = .xi m q (info q).sums := rfl
  rw [e, famSeq]
  have hr : q ∈ subs (.Xi m q) := subs_xi (self_mem_subs q)
  have hGL : ∀ z, WNF (.Xi m z) →
      (∀ v, v ∈ subs (.Xi m q) → v ≠ .Xi m q → Lt v (.Xi m q) → Lt v (.Xi m z)) →
      ∀ y, WNF y → isPrincipal y = true → y ≠ .one → Le (.Xi m z) y →
        Gp (.Psi .zero (.Xi m q) (sc q)) y := fun z hy₀ hl y hyF hyp hy1 hle =>
    gp_floor ht hr hyF hyp hy1 fun v hv hne hl' =>
      lt_of_lt_of_leY (hρ.of_mem_subs hv) hy₀ hyF (hl v hv hne hl') hle
  by_cases h1 : q = .one
  · refine vk_spec ht hc hS hqs hqσ (fun p hm' => (maxL_frt ht hm').1) (fun _ _ _ h' => absurd h1 h')
      (fun y hyF hyp hy1 _ _ _ => ?_) (fun _ _ _ h' => absurd h1 h')
    refine gp_floor ht hr hyF hyp hy1 fun v hv hne _ => ?_
    rw [h1] at hv hne
    simp only [subs, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with e' | e'
    · exact absurd e' hne
    · rw [e']
      exact one_lt_of_prin hyF hyp hy1
  by_cases hs : isSucc q = true
  · have hc' : xcanon (.Xi m q) m q = .Xi m (pred q) := by
      unfold xcanon
      rw [ite_eq_right h1, ite_eq_left hs]
    have hpq : Lt (pred q) q := pred_lt hqF hs
    have hpF := wnf_pred hqF
    have hpne : pred q ≠ .zero := by
      intro e'
      apply h1
      rw [← succT_pred hqF hs, e']
      rfl
    have hy₁ : WNF (.Xi m (pred q)) := wnf_xi_mk hm hpF hpne
      (ne_gt_of_le (le_transY hpF hqF (WNF.succK hm) (Or.inr hpq)
        (le_of_ne_gtY hqF (WNF.succK hm) hρ.xi.2.2.2.1)))
      (inC_pred_self hqF hs hρ.xi.2.2.2.2)
    have hF : ∀ f, f ∈ fr (.Xi m q) (.Xi m q) → Lt f (.Xi m (pred q)) := fun f hf => by
      have e' : fr (.K m) q = fr (.K m) (pred q) := by
        have := fr_succT (.K m) (pred q)
        rwa [succT_pred hqF hs] at this
      have h := fr_cover_xi hρ hf
      rw [e'] at h
      exact FWOrder.k2x hy₁ f h
    have hlt : ∀ {n a : Tm}, n ∈ subs (pred q) → a ∈ subs n → a.size < n.size → Lt a q → Lt a (pred q) := by
      intro n a hn' ha hsz hlt
      have haF := hpF.of_mem_subs (subs_trans hn' ha)
      rcases le_of_lt_succT haF hpF (by rw [succT_pred hqF hs]; exact hlt) with e' | e'
      · exfalso
        have e1 := size_le_of_mem_subs hn'
        rw [← e'] at e1
        omega
      · exact e'
    have hc1 : ∀ s k a, Tm.Psi s k a ∈ subs q → Lt a q → Lt a (pred q) := fun s k a hn h =>
      hlt (node_mem_subs_pred hqF hs rfl (by intro e'; cases e') hn) (subs_psi_a (self_mem_subs a))
        (by simp only [Tm.size]; omega) h
    have hc1x : ∀ m' b, Tm.Xi m' b ∈ subs q → Lt b q → Lt b (pred q) := fun m' b hn h =>
      hlt (node_mem_subs_pred hqF hs rfl (by intro e'; cases e') hn) (subs_xi (self_mem_subs b))
        (by simp only [Tm.size]; omega) h
    have hl := floor_lowx hρ hy₁ hF hc1 hc1x
    refine vk_spec ht hc hS hqs hqσ (fun p hm' => (maxL_frt ht hm').1) (fun _ _ h' _ => absurd hs h')
      (fun y hyF hyp hy1 _ hle _ => ?_) (fun _ _ h' _ => absurd hs h')
    rw [hc'] at hle
    exact hGL _ hy₁ hl y hyF hyp hy1 hle
  -- 極限
  obtain ⟨pre, R, hsum, hR1, -, -, -, o0⟩ := s0x_out ht hc hS hqs hqσ hq0 hs
  obtain ⟨P₀, x₀, hP₀, hz₀, hfF, hx₀F, hx₀R, hz₀q, -, -, hx₀0, hx₀g⟩ := o0.form _ o0.mem
  have e0 : P₀ = .zero := by
    rcases hP₀ with h | h <;> exact h
  subst e0
  have hc' : xcanon (.Xi m q) m q = (s0X (.Xi m q) m q).first := by
    unfold xcanon
    rw [ite_eq_right h1, ite_eq_right hs]
  have hRm : R ∈ summands q := by
    rw [hsum]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hRp := nfl_principal (nfl_summands hqF) R hRm
  have hR0 : R ≠ .zero := by
    intro e'
    rw [e'] at hRp
    cases hRp
  have G : XiG m q .zero .one pre [] R :=
    ⟨hρ, hsum, WNF.zero, zero_lt hR0, zero_lt (by intro e'; cases e'), Or.inr rfl, hR1⟩
  have hA : ∀ {n a : Tm}, n ∈ subs q → isPrincipal n = true → a ∈ subs n → a.size < n.size → Lt a q →
      Lt a (xA .one pre .zero x₀) := fun hn hnp ha hsz hlt => by
    obtain ⟨S, hSm, hnS⟩ := mem_subs_summand hnp hn
    rw [hsum] at hSm
    exact G.lt_xA hx₀F hx₀R hx₀0 hx₀g hSm (subs_trans hnS ha)
      (ne_of_size_lt (Nat.lt_of_lt_of_le hsz (size_le_of_mem_subs hnS))) hlt
  have hc1 : ∀ s k a, Tm.Psi s k a ∈ subs q → Lt a q → Lt a (xA .one pre .zero x₀) := fun s k a hn hlt =>
    hA hn rfl (subs_psi_a (self_mem_subs a)) (by simp only [Tm.size]; omega) hlt
  have hc1x : ∀ m' b, Tm.Xi m' b ∈ subs q → Lt b q → Lt b (xA .one pre .zero x₀) := fun m' b hn hlt =>
    hA hn rfl (subs_xi (self_mem_subs b)) (by simp only [Tm.size]; omega) hlt
  have hnefirst : ∀ p, p ∈ fr (.Xi m q) (.Xi m q) → (s0X (.Xi m q) m q).first ≠ p := by
    intro p hp e'
    rw [hz₀] at e'
    subst e'
    have hps := (fr_spec hp).1
    simp only [subs, List.mem_cons] at hps
    rcases hps with e' | h
    · exact (fr_spec hp).2.ne e'
    · exact Lt.irrefl _ (hc1x _ _ h hz₀q)
  by_cases hE : ∃ p, maxL (frB (.Xi m q) (.Xi m q)) = some p ∧ Lt (s0X (.Xi m q) m q).first p
  · obtain ⟨p, hm', hlt⟩ := hE
    refine vk_spec ht hc hS hqs hqσ (fun p' hm'' => (maxL_frt ht hm'').1)
      (fun p' hm'' _ _ _ e' => hnefirst p' (maxL_frt ht hm'').2.1 e') (fun y hyF hyp _ _ hle hq' => ?_)
      (fun p' hm'' _ _ hlt' => ?_)
    · exfalso
      rcases hq' with h | h | h
      · exact h1 h
      · exact hs h
      · exact h p hm' (by rw [hc']; exact hlt)
    · obtain ⟨S', hpm, hmax⟩ := maxL_frt ht hm''
      exact vtail_floor ht hS hqs hqσ hs S' hpm hmax hlt'
  · have hfF' := hfF
    rw [hz₀] at hfF'
    have hF : ∀ f, f ∈ fr (.Xi m q) (.Xi m q) → Lt f (.Xi m (xA .one pre .zero x₀)) := by
      intro f hf
      rw [← hz₀]
      cases hm' : maxL (frB (.Xi m q) (.Xi m q)) with
      | none =>
        have h3 := maxL_none hm'
        rw [frB_eq_fr] at h3
        rw [h3] at hf
        cases hf
      | some p =>
        obtain ⟨S', hpm, hmax⟩ := maxL_frt ht hm'
        have hpf : Lt p (s0X (.Xi m q) m q).first := by
          rcases triY S'.hF hfF with h | h | h
          · exact h
          · exact absurd h.symm (hnefirst p hpm)
          · exact absurd ⟨p, hm', h⟩ hE
        exact lt_of_le_of_ltY (hρ.of_mem_subs (fr_spec hf).1) S'.hF hfF (hmax f hf) hpf
    have hl := floor_lowx hρ hfF' hF hc1 hc1x
    refine vk_spec ht hc hS hqs hqσ (fun p' hm'' => (maxL_frt ht hm'').1)
      (fun p' hm'' _ _ _ e' => hnefirst p' (maxL_frt ht hm'').2.1 e') (fun y hyF hyp hy1 _ hle _ => ?_)
      (fun p' hm'' _ _ hlt' => absurd ⟨p', hm'', hlt'⟩ hE)
    rw [hc', hz₀] at hle
    exact hGL _ hfF' hl y hyF hyp hy1 hle

end RTKA.Fund
