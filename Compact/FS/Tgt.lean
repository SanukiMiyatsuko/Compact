import Compact.FS.Hull

/-! 崩壊 `y = Ψ^ξ_π(Y)` より上の項の構造と、目標の部分項の比較。

`above_coll`：`y ≤ z < π` なら、`z` の見える位置（`y` 以上の節点だけをたどった先）に、目標が `π` で引数が `Y` 以上の節点がある。
`z` の形と比較の展開で場合分けする：

* `Ξ_n(b) < Ξ_n(q)`・`Ψ^σ_ρ(δ) < π` の条件のうち引数が小さい場合（`b ∈ C(q, π)` など）、成分が全て `C(Y, y)` に入るなら
  `z < y` なので、`π` についての前線に `y` 以上の元があり、帰納法で下りる。
* 引数が大きい場合は「`π` の成分が `C(δ, z)` に入らない」という条件で、`π` の前線が全て `y ≤ z` 未満なので成り立たない。
* Mahlo 添字が大きい場合（比較の c4：`ζ < σ`、`ζ ∉ C(σ, z)`）も、`ζ ∈ C(ζ, π)`（`FWOrder.ms`）と前線の評価で成り立たない。

系として、目標の部分項で `π` 未満のものは崩壊未満（`lt_of_mem_tgt`：見つかる節点は `π` を含むので大きさで矛盾）。 -/

namespace RTKA.Fund

open Tm W

/-- 前線の元は、より小さい基準でも（その基準未満なら）前線の元 -/
theorem fr_of_fr {R R' : Tm} (hR : WNF R) (hR' : WNF R') (hle : Le R' R) :
    ∀ {x w : Tm}, WNF x → w ∈ fr R x → Lt w R' → w ∈ fr R' x
  | .zero, _, _, h, _ | .one, _, _, h, _ | .K _, _, _, h, _ => by simp [fr] at h
  | .plus a b, w, hx, h, hw => by
    obtain ⟨ha, hb, -, -⟩ := hx.plus
    rw [fr, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (fr_of_fr hR hR' hle ha h hw)
    · exact Or.inr (fr_of_fr hR hR' hle hb h hw)
  | .Om a, w, hx, h, hw => by
    rw [fr] at h ⊢
    exact fr_of_fr hR hR' hle hx.om.1 h hw
  | .Xi m a, w, hx, h, hw => by
    rw [fr] at h ⊢
    by_cases h1 : Lt (.Xi m a) R
    · simp only [h1, ↓reduceIte, List.mem_singleton] at h
      subst h
      simp [hw]
    · simp only [h1, ↓reduceIte] at h
      have h2 : ¬ Lt (.Xi m a) R' := fun h' => h1 (lt_of_lt_of_leY hx hR' hR h' hle)
      simp only [h2, ↓reduceIte]
      exact fr_of_fr hR hR' hle hx.xi.2.1 h hw
  | .Psi s p a, w, hx, h, hw => by
    have hP := hx.psi
    rw [fr] at h ⊢
    by_cases h1 : Lt (.Psi s p a) R
    · simp only [h1, ↓reduceIte, List.mem_singleton] at h
      subst h
      simp [hw]
    · simp only [h1, ↓reduceIte, List.mem_append] at h
      have h2 : ¬ Lt (.Psi s p a) R' := fun h' => h1 (lt_of_lt_of_leY hx hR' hR h' hle)
      simp only [h2, ↓reduceIte, List.mem_append]
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (fr_of_fr hR hR' hle hP.xiF h hw))
      · exact Or.inl (Or.inr (fr_of_fr hR hR' hle hP.piF h hw))
      · exact Or.inr (fr_of_fr hR hR' hle hP.aF h hw)

/-- `Ξ_n(q)` の引数の `K_n` についての前線は `Ξ_n(q)` 自身の前線 -/
theorem fr_xi_self {n : Nat} {q w : Tm} (h : WNF (.Xi n q)) (hw : w ∈ fr (.K n) q) :
    w ∈ fr (.Xi n q) (.Xi n q) := by
  have hn := h.xi.1
  have hlt : Lt (.Xi n q) (.K n) := (lt_K_iffY h hn).mpr (Nat.le_refl _)
  have hne : ¬ Lt (Tm.Xi n q) (.Xi n q) := Lt.irrefl _
  rw [fr]
  simp only [hne, ↓reduceIte]
  exact fr_of_fr (WNF.K' hn) h (Or.inr hlt) h.xi.2.1 hw (FWOrder.k2x h w hw)

/-- `π = Ψ^ζ_κ(c)` の成分の前線（`π` について）は `π` の前線 -/
theorem fr_psi_self {ζ κ c w : Tm} {x : Tm} (hx : x = ζ ∨ x = κ ∨ x = c)
    (hw : w ∈ fr (.Psi ζ κ c) x) : w ∈ fr (.Psi ζ κ c) (.Psi ζ κ c) := by
  have hne : ¬ Lt (Tm.Psi ζ κ c) (.Psi ζ κ c) := Lt.irrefl _
  rw [fr]
  simp only [hne, ↓reduceIte, List.mem_append]
  rcases hx with rfl | rfl | rfl
  · exact Or.inl (Or.inl hw)
  · exact Or.inl (Or.inr hw)
  · exact Or.inr hw

/-- 目標 `κ` の前線は、`κ` への崩壊 `π` の前線 -/
theorem fr_tgt_step {ζ κ c w : Tm} (hπ : WNF (.Psi ζ κ c)) (hw : w ∈ fr κ κ) :
    w ∈ fr (.Psi ζ κ c) (.Psi ζ κ c) :=
  fr_psi_self (x := κ) (Or.inr (Or.inl rfl))
    (fr_of_fr hπ.psi.piF hπ (Or.inr (lt_psi_targetY hπ)) hπ.psi.piF hw (FWOrder.k2t hπ w hw))

/-- `ζ ≠ 0` の `Ψ^ζ_κ(c)` の目標は `Ω` でない -/
theorem tgt_not_om {ζ κ c : Tm} (hπ : WNF (.Psi ζ κ c)) (hζ : ζ ≠ .zero) : ∀ e, κ ≠ .Om e := by
  rintro e rfl
  exact hζ (hπ.psiOm.2.2.2.2.2)

/-- 目標の引数は崩壊の引数未満 -/
theorem arg_lt_of_psi {ζ κ c r : Tm} (hπ : WNF (.Psi ζ κ c)) (hr : argR? κ = some r) : Lt r c := by
  have hP := hπ.psi
  have hC := hP.Cpi
  rcases hP.tgt with ⟨e, rfl, -⟩ | ⟨n, q, rfl⟩ | ⟨z, k, b, rfl, -⟩
  · simp [argR?] at hr
  · simp only [argR?, Option.some.injEq] at hr
    subst hr
    rcases inC_xi_iff.mp hC with h | ⟨-, h⟩
    · exact absurd h (Lt.irrefl _)
    · exact h
  · simp only [argR?, Option.some.injEq] at hr
    subst hr
    rcases inC_psi_iff.mp hC with h | ⟨-, -, -, h⟩
    · exact absurd h (Lt.irrefl _)
    · exact h

/-- 前線が全て `Ξ_n(b)` 未満で、目標の引数が `b` 以下なら、`Ξ_n(b)` は目標未満でない -/
theorem xi_not_lt_tgt : ∀ (s : Nat) {π : Tm} {n : Nat} {b : Tm}, π.size ≤ s → WNF π → IsTgt π →
    (∀ e, π ≠ .Om e) → lev π = n → WNF (.Xi n b) → (∀ w, w ∈ fr π π → Lt w (.Xi n b)) →
    (∀ r, argR? π = some r → Le r b) → ¬ Lt (.Xi n b) π := by
  intro s
  induction s with
  | zero =>
    intro π _ _ h
    have := Tm.size_pos π
    omega
  | succ s ih =>
    intro π n b hsz hπ ht hne hl hz hF hr hlt
    rcases ht with ⟨e, rfl, -⟩ | ⟨m, q, rfl⟩ | ⟨ζ, κ, c, rfl, hζ⟩
    · exact hne e rfl
    · have hmn : m = n := hl
      subst hmn
      rcases hr q rfl with e | hqb
      · subst e
        exact Lt.irrefl _ hlt
      · have hqF := hπ.xi.2.1
        have hn := hπ.xi.1
        have hK := WNF.K' hn
        have hzK : Lt (.Xi m b) (.K m) := (lt_K_iffY hz hn).mpr (Nat.le_refl _)
        rcases (lt_xi_xi0 hqb.ne.symm).mp hlt with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact Lt.asymmY hqF hz.xi.2.1 hqb h1
        · have h3 := inC_of_fr_lt hqF hK hz hqF hz.xi.2.1 hπ.xi.2.2.2.2 (Or.inr hzK) (Or.inr hqb)
            fun w hw => hF w (fr_xi_self hπ hw)
          rw [h3] at h2
          cases h2
    · have hP := hπ.psi
      have hlκ : lev κ = n := hl
      have h1 : ¬ Lt (.Psi ζ κ c) (.Xi n b) := (lt_xi_psiY hlκ).mp hlt
      have h2 : ¬ cmp κ (.Xi n b) ≠ .gt := fun h => h1 ((lt_psi_xiY hlκ).mpr (Or.inl h))
      have h3 : Lt (.Xi n b) κ := by
        have h4 : cmp κ (.Xi n b) = .gt := by simpa using h2
        unfold Lt
        rw [FWOrder.swap hP.piF hz, h4]
        rfl
      refine ih (by simp only [Tm.size] at hsz; omega) hP.piF hP.tgt (tgt_not_om hπ hζ) hlκ hz
        (fun w hw => hF w (fr_tgt_step hπ hw)) (fun r hrr => ?_) h3
      exact Or.inr (lt_of_lt_of_leY (wnf_of_argR hP.piF hrr) hP.aF hz.xi.2.1 (arg_lt_of_psi hπ hrr)
        (hr c rfl))

/-- `z` の中の、`d ≤ y` の `C(g, d)` から見える目標 `π` の節点で、引数が `Y` 以上のもの -/
def Above (π Y y z : Tm) : Prop :=
  ∃ s a, Tm.Psi s π a ∈ subs z ∧ Le Y a ∧ Le y (.Psi s π a) ∧
    ∀ g d, WNF d → Le d y → inC z g d = true → inC (.Psi s π a) g d = true

/-- 見える部分項から持ち上げる -/
theorem Above.sub {π Y y z e : Tm} (h : Above π Y y e) (he : e ∈ subs z)
    (hvis : ∀ g d, WNF d → Le d y → inC z g d = true → inC e g d = true) : Above π Y y z := by
  obtain ⟨s, a, h1, h2, h4, h3⟩ := h
  exact ⟨s, a, subs_trans he h1, h2, h4, fun g d hd hdy hC => h3 g d hd hdy (hvis g d hd hdy hC)⟩

/-- 部分項の前線の元から持ち上げる -/
theorem Above.fr {π Y y z e w : Tm} (hπ : WNF π) (hyF : WNF y) (hyπ : Lt y π) (heF : WNF e)
    (h : Above π Y y w) (he : e ∈ subs z)
    (hvis : ∀ g d, WNF d → Le d y → inC z g d = true → inC e g d = true) (hw : w ∈ fr π e) :
    Above π Y y z := by
  refine Above.sub h (subs_trans he (fr_spec hw).1) fun g d hd hdy hC => ?_
  refine fr_of_inC e (fun u hu hn hud => hn ?_) (hvis g d hd hdy hC) w hw
  exact lt_transY (heF.of_mem_subs hu) hd hπ hud (lt_of_le_of_ltY hd hyF hπ hdy hyπ)

/-- 崩壊 `y = Ψ^ξ_π(Y)` 以上で目標 `π` 未満の項には、見える位置に、目標 `π` で引数が `Y` 以上の節点がある -/
theorem above_coll {ξ π Y : Tm} (hy : WNF (.Psi ξ π Y)) : ∀ (n : Nat) {z : Tm}, z.size ≤ n → WNF z →
    Lt z π → Le (.Psi ξ π Y) z → Above π Y (.Psi ξ π Y) z := by
  have hYP := hy.psi
  have hπF := hYP.piF
  have hYF := hYP.aF
  have hyπ : Lt (.Psi ξ π Y) π := lt_psi_targetY hy
  have hyle : Le (.Psi ξ π Y) π := Or.inr hyπ
  have hnlow : ∀ {z d : Tm}, WNF z → WNF d → Le d (.Psi ξ π Y) → Le (.Psi ξ π Y) z → ¬ Lt z d :=
    fun hz hd hdy hyz h => not_lt_of_leY hy hz hyz (lt_of_lt_of_leY hz hd hy h hdy)
  have hex : ∀ {e g0 : Tm}, WNF e → WNF g0 → Le g0 Y → inC e g0 π = true →
      ¬ inC e Y (.Psi ξ π Y) = true → ∃ w, w ∈ fr π e ∧ ¬ Lt w (.Psi ξ π Y) := by
    intro e g0 heF hg0 hgY hC hnC
    refine Classical.byContradiction fun hn => hnC ?_
    refine inC_of_fr_lt heF hπF hy hg0 hYF hC hyle hgY fun w hw => ?_
    exact Classical.byContradiction fun hl => hn ⟨w, hw, hl⟩
  have hπC : inC π Y (.Psi ξ π Y) = true :=
    inC_of_fr_lt hπF hπF hy hYF hYF hYP.Cpi hyle (Or.inl rfl) fun w hw => FWOrder.k2t hy w hw
  intro n
  induction n with
  | zero =>
    intro z h
    have := Tm.size_pos z
    omega
  | succ n ih =>
    intro z hsz hz hzπ hyz
    have hnyz : ¬ Lt z (.Psi ξ π Y) := not_lt_of_leY hy hz hyz
    have hup : ∀ {e w : Tm}, WNF e → e.size ≤ n → e ∈ subs z →
        (∀ g d, WNF d → Le d (.Psi ξ π Y) → inC z g d = true → inC e g d = true) →
        w ∈ fr π e → ¬ Lt w (.Psi ξ π Y) → Above π Y (.Psi ξ π Y) z := by
      intro e w heF hes hez hvis hw hwy
      have hwF := heF.of_mem_subs (fr_spec hw).1
      have hws := size_le_of_mem_subs (fr_spec hw).1
      exact Above.fr hπF hy hyπ heF (ih (by omega) hwF (fr_spec hw).2 (le_of_not_ltY hwF hy hwy)) hez
        hvis hw
    cases z with
    | zero =>
      rcases hyz with e | h
      · cases e
      · exact absurd h (not_lt_zero _)
    | one => exact absurd (coll_psiY hy .one WNF.one (inC_one _ _) hzπ) hnyz
    | K m => exact absurd (coll_psiY hy _ hz (inC_K _ _ _) hzπ) hnyz
    | plus a b =>
      have ha := hz.plus.1
      have hyp : isPrincipal (.Psi ξ π Y) = true := rfl
      have hπp : isPrincipal π = true := by
        rcases hYP.tgt with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩ <;> rfl
      have hay : ¬ Lt a (.Psi ξ π Y) := fun h => hnyz ((lt_plus_prin_iffY hz hyp).mpr h)
      have haπ : Lt a π := (lt_plus_prin_iffY hz hπp).mp hzπ
      refine Above.sub (ih ?_ ha haπ (le_of_not_ltY ha hy hay)) (subs_plus_l (self_mem_subs a))
        fun g d _ _ hC => ?_
      · simp only [Tm.size] at hsz
        have := Tm.size_pos b
        omega
      · rw [inC_plus, Bool.and_eq_true] at hC
        exact hC.1
    | Om j =>
      have hj := hz.om.1
      have hjπ : Lt j π := lt_transY hj hz hπF hz.om.2.2 hzπ
      by_cases hom : ∃ c, π = .Om c
      · obtain ⟨c, rfl⟩ := hom
        have e0 := hy.psiOm.2.2.2.2.2
        subst e0
        exact absurd ((lt_om_psiY hy).mpr ((lt_om_iffY hj hπF.om.1).mp hzπ)) hnyz
      · have hOF : IsOF (.Psi ξ π Y) := IsOF.psi hy fun c e => hom ⟨c, e⟩
        have hyj : Le (.Psi ξ π Y) j := by
          rcases hyz with e | h
          · cases e
          · exact Or.inr ((lt_OF_omG hOF hy hj).mp h)
        refine Above.sub (ih (by simp only [Tm.size] at hsz; omega) hj hjπ hyj) (mem_subs_om j)
          fun g d _ _ hC => ?_
        rwa [inC_om] at hC
    | Xi m b =>
      have hbF := hz.xi.2.1
      have hvis : ∀ g d, WNF d → Le d (.Psi ξ π Y) → inC (.Xi m b) g d = true → inC b g d = true :=
        fun g d hd hdy hC => by
          rcases inC_xi_iff.mp hC with h | ⟨h, -⟩
          · exact absurd h (hnlow hz hd hdy hyz)
          · exact h
      have hbs : b.size ≤ n := by
        simp only [Tm.size] at hsz
        omega
      have hm : m ≤ lev π := show lev (Tm.Xi m b) ≤ lev π from lev_le_of_lt_gen hzπ
      rcases Nat.lt_or_eq_of_le hm with hm | hl
      · exact absurd (lt_of_lev_lt' (a := .Xi m b) (b := .Psi ξ π Y) hm) hnyz
      · have hl' : lev π = m := hl.symm
        have hyz' : Lt (.Psi ξ π Y) (.Xi m b) := hyz.resolve_left (by intro e; cases e)
        rcases (lt_psi_xiY hl').mp hyz' with h1 | ⟨hbY, hnC⟩
        · exact absurd hzπ (not_lt_of_leY hπF hz (le_of_ne_gtY hπF hz h1))
        · have hF : ∀ w, w ∈ fr π π → Lt w (.Xi m b) := fun w hw =>
            lt_transY (hπF.of_mem_subs (fr_spec hw).1) hy hz (FWOrder.k2t hy w hw) hyz'
          have hnC' : ¬ inC b Y (.Psi ξ π Y) = true := by
            rw [hnC]
            simp
          rcases hYP.tgt with ⟨c, e, -⟩ | ⟨n', q, e⟩ | ⟨ζ, κ, c, e, hζ⟩
          · subst e
            have e0 := hy.psiOm.2.2.2.2.2
            subst e0
            exact absurd (lt_psi_om_of_lt_om hy hz rfl hzπ (fun s a e => by cases e)) hnyz
          · subst e
            have hnm : n' = m := hl'
            subst hnm
            have hqF := hπF.xi.2.1
            have hb_ne : b ≠ q := fun e => hzπ.ne (by rw [e])
            have hqY : Lt q Y := arg_lt_of_psi hy rfl
            rcases (lt_xi_xi0 hb_ne).mp hzπ with ⟨-, hC⟩ | ⟨hqb, hn2⟩
            · obtain ⟨w, hw, hwy⟩ := hex hbF hqF (Or.inr hqY) hC hnC'
              exact hup hbF hbs (mem_subs_xi n' b) hvis hw hwy
            · have hn1 := hπF.xi.1
              have h3 := inC_of_fr_lt hqF (WNF.K' hn1) hz hqF hbF hπF.xi.2.2.2.2
                (Or.inr ((lt_K_iffY hz hn1).mpr (Nat.le_refl _))) (Or.inr hqb)
                fun w hw => hF w (fr_xi_self hπF hw)
              rw [h3] at hn2
              cases hn2
          · subst e
            have hPπ := hπF.psi
            have hlκ : lev κ = m := hl'
            have h1 : ¬ Lt (.Psi ζ κ c) (.Xi m b) := (lt_xi_psiY hlκ).mp hzπ
            have hcY : Lt c Y := arg_lt_of_psi hy rfl
            by_cases hbc : Lt b c
            · cases hC : inC b c (.Psi ζ κ c) with
              | true =>
                obtain ⟨w, hw, hwy⟩ := hex hbF hPπ.aF (Or.inr hcY) hC hnC'
                exact hup hbF hbs (mem_subs_xi m b) hvis hw hwy
              | false => exact absurd ((lt_psi_xiY hlκ).mpr (Or.inr ⟨hbc, hC⟩)) h1
            · have hcb : Le c b := le_of_not_ltY hbF hPπ.aF hbc
              have h2 : ¬ cmp κ (.Xi m b) ≠ .gt := fun h' => h1 ((lt_psi_xiY hlκ).mpr (Or.inl h'))
              have h3 : Lt (.Xi m b) κ := by
                have h4 : cmp κ (.Xi m b) = .gt := by simpa using h2
                unfold Lt
                rw [FWOrder.swap hPπ.piF hz, h4]
                rfl
              exact absurd h3 (xi_not_lt_tgt _ (Nat.le_refl _) hPπ.piF hPπ.tgt (tgt_not_om hπF hζ) hlκ hz
                (fun w hw => hF w (fr_tgt_step hπF hw))
                (fun r hrr => Or.inr (lt_of_lt_of_leY (wnf_of_argR hPπ.piF hrr) hPπ.aF hbF
                  (arg_lt_of_psi hπF hrr) hcb)))
    | Psi σ ρ δ =>
      have hvP := hz.psi
      have hρF := hvP.piF
      have hσF := hvP.xiF
      have hδF := hvP.aF
      have hvis : ∀ g d, WNF d → Le d (.Psi ξ π Y) → inC (.Psi σ ρ δ) g d = true →
          inC ρ g d = true ∧ inC σ g d = true ∧ inC δ g d = true := fun g d hd hdy hC => by
        rcases inC_psi_iff.mp hC with h | ⟨h1, h2, h3, -⟩
        · exact absurd h (hnlow hz hd hdy hyz)
        · exact ⟨h1, h2, h3⟩
      have hsizes : ρ.size ≤ n ∧ σ.size ≤ n ∧ δ.size ≤ n := by
        simp only [Tm.size] at hsz
        omega
      have hm : lev ρ ≤ lev π := show lev (Tm.Psi σ ρ δ) ≤ lev π from lev_le_of_lt_gen hzπ
      rcases Nat.lt_or_eq_of_le hm with hm | hl
      · exact absurd (lt_of_lev_lt' (a := .Psi σ ρ δ) (b := .Psi ξ π Y) hm) hnyz
      · by_cases hρπ : Lt ρ π
        · refine Above.sub (ih hsizes.1 hρF hρπ ?_) (subs_psi_p (self_mem_subs ρ))
            fun g d hd hdy hC => (hvis g d hd hdy hC).1
          exact Or.inr (lt_of_le_of_ltY hy hz hρF hyz (lt_psi_targetY hz))
        by_cases hρe : ρ = π
        · subst hρe
          by_cases hYδ : Lt δ Y
          · have hne : Tm.Psi σ ρ δ ≠ .Psi ξ ρ Y := fun e => by
              cases e
              exact Lt.irrefl _ hYδ
            have hnot : ¬ (inC δ Y (.Psi ξ ρ Y) = true ∧ inC σ Y (.Psi ξ ρ Y) = true) :=
              fun h => hnyz ((lt_psi_psiY rfl hne).mpr (Or.inr ⟨hyπ, hzπ, Or.inl
                ⟨hYδ, h.1, h.2, hπC⟩⟩))
            by_cases hδC : inC δ Y (.Psi ξ ρ Y) = true
            · obtain ⟨w, hw, hwy⟩ := hex hσF hδF (Or.inr hYδ) hvP.Cxi fun h => hnot ⟨hδC, h⟩
              exact hup hσF hsizes.2.1 (subs_psi_s (self_mem_subs σ))
                (fun g d hd hdy hC => (hvis g d hd hdy hC).2.1) hw hwy
            · obtain ⟨w, hw, hwy⟩ := hex hδF hδF (Or.inr hYδ) hvP.Ca hδC
              exact hup hδF hsizes.2.2 (subs_psi_a (self_mem_subs δ))
                (fun g d hd hdy hC => (hvis g d hd hdy hC).2.2) hw hwy
          · exact ⟨σ, δ, self_mem_subs _, le_of_not_ltY hδF hYF hYδ, hyz, fun _ _ _ _ h => h⟩
        have hπρ : Lt π ρ := by
          rcases le_of_not_ltY hρF hπF hρπ with e | h
          · exact absurd e.symm hρe
          · exact h
        have hyρ : Lt (.Psi ξ π Y) ρ := lt_transY hy hπF hρF hyπ hπρ
        have hF : ∀ w, w ∈ fr π π → Lt w (.Psi σ ρ δ) := fun w hw =>
          lt_of_lt_of_leY (hπF.of_mem_subs (fr_spec hw).1) hy hz (FWOrder.k2t hy w hw) hyz
        have hne' : Tm.Psi σ ρ δ ≠ .Psi ξ π Y := fun e => by
          cases e
          exact hρe rfl
        rcases hYP.tgt with ⟨c, e, -⟩ | ⟨n', q, e⟩ | ⟨ζ, κ, c, e, hζ⟩
        · subst e
          have e0 := hy.psiOm.2.2.2.2.2
          subst e0
          exact absurd (lt_psi_om_of_lt_om hy hz rfl hzπ (fun s a e => by
            cases e
            exact hρe rfl)) hnyz
        · subst e
          have hl' : lev ρ = n' := hl
          have hqF := hπF.xi.2.1
          have hn1 := hπF.xi.1
          rcases (lt_psi_xiY hl').mp hzπ with h1 | ⟨hqδ, hnC⟩
          · exact absurd hπρ (not_lt_of_leY hρF hπF (le_of_ne_gtY hρF hπF h1))
          · have hvK : Lt (.Psi σ ρ δ) (.K n') := (lt_K_iffY hz hn1).mpr (by
              simp only [lev]
              exact Nat.le_of_eq hl')
            have h3 := inC_of_fr_lt hqF (WNF.K' hn1) hz hqF hδF hπF.xi.2.2.2.2 (Or.inr hvK)
              (Or.inr hqδ) fun w hw => hF w (fr_xi_self hπF hw)
            rw [h3] at hnC
            cases hnC
        · subst e
          have hPπ := hπF.psi
          have hκF := hPπ.piF
          have hcF := hPπ.aF
          have hcY : Lt c Y := arg_lt_of_psi hy rfl
          have hl' : lev ρ = lev κ := hl
          have hyκ : Le (.Psi ξ (.Psi ζ κ c) Y) κ :=
            Or.inr (lt_transY hy hπF hκF hyπ (lt_psi_targetY hπF))
          have hparts : ∀ {e g : Tm}, (e = ζ ∨ e = κ ∨ e = c) → WNF e → inC e c κ = true → WNF g →
              Le c g → Le (.Psi σ ρ δ) κ → inC e g (.Psi σ ρ δ) = true := by
            intro e g he heF hC hg hcg hle'
            refine inC_of_fr_lt heF hκF hz hcF hg hC hle' hcg fun w hw => hF w ?_
            have hlt' : Lt w (.Psi ζ κ c) := by
              rcases he with rfl | rfl | rfl
              · exact FWOrder.k2s hπF w hw
              · exact FWOrder.k2t hπF w hw
              · exact FWOrder.k2 hπF w hw
            exact fr_psi_self he (fr_of_fr hκF hπF (Or.inr (lt_psi_targetY hπF)) heF hw hlt')
          have hzy : ¬ (Lt δ Y ∧ inC δ Y (.Psi ξ (.Psi ζ κ c) Y) = true ∧
              inC σ Y (.Psi ξ (.Psi ζ κ c) Y) = true ∧ inC ρ Y (.Psi ξ (.Psi ζ κ c) Y) = true) :=
            fun h => hnyz ((lt_psi_psiY hl hne').mpr (Or.inr ⟨hyρ, hzπ, Or.inl h⟩))
          have hthree : Lt δ Y → (inC δ c (.Psi ζ κ c) = true) → inC σ c (.Psi ζ κ c) = true →
              inC ρ c (.Psi ζ κ c) = true → Above (.Psi ζ κ c) Y (.Psi ξ (.Psi ζ κ c) Y) (.Psi σ ρ δ) := by
            intro h4 h3 h2 h0
            by_cases hδC : inC δ Y (.Psi ξ (.Psi ζ κ c) Y) = true
            · by_cases hσC : inC σ Y (.Psi ξ (.Psi ζ κ c) Y) = true
              · obtain ⟨w, hw, hwy⟩ := hex hρF hcF (Or.inr hcY) h0 fun h => hzy ⟨h4, hδC, hσC, h⟩
                exact hup hρF hsizes.1 (subs_psi_p (self_mem_subs ρ))
                  (fun g d hd hdy hC => (hvis g d hd hdy hC).1) hw hwy
              · obtain ⟨w, hw, hwy⟩ := hex hσF hcF (Or.inr hcY) h2 hσC
                exact hup hσF hsizes.2.1 (subs_psi_s (self_mem_subs σ))
                  (fun g d hd hdy hC => (hvis g d hd hdy hC).2.1) hw hwy
            · obtain ⟨w, hw, hwy⟩ := hex hδF hcF (Or.inr hcY) h3 hδC
              exact hup hδF hsizes.2.2 (subs_psi_a (self_mem_subs δ))
                (fun g d hd hdy hC => (hvis g d hd hdy hC).2.2) hw hwy
          rcases (lt_psi_psiY hl' hzπ.ne).mp hzπ with h1 | ⟨-, hvκ, hc | hc | hc | hc⟩
          · exact absurd hπρ h1
          · obtain ⟨h4, h3, h2, h0⟩ := hc
            exact hthree (lt_transY hδF hcF hYF h4 hcY) h3 h2 h0
          · exfalso
            obtain ⟨h2, h3⟩ := hc
            have hcδ : Le c δ := le_of_ne_gtY hcF hδF h2
            exact h3 ⟨hparts (Or.inr (Or.inr rfl)) hcF hPπ.Ca hδF hcδ (Or.inr hvκ),
              hparts (Or.inl rfl) hPπ.xiF hPπ.Cxi hδF hcδ (Or.inr hvκ),
              hparts (Or.inr (Or.inl rfl)) hκF hPπ.Cpi hδF hcδ (Or.inr hvκ)⟩
          · obtain ⟨h2, h3, h4, h5⟩ := hc
            have hδc : δ = c := FWOrder.eq hδF hcF h2
            subst hδc
            subst h3
            have hδC : inC δ Y (.Psi ξ (.Psi ζ κ δ) Y) = true :=
              inC_of_fr_lt hcF hκF hy hcF hYF hPπ.Ca hyκ (Or.inr hcY) fun w hw =>
                FWOrder.k2t hy w (fr_psi_self (Or.inr (Or.inr rfl))
                  (fr_of_fr hκF hπF (Or.inr (lt_psi_targetY hπF)) hcF hw (FWOrder.k2 hπF w hw)))
            have hκC : inC κ Y (.Psi ξ (.Psi ζ κ δ) Y) = true :=
              inC_of_fr_lt hκF hκF hy hcF hYF hPπ.Cpi hyκ (Or.inr hcY) fun w hw =>
                FWOrder.k2t hy w (fr_tgt_step hπF hw)
            obtain ⟨w, hw, hwy⟩ := hex hσF hcF (Or.inr hcY) h5 fun h =>
              hzy ⟨hcY, hδC, h, hκC⟩
            exact hup hσF hsizes.2.1 (subs_psi_s (self_mem_subs σ))
              (fun g d hd hdy hC => (hvis g d hd hdy hC).2.1) hw hwy
          · exfalso
            obtain ⟨h2, h3⟩ := hc
            have h4 : inC ζ σ (.Psi σ ρ δ) = true :=
              inC_of_fr_lt hPπ.xiF hπF hz hPπ.xiF hσF (FWOrder.ms hπF) (Or.inr hzπ) (Or.inr h2)
                fun w hw => hF w (fr_psi_self (Or.inl rfl) hw)
            rw [h4] at h3
            cases h3

/-- 目標の部分項で `π` 未満のものは、`π` への崩壊未満 -/
theorem lt_of_mem_tgt {ξ π Y v : Tm} (hy : WNF (.Psi ξ π Y)) (hv : v ∈ subs π) (hlt : Lt v π) :
    Lt v (.Psi ξ π Y) := by
  have hvF := hy.psi.piF.of_mem_subs hv
  by_cases h : Lt v (.Psi ξ π Y)
  · exact h
  · exfalso
    obtain ⟨s, a, h1, -, -, -⟩ := above_coll hy _ (Nat.le_refl _) hvF hlt (le_of_not_ltY hvF hy h)
    have h2 := size_le_of_mem_subs (subs_trans hv h1)
    simp only [Tm.size] at h2
    omega

/-- 目標 `π` の崩壊の真の部分項の比較は、引数の部分項の比較に帰着する -/
theorem gap_of_arg_gen {ξ π X Y v : Tm} (ht : WNF (.Psi .zero π X)) (hy : WNF (.Psi ξ π Y))
    (harg : ∀ u, u ∈ subs X → Lt u (.Psi .zero π X) → Lt u (.Psi ξ π Y))
    (hv : v ∈ subs (.Psi .zero π X)) (hne : v ≠ .Psi .zero π X)
    (hlt : Lt v (.Psi .zero π X)) : Lt v (.Psi ξ π Y) := by
  simp only [subs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
  rcases hv with e | (h | h) | h
  · exact absurd e hne
  · rw [h]
    exact zero_lt (by intro e; cases e)
  · exact lt_of_mem_tgt hy h (lt_transY (ht.psi.piF.of_mem_subs h) ht ht.psi.piF hlt
      (lt_psi_targetY ht))
  · exact harg v h hlt

end RTKA.Fund
