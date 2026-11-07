import Compact.FS.Split

/-! 崩壊 `t = Ψ^0_π(X)` から、より小さい引数の崩壊 `y = Ψ^ξ_κ(Y)`（`π ≤ κ`、同じ階）への `C` の移し替え。

`π` の前線が `y` 未満で、`t` の上の目標を持つ節点の引数について「`X` 未満なら `Y` 未満」（`ArgCond`）、引数が `X` 以上の節点について
`Arg2` が成り立つなら、`C(X, t)` の元は `C(Y, y)` に入る（`HullHyp.transfer`）。特に `t` 未満で `κ` 未満の項は `y` 未満
（`HullHyp.lt_of_lt`）。`Arg2` は `X` の前線が `y` 未満なら成り立つ（`arg2_of_fr`）。

証明は節点についての帰納法：`z < t` の比較（Prop. 4.20）で、

* 目標 `ρ ≤ t` なら `ρ` を帰納法で `y` 未満にして `z < ρ < y`。
* `a < X`（c1）なら成分が移るので `z ∈ C(Y, y)`。
* `X ≤ a`（c2）なら `X` か `π` が `C(a, z)` に入らない。`y ≤ z` なら `π` は入り、`X` も入るか目標 `ρ` が `t` 未満（`Arg2`）。

後者の引数では `Y = pred X` に使う（`ArgCond` は大きさの議論で成り立つ）。 -/

namespace RTKA.Fund

open Tm W

/-- 移し替えの仮定 -/
structure HullHyp (π X ξ κ Y : Tm) : Prop where
  ht : WNF (.Psi .zero π X)
  hy : WNF (.Psi ξ κ Y)
  hπκ : Le π κ
  hl : lev π = lev κ
  hle : Le Y X
  /-- 目標の前線は `y` 未満 -/
  hFt : ∀ f, f ∈ fr π π → Lt f (.Psi ξ κ Y)

/-- `e` の中の、`t` の上の節点の引数について「`X` 未満なら `Y` 未満」 -/
def ArgCond (t X Y e : Tm) : Prop :=
  (∀ s k a, Tm.Psi s k a ∈ subs e → Lt t k → Lt a X → Lt a Y) ∧
    ∀ m b, Tm.Xi m b ∈ subs e → ¬ Lt (.Xi m b) t → Lt b X → Lt b Y

theorem ArgCond.sub {t X Y e w : Tm} (h : ArgCond t X Y e) (hw : w ∈ subs e) : ArgCond t X Y w :=
  ⟨fun s k a hz => h.1 s k a (subs_trans hw hz), fun m b hz => h.2 m b (subs_trans hw hz)⟩

/-- `e` の中の、`t` 未満で `y` 以上の節点で引数が `X` 以上のものについて、`X` が `C(a, z)` に入るか、目標が `t` 未満 -/
def Arg2 (t X y e : Tm) : Prop :=
  ∀ s k a, Tm.Psi s k a ∈ subs e → Lt (.Psi s k a) t → Le X a → Le y (.Psi s k a) →
    inC X a (.Psi s k a) = true ∨ Lt k t

theorem Arg2.sub {t X y e w : Tm} (h : Arg2 t X y e) (hw : w ∈ subs e) : Arg2 t X y w :=
  fun s k a hz => h s k a (subs_trans hw hz)

namespace HullHyp

variable {π X ξ κ Y : Tm}

theorem hπF (H : HullHyp π X ξ κ Y) : WNF π := H.ht.psi.piF
theorem hκF (H : HullHyp π X ξ κ Y) : WNF κ := H.hy.psi.piF
theorem hX (H : HullHyp π X ξ κ Y) : WNF X := H.ht.psi.aF

theorem tlt (H : HullHyp π X ξ κ Y) : Lt (.Psi .zero π X) κ :=
  lt_of_lt_of_leY H.ht H.hπF H.hκF (lt_psi_targetY H.ht) H.hπκ

/-- 目標（`Ψ^0` でない）は `t` と等しくない -/
theorem tgt_ne {k Z π : Tm} (hk : IsTgt k) : k ≠ .Psi .zero π Z := by
  rcases hk with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ | ⟨ζ, κ', b, rfl, hζ⟩
  · intro e; cases e
  · intro e; cases e
  · intro e
    cases e
    exact hζ rfl

/-- 節点が `t` 未満で、階が同じ場合の、成分に移す前の場合分け -/
theorem psi_of_lt (H : HullHyp π X ξ κ Y) {s k a : Tm} (he : WNF (.Psi s k a))
    (h2 : Lt (.Psi s k a) (.Psi .zero π X) → Le X a → Le (.Psi ξ κ Y) (.Psi s k a) →
      inC X a (.Psi s k a) = true ∨ Lt k (.Psi .zero π X))
    (hS_k : inC k X (.Psi .zero π X) = true → inC k Y (.Psi ξ κ Y) = true)
    (parts : Lt (.Psi .zero π X) k → inC k X (.Psi .zero π X) = true →
      inC s X (.Psi .zero π X) = true → inC a X (.Psi .zero π X) = true → Lt a X →
      inC (.Psi s k a) Y (.Psi ξ κ Y) = true)
    (h1 : Lt (.Psi s k a) (.Psi .zero π X)) :
    inC (.Psi s k a) Y (.Psi ξ κ Y) = true := by
  have hP := he.psi
  have ht := H.ht
  have hy := H.hy
  have hπF := H.hπF
  have hκF := H.hκF
  have hX := H.hX
  by_cases hl : lev k = lev π
  · rcases (lt_psi_psiY hl h1.ne).mp h1 with hA | ⟨hB1, hB2, hc1 | hc2 | hc3 | hc4⟩
    · have hkt : Le k (.Psi .zero π X) := le_of_not_ltY ht hP.piF hA
      have hkt' : Lt k (.Psi .zero π X) := hkt.resolve_left (tgt_ne hP.tgt)
      have hkκ : Lt k κ := lt_transY hP.piF ht hκF hkt' H.tlt
      have hC := hS_k (WFY.inC_of_ltY _ hP.piF ht hkt')
      have hky := coll_psiY hy k hP.piF hC hkκ
      exact inC_psi_iff.mpr (Or.inl (lt_transY he hP.piF hy (lt_psi_targetY he) hky))
    · obtain ⟨h4, h3, h2, h0⟩ := hc1
      exact parts hB1 h0 h2 h3 h4
    · by_cases hzy : Lt (.Psi s k a) (.Psi ξ κ Y)
      · exact inC_psi_iff.mpr (Or.inl hzy)
      · exfalso
        have hyz : Le (.Psi ξ κ Y) (.Psi s k a) := le_of_not_ltY he hy hzy
        have hlow : ∀ f, WNF f → Lt f (.Psi ξ κ Y) → inC f a (.Psi s k a) = true :=
          fun f hf hfy => WFY.inC_of_ltY _ hf he (lt_of_lt_of_leY hf hy he hfy hyz)
        have hXa : Le X a := le_of_ne_gtY hX hP.aF hc2.1
        have hzπ : Le (.Psi s k a) π := Or.inr hB2
        have h5 : inC X a (.Psi s k a) = true := by
          rcases h2 h1 hXa hyz with h5 | hkt
          · exact h5
          · exfalso
            have hkκ : Lt k κ := lt_transY hP.piF ht hκF hkt H.tlt
            have hky := coll_psiY hy k hP.piF (hS_k (WFY.inC_of_ltY _ hP.piF ht hkt)) hkκ
            exact hzy (lt_transY he hP.piF hy (lt_psi_targetY he) hky)
        have h6 : inC π a (.Psi s k a) = true :=
          (inC_frY hπF hπF he hX hP.aF ht.psi.Cpi hzπ hXa).mpr fun w hw =>
            hlow w (hπF.of_mem_subs (fr_spec hw).1) (H.hFt w hw)
        exact hc2.2 ⟨h5, inC_zero _ _, h6⟩
    · exact absurd hc3.2.2.1 (not_lt_zero _)
    · have := hc4.2
      rw [inC_zero] at this
      cases this
  · have h0 : lev (.Psi s k a) ≤ lev (.Psi .zero π X) := lev_le_of_lt_gen h1
    have h0' : lev k < lev κ := by
      simp only [lev] at h0
      have := H.hl
      omega
    exact inC_psi_iff.mpr (Or.inl ((lt_principal_iff rfl rfl).mpr (cmpP_of_lev_lt h0')))

/-- `C(X, t)` の元は `C(Y, y)` に入る -/
theorem transfer (H : HullHyp π X ξ κ Y) : ∀ {e : Tm}, WNF e → ArgCond (.Psi .zero π X) X Y e →
    Arg2 (.Psi .zero π X) X (.Psi ξ κ Y) e →
    inC e X (.Psi .zero π X) = true → inC e Y (.Psi ξ κ Y) = true
  | .zero, _, _, _, _ => inC_zero _ _
  | .one, _, _, _, _ => inC_one _ _
  | .K _, _, _, _, _ => inC_K _ _ _
  | .plus a b, he, hc, hd, h => by
    obtain ⟨ha, hb, -, -⟩ := he.plus
    rw [inC_plus, Bool.and_eq_true] at h ⊢
    exact ⟨transfer H ha (hc.sub (subs_plus_l (self_mem_subs a))) (hd.sub (subs_plus_l (self_mem_subs a))) h.1,
      transfer H hb (hc.sub (subs_plus_r (self_mem_subs b))) (hd.sub (subs_plus_r (self_mem_subs b))) h.2⟩
  | .Om a, he, hc, hd, h => by
    rw [inC_om] at h ⊢
    exact transfer H he.om.1 (hc.sub (mem_subs_om a)) (hd.sub (mem_subs_om a)) h
  | .Xi m b, he, hc, hd, h => by
    have hbF := he.xi.2.1
    have hS := transfer H hbF (hc.sub (mem_subs_xi m b)) (hd.sub (mem_subs_xi m b))
    have ht := H.ht
    have hX := H.hX
    have hYF : WNF Y := H.hy.psi.aF
    by_cases h1 : Lt (.Xi m b) (.Psi .zero π X)
    · by_cases hl : lev π = m
      · have hl' : lev κ = m := by rw [← H.hl]; exact hl
        have e1 := (lt_xi_psiY hl).mp h1
        rw [lt_psi_xiY hl] at e1
        refine inC_xi_iff.mpr (Or.inl ((lt_xi_psiY hl').mpr ?_))
        rw [lt_psi_xiY hl']
        rintro (h3 | ⟨h3, h4⟩)
        · exact not_lt_of_leY H.hκF he (le_of_ne_gtY H.hκF he h3) (lt_transY he ht H.hκF h1 H.tlt)
        · by_cases h5 : inC b X (.Psi .zero π X) = true
          · rw [hS h5] at h4
            cases h4
          · exact e1 (Or.inr ⟨lt_of_lt_of_leY hbF hYF hX h3 H.hle, by simpa using h5⟩)
      · have h0 : lev (.Xi m b) ≤ lev (.Psi .zero π X) := lev_le_of_lt_gen h1
        have h0' : m < lev κ := by
          simp only [lev] at h0
          have := H.hl
          omega
        exact inC_xi_iff.mpr (Or.inl ((lt_principal_iff rfl rfl).mpr
          (cmpP_of_lev_lt (y := .Psi ξ κ Y) h0')))
    · rcases inC_xi_iff.mp h with h2 | ⟨h2, h3⟩
      · exact absurd h2 h1
      · exact inC_xi_iff.mpr (Or.inr ⟨hS h2, hc.2 m b (self_mem_subs _) h1 h3⟩)
  | .Psi s k a, he, hc, hd, h => by
    have hP := he.psi
    have hS_k := transfer H hP.piF (hc.sub (subs_psi_p (self_mem_subs k))) (hd.sub (subs_psi_p (self_mem_subs k)))
    have hS_s := transfer H hP.xiF (hc.sub (subs_psi_s (self_mem_subs s))) (hd.sub (subs_psi_s (self_mem_subs s)))
    have hS_a := transfer H hP.aF (hc.sub (subs_psi_a (self_mem_subs a))) (hd.sub (subs_psi_a (self_mem_subs a)))
    have parts : Lt (.Psi .zero π X) k → inC k X (.Psi .zero π X) = true →
        inC s X (.Psi .zero π X) = true → inC a X (.Psi .zero π X) = true → Lt a X →
        inC (.Psi s k a) Y (.Psi ξ κ Y) = true := fun h0 h1 h2 h3 h4 =>
      inC_psi_iff.mpr (Or.inr ⟨hS_k h1, hS_s h2, hS_a h3,
        hc.1 s k a (self_mem_subs _) h0 h4⟩)
    by_cases h1 : Lt (.Psi s k a) (.Psi .zero π X)
    · exact psi_of_lt H he (hd s k a (self_mem_subs _)) hS_k parts h1
    · rcases inC_psi_iff.mp h with h2 | ⟨h2, h3, h4, h5⟩
      · exact absurd h2 h1
      · exact parts (lt_of_le_of_ltY H.ht he hP.piF (le_of_not_ltY he H.ht h1) (lt_psi_targetY he))
          h2 h3 h4 h5

/-- `t` 未満の項は（`ArgCond` のもとで）`y` 未満 -/
theorem lt_of_lt (H : HullHyp π X ξ κ Y) {v : Tm} (hv : WNF v) (hc : ArgCond (.Psi .zero π X) X Y v)
    (hd : Arg2 (.Psi .zero π X) X (.Psi ξ κ Y) v)
    (hlt : Lt v (.Psi .zero π X)) : Lt v (.Psi ξ κ Y) :=
  coll_psiY H.hy v hv (transfer H hv hc hd (WFY.inC_of_ltY _ hv H.ht hlt))
    (lt_transY hv H.ht H.hκF hlt H.tlt)

/-- `X` の前線が `y` 未満なら `Arg2` が成り立つ -/
theorem arg2_of_fr (H : HullHyp π X ξ κ Y) (hF : ∀ f, f ∈ fr π X → Lt f (.Psi ξ κ Y)) {e : Tm}
    (he : WNF e) : Arg2 (.Psi .zero π X) X (.Psi ξ κ Y) e := by
  intro s k a hz hlt hXa hyz
  have hzF : WNF (.Psi s k a) := he.of_mem_subs hz
  have ht := H.ht
  refine Or.inl ((inC_frY H.hX H.hπF hzF H.hX hzF.psi.aF ht.psi.Ca
    (Or.inr (lt_transY hzF ht H.hπF hlt (lt_psi_targetY ht))) hXa).mpr fun w hw => ?_)
  have hwF := H.hX.of_mem_subs (fr_spec hw).1
  exact WFY.inC_of_ltY _ hwF hzF (lt_of_lt_of_leY hwF H.hy hzF (hF w hw) hyz)

end HullHyp

/-! ### 後者の引数：`t` の引数の部分項で `t` 未満のものは種 `Ψ^0_κ(pred X)` 未満 -/

/-- 主要項の部分項は、ある加数の部分項 -/
theorem mem_subs_summand {v : Tm} (hv : isPrincipal v = true) : ∀ {X : Tm}, v ∈ subs X →
    ∃ s, s ∈ summands X ∧ v ∈ subs s
  | .plus a b, h => by
    simp only [subs, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · cases hv
    · exact ⟨a, by rw [summands_plus]; exact List.mem_cons_self, h⟩
    · obtain ⟨s, hs, hvs⟩ := mem_subs_summand hv h
      exact ⟨s, by rw [summands_plus]; exact List.mem_cons_of_mem _ hs, hvs⟩
  | .zero, h => by
    simp only [subs, List.mem_singleton] at h
    rw [h] at hv
    cases hv
  | .one, h => ⟨.one, List.mem_singleton.mpr rfl, h⟩
  | .K n, h => ⟨.K n, List.mem_singleton.mpr rfl, h⟩
  | .Om a, h => ⟨.Om a, List.mem_singleton.mpr rfl, h⟩
  | .Xi m a, h => ⟨.Xi m a, List.mem_singleton.mpr rfl, h⟩
  | .Psi s p a, h => ⟨.Psi s p a, List.mem_singleton.mpr rfl, h⟩

/-- 後者 `X` の節点は `pred X` の部分項 -/
theorem node_mem_subs_pred {X v : Tm} (hX : WNF X) (hs : isSucc X = true) (hv : isPrincipal v = true)
    (hv1 : v ≠ .one) (h : v ∈ subs X) : v ∈ subs (pred X) := by
  obtain ⟨s, hsm, hvs⟩ := mem_subs_summand hv h
  rw [summands_eq_dropLast_one hs] at hsm
  rcases List.mem_append.mp hsm with hsm | hsm
  · exact subs_trans (mem_subs_of_mem_summands (by
      unfold pred
      rw [summands_ofSummands _ (fun x hx => nfl_principal (nfl_summands hX) x (List.dropLast_subset _ hx))]
      exact hsm)) hvs
  · rw [List.mem_singleton] at hsm
    subst hsm
    simp only [subs, List.mem_singleton] at hvs
    exact absurd hvs hv1

/-- 後者の引数：`ArgCond` は大きさの議論で成り立つ -/
theorem argCond_succ {t X : Tm} (hX : WNF X) (hs : isSucc X = true) : ArgCond t X (pred X) X := by
  have hp := wnf_pred hX
  constructor
  · intro s k a hz _ hlt
    have hz' := node_mem_subs_pred hX hs rfl (by intro e; cases e) hz
    have haF := hp.of_mem_subs (subs_trans hz' (subs_psi_a (self_mem_subs a)))
    rcases le_of_lt_succT haF hp (by rw [succT_pred hX hs]; exact hlt) with e | e
    · exfalso
      have e1 := size_le_of_mem_subs hz'
      rw [← e] at e1
      simp only [Tm.size] at e1
      omega
    · exact e
  · intro m b hz _ hlt
    have hz' := node_mem_subs_pred hX hs rfl (by intro e; cases e) hz
    have hbF := hp.of_mem_subs (subs_trans hz' (subs_xi (self_mem_subs b)))
    rcases le_of_lt_succT hbF hp (by rw [succT_pred hX hs]; exact hlt) with e | e
    · exfalso
      have e1 := size_le_of_mem_subs hz'
      rw [← e] at e1
      simp only [Tm.size] at e1
      omega
    · exact e

/-- 後者の引数の崩壊の、種への移し替えの仮定 -/
theorem hullHyp_succ {κ X : Tm} (ht : WNF (.Psi .zero κ X)) (hs : isSucc X = true)
    (hp : WNF (.Psi .zero κ (pred X))) : HullHyp κ X .zero κ (pred X) where
  ht := ht
  hy := hp
  hπκ := Or.inl rfl
  hl := rfl
  hle := Or.inr (pred_lt ht.psi.aF hs)
  hFt f hf := FWOrder.k2t hp f hf

/-- 後者の引数の部分項で `t` 未満のものは種未満 -/
theorem lt_seed_of_sub {κ X v : Tm} (ht : WNF (.Psi .zero κ X)) (hs : isSucc X = true)
    (hp : WNF (.Psi .zero κ (pred X))) (hv : v ∈ subs X) (hlt : Lt v (.Psi .zero κ X)) :
    Lt v (.Psi .zero κ (pred X)) :=
  (hullHyp_succ ht hs hp).lt_of_lt (ht.psi.aF.of_mem_subs hv)
    ((argCond_succ ht.psi.aF hs).sub hv)
    ((hullHyp_succ ht hs hp).arg2_of_fr (fun f hf => by
      have e := succT_pred ht.psi.aF hs
      rw [← e, fr_succT] at hf
      exact FWOrder.k2 hp f hf) (ht.psi.aF.of_mem_subs hv)) hlt

/-- `pred (z + 1) = z` -/
theorem pred_succT {z : Tm} (hz : WNF z) : pred (succT z) = z := by
  unfold pred
  rw [summands_succT, List.dropLast_concat, ofSummands_summands z hz]

/-- `Y` の中の節点の引数は、`Y + 1` 未満なら `Y` 未満（大きさの議論） -/
theorem argCond_pred {t Y : Tm} (hY : WNF Y) : ArgCond t (succT Y) Y Y := by
  constructor
  · intro s k a hz _ hlt
    have haF := hY.of_mem_subs (subs_trans hz (subs_psi_a (self_mem_subs a)))
    rcases le_of_lt_succT haF hY hlt with e | e
    · exfalso
      have e1 := size_le_of_mem_subs hz
      rw [← e] at e1
      simp only [Tm.size] at e1
      omega
    · exact e
  · intro m b hz _ hlt
    have hbF := hY.of_mem_subs (subs_trans hz (subs_xi (self_mem_subs b)))
    rcases le_of_lt_succT hbF hY hlt with e | e
    · exfalso
      have e1 := size_le_of_mem_subs hz
      rw [← e] at e1
      simp only [Tm.size] at e1
      omega
    · exact e

/-- `Y` の部分項で `Ψ^0_κ(Y + 1)` 未満のものは `Ψ^0_κ(Y)` 未満 -/
theorem lt_seed_of_sub_pred {κ Y v : Tm} (_hs : isSucc (succT Y) = true)
    (ht : WNF (.Psi .zero κ (succT Y))) (hY : WNF Y) (hv : v ∈ subs Y)
    (hlt : Lt v (.Psi .zero κ (succT Y))) (hp : WNF (.Psi .zero κ Y)) : Lt v (.Psi .zero κ Y) := by
  have hH : HullHyp κ (succT Y) .zero κ Y :=
    { ht, hy := hp, hπκ := Or.inl rfl, hl := rfl, hle := Or.inr (lt_succT Y)
      hFt := fun f hf => FWOrder.k2t hp f hf }
  exact hH.lt_of_lt (hY.of_mem_subs hv) ((argCond_pred hY).sub hv)
    (hH.arg2_of_fr (fun f hf => by
      rw [fr_succT] at hf
      exact FWOrder.k2 hp f hf) (hY.of_mem_subs hv)) hlt

/-! ### 目標が `Ω_c`：目標の中の部分項 -/

/-- `Ω_c` 未満の主要項で、目標が `Ω_c` の崩壊でないものは `Ψ^0_{Ω_c}(Y)` 未満 -/
theorem lt_psi_om_of_lt_om {c Y v : Tm} (hy : WNF (.Psi .zero (.Om c) Y)) (hv : WNF v)
    (hvp : isPrincipal v = true) (hlt : Lt v (.Om c)) (hne : ∀ s a, v ≠ .Psi s (.Om c) a) :
    Lt v (.Psi .zero (.Om c) Y) := by
  have hP := hy.psi
  have hκF := hP.piF
  have hc := hκF.om.1
  have hcκ : Lt c (.Om c) := hκF.om.2.2
  have hs : isSucc c = true := by
    rcases hP.tgt with ⟨c', e, hs⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, -⟩
    · cases e
      exact hs
    · cases e
    · cases e
  have hc' := wnf_pred hc
  have hc'κ : Lt (pred c) (.Om c) := lt_transY hc' hc hκF (pred_lt hc hs) hcκ
  have hc'y : Lt (pred c) (.Psi .zero (.Om c) Y) := by
    refine coll_psiY hy _ hc' ?_ hc'κ
    refine inC_of_fr_lt hc' hκF hy hP.aF hP.aF (WFY.inC_of_ltY _ hc' hκF hc'κ)
      (Or.inr (lt_psi_targetY hy)) (Or.inl rfl) fun w hw => FWOrder.k2t hy w ?_
    have e := fr_succT (.Om c) (pred c)
    rw [succT_pred hc hs] at e
    show w ∈ fr (.Om c) c
    rw [e]
    exact hw
  have hOF : ∀ {u : Tm}, WNF u → IsOF u → Lt u (.Om c) → Lt u (.Psi .zero (.Om c) Y) := by
    intro u hu hof hlt'
    have h1 : ¬ Lt c u := fun h => Lt.asymmY hu hκF hlt' ((lt_om_OFG hof).mpr h)
    have h2 : Le u c := le_of_not_ltY hc hu h1
    have h3 : u ≠ c := by
      intro e
      subst e
      rw [isSucc_principal hof.principal] at hs
      rcases hof with ⟨n, a, rfl⟩ | ⟨ξ, π, a, rfl, -, -⟩ <;> cases hs
    have h4 : Lt u c := h2.resolve_left h3
    exact lt_of_le_of_ltY hu hc' hy (le_of_lt_succT hu hc' (by rw [succT_pred hc hs]; exact h4)) hc'y
  match v, hv, hvp, hlt, hne with
  | .one, _, _, hlt, _ => exact coll_psiY hy .one WNF.one (inC_one _ _) hlt
  | .K n, hv, _, hlt, _ => exact coll_psiY hy _ hv (inC_K _ _ _) hlt
  | .Om j, hv, _, hlt, _ =>
    have hj := hv.om.1
    exact (lt_om_psiY hy).mpr ((lt_om_iffY hj hc).mp hlt)
  | .Xi m b, hv, _, hlt, _ => exact hOF hv (Or.inl ⟨m, b, rfl⟩) hlt
  | .Psi s p a, hv, _, hlt, hne =>
    by_cases hp : ∃ d, p = .Om d
    · obtain ⟨d, rfl⟩ := hp
      have hPv := hv.psi
      have hs0 : s = .zero := lt_oneY hPv.xiF hPv.mlt
      subst hs0
      have hd := hPv.piF.om.1
      have hne' : d ≠ c := fun e => hne .zero a (by rw [e])
      rcases Nat.lt_trichotomy (lev d) (lev c) with hl | hl | hl
      · exact lt_of_lev_lt' (by simpa [lev] using hl)
      · have h1 : ¬ Lt c d := (lt_psi_om c d a hl.symm).mp hlt
        have h2 : Lt d c := by
          rcases triY hd hc with h | h | h
          · exact h
          · exact absurd h hne'
          · exact absurd h h1
        rw [lt_principal_iff rfl rfl, cmpP_psi_psi (by simpa [lev] using hl), cmpPsi_psi0 hl]
        have hneq : Tm.Psi .zero (.Om d) a ≠ .Psi .zero (.Om c) Y := by
          intro e
          cases e
          exact hne' rfl
        have h2' : cmp d c = .lt := h2
        simp [hneq, h2']
      · have := lev_le_of_lt_gen hlt
        simp only [lev] at this
        omega
    · exact hOF hv (IsOF.psi hv (fun c' e => hp ⟨c', e⟩)) hlt

end RTKA.Fund
