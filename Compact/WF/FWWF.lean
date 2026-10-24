import Compact.WF.FWHyp

/-! 体系全体の整列性（順序の仮定 `FWOrder` の下で、`wellFounded_W`）。

`FZWF.lean` と同じく、`Wmax` が `0`・`1`・`+`・`Ω`・`K_n`・`Ξ_n`・`Ψ^ξ_π` で閉じることを示す。新しいのは、目標を
たどる列（`Ψ^ξ_π(a)`、`π`、`π` の目標、…）の上で `Good` から `Wmax` を導く部分（`H15`）。

* 列の行き着く先が `K_n` のとき（`Ξ_n(b)`）、Mahlo 添字 `b` は `K_n` 以上になりうるので `Wmax` には入っていない。
  そこで `K_n^+` 以下の `C^{K_n}(Wmax)` の元で、`K_n` 以上の節点の引数が `K_n^+` 未満のもの（`WK n`）の整礎性
  （`acc_wk`）を先に示し、`b ∈ WK n` についての帰納法で `Ξ_n(b) ∈ Wmax` を示す（`coll_wk`）。
* 列の行き着く先が `Ξ_j(a)` か `Ψ^ξ_π(a)` のとき、列の上の `Good` な `γ` の Mahlo 添字は `a` 未満の引数の
  崩壊から作られ、引数についての帰納法の仮定で `WK n` に入る。Mahlo 添字は列の上で真に減るので、Mahlo 添字に
  ついての帰納法で `γ ∈ Wmax`（`mahlo_step`）。
* 主定理は、`K_n` について帰納法で `Good K_n`・`acc_wk`・`coll_wk`・`K_n ∈ Wmax` を順に示し、最後に項の構造に
  ついての帰納法でまとめる。 -/

namespace RTKA.W.WFY

open Tm
open WFX (fr_mem_psi_p)

variable [FWOrder]

/-! ### 基本の項 -/

omit [FWOrder] in
theorem not_tgt_of_shape {t : Tm} (h0 : ∀ c, t ≠ .Om c) (h1 : ∀ n p, t ≠ .Xi n p)
    (h2 : ∀ ζ κ b, t ≠ .Psi ζ κ b) : ¬ IsTgt t := by
  rintro (⟨c, e, -⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, -⟩)
  · exact h0 c e
  · exact h1 n p e
  · exact h2 ζ κ b e

theorem wmax_zero : Wmax .zero :=
  wmax_of_good_nt ⟨Hull.zero, fun _ _ h => absurd h (not_lt_zero _)⟩
    (not_tgt_of_shape (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ _ e => by cases e))
    (fun _ e => by cases e)

theorem wmax_one : Wmax .one :=
  wmax_of_good_nt ⟨Hull.one, fun _ hβ h => by
    have := lt_oneY hβ.wf_of h
    subst this
    exact wmax_zero⟩
    (not_tgt_of_shape (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ _ _ e => by cases e))
    (fun _ e => by cases e)

theorem wmax_add {a b : Tm} (hw : WNF (.plus a b)) (ha : Wmax a) (hb : Wmax b) :
    Wmax (.plus a b) := by
  have key : ∀ b, Acc (Rel Wmax) b → Wmax b → WNF (.plus a b) → Wmax (.plus a b) := by
    intro b hacc
    induction hacc with
    | intro b _ ih =>
      intro hb hw
      have hn := nr_specY _ hw
      have hap := hw.plus.2.2.1
      have ha_lt := lt_transY (wmax_wf ha) hw hn.1 (lt_plus_leftY hw) hn.2.2
      refine wmax_of_good_nt ⟨Hull.plus hw (wmax_hull ha hw) (wmax_hull hb hw), ?_⟩
        (not_tgt_of_shape (fun _ e => by cases e) (fun _ _ e => by cases e)
          (fun _ _ _ e => by cases e)) (fun _ e => by cases e)
      intro γ hγ hγlt
      have wγ := hγ.wf_of
      cases γ with
      | zero => exact wmax_zero
      | plus γ₁ γ₂ =>
        by_cases e : γ₁ = a
        · subst e
          have hγlt' := lt_plus_plus_same.mp hγlt
          cases hγ with
          | mem hX _ _ => exact hX
          | plus hw' _ hγ₂ =>
            have hγ₂W := wmax_bounded hw hγ₂ hb (Or.inr hγlt')
              (lt_transY (wmax_wf hb) hw hn.1 (lt_plus_rightY hw) hn.2.2)
            exact ih γ₂ ⟨hγ₂W, hγlt'⟩ hγ₂W hw'
        · exact wmax_bounded hw hγ ha
            (Or.inr ((lt_plus_prin_iffY wγ hap).mpr ((lt_plus_plus_neY wγ hw e).mp hγlt))) ha_lt
      | _ => exact wmax_bounded hw hγ ha ((lt_prin_plus_iffY wγ rfl hw).mp hγlt) ha_lt
  exact key b (wmax_acc hb) hb hw

theorem wmax_om : ∀ c, Wmax c → WNF (.Om c) → Wmax (.Om c) := by
  have key : ∀ c, Acc (Rel Wmax) c → Wmax c → WNF (.Om c) → Wmax (.Om c) := by
    intro c hacc
    induction hacc with
    | intro c _ ihc =>
      intro hc hw
      have hn := nr_specY _ hw
      have wc := wmax_wf hc
      have hc_lt := lt_transY wc hw hn.1 hw.om.2.2 hn.2.2
      have hG : Good (.Om c) := by
        refine ⟨Hull.om hw (wmax_hull hc hw), ?_⟩
        intro β
        induction β using size_induction with
        | h β ihβ =>
          intro hβ hβlt
          have below : ∀ x, WNF x → Lt x β → Lt x (.Om c) :=
            fun x wx h => lt_transY wx hβ.wf_of hw h hβlt
          cases hβ with
          | zero => exact wmax_zero
          | one => exact wmax_one
          | K hn' =>
            exact wmax_bounded hw (Hull.K hn') hc (Or.inr ((lt_K_omY hn' wc).mp hβlt)) hc_lt
          | mem hX _ _ => exact hX
          | plus hw' hb₁ hb₂ =>
            exact wmax_add hw'
              (ihβ _ (by size_omega) hb₁ (below _ hw'.plus.1 (lt_plus_leftY hw')))
              (ihβ _ (by size_omega) hb₂ (below _ hw'.plus.2.1 (lt_plus_rightY hw')))
          | om hw' hd =>
            have hdW := ihβ _ (by size_omega) hd (below _ hw'.om.1 hw'.om.2.2)
            exact ihc _ ⟨hdW, (lt_om_iffY hw'.om.1 wc).mp hβlt⟩ hdW hw'
          | @xi n d hw' hK hd =>
            exact wmax_bounded hw (Hull.xi hw' hK hd) hc
              (Or.inr ((lt_OF_omG (Or.inl ⟨n, d, rfl⟩) hw' wc).mp hβlt)) hc_lt
          | @psi s π d hw' hσ hs hπ hd =>
            rcases hw'.shape with ⟨c', rfl, rfl⟩ | hsh
            · exact absurd ((lt_om_iffY wc hw'.psiOm.1).mp hσ)
                (not_lt_of_leY hw'.psiOm.1 wc ((lt_psi_omY hw' wc).mp hβlt))
            · exact wmax_bounded hw (Hull.psi hw' hσ hs hπ hd) hc
                (Or.inr ((lt_OF_omG (IsOF.psi hw' (notOm_of_shape hsh)) hw' wc).mp hβlt)) hc_lt
      exact wmax_of_good_hyp hG (hyp_of_good hG (h15_om c))
  intro c hc
  exact key c (wmax_acc hc) hc

/-- `K_n` 未満の `C^{K_n}(Wmax)` の元は `Wmax` に入る（`K_j`（`j < n`）が `Wmax` に入るとき） -/
theorem goodK {n : Nat} (hn : 1 ≤ n) (ihK : ∀ j, 1 ≤ j → j < n → Wmax (.K j)) :
    Good (.K n) := by
  have hw := WNF.K' hn
  refine ⟨Hull.K hn, ?_⟩
  intro β
  induction β using size_induction with
  | h β ihβ =>
    intro hβ hβlt
    have below : ∀ x, WNF x → Lt x β → Lt x (.K n) :=
      fun x wx h => lt_transY wx hβ.wf_of hw h hβlt
    cases hβ with
    | zero => exact wmax_zero
    | one => exact wmax_one
    | @K j hj =>
      have h1 := (lt_K_iffY (WNF.K' hj) hn).mp hβlt
      simp only [lev] at h1
      exact ihK j hj (by omega)
    | mem hX _ _ => exact hX
    | plus hw' hb₁ hb₂ =>
      exact wmax_add hw'
        (ihβ _ (by size_omega) hb₁ (below _ hw'.plus.1 (lt_plus_leftY hw')))
        (ihβ _ (by size_omega) hb₂ (below _ hw'.plus.2.1 (lt_plus_rightY hw')))
    | om hw' hd =>
      exact wmax_om _ (ihβ _ (by size_omega) hd (below _ hw'.om.1 hw'.om.2.2)) hw'
    | xi hw' hK _ =>
      exfalso
      have h1 := (lt_K_iffY hw' hn).mp hβlt
      have h2 := (lt_K_iffY hw hw'.xi.1).mp hK
      simp only [lev] at h1 h2
      omega
    | psi hw' hσ _ _ _ =>
      exfalso
      have h1 := (lt_K_iffY hw' hn).mp hβlt
      have h2 := lev_le_of_lt_gen hσ
      simp only [lev] at h1 h2
      omega


/-! ### `K_n^+` 以下の Mahlo 添字の範囲 `WK n` -/

/-- `K_n^+` 以下の `C^{K_n}(Wmax)` の元で、`K_n` 以上の節点の引数が `K_n^+` 未満のもの -/
def WK (n : Nat) (x : Tm) : Prop :=
  Hull (.K n) Wmax x ∧ inC x (succK n) (.K n) = true ∧ Le x (succK n)

theorem WK.wf {n : Nat} {x : Tm} (h : WK n x) : WNF x := h.1.wf_of

omit [FWOrder] in
theorem nrY_K (n : Nat) : nrY (.K n) = succK n := rfl

theorem succK_WNF {n : Nat} (hn : 1 ≤ n) : WNF (succK n) := WNF.om_succT (WNF.K' hn)

theorem K_lt_succK {n : Nat} (hn : 1 ≤ n) : Lt (.K n) (succK n) := (nr_specY _ (WNF.K' hn)).2.2

/-- `x < d` なら `x ∈ C(g, d)` -/
theorem inC_of_ltY : ∀ {x : Tm} (g : Tm) {d : Tm}, WNF x → WNF d → Lt x d → inC x g d = true
  | .zero, _, _, _, _, _ => inC_zero _ _
  | .one, _, _, _, _, _ => inC_one _ _
  | .K _, _, _, _, _, _ => inC_K _ _ _
  | .plus a b, g, d, hx, hd, h => by
    obtain ⟨ha, hb, -, -⟩ := hx.plus
    rw [inC_plus, inC_of_ltY g ha hd (lt_transY ha hx hd (lt_plus_leftY hx) h),
      inC_of_ltY g hb hd (lt_transY hb hx hd (lt_plus_rightY hx) h)]
    rfl
  | .Om a, g, d, hx, hd, h => by
    rw [inC_om]
    exact inC_of_ltY g hx.om.1 hd (lt_transY hx.om.1 hx hd hx.om.2.2 h)
  | .Xi m a, _, _, _, _, h => inC_of_lt_node (Or.inl ⟨m, a, rfl⟩) h
  | .Psi s p a, _, _, _, _, h => inC_of_lt_node (Or.inr ⟨s, p, a, rfl⟩) h

theorem hull_plus_inv {α a b : Tm} (wα : WNF α) (h : Hull α Wmax (.plus a b)) :
    Hull α Wmax a ∧ Hull α Wmax b := by
  cases h with
  | mem hX _ _ =>
    have hG := wmax_good hX
    cases hG.1 with
    | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
    | plus hw' ha hb =>
      exact ⟨wmax_hull (hG.2 _ ha (lt_plus_leftY hw')) wα,
        wmax_hull (hG.2 _ hb (lt_plus_rightY hw')) wα⟩
  | plus _ ha hb => exact ⟨ha, hb⟩

theorem WK.plus {n : Nat} (hn : 1 ≤ n) {a b : Tm} (h : WK n (.plus a b)) : WK n a ∧ WK n b := by
  have wx := h.wf
  have wS := succK_WNF hn
  obtain ⟨ha, hb⟩ := hull_plus_inv (WNF.K' hn) h.1
  have hC := h.2.1
  rw [inC_plus, Bool.and_eq_true] at hC
  exact ⟨⟨ha, hC.1, Or.inr (lt_of_lt_of_leY wx.plus.1 wx wS (lt_plus_leftY wx) h.2.2)⟩,
    ⟨hb, hC.2, Or.inr (lt_of_lt_of_leY wx.plus.2.1 wx wS (lt_plus_rightY wx) h.2.2)⟩⟩

theorem WK.psi_arg {n : Nat} {σ κ d : Tm} (h : WK n (.Psi σ κ d))
    (hK : ¬ Lt (.Psi σ κ d) (.K n)) : WK n d ∧ Lt d (succK n) := by
  have hd : Hull (.K n) Wmax d := by
    cases h.1 with
    | mem _ _ hlt => exact absurd hlt hK
    | psi _ _ _ _ hd => exact hd
  rcases inC_psi_iff.mp h.2.1 with h' | ⟨-, -, hdC, hdS⟩
  · exact absurd h' hK
  · exact ⟨⟨hd, hdC, Or.inr hdS⟩, hdS⟩

/-! #### `K_n^+` 未満の項の形 -/

theorem om_lt_succK {n : Nat} (hn : 1 ≤ n) {c : Tm} (hw : WNF (.Om c))
    (h : Lt (.Om c) (succK n)) : Lt (.Om c) (.K n) := by
  have wc := hw.om.1
  have wK := WNF.K' hn
  have wS := succT_WNF wK
  have hc : Lt c (succT (.K n)) := (lt_om_iffY wc wS).mp h
  have hcK : Lt c (.K n) := by
    rcases triY wc wK with h' | e | h'
    · exact h'
    · exact absurd e hw.om_ne_k
    · exact absurd hc (not_lt_of_leY wS wc (succT_leY wK wc h'))
  rw [lt_K_iffY hw hn]
  exact (lt_K_iffY wc hn).mp hcK

theorem K_lt_of_lev {n : Nat} (hn : 1 ≤ n) {x : Tm} (hx : WNF x) (hl : lev x = n + 1)
    (hne : x ≠ .K n) : Lt (.K n) x := by
  rcases triY (WNF.K' hn) hx with h | e | h
  · exact h
  · exact absurd e.symm hne
  · have := (lt_K_iffY hx hn).mp h; omega

theorem xi_le_succK {n m : Nat} (hn : 1 ≤ n) {d : Tm} (hw : WNF (.Xi m d))
    (h : Le (.Xi m d) (succK n)) : Lt (.Xi m d) (.K n) := by
  have wS := succK_WNF hn
  have hl : m ≤ n + 1 := by
    rcases h with e | h
    · cases e
    · have := lev_le_of_lt_gen h; simpa [lev, succK] using this
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · exact (lt_K_iffY hw hn).mpr (by simp only [lev]; omega)
  · exfalso
    subst hl
    have h1 : Lt (.K n) (.Xi (n + 1) d) := K_lt_of_lev hn hw (by simp [lev]) (fun e => by cases e)
    have h2 : Lt (succT (.K n)) (.Xi (n + 1) d) :=
      (lt_plus_prin_iffY (succT_WNF (WNF.K' hn)) rfl).mpr h1
    have h3 : Lt (succK n) (.Xi (n + 1) d) := (lt_om_OFG (Or.inl ⟨n + 1, d, rfl⟩)).mpr h2
    exact not_lt_of_leY hw wS h h3

theorem K_le_succK {n m : Nat} (h : Le (.K m) (succK n)) : m ≤ n := by
  rcases h with e | h
  · cases e
  · have := lev_le_of_lt_gen h; simp [lev, succK] at this; omega

/-- `K_n ≤ Ψ^σ_κ(d) < K_n^+` なら `κ = K_n^+`、`σ = 0` -/
theorem psi_lt_succK {n : Nat} (hn : 1 ≤ n) {σ κ d : Tm} (hw : WNF (.Psi σ κ d))
    (h : Lt (.Psi σ κ d) (succK n)) (hK : ¬ Lt (.Psi σ κ d) (.K n)) :
    κ = succK n ∧ σ = .zero := by
  have wK := WNF.K' hn
  have wS1 := succT_WNF wK
  have hl1 : lev κ ≤ n + 1 := by have := lev_le_of_lt_gen h; simpa [lev, succK] using this
  have hl2 : n + 1 ≤ lev κ := by
    apply Nat.le_of_not_lt
    intro hc
    exact hK ((lt_K_iffY hw hn).mpr (by simp only [lev]; omega))
  rcases hw.shape with ⟨c, rfl, rfl⟩ | hsh
  · obtain ⟨wc, -, hs, -, -, -⟩ := hw.psiOm
    have hcS : Le c (succT (.K n)) := (lt_psi_omY hw wS1).mp h
    have hlc : lev c = n + 1 := by simp only [lev] at hl1 hl2; omega
    have hKc : Lt (.K n) c := by
      rcases triY wK wc with h' | e | h'
      · exact h'
      · subst e; simp [isSucc, summands] at hs
      · have := (lt_K_iffY wc hn).mp h'; omega
    have := le_antisymmY wc wS1 hcS (succT_leY wK wc hKc)
    subst this
    exact ⟨rfl, rfl⟩
  · exfalso
    have hO := IsOF.psi hw (notOm_of_shape hsh)
    have h1 : Lt (.Psi σ κ d) (succT (.K n)) := (lt_OF_omG hO hw wS1).mp h
    rcases (lt_prin_plus_iffY hw rfl wS1).mp h1 with e | h2
    · cases e
    · exact hK h2

/-! #### `WK n` の整礎性 -/

theorem acc_wk_of_wmax {n : Nat} (hn : 1 ≤ n) {x : Tm} (hx : Wmax x) (h : Lt x (succK n)) :
    Acc (Rel (WK n)) x :=
  acc_of_below (fun _ h => h.wf) x (wmax_acc hx) (wmax_wf hx)
    (fun _ hy hyx => wmax_bounded (WNF.K' hn) hy.1 hx (Or.inr hyx) (by rw [nrY_K]; exact h))

theorem acc_wk_of_ltK {n : Nat} (hn : 1 ≤ n) (hG : Good (.K n)) {x : Tm} (hx : WK n x)
    (h : Lt x (.K n)) : Acc (Rel (WK n)) x :=
  acc_wk_of_wmax hn (hG.2 x hx.1 h)
    (lt_transY hx.wf (WNF.K' hn) (succK_WNF hn) h (K_lt_succK hn))

theorem acc_wk_K {n : Nat} (hn : 1 ≤ n) (hG : Good (.K n)) : Acc (Rel (WK n)) (.K n) :=
  Acc.intro _ (fun _ hy => acc_wk_of_ltK hn hG hy.1 hy.2)

theorem acc_wk_plus {n : Nat} (hn : 1 ≤ n) : ∀ v, Acc (Rel (WK n)) v → ∀ u,
    Acc (Rel (WK n)) u → WNF (.plus u v) → Acc (Rel (WK n)) (.plus u v) := by
  intro v hacc
  induction hacc with
  | intro v _ ih =>
    intro u hu hw
    have hup := hw.plus.2.2.1
    refine Acc.intro _ (fun y hyr => ?_)
    obtain ⟨hy, hyl⟩ := hyr
    have wy := hy.wf
    cases y with
    | zero => exact Acc.intro _ (fun z hz => absurd hz.2 (not_lt_zero _))
    | plus y₁ y₂ =>
      by_cases e : y₁ = u
      · subst e
        exact ih y₂ ⟨(hy.plus hn).2, lt_plus_plus_same.mp hyl⟩ y₁ hu wy
      · exact hu.inv ⟨hy, (lt_plus_prin_iffY wy hup).mpr ((lt_plus_plus_neY wy hw e).mp hyl)⟩
    | _ =>
      rcases (lt_prin_plus_iffY wy rfl hw).mp hyl with e | h
      · rw [e]; exact hu
      · exact hu.inv ⟨hy, h⟩

omit [FWOrder] in
theorem fr_succK_self (n : Nat) : fr (succK n) (succK n) = [] := by
  simp [fr, succK, succT]

/-- `K_n^+` を目標とする崩壊：`d ∈ WK n` が整礎なら `Ψ^0_{K_n^+}(d)` も -/
theorem acc_psiK {n : Nat} (hn : 1 ≤ n) (hG : Good (.K n)) :
    ∀ d, Acc (Rel (WK n)) d → WK n d → Lt d (succK n) → WNF (.Psi .zero (succK n) d) →
      Acc (Rel (WK n)) (.Psi .zero (succK n) d) := by
  have wS := succK_WNF hn
  intro d hacc
  induction hacc with
  | intro d hd' ihd =>
    intro hd hdS hw
    have wd := hd.wf
    have hψS : Lt (.Psi .zero (succK n) d) (succK n) := lt_psi_targetY hw
    refine Acc.intro _ (fun y hyr => ?_)
    obtain ⟨hy, hyl⟩ := hyr
    revert hy hyl
    induction y using size_induction with
    | h y ihy =>
    intro hy hyl
    have wy := hy.wf
    by_cases hyK : Lt y (.K n)
    · exact acc_wk_of_ltK hn hG hy hyK
    have hyS : Lt y (succK n) := lt_transY wy hw wS hyl hψS
    cases y with
    | zero => exact absurd ((lt_K_iffY wy hn).mpr (by simp [lev])) hyK
    | one => exact absurd ((lt_K_iffY wy hn).mpr (by simp [lev]; omega)) hyK
    | K m =>
      have hm := K_le_succK (Or.inr hyS)
      rcases Nat.lt_or_eq_of_le hm with hm | rfl
      · exact absurd ((lt_K_iffY wy hn).mpr (by simp [lev]; omega)) hyK
      · exact acc_wk_K hn hG
    | plus y₁ y₂ =>
      have h12 := hy.plus hn
      have h1 : Lt y₁ (.Psi .zero (succK n) d) := (lt_plus_prin_iffY wy rfl).mp hyl
      have h2 : Lt y₂ (.Psi .zero (succK n) d) :=
        lt_transY wy.plus.2.1 wy hw (lt_plus_rightY wy) hyl
      exact acc_wk_plus hn y₂ (ihy y₂ (by size_omega) h12.2 h2) y₁
        (ihy y₁ (by size_omega) h12.1 h1) wy
    | Om c => exact absurd (om_lt_succK hn wy hyS) hyK
    | Xi m e => exact absurd (xi_le_succK hn wy (Or.inr hyS)) hyK
    | Psi σ κ e =>
      obtain ⟨rfl, rfl⟩ := psi_lt_succK hn wy hyS hyK
      obtain ⟨he, heS⟩ := hy.psi_arg hyK
      have we := he.wf
      rcases (lt_psi_psiY rfl hyl.ne).mp hyl with
        h1 | ⟨-, -, (⟨hed, -, -, -⟩ | ⟨hde, hn'⟩ | ⟨-, -, h0, -⟩ | ⟨h0, -⟩)⟩
      · exact absurd hψS h1
      · exact ihd e ⟨he, hed⟩ he heS wy
      · obtain ⟨w, hwfr, hwn⟩ := wit_c2 hw wy we (le_of_ne_gtY wd we hde) hyS hn'
        rcases hwfr with hwfr | hwfr | hwfr
        · have hwd := fr_leY wS wd hwfr
          have wW : WNF w := wd.of_mem_subs (fr_spec hwfr).1
          rcases le_transY wy wW wd (le_of_not_ltY wW wy hwn) hwd with e' | h'
          · rw [e']; exact Acc.intro d hd'
          · exact hd' _ ⟨hy, h'⟩
        · rw [fr_succK_self] at hwfr; cases hwfr
        · simp [fr] at hwfr
      · exact absurd h0 (Lt.irrefl _)
      · exact absurd h0 (Lt.irrefl _)

/-- `WK n` は整礎 -/
theorem acc_wk {n : Nat} (hn : 1 ≤ n) (hG : Good (.K n)) :
    ∀ x, WK n x → Acc (Rel (WK n)) x := by
  have key : ∀ x, WK n x → Lt x (succK n) → Acc (Rel (WK n)) x := by
    intro x
    induction x using size_induction with
    | h x ih =>
    intro hx hxS
    have wx := hx.wf
    by_cases hxK : Lt x (.K n)
    · exact acc_wk_of_ltK hn hG hx hxK
    cases x with
    | zero => exact absurd ((lt_K_iffY wx hn).mpr (by simp [lev])) hxK
    | one => exact absurd ((lt_K_iffY wx hn).mpr (by simp [lev]; omega)) hxK
    | K m =>
      have hm := K_le_succK (Or.inr hxS)
      rcases Nat.lt_or_eq_of_le hm with hm | rfl
      · exact absurd ((lt_K_iffY wx hn).mpr (by simp [lev]; omega)) hxK
      · exact acc_wk_K hn hG
    | plus a b =>
      have hab := hx.plus hn
      have wS := succK_WNF hn
      exact acc_wk_plus hn b (ih b (by size_omega) hab.2
          (lt_transY wx.plus.2.1 wx wS (lt_plus_rightY wx) hxS)) a
        (ih a (by size_omega) hab.1 (lt_transY wx.plus.1 wx wS (lt_plus_leftY wx) hxS)) wx
    | Om c => exact absurd (om_lt_succK hn wx hxS) hxK
    | Xi m e => exact absurd (xi_le_succK hn wx (Or.inr hxS)) hxK
    | Psi σ κ e =>
      obtain ⟨rfl, rfl⟩ := psi_lt_succK hn wx hxS hxK
      obtain ⟨he, heS⟩ := hx.psi_arg hxK
      exact acc_psiK hn hG e (ih e (by size_omega) he heS) he heS wx
  intro x hx
  rcases hx.2.2 with e | h
  · subst e
    exact Acc.intro _ (fun y hy => key y hy.1 hy.2)
  · exact key x hx h


/-! ### 崩壊の閉包のための補題 -/

omit [FWOrder] in
theorem WNF.mi {π : Tm} (h : WNF π) : WNF (mi π) := by
  cases π with
  | Om _ => exact WNF.one
  | Xi _ _ => exact h.xi.2.1
  | Psi _ _ _ => exact h.psi.xiF
  | _ => exact WNF.zero

theorem inC_mono_d {x g d d' : Tm} (hx : WNF x) (hd : WNF d) (hd' : WNF d') (hle : Le d d')
    (h : inC x g d = true) : inC x g d' = true :=
  inC_mono x g d g d' h (fun v hv hvd => lt_of_lt_of_leY (hx.of_mem_subs hv) hd hd' hvd hle)
    (fun _ _ h => h)

theorem inC_mono_g {x g g' d : Tm} (hx : WNF x) (hg : WNF g) (hg' : WNF g') (hle : Le g g')
    (h : inC x g d = true) : inC x g' d = true :=
  inC_mono x g d g' d h (fun _ _ h => h)
    (fun v hv hvg => lt_of_lt_of_leY (hx.of_mem_subs hv) hg hg' hvg hle)

theorem succK_mono {j n : Nat} (hj : 1 ≤ j) (h : j ≤ n) : Le (succK j) (succK n) := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact Or.inr (lt_of_lev_lt' (by simp [lev, succK]; omega))
  · exact Or.inl rfl

theorem K_le_K {j n : Nat} (h : j ≤ n) : Le (.K j) (.K n) := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact Or.inr (lt_of_lev_lt' (by simp [lev]; omega))
  · exact Or.inl rfl

/-- 列の上で Mahlo 添字は減る：`x` から `Ψ^ζ_ρ(b)` に至る列なら `x = Ψ^{ζ'}_{ρ'}(b')` で `m(ρ') ≤ m(ρ)` -/
theorem Ch.mahlo {x y : Tm} (h : Ch x y) (hx : WNF x) :
    ∀ ζ ρ b, y = .Psi ζ ρ b → ∃ ζ' ρ' b', x = .Psi ζ' ρ' b' ∧ Le (mi ρ') (mi ρ) := by
  induction h with
  | refl => intro ζ ρ b e; exact ⟨ζ, ρ, b, e, Or.inl rfl⟩
  | step h' ih =>
    intro ζ ρ b e
    obtain ⟨ζ', ρ', b', hx', hle⟩ := ih _ _ _ rfl
    subst e
    have w0 := h'.wnf hx
    have wρ0 := w0.psi.piF
    have wx' : WNF (.Psi ζ' ρ' b') := hx' ▸ hx
    exact ⟨ζ', ρ', b', hx', Or.inr (lt_of_le_of_ltY (WNF.mi wx'.psi.piF) wρ0.psi.xiF (WNF.mi wρ0.psi.piF)
      hle wρ0.psi.mlt)⟩

/-- `Ξ_j(d) < π`（`π` は `Ω_c` 以外の目標、階 `j`）、`π ∈ C(a, π)`、`a ≤ d` なら、`π` の前線（`π` について）に
    `Ξ_j(d)` 未満でない元がある -/
theorem wit_xi_tgt : ∀ π : Tm, WNF π →
    ((∃ n p, π = .Xi n p) ∨ ∃ ζ κ b, π = .Psi ζ κ b ∧ ζ ≠ .zero) →
    ∀ {j : Nat} {d a : Tm}, WNF (.Xi j d) → WNF a → Lt (.Xi j d) π → lev π = j →
      inC π a π = true → Le a d → ∃ w, w ∈ fr π π ∧ ¬ Lt w (.Xi j d) := by
  intro π
  induction π using size_induction with
  | h π ih =>
  intro wπ hsh j d a wx wa hlt hl hC had
  have wd := wx.xi.2.1
  rcases hsh with ⟨m, q, rfl⟩ | ⟨ζ, κ, b, rfl, hζ⟩
  · simp only [lev] at hl
    subst hl
    have wq := wπ.xi.2.1
    rcases inC_xi_iff.mp hC with h | ⟨-, hqa⟩
    · exact absurd h (Lt.irrefl _)
    have hqd : Lt q d := lt_of_lt_of_leY wq wa wd hqa had
    have hne : d ≠ q := fun e => by subst e; exact Lt.irrefl _ hqd
    rcases (ff_xiY wx wπ hne).mp hlt with ⟨hdq, -⟩ | ⟨-, w, hwfr, hwn⟩
    · exact absurd hdq (Lt.asymmY wq wd hqd)
    · refine ⟨w, ?_, hwn⟩
      rw [fr]
      simp only [Lt.irrefl, ↓reduceIte]
      exact fr_sub (WNF.K' wπ.xi.1) wπ (Or.inr ((lt_K_iffY wπ wπ.xi.1).mpr (Nat.le_refl _))) wq
        hwfr (FWOrder.k2x wπ w hwfr)
  · have wκ := wπ.psi.piF
    have hlκ : lev κ = j := hl
    have hxκ : Lt (.Xi j d) κ := by
      have h1 := (lt_xi_psiY (π := κ) hlκ).mp hlt
      rw [lt_psi_xiY hlκ] at h1
      cases e : cmp κ (.Xi j d) with
      | gt => exact lt_of_gtY wκ wx e
      | _ => exact absurd (Or.inl (by rw [e]; decide)) h1
    have hπκ : Lt (.Psi ζ κ b) κ := lt_psi_targetY wπ
    have hκC : inC κ a κ = true := by
      rcases inC_psi_iff.mp hC with h | ⟨h, -, -, -⟩
      · exact absurd h (Lt.irrefl _)
      · exact inC_mono_d wκ wπ wκ (Or.inr hπκ) h
    have hshκ : (∃ n p, κ = .Xi n p) ∨ ∃ ζ' κ' b', κ = .Psi ζ' κ' b' ∧ ζ' ≠ .zero := by
      rcases wπ.shape with ⟨c, rfl, e⟩ | h | h
      · exact absurd e hζ
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨w, hwfr, hwn⟩ := ih κ (by size_omega) wκ hshκ wx wa hxκ hlκ hκC had
    refine ⟨w, fr_mem_psi_p (Lt.irrefl _) ?_, hwn⟩
    exact fr_sub wκ wπ (Or.inr hπκ) wκ hwfr (FWOrder.k2t wπ w hwfr)

/-- `b` を引数とする崩壊が `Wmax` に入る（階 `n` 以下、Mahlo 添字は `WK n`） -/
def CollOK (n : Nat) (b : Tm) : Prop :=
  (∀ j, 1 ≤ j → j ≤ n → WNF (.Xi j b) → Wmax (.Xi j b)) ∧
    (∀ ξ π, WK n ξ → Wmax π → Lt π (.K n) → WNF (.Psi ξ π b) → Wmax (.Psi ξ π b))

/-- 係数についての帰納法で使う性質 -/
def PK (n : Nat) (x : Tm) : Prop :=
  Hull (.K n) Wmax x ∧ (Le x (succK n) → inC x (succK n) (.K n) = true)

/-- `C^{K_n}(Wmax)` の元の前線（`K_n` 以下の `R` について）は `Wmax` に入る -/
theorem fr_hullK {n : Nat} (hn : 1 ≤ n) (hG : Good (.K n)) {x R : Tm}
    (hx : Hull (.K n) Wmax x) (wR : WNF R) (hR : Le R (.K n)) :
    ∀ w, w ∈ fr R x → Wmax w := by
  intro w hw
  rcases fr_hull_wmax (fun m hm _ => fr_wmax wR m hm) x hx w hw with h | h
  · exact h
  · exact hG.2 w h (lt_of_lt_of_leY (hx.wf_of.of_mem_subs (fr_spec hw).1) wR (WNF.K' hn)
      (fr_spec hw).2 hR)

/-- 係数についての帰納法（引数 `a` 未満の引数の崩壊が `Wmax` に入るとき） -/
theorem coeffK {n : Nat} (hn : 1 ≤ n) (hG : Good (.K n)) {a : Tm} (ha : WK n a)
    (MIH : ∀ b, WK n b → Lt b a → CollOK n b) {θ R g : Tm} (wθ : WNF θ) (hθK : Lt θ (.K n))
    (wg : WNF g) (hga : Le g a) (S : Nat)
    (good : ∀ x, Hull θ Wmax x → Lt x θ → x.size < S → Wmax x) :
    ∀ x, Hull θ Wmax x → x.size < S → (∀ w, w ∈ fr R x → Lt w θ) → inC x g R = true →
      PK n x := by
  have wK := WNF.K' hn
  have wS := succK_WNF hn
  have wa := ha.wf
  have hgS : ∀ {d}, WNF d → Lt d g → Lt d (succK n) := fun wd h =>
    lt_of_lt_of_leY wd wg wS h (le_transY wg wa wS hga ha.2.2)
  refine coeff_induction (PK n) S
    (fun x hx hxθ hs => ⟨wmax_hull (good x hx hxθ hs) wK,
      fun _ => inC_of_ltY _ hx.wf_of wK (lt_transY hx.wf_of wθ wK hxθ hθK)⟩)
    ⟨Hull.zero, fun _ => inC_zero _ _⟩ ⟨Hull.one, fun _ => inC_one _ _⟩
    (fun hj => ⟨Hull.K hj, fun _ => inC_K _ _ _⟩) ?_ ?_ ?_ ?_
  · intro a' b' hw h1 h2
    refine ⟨Hull.plus hw h1.1 h2.1, fun hle => ?_⟩
    rw [inC_plus, Bool.and_eq_true]
    exact ⟨h1.2 (Or.inr (lt_of_lt_of_leY hw.plus.1 hw wS (lt_plus_leftY hw) hle)),
      h2.2 (Or.inr (lt_of_lt_of_leY hw.plus.2.1 hw wS (lt_plus_rightY hw) hle))⟩
  · intro a' hw h1
    refine ⟨Hull.om hw h1.1, fun hle => ?_⟩
    rw [inC_om]
    exact h1.2 (Or.inr (lt_of_lt_of_leY hw.om.1 hw wS hw.om.2.2 hle))
  · intro j d hw hdg hd
    have wd := hw.xi.2.1
    have hj := hw.xi.1
    by_cases hjn : j ≤ n
    · have hnode : Lt (.Xi j d) (.K n) := (lt_K_iffY hw hn).mpr hjn
      have hdS : Le d (succK n) :=
        le_transY wd (succK_WNF hj) wS (le_of_ne_gtY wd (succK_WNF hj) hw.xi.2.2.2.1)
          (succK_mono hj hjn)
      have hW : Wmax (.Xi j d) :=
        (MIH d ⟨hd.1, hd.2 hdS, hdS⟩ (lt_of_lt_of_leY wd wg wa hdg hga)).1 j hj hjn hw
      exact ⟨wmax_hull hW wK, fun _ => inC_of_ltY _ hw wK hnode⟩
    · have hKj : Lt (.K n) (.K j) := lt_of_lev_lt' (by simp [lev]; omega)
      refine ⟨Hull.xi hw hKj hd.1, fun hle => ?_⟩
      have := (lt_K_iffY hw hn).mp (xi_le_succK hn hw hle)
      simp only [lev] at this
      exact absurd this hjn
  · intro σ κ d hw hdg hσ hκ hd
    have hP := hw.psi
    have wd := hP.aF
    have hdS : Lt d (succK n) := hgS wd hdg
    by_cases hnode : Lt (.Psi σ κ d) (.K n)
    · have hσd : Le σ d := le_of_ne_gtY hP.xiF wd hP.le
      have hσS : Le σ (succK n) := Or.inr (lt_of_le_of_ltY hP.xiF wd wS hσd hdS)
      have hκK : Lt κ (.K n) := (lt_K_iffY hP.piF hn).mpr ((lt_K_iffY hw hn).mp hnode)
      have hW : Wmax (.Psi σ κ d) :=
        (MIH d ⟨hd.1, hd.2 (Or.inr hdS), Or.inr hdS⟩ (lt_of_lt_of_leY wd wg wa hdg hga)).2 σ κ
          ⟨hσ.1, hσ.2 hσS, hσS⟩ (hG.2 κ hκ.1 hκK) hκK hw
      exact ⟨wmax_hull hW wK, fun _ => inC_of_ltY _ hw wK hnode⟩
    · have hKκ : Lt (.K n) κ :=
        lt_of_le_of_ltY wK hw hP.piF (le_of_not_ltY hw wK hnode) (lt_psi_targetY hw)
      refine ⟨Hull.psi hw hKκ hσ.1 hκ.1 hd.1, fun hle => ?_⟩
      have hlt : Lt (.Psi σ κ d) (succK n) := by
        rcases hle with e | h
        · cases e
        · exact h
      obtain ⟨rfl, rfl⟩ := psi_lt_succK hn hw hlt hnode
      exact inC_psi_iff.mpr (Or.inr ⟨hκ.2 (Or.inl rfl), inC_zero _ _, hd.2 (Or.inr hdS), hdS⟩)

/-- 列の上の `Good` な崩壊の Mahlo 添字は `WK n` に入る -/
theorem mahlo_wk {n : Nat} (hn : 1 ≤ n) (hG : Good (.K n)) {a : Tm} (ha : WK n a)
    (MIH : ∀ b, WK n b → Lt b a → CollOK n b) {ζ ρ b : Tm} (hγ : Good (.Psi ζ ρ b))
    (hK : Lt (.Psi ζ ρ b) (.K n)) (hma : Le (mi ρ) a) : WK n ζ := by
  have wγ := hγ.1.wf_of
  have hP := wγ.psi
  have wm := WNF.mi hP.piF
  have wS := succK_WNF hn
  have hζH : Hull (.Psi ζ ρ b) Wmax ζ := by
    cases hγ.1 with
    | mem _ _ hlt => exact absurd hlt (Lt.irrefl _)
    | psi _ _ hs _ _ => exact hs
  have hPζ := coeffK hn hG ha MIH wγ hK wm hma (ζ.size + 1)
    (fun x hx hxθ _ => hγ.2 x hx hxθ) ζ hζH (Nat.lt_succ_self _) (FWOrder.k2s wγ) hP.mC
  have hζS : Le ζ (succK n) :=
    Or.inr (lt_of_lt_of_leY hP.xiF wm wS hP.mlt (le_transY wm ha.wf wS hma ha.2.2))
  exact ⟨hPζ.1, hPζ.2 hζS, hζS⟩

/-- Mahlo 添字についての帰納法：引数 `a` 未満の引数の崩壊が `Wmax` に入るとき、Mahlo 添字が `a` 以下で
    `WK n` に入る `K_n` 未満の `Good` な `Ψ^ζ_ρ(b)` は `Wmax` に入る -/
theorem mahlo_step {n : Nat} (hn : 1 ≤ n) (hG : Good (.K n)) {a : Tm} (ha : WK n a)
    (MIH : ∀ b, WK n b → Lt b a → CollOK n b) :
    ∀ ζ, Acc (Rel (WK n)) ζ → WK n ζ → Le ζ a → ∀ ρ b, WNF (.Psi ζ ρ b) →
      Lt (.Psi ζ ρ b) (.K n) → Good (.Psi ζ ρ b) → Wmax (.Psi ζ ρ b) := by
  have wK := WNF.K' hn
  intro ζ hacc
  induction hacc with
  | intro ζ _ IH =>
  intro hζ hζa ρ b hw hK hGγ
  refine wmax_of_good_hyp hGγ (hyp_of_good hGγ ?_)
  intro γ' τ' hγ' hγ'γ _ hc hch _ _
  have wγ' := hγ'.1.wf_of
  rcases hc with ⟨m, b', e, -⟩ | ⟨ζ', b', rfl⟩
  · cases e
  obtain ⟨ζ'', ρ'', b'', rfl, hle⟩ := hch.mahlo wγ' _ _ _ rfl
  have hP := wγ'.psi
  have wm := WNF.mi hP.piF
  have hle' : Le (mi ρ'') ζ := hle
  have hζ''ζ : Lt ζ'' ζ := lt_of_lt_of_leY hP.xiF wm hζ.wf hP.mlt hle'
  have hK' : Lt (.Psi ζ'' ρ'' b'') (.K n) := lt_transY wγ' hw wK hγ'γ hK
  have hW := mahlo_wk hn hG ha MIH hγ' hK' (le_transY wm hζ.wf ha.wf hle' hζa)
  exact IH ζ'' ⟨hW, hζ''ζ⟩ hW (le_transY hP.xiF hζ.wf ha.wf (Or.inr hζ''ζ) hζa) ρ'' b'' wγ'
    hK' hγ'


/-! ### `K_n` 未満の崩壊の閉包 -/

/-- `WK n` の元を引数とする階 `n` 以下の崩壊は `Wmax` に入る（引数 `a ∈ WK n` についての帰納法。
    `Ψ^ξ_π(a)` はさらに Mahlo 添字 `ξ ∈ WK n` についての帰納法） -/
theorem coll_wk {n : Nat} (hn : 1 ≤ n) (hG : Good (.K n)) : ∀ a, WK n a → CollOK n a := by
  have wK := WNF.K' hn
  have wS := succK_WNF hn
  have key : ∀ a, Acc (Rel (WK n)) a → WK n a → CollOK n a := by
    intro a hacc
    induction hacc with
    | intro a _ MIH0 =>
      intro ha
      have MIH : ∀ b, WK n b → Lt b a → CollOK n b := fun b hb hba => MIH0 b ⟨hb, hba⟩ hb
      have wa := ha.wf
      have hullK : ∀ {η x}, WNF η → Lt η (.K n) → Hull (.K n) Wmax x → Hull η Wmax x :=
        fun wη hηK hx => Hull.lower HW wη wK (Or.inr hηK) hx
      have wkOf : ∀ {x}, PK n x → Le x (succK n) → WK n x := fun h hle => ⟨h.1, h.2 hle, hle⟩
      have leS : ∀ {x}, WNF x → Le x a → Le x (succK n) := fun wx h => le_transY wx wa wS h ha.2.2
      refine ⟨fun j hj hjn hw => ?_, fun ξ0 π hξ0 hπ hπK hw0 => ?_⟩
      · -- `Ξ_j(a)`
        have wKj := WNF.K' hj
        have hXK : Lt (.Xi j a) (.K j) := (lt_K_iffY hw hj).mpr (Nat.le_refl _)
        have hXKn : Lt (.Xi j a) (.K n) := lt_of_lt_of_leY hw wKj wK hXK (K_le_K hjn)
        have hnα := nr_specY _ hw
        have bound : ∀ x w, Hull (.Xi j a) Wmax x → Wmax w → Lt w (.Xi j a) → ¬ Lt w x →
            Wmax x := fun x w hx hW hwlt hn =>
          wmax_bounded hw hx hW (le_of_not_ltY (wmax_wf hW) hx.wf_of hn)
            (lt_transY (wmax_wf hW) hw hnα.1 hwlt hnα.2.2)
        have hGx : Good (.Xi j a) := by
          refine ⟨Hull.xi hw hXK (hullK hw hXKn ha.1), ?_⟩
          intro β1
          induction β1 using size_induction with
          | h β1 LIH =>
            intro hβ hβlt
            have below : ∀ x, WNF x → Lt x β1 → Lt x (.Xi j a) :=
              fun x wx h => lt_transY wx hβ.wf_of hw h hβlt
            cases hβ with
            | zero => exact wmax_zero
            | one => exact wmax_one
            | K hj' => exact hG.2 _ (Hull.K hj') (lt_transY (WNF.K' hj') hw wK hβlt hXKn)
            | mem hX _ _ => exact hX
            | plus hw₁ hb₁ hb₂ =>
              exact wmax_add hw₁
                (LIH _ (by size_omega) hb₁ (below _ hw₁.plus.1 (lt_plus_leftY hw₁)))
                (LIH _ (by size_omega) hb₂ (below _ hw₁.plus.2.1 (lt_plus_rightY hw₁)))
            | om hw₁ hd =>
              exact wmax_om _ (LIH _ (by size_omega) hd (below _ hw₁.om.1 hw₁.om.2.2)) hw₁
            | @xi j' d hw₁ hXKj hd =>
              have hjj : j' = j := by
                have h1 := (lt_K_iffY hw hw₁.xi.1).mp hXKj
                have h2 := lev_le_of_lt_gen hβlt
                simp only [lev] at h1 h2
                omega
              subst hjj
              by_cases hda : d = a
              · subst hda
                exact absurd hβlt (Lt.irrefl _)
              rcases (ff_xiY hw₁ hw hda).mp hβlt with ⟨hdlt, hfr⟩ | ⟨-, w, hwfr, hwn⟩
              · have wd := hw₁.xi.2.1
                have hPd := coeffK hn hG ha MIH hw hXKn wd (Or.inr hdlt) _
                  (fun x hx hxθ hs => LIH x hs hx hxθ) d hd (by size_omega) hfr hw₁.xi.2.2.2.2
                exact (MIH d (wkOf hPd (leS wd (Or.inr hdlt))) hdlt).1 j' hj hjn hw₁
              · exact bound _ w (Hull.xi hw₁ hXKj hd)
                  (fr_hullK hn hG ha.1 wKj (K_le_K hjn) w hwfr) (FWOrder.k2x hw w hwfr) hwn
            | @psi s κ d hw₁ hσ hs hκ hd =>
              rcases hw₁.shape with ⟨c', rfl, rfl⟩ | -
              · exact absurd hβlt (Lt.asymmY hw hw₁ ((lt_OF_psiOm (Or.inl ⟨j, a, rfl⟩) hw hw₁).mpr
                  ((lt_OF_omG (Or.inl ⟨j, a, rfl⟩) hw hw₁.psiOm.1).mp hσ)))
              · have hl : lev κ = j := by
                  have h1 := lev_le_of_lt_gen hσ
                  have h2 := lev_le_of_lt_gen hβlt
                  simp only [lev] at h1 h2
                  omega
                obtain ⟨-, w, hwfr, hwn⟩ := wit_psi_xi hw₁ hw hl hβlt hσ
                exact bound _ w (Hull.psi hw₁ hσ hs hκ hd)
                  (fr_hullK hn hG ha.1 wKj (K_le_K hjn) w hwfr) (FWOrder.k2x hw w hwfr) hwn
        have h15xi : H15 (.Xi j a) := by
          intro γ' τ' hγ' hγ'γ _ hc hch _ _
          have wγ' := hγ'.1.wf_of
          rcases hc with ⟨m, b', e, -⟩ | ⟨ζ', b', rfl⟩
          · cases e
          obtain ⟨ζ'', ρ'', b'', rfl, hle⟩ := hch.mahlo wγ' _ _ _ rfl
          have hP := wγ'.psi
          have hle' : Le (mi ρ'') a := hle
          have hK' : Lt (.Psi ζ'' ρ'' b'') (.K n) := lt_transY wγ' hw wK hγ'γ hXKn
          have hW := mahlo_wk hn hG ha MIH hγ' hK' hle'
          exact mahlo_step hn hG ha MIH ζ'' (acc_wk hn hG ζ'' hW) hW
            (Or.inr (lt_of_lt_of_leY hP.xiF (WNF.mi hP.piF) wa hP.mlt hle')) ρ'' b'' wγ' hK' hγ'
        exact wmax_of_good_hyp hGx (hyp_of_good hGx h15xi)
      · -- `Ψ^ξ_π(a)`：Mahlo 添字 `ξ` についての帰納法
        have wπ := wmax_wf hπ
        have keyξ : ∀ ξ, Acc (Rel (WK n)) ξ → WK n ξ → WNF (.Psi ξ π a) → Wmax (.Psi ξ π a) := by
          intro ξ haccξ
          induction haccξ with
          | intro ξ _ XIH0 =>
            intro hξ hw
            have XIH : ∀ σ, WK n σ → Lt σ ξ → WNF (.Psi σ π a) → Wmax (.Psi σ π a) :=
              fun σ hσ hσξ => XIH0 σ ⟨hσ, hσξ⟩ hσ
            have wξ := hw.psi.xiF
            have hnα := nr_specY _ hw
            have hγπ := lt_psi_targetY hw
            have hηK : Lt (.Psi ξ π a) (.K n) := lt_transY hw wπ wK hγπ hπK
            have bound : ∀ x w, Hull (.Psi ξ π a) Wmax x → Wmax w → Lt w (.Psi ξ π a) →
                ¬ Lt w x → Wmax x := fun x w hx hW hwlt hn =>
              wmax_bounded hw hx hW (le_of_not_ltY (wmax_wf hW) hx.wf_of hn)
                (lt_transY (wmax_wf hW) hw hnα.1 hwlt hnα.2.2)
            have hπK' : Le π (.K n) := Or.inr hπK
            have hGη : Good (.Psi ξ π a) := by
              refine ⟨Hull.psi hw hγπ (hullK hw hηK hξ.1) (wmax_hull hπ hw)
                (hullK hw hηK ha.1), ?_⟩
              intro β1
              induction β1 using size_induction with
              | h β1 LIH =>
                intro hβ hβlt
                have good : ∀ x, Hull (.Psi ξ π a) Wmax x → Lt x (.Psi ξ π a) →
                    x.size < β1.size → Wmax x := fun x hx hxθ hs => LIH x hs hx hxθ
                have below : ∀ x, WNF x → Lt x β1 → Lt x (.Psi ξ π a) :=
                  fun x wx h => lt_transY wx hβ.wf_of hw h hβlt
                have coeffA : ∀ x, Hull (.Psi ξ π a) Wmax x → x.size < β1.size →
                    inC x a (.Psi ξ π a) = true → PK n x := fun x hx hs hC =>
                  coeffK hn hG ha MIH hw hηK wa (Or.inl rfl) _ good x hx hs
                    (fun w hw' => (fr_spec hw').2) hC
                cases hβ with
                | zero => exact wmax_zero
                | one => exact wmax_one
                | K hj' => exact hG.2 _ (Hull.K hj') (lt_transY (WNF.K' hj') hw wK hβlt hηK)
                | mem hX _ _ => exact hX
                | plus hw₁ hb₁ hb₂ =>
                  exact wmax_add hw₁
                    (LIH _ (by size_omega) hb₁ (below _ hw₁.plus.1 (lt_plus_leftY hw₁)))
                    (LIH _ (by size_omega) hb₂ (below _ hw₁.plus.2.1 (lt_plus_rightY hw₁)))
                | om hw₁ hd =>
                  exact wmax_om _ (LIH _ (by size_omega) hd (below _ hw₁.om.1 hw₁.om.2.2)) hw₁
                | @xi j d hw₁ hK hd =>
                  rcases hw.shape with ⟨c, rfl, rfl⟩ | hsh
                  · exact wmax_bounded hw (Hull.xi hw₁ hK hd) (wmax_om_arg hπ)
                      (Or.inr ((lt_OF_psiOm (Or.inl ⟨j, d, rfl⟩) hw₁ hw).mp hβlt))
                      (lt_transY hw.psiOm.1 hw hnα.1 (FWOrder.cx hw) hnα.2.2)
                  · have hl : lev π = j := by
                      have h1 := lev_le_of_lt_gen hβlt
                      have h2 := (lt_K_iffY hw hw₁.xi.1).mp hK
                      simp only [lev] at h1 h2
                      omega
                    have hjn : j ≤ n := by
                      have := (lt_K_iffY wπ hn).mp hπK
                      omega
                    have wd := hw₁.xi.2.1
                    have hn' := (lt_xi_psiY hl).mp hβlt
                    rw [lt_psi_xiY hl] at hn'
                    by_cases hda : Lt d a
                    · have hC : inC d a (.Psi ξ π a) = true := by
                        cases e : inC d a (Tm.Psi ξ π a)
                        · exact absurd (Or.inr ⟨hda, e⟩) hn'
                        · rfl
                      have hPd := coeffA d hd (by size_omega) hC
                      have hdS : Le d (succK n) :=
                        le_transY wd (succK_WNF hw₁.xi.1) wS
                          (le_of_ne_gtY wd (succK_WNF hw₁.xi.1) hw₁.xi.2.2.2.1)
                          (succK_mono hw₁.xi.1 hjn)
                      exact (MIH d (wkOf hPd hdS) hda).1 j hw₁.xi.1 hjn hw₁
                    · have hxπ : Lt (.Xi j d) π := by
                        cases e : cmp π (.Xi j d) with
                        | gt => exact lt_of_gtY wπ hw₁ e
                        | _ => exact absurd (Or.inl (by rw [e]; decide)) hn'
                      obtain ⟨w, hwfr, hwn⟩ := wit_xi_tgt π wπ hsh hw₁ wa hxπ hl hw.psi.Cpi
                        (le_of_not_ltY wd wa hda)
                      exact bound _ w (Hull.xi hw₁ hK hd) (fr_wmax wπ π hπ w hwfr)
                        (FWOrder.k2t hw w hwfr) hwn
                | @psi σ κ d hw₁ hσ hσH hκ hd =>
                  have wσ := hw₁.psi.xiF
                  have wd := hw₁.psi.aF
                  have hl : lev κ = lev π := by
                    have h1 := lev_le_of_lt_gen hσ
                    have h2 := lev_le_of_lt_gen hβlt
                    simp only [lev] at h1 h2
                    omega
                  rcases (lt_psi_psiY hl hβlt.ne).mp hβlt with
                    h1 | ⟨-, hβπ, (⟨hda, hdC, hσC, hκC⟩ | ⟨had, hnC⟩ | ⟨hda, e, hσξ, hσC⟩ |
                      ⟨hξσ, hnC⟩)⟩
                  · exact absurd hσ h1
                  · -- (1)
                    have hPd := coeffA d hd (by size_omega) hdC
                    have hPσ := coeffA σ hσH (by size_omega) hσC
                    have hPκ := coeffA κ hκ (by size_omega) hκC
                    have hκK : Lt κ (.K n) := by
                      have := (lt_K_iffY wπ hn).mp hπK
                      exact (lt_K_iffY hw₁.psi.piF hn).mpr (by omega)
                    have hdS := leS wd (Or.inr hda)
                    have hσS : Le σ (succK n) :=
                      le_transY wσ wd wS (le_of_ne_gtY wσ wd hw₁.psi.le) hdS
                    exact (MIH d (wkOf hPd hdS) hda).2 σ κ (wkOf hPσ hσS)
                      (hG.2 κ hPκ.1 hκK) hκK hw₁
                  · -- (2)
                    obtain ⟨w, hwfr, hwn⟩ := wit_c2 hw hw₁ wd (le_of_ne_gtY wa wd had) hβπ hnC
                    rcases hwfr with hwfr | hwfr | hwfr
                    · exact bound _ w (Hull.psi hw₁ hσ hσH hκ hd)
                        (fr_hullK hn hG ha.1 wπ hπK' w hwfr) (FWOrder.k2 hw w hwfr) hwn
                    · exact bound _ w (Hull.psi hw₁ hσ hσH hκ hd) (fr_wmax wπ π hπ w hwfr)
                        (FWOrder.k2t hw w hwfr) hwn
                    · exact bound _ w (Hull.psi hw₁ hσ hσH hκ hd)
                        (fr_hullK hn hG hξ.1 wπ hπK' w hwfr) (FWOrder.k2s hw w hwfr) hwn
                  · -- (3)
                    have e' := FWOrder.eq wd wa hda
                    subst e' e
                    have hPσ := coeffA σ hσH (by size_omega) hσC
                    have hσS : Le σ (succK n) := leS wσ (le_of_ne_gtY wσ wd hw₁.psi.le)
                    exact XIH σ (wkOf hPσ hσS) hσξ hw₁
                  · -- (4)
                    obtain ⟨w, hwfr, hwn⟩ := wit_c4 hw hw₁ wσ hβlt hξσ hnC
                    exact bound _ w (Hull.psi hw₁ hσ hσH hκ hd)
                      (fr_hullK hn hG hξ.1 hw (Or.inr hηK) w hwfr) (fr_spec hwfr).2 hwn
            exact mahlo_step hn hG ha MIH ξ (acc_wk hn hG ξ hξ) hξ
              (le_of_ne_gtY wξ wa hw.psi.le) π a hw hηK hGη
        exact keyξ ξ0 (acc_wk hn hG ξ0 hξ0) hξ0 hw0
  intro a ha
  exact key a (acc_wk hn hG a ha) ha

/-! ### `K_n` -/

theorem wmax_K : ∀ n, 1 ≤ n → Wmax (.K n) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihn =>
    intro hn
    have wK := WNF.K' hn
    have hG := goodK hn (fun j hj hjn => ihn j hjn hj)
    have hcoll := coll_wk hn hG
    refine wmax_of_good_hyp hG (hyp_of_good hG ?_)
    intro γ τ hγ _ Obs hc hch hτH hfr
    have wγ := hγ.1.wf_of
    rcases hc with ⟨m, b, e, rfl⟩ | ⟨ξ, b, rfl⟩
    · injection e with e
      subst e
      have hγτ := hch.le wγ
      cases hτH with
      | mem hX _ _ => exact Obs _ hX hγτ
      | xi hw _ hb =>
        have hτK : Lt (.Xi n b) (.K n) := (lt_K_iffY hw hn).mpr (Nat.le_refl _)
        have hbK : Hull (.K n) Wmax b :=
          hull_transfer wK wK (Or.inl rfl) (b.size + 1) (fun x hx hxγ _ => hγ.2 x hx hxγ) b hb
            (Nat.lt_succ_self _) (fun w hw' => hfr w (by
              rw [fr]
              simp only [Lt.irrefl, ↓reduceIte]
              exact fr_sub wK hw (Or.inr hτK) hw.xi.2.1 hw' (FWOrder.k2x hw w hw')))
        have wb := hw.xi.2.1
        have hbS : Le b (succK n) := le_of_ne_gtY wb (succK_WNF hn) hw.xi.2.2.2.1
        have hbC : inC b (succK n) (.K n) = true :=
          inC_mono_g wb wb (succK_WNF hn) hbS hw.xi.2.2.2.2
        exact Obs _ ((hcoll b ⟨hbK, hbC, hbS⟩).1 n hn (Nat.le_refl _) hw) hγτ
    · exfalso
      exact not_tgt_of_shape (fun _ e => by cases e) (fun _ _ e => by cases e)
        (fun _ _ _ e => by cases e) (hch.wnf wγ).psi.tgt

/-! ### 主定理 -/

/-- 体系全体の標準形は全て最大区別集合に入る -/
theorem wmax_of_WNF : ∀ t : Tm, WNF t → Wmax t
  | .zero, _ => wmax_zero
  | .one, _ => wmax_one
  | .K _, h => wmax_K _ h.k
  | .plus a b, h => wmax_add h (wmax_of_WNF a h.plus.1) (wmax_of_WNF b h.plus.2.1)
  | .Om a, h => wmax_om a (wmax_of_WNF a h.om.1) h
  | .Xi j a, h => by
    have hj := h.xi.1
    have wa := h.xi.2.1
    have hG := goodK hj (fun i hi _ => wmax_K i hi)
    have hS : Le a (succK j) := le_of_ne_gtY wa (succK_WNF hj) h.xi.2.2.2.1
    exact (coll_wk hj hG a ⟨wmax_hull (wmax_of_WNF a wa) (WNF.K' hj),
      inC_mono_g wa wa (succK_WNF hj) hS h.xi.2.2.2.2, hS⟩).1 j hj (Nat.le_refl _) h
  | .Psi x p a, h => by
    have hP := h.psi
    have hn : 1 ≤ lev x + lev p + lev a + 1 := by omega
    have wK := WNF.K' hn
    have hG := goodK hn (fun i hi _ => wmax_K i hi)
    have wk : ∀ y, WNF y → lev y ≤ lev x + lev p + lev a + 1 → Wmax y →
        WK (lev x + lev p + lev a + 1) y := fun y wy hl hy =>
      have hyK := (lt_K_iffY wy hn).mpr hl
      ⟨wmax_hull hy wK, inC_of_ltY _ wy wK hyK,
        Or.inr (lt_transY wy wK (succK_WNF hn) hyK (K_lt_succK hn))⟩
    exact (coll_wk hn hG a (wk a hP.aF (by omega) (wmax_of_WNF a hP.aF))).2 x p
      (wk x hP.xiF (by omega) (wmax_of_WNF x hP.xiF)) (wmax_of_WNF p hP.piF)
      ((lt_K_iffY hP.piF hn).mpr (by omega)) h

end RTKA.W.WFY

namespace RTKA.W

open WFY

variable [FWOrder]

theorem acc_W {t : Tm} (ht : WNF t) : Acc (fun u v => WNF u ∧ Lt u v) t := by
  have key : ∀ t, Acc (Rel Wmax) t → Acc (fun u v => WNF u ∧ Lt u v) t := by
    intro t hacc
    induction hacc with
    | intro t _ ih => exact Acc.intro t (fun u hu => ih u ⟨wmax_of_WNF u hu.1, hu.2⟩)
  exact key t (wmax_acc (wmax_of_WNF t ht))

/-- 順序の仮定 `FWOrder` の下で、体系全体の標準形の上の `<` は整礎 -/
theorem wellFounded_W : WellFounded (fun a b : {t : Tm // WNF t} => Lt a.1 b.1) := by
  constructor
  rintro ⟨t, ht⟩
  have key : ∀ t, Acc (fun u v => WNF u ∧ Lt u v) t → ∀ ht : WNF t,
      Acc (fun a b : {t : Tm // WNF t} => Lt a.1 b.1) ⟨t, ht⟩ := by
    intro t h
    induction h with
    | intro t _ ih =>
      intro ht
      exact Acc.intro _ (fun ⟨u, hu⟩ hlt => ih u ⟨hu, hlt⟩ hu)
  exact key t (acc_W ht) ht

end RTKA.W
