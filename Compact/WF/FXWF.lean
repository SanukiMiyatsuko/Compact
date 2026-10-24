import Compact.WF.FXHyp

/-! 断片 `FX` の整列性（`wellFounded_FX`）。

`Good α → α ∈ Wmax`（`wmax_of_good`）から、`Wmax` が `0`・`1`・`+`・`Ω`・`K_n`・`Ξ_n`・`Ψ_{Ω_c}` で閉じる
ことを示し、`FX` の標準形が全て `Wmax` に入ることを導く。

* `wmax_om`：`Ω_c`。`c ∈ Wmax` についての帰納法。
* `wmax_K`：`K_m`。`m` についての帰納法（`K_m` 未満の `Ξ`・`Ψ` は `C^{K_m}(Wmax)` で生成されない）。
* `wmax_coll`：`Ξ_n(a)` と `Ψ_{Ω_c}(a)`。引数 `a ∈ Wmax` についての帰納法で同時に示す。同じ添字の崩壊
  `Ξ_n(b) < Ξ_n(a)`（`Ψ` も同様）は前線による比較（`ff_xi_FX`）で場合を分け、`b < a` なら係数についての
  帰納法（`coeff_induction`）で `b ∈ Wmax` を示して帰納法の仮定を使い、そうでなければ `a` の前線の元
  （`fr_wmax` で `Wmax` に入る）で上から押さえる。 -/

namespace RTKA.WFX

open Tm

theorem wmax_zero : Wmax .zero :=
  wmax_of_good ⟨Hull.zero, fun _ _ h => absurd h (not_lt_zero _)⟩

theorem wmax_one : Wmax .one :=
  wmax_of_good ⟨Hull.one, fun _ hβ h => by
    have := lt_oneX hβ.wf_of h
    subst this
    exact wmax_zero⟩

theorem wmax_add {a b : Tm} (hw : FXNF (.plus a b)) (ha : Wmax a) (hb : Wmax b) :
    Wmax (.plus a b) := by
  have key : ∀ b, Acc (Rel Wmax) b → Wmax b → FXNF (.plus a b) → Wmax (.plus a b) := by
    intro b hacc
    induction hacc with
    | intro b _ ih =>
      intro hb hw
      have hn := nr_spec _ hw
      have hap := hw.plus.2.2.1
      have ha_lt := lt_trans_FX (wmax_wf ha) hw hn.1 (lt_plus_leftX hw) hn.2.2
      refine wmax_of_good ⟨Hull.plus hw (wmax_hull ha hw) (wmax_hull hb hw), ?_⟩
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
              (lt_trans_FX (wmax_wf hb) hw hn.1 (lt_plus_rightX hw) hn.2.2)
            exact ih γ₂ ⟨hγ₂W, hγlt'⟩ hγ₂W hw'
        · exact wmax_bounded hw hγ ha
            (Or.inr ((lt_plus_prin_iff wγ hap).mpr ((lt_plus_plus_ne wγ hw e).mp hγlt))) ha_lt
      | _ => exact wmax_bounded hw hγ ha ((lt_prin_plus_iff wγ rfl hw).mp hγlt) ha_lt
  exact key b (wmax_acc hb) hb hw

theorem wmax_om : ∀ c, Wmax c → FXNF (.Om c) → Wmax (.Om c) := by
  have key : ∀ c, Acc (Rel Wmax) c → Wmax c → FXNF (.Om c) → Wmax (.Om c) := by
    intro c hacc
    induction hacc with
    | intro c _ ihc =>
      intro hc hw
      have hn := nr_spec _ hw
      have wc := wmax_wf hc
      have hc_lt := lt_trans_FX wc hw hn.1 hw.om.2.2 hn.2.2
      refine wmax_of_good ⟨Hull.om hw (wmax_hull hc hw), ?_⟩
      intro β
      induction β using size_induction with
      | h β ihβ =>
        intro hβ hβlt
        have below : ∀ x, FXNF x → Lt x β → Lt x (.Om c) :=
          fun x wx h => lt_trans_FX wx hβ.wf_of hw h hβlt
        cases hβ with
        | zero => exact wmax_zero
        | one => exact wmax_one
        | K hn' =>
          exact wmax_bounded hw (Hull.K hn') hc (Or.inr ((lt_K_omG hn' wc).mp hβlt)) hc_lt
        | mem hX _ _ => exact hX
        | plus hw' hb₁ hb₂ =>
          exact wmax_add hw'
            (ihβ _ (by size_omega) hb₁ (below _ hw'.plus.1 (lt_plus_leftX hw')))
            (ihβ _ (by size_omega) hb₂ (below _ hw'.plus.2.1 (lt_plus_rightX hw')))
        | om hw' hd =>
          have hdW := ihβ _ (by size_omega) hd (below _ hw'.om.1 hw'.om.2.2)
          exact ihc _ ⟨hdW, (lt_om_iffX hw'.om.1 wc).mp hβlt⟩ hdW hw'
        | xi hw' hK hd =>
          exact wmax_bounded hw (Hull.xi hw' hK hd) hc (Or.inr ((lt_xi_omG hw' wc).mp hβlt))
            hc_lt
        | psi hw' hσ _ _ =>
          exact absurd ((lt_om_iffX wc hw'.psi'.1).mp hσ)
            (not_lt_of_leX hw'.psi'.1 wc ((lt_psi_omG hw' wc).mp hβlt))
  intro c hc
  exact key c (wmax_acc hc) hc

theorem wmax_K : ∀ m, 1 ≤ m → Wmax (.K m) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ihm =>
    intro hm
    have hw := FXNF.K' hm
    refine wmax_of_good ⟨Hull.K hm, ?_⟩
    intro β
    induction β using size_induction with
    | h β ihβ =>
      intro hβ hβlt
      have below : ∀ x, FXNF x → Lt x β → Lt x (.K m) :=
        fun x wx h => lt_trans_FX wx hβ.wf_of hw h hβlt
      cases hβ with
      | zero => exact wmax_zero
      | one => exact wmax_one
      | @K j hj =>
        have h1 := (lt_K_iff (FXNF.K' hj) hm).mp hβlt
        simp only [lev] at h1
        exact ihm j (by omega) hj
      | mem hX _ _ => exact hX
      | plus hw' hb₁ hb₂ =>
        exact wmax_add hw'
          (ihβ _ (by size_omega) hb₁ (below _ hw'.plus.1 (lt_plus_leftX hw')))
          (ihβ _ (by size_omega) hb₂ (below _ hw'.plus.2.1 (lt_plus_rightX hw')))
      | om hw' hd =>
        exact wmax_om _ (ihβ _ (by size_omega) hd (below _ hw'.om.1 hw'.om.2.2)) hw'
      | xi hw' hK _ =>
        exfalso
        have h1 := (lt_K_iff hw' hm).mp hβlt
        have h2 := (lt_K_iff hw hw'.xi.1).mp hK
        simp only [lev] at h1 h2
        omega
      | psi hw' hσ _ _ =>
        exfalso
        have h1 := (lt_K_iff hw' hm).mp hβlt
        have h2 := lev_le_of_lt_gen hσ
        simp only [lev] at h1 h2
        omega

/-- `Ξ_n(a)` と `Ψ_{Ω_c}(a)`：引数 `a ∈ Wmax` についての帰納法（Arai の Lemma 8.2 にあたる） -/
theorem wmax_coll : ∀ a, Wmax a →
    (∀ n, FXNF (.Xi n a) → Wmax (.Xi n a)) ∧
      (∀ c, Wmax c → FXNF (.Psi .zero (.Om c) a) → Wmax (.Psi .zero (.Om c) a)) := by
  have key : ∀ a, Acc (Rel Wmax) a → Wmax a →
      (∀ n, FXNF (.Xi n a) → Wmax (.Xi n a)) ∧
        (∀ c, Wmax c → FXNF (.Psi .zero (.Om c) a) → Wmax (.Psi .zero (.Om c) a)) := by
    intro a hacc
    induction hacc with
    | intro a _ MIH0 =>
      intro ha
      have MIH : ∀ b, Wmax b → Lt b a →
          (∀ n, FXNF (.Xi n b) → Wmax (.Xi n b)) ∧
            (∀ c, Wmax c → FXNF (.Psi .zero (.Om c) b) → Wmax (.Psi .zero (.Om c) b)) :=
        fun b hb hba => MIH0 b ⟨hb, hba⟩ hb
      have wa := wmax_wf ha
      refine ⟨fun n hw => ?_, fun c hc hw => ?_⟩
      · -- `Ξ_n(a)`
        have hn1 := hw.xi.1
        have wK := FXNF.K' hn1
        have hXK : Lt (.Xi n a) (.K n) := (lt_K_iff hw hn1).mpr (Nat.le_refl _)
        have hnα := nr_spec _ hw
        refine wmax_of_good ⟨Hull.xi hw hXK (wmax_hull ha hw), ?_⟩
        intro β1
        induction β1 using size_induction with
        | h β1 LIH =>
          intro hβ hβlt
          have below : ∀ x, FXNF x → Lt x β1 → Lt x (.Xi n a) :=
            fun x wx h => lt_trans_FX wx hβ.wf_of hw h hβlt
          cases hβ with
          | zero => exact wmax_zero
          | one => exact wmax_one
          | K hj => exact wmax_K _ hj
          | mem hX _ _ => exact hX
          | plus hw₁ hb₁ hb₂ =>
            exact wmax_add hw₁
              (LIH _ (by size_omega) hb₁ (below _ hw₁.plus.1 (lt_plus_leftX hw₁)))
              (LIH _ (by size_omega) hb₂ (below _ hw₁.plus.2.1 (lt_plus_rightX hw₁)))
          | om hw₁ hd =>
            exact wmax_om _ (LIH _ (by size_omega) hd (below _ hw₁.om.1 hw₁.om.2.2)) hw₁
          | @xi j d hw₁ hXKj hd =>
            have hjn : j = n := by
              have h1 := (lt_K_iff hw hw₁.xi.1).mp hXKj
              have h2 := lev_le_of_lt_gen hβlt
              simp only [lev] at h1 h2
              omega
            subst hjn
            by_cases hda : d = a
            · subst hda
              exact absurd hβlt (Lt.irrefl _)
            rcases (ff_xi_FX hw₁ hw hda).mp hβlt with ⟨hdlt, hfr⟩ | ⟨-, w, hwfr, hwn⟩
            · -- `d < a`：`d ∈ Wmax` を係数についての帰納法で示す
              have wd := hw₁.xi.2.1
              have hdW : Wmax d := coeff_induction Wmax _
                (fun x hx hxθ hs => LIH x hs hx hxθ) wmax_zero wmax_one (wmax_K _)
                (fun hw' h1 h2 => wmax_add hw' h1 h2) (fun hw' h => wmax_om _ h hw')
                (fun hw' he h => (MIH _ h (lt_trans_FX hw'.xi.2.1 wd wa he hdlt)).1 _ hw')
                (fun hw' he hσ h =>
                  (MIH _ h (lt_trans_FX hw'.psi'.2.2.2.1 wd wa he hdlt)).2 _ (wmax_om_arg hσ) hw')
                d hd (by size_omega) hfr hw₁.xi.2.2.2.2
              exact (MIH d hdW hdlt).1 _ hw₁
            · -- `a < d`：`a` の前線の元 `w ≥ Ξ_n(d)` で押さえる
              have wW := fr_wmax wK a ha w hwfr
              have ww := wmax_wf wW
              exact wmax_bounded hw (Hull.xi hw₁ hXKj hd) wW (le_of_not_ltX ww hw₁ hwn)
                (lt_trans_FX ww hw hnα.1 (k2x_FX hw w hwfr) hnα.2.2)
          | psi hw₁ hσ _ _ =>
            exact absurd hβlt (Lt.asymmX hw hw₁
              ((xi_lt_psiG hw hw₁).mpr ((lt_xi_omG hw hw₁.psi'.1).mp hσ)))
      · -- `Ψ_{Ω_c}(a)`
        obtain ⟨wc, wσ, -, -, -⟩ := hw.psi'
        have hσW : Wmax (.Om c) := wmax_om c hc wσ
        have hnα := nr_spec _ hw
        refine wmax_of_good
          ⟨Hull.psi hw (lt_psi_om_self c a) (wmax_hull hσW hw) (wmax_hull ha hw), ?_⟩
        intro β1
        induction β1 using size_induction with
        | h β1 LIH =>
          intro hβ hβlt
          have below : ∀ x, FXNF x → Lt x β1 → Lt x (.Psi .zero (.Om c) a) :=
            fun x wx h => lt_trans_FX wx hβ.wf_of hw h hβlt
          cases hβ with
          | zero => exact wmax_zero
          | one => exact wmax_one
          | K hj => exact wmax_K _ hj
          | mem hX _ _ => exact hX
          | plus hw₁ hb₁ hb₂ =>
            exact wmax_add hw₁
              (LIH _ (by size_omega) hb₁ (below _ hw₁.plus.1 (lt_plus_leftX hw₁)))
              (LIH _ (by size_omega) hb₂ (below _ hw₁.plus.2.1 (lt_plus_rightX hw₁)))
          | om hw₁ hd =>
            exact wmax_om _ (LIH _ (by size_omega) hd (below _ hw₁.om.1 hw₁.om.2.2)) hw₁
          | xi hw₁ hK hd =>
            exact wmax_bounded hw (Hull.xi hw₁ hK hd) hc (Or.inr ((xi_lt_psiG hw₁ hw).mp hβlt))
              (lt_trans_FX wc hw hnα.1 (cx_FX hw) hnα.2.2)
          | @psi c' d hw₁ hσ hσH hd =>
            rcases (lt_psi_omG hw hw₁.psi'.1).mp hσ with e | hcc'
            · subst e
              by_cases hda : d = a
              · subst hda
                exact absurd hβlt (Lt.irrefl _)
              rcases (ff_psi_FX hw₁ hw hda).mp hβlt with ⟨hdlt, hfr⟩ | ⟨-, w, hwfr, hwn⟩
              · have wd := hw₁.psi'.2.2.2.1
                have hdW : Wmax d := coeff_induction Wmax _
                  (fun x hx hxθ hs => LIH x hs hx hxθ) wmax_zero wmax_one (wmax_K _)
                  (fun hw' h1 h2 => wmax_add hw' h1 h2) (fun hw' h => wmax_om _ h hw')
                  (fun hw' he h => (MIH _ h (lt_trans_FX hw'.xi.2.1 wd wa he hdlt)).1 _ hw')
                  (fun hw' he hσ' h =>
                    (MIH _ h (lt_trans_FX hw'.psi'.2.2.2.1 wd wa he hdlt)).2 _
                      (wmax_om_arg hσ') hw')
                  d hd (by size_omega) hfr hw₁.psi'.2.2.2.2
                exact (MIH d hdW hdlt).2 _ hc hw₁
              · have wW := fr_wmax wσ a ha w hwfr
                have ww := wmax_wf wW
                exact wmax_bounded hw (Hull.psi hw₁ hσ hσH hd) wW (le_of_not_ltX ww hw₁ hwn)
                  (lt_trans_FX ww hw hnα.1 (k2_FX hw w hwfr) hnα.2.2)
            · exact absurd hβlt (Lt.asymmX hw hw₁ (lt_psi_psiG hcc'))
  intro a ha
  exact key a (wmax_acc ha) ha

/-- `FX` の標準形は全て最大区別集合に入る -/
theorem wmax_of_FXNF : ∀ t : Tm, FXNF t → Wmax t
  | .zero, _ => wmax_zero
  | .one, _ => wmax_one
  | .K _, h => wmax_K _ h.k
  | .plus a b, h => wmax_add h (wmax_of_FXNF a h.plus.1) (wmax_of_FXNF b h.plus.2.1)
  | .Om a, h => wmax_om a (wmax_of_FXNF a h.om.1) h
  | .Xi _ a, h => (wmax_coll a (wmax_of_FXNF a h.xi.2.1)).1 _ h
  | .Psi _ p a, h => by
    obtain ⟨rfl, c, rfl, -⟩ := h.psi
    exact (wmax_coll a (wmax_of_FXNF a h.psi'.2.2.2.1)).2 c
      (wmax_om_arg (wmax_of_FXNF _ h.psi'.2.1)) h

end RTKA.WFX

namespace RTKA

open WFX

theorem acc_FX {t : Tm} (ht : FXNF t) : Acc (fun u v => FXNF u ∧ Lt u v) t := by
  have key : ∀ t, Acc (Rel Wmax) t → Acc (fun u v => FXNF u ∧ Lt u v) t := by
    intro t hacc
    induction hacc with
    | intro t _ ih => exact Acc.intro t (fun u hu => ih u ⟨wmax_of_FXNF u hu.1, hu.2⟩)
  exact key t (wmax_acc (wmax_of_FXNF t ht))

/-- `FX` の標準形の上の `<` は整礎 -/
theorem wellFounded_FX : WellFounded (fun a b : {t : Tm // FXNF t} => Lt a.1 b.1) := by
  constructor
  rintro ⟨t, ht⟩
  have key : ∀ t, Acc (fun u v => FXNF u ∧ Lt u v) t → ∀ ht : FXNF t,
      Acc (fun a b : {t : Tm // FXNF t} => Lt a.1 b.1) ⟨t, ht⟩ := by
    intro t h
    induction h with
    | intro t _ ih =>
      intro ht
      exact Acc.intro _ (fun ⟨u, hu⟩ hlt => ih u ⟨hu, hlt⟩ hu)
  exact key t (acc_FX ht) ht

end RTKA
