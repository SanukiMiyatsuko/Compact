import Compact.WF.FYHyp

/-! 断片 `FY` の整列性（順序の仮定 `FYOrder` の下で、`wellFounded_FY`）。

`FXWF.lean` と同じく、`Wmax` が `0`・`1`・`+`・`Ω`・`K_n`・`Ξ_n`・`Ψ^0_π` で閉じることを示す。`Ξ_n(a)` と
`Ψ^0_π(a)` は引数 `a ∈ Wmax` についての帰納法で同時に示す（`wmax_coll`）。`Ψ^0_π(a)` の `Good` 性では、
`C^{Ψ_π(a)}(Wmax)` の元 `Ψ^0_κ(d) < Ψ_π(a)` を目標 `κ` と `π` の大小で分ける。

* `κ = π`：前線による比較（`ff_psiY`）で、`d < a` なら係数についての帰納法、そうでなければ `a` の前線。
* `κ < π`：`π` についての `a` か `π` の前線に `Ψ_κ(d)` 以上の元がある（`wit_psi_psi`）。
* `κ > π`：`cmpPsi` の `c1`（`d`・`κ ∈ C(a, Ψ_π(a))`、`d < a`）なら係数についての帰納法で `d`・`κ ∈ Wmax`、
  `c2` なら `a` か `π` の前線（`wit_c2`）。 -/

namespace RTKA.WFY

open Tm

variable [FYOrder]

/-- `cmpPsi` の `c2` の形の比較から前線の証人を取り出す -/
theorem wit_c2 {π κ a b : Tm} (hx : FYNF (.Psi .zero π a)) (hy : FYNF (.Psi .zero κ b))
    (hba : Le b a) (hxκ : Lt (.Psi .zero π a) κ)
    (hn : ¬ (inC b a (.Psi .zero π a) = true ∧ inC κ a (.Psi .zero π a) = true)) :
    ∃ w, (w ∈ fr κ b ∨ w ∈ fr κ κ) ∧ ¬ Lt w (.Psi .zero π a) := by
  obtain ⟨-, -, -, haF, -, -⟩ := hx.psi
  obtain ⟨-, -, hκF, hbF, hbC, hκC⟩ := hy.psi
  by_cases hb : ∀ w, w ∈ fr κ b → Lt w (.Psi .zero π a)
  · by_cases hk : ∀ w, w ∈ fr κ κ → Lt w (.Psi .zero π a)
    · exfalso
      apply hn
      exact ⟨(inC_frY hbF hκF hx hbF haF hbC (Or.inr hxκ) hba).mpr
          (fun w hw => inC_of_lt_node (fr_node hw) (hb w hw)),
        (inC_frY hκF hκF hx hbF haF hκC (Or.inr hxκ) hba).mpr
          (fun w hw => inC_of_lt_node (fr_node hw) (hk w hw))⟩
    · obtain ⟨w, hw, hw'⟩ := exists_of_not_forall_mem _ hk
      exact ⟨w, Or.inr hw, hw'⟩
  · obtain ⟨w, hw, hw'⟩ := exists_of_not_forall_mem _ hb
    exact ⟨w, Or.inl hw, hw'⟩

theorem wmax_zero : Wmax .zero :=
  wmax_of_good ⟨Hull.zero, fun _ _ h => absurd h (not_lt_zero _)⟩

theorem wmax_one : Wmax .one :=
  wmax_of_good ⟨Hull.one, fun _ hβ h => by
    have := lt_oneY hβ.wf_of h
    subst this
    exact wmax_zero⟩

theorem wmax_add {a b : Tm} (hw : FYNF (.plus a b)) (ha : Wmax a) (hb : Wmax b) :
    Wmax (.plus a b) := by
  have key : ∀ b, Acc (Rel Wmax) b → Wmax b → FYNF (.plus a b) → Wmax (.plus a b) := by
    intro b hacc
    induction hacc with
    | intro b _ ih =>
      intro hb hw
      have hn := nr_specY _ hw
      have hap := hw.plus.2.2.1
      have ha_lt := lt_transY (wmax_wf ha) hw hn.1 (lt_plus_leftY hw) hn.2.2
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
              (lt_transY (wmax_wf hb) hw hn.1 (lt_plus_rightY hw) hn.2.2)
            exact ih γ₂ ⟨hγ₂W, hγlt'⟩ hγ₂W hw'
        · exact wmax_bounded hw hγ ha
            (Or.inr ((lt_plus_prin_iffY wγ hap).mpr ((lt_plus_plus_neY wγ hw e).mp hγlt))) ha_lt
      | _ => exact wmax_bounded hw hγ ha ((lt_prin_plus_iffY wγ rfl hw).mp hγlt) ha_lt
  exact key b (wmax_acc hb) hb hw

theorem wmax_om : ∀ c, Wmax c → FYNF (.Om c) → Wmax (.Om c) := by
  have key : ∀ c, Acc (Rel Wmax) c → Wmax c → FYNF (.Om c) → Wmax (.Om c) := by
    intro c hacc
    induction hacc with
    | intro c _ ihc =>
      intro hc hw
      have hn := nr_specY _ hw
      have wc := wmax_wf hc
      have hc_lt := lt_transY wc hw hn.1 hw.om.2.2 hn.2.2
      refine wmax_of_good ⟨Hull.om hw (wmax_hull hc hw), ?_⟩
      intro β
      induction β using size_induction with
      | h β ihβ =>
        intro hβ hβlt
        have below : ∀ x, FYNF x → Lt x β → Lt x (.Om c) :=
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
        | @psi π d hw' hσ hπ hd =>
          rcases hw'.psi.2.1 with ⟨c', rfl, -⟩ | ⟨n, p, rfl⟩
          · exact absurd ((lt_om_iffY wc hw'.psiOm.1).mp hσ)
              (not_lt_of_leY hw'.psiOm.1 wc ((lt_psi_omY hw' wc).mp hβlt))
          · exact wmax_bounded hw (Hull.psi hw' hσ hπ hd) hc
              (Or.inr ((lt_OF_omG (Or.inr ⟨n, p, d, rfl⟩) hw' wc).mp hβlt)) hc_lt
  intro c hc
  exact key c (wmax_acc hc) hc

theorem wmax_K : ∀ m, 1 ≤ m → Wmax (.K m) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ihm =>
    intro hm
    have hw := FYNF.K' hm
    refine wmax_of_good ⟨Hull.K hm, ?_⟩
    intro β
    induction β using size_induction with
    | h β ihβ =>
      intro hβ hβlt
      have below : ∀ x, FYNF x → Lt x β → Lt x (.K m) :=
        fun x wx h => lt_transY wx hβ.wf_of hw h hβlt
      cases hβ with
      | zero => exact wmax_zero
      | one => exact wmax_one
      | @K j hj =>
        have h1 := (lt_K_iffY (FYNF.K' hj) hm).mp hβlt
        simp only [lev] at h1
        exact ihm j (by omega) hj
      | mem hX _ _ => exact hX
      | plus hw' hb₁ hb₂ =>
        exact wmax_add hw'
          (ihβ _ (by size_omega) hb₁ (below _ hw'.plus.1 (lt_plus_leftY hw')))
          (ihβ _ (by size_omega) hb₂ (below _ hw'.plus.2.1 (lt_plus_rightY hw')))
      | om hw' hd =>
        exact wmax_om _ (ihβ _ (by size_omega) hd (below _ hw'.om.1 hw'.om.2.2)) hw'
      | xi hw' hK _ =>
        exfalso
        have h1 := (lt_K_iffY hw' hm).mp hβlt
        have h2 := (lt_K_iffY hw hw'.xi.1).mp hK
        simp only [lev] at h1 h2
        omega
      | psi hw' hσ _ _ =>
        exfalso
        have h1 := (lt_K_iffY hw' hm).mp hβlt
        have h2 := lev_le_of_lt_gen hσ
        simp only [lev] at h1 h2
        omega


/-- `Ξ_n(a)` と `Ψ^0_π(a)`：引数 `a ∈ Wmax` についての帰納法（Arai の Lemma 8.2 にあたる） -/
theorem wmax_coll : ∀ a, Wmax a →
    (∀ n, FYNF (.Xi n a) → Wmax (.Xi n a)) ∧
      (∀ π, Wmax π → FYNF (.Psi .zero π a) → Wmax (.Psi .zero π a)) := by
  have key : ∀ a, Acc (Rel Wmax) a → Wmax a →
      (∀ n, FYNF (.Xi n a) → Wmax (.Xi n a)) ∧
        (∀ π, Wmax π → FYNF (.Psi .zero π a) → Wmax (.Psi .zero π a)) := by
    intro a hacc
    induction hacc with
    | intro a _ MIH0 =>
      intro ha
      have MIH : ∀ b, Wmax b → Lt b a →
          (∀ n, FYNF (.Xi n b) → Wmax (.Xi n b)) ∧
            (∀ π, Wmax π → FYNF (.Psi .zero π b) → Wmax (.Psi .zero π b)) :=
        fun b hb hba => MIH0 b ⟨hb, hba⟩ hb
      have wa := wmax_wf ha
      -- 係数についての帰納法（引数の上界 `g ≤ a`）
      have coeff : ∀ {θ R g : Tm}, FYNF g → Le g a → ∀ S,
          (∀ x, Hull θ Wmax x → Lt x θ → x.size < S → Wmax x) →
          ∀ x, Hull θ Wmax x → x.size < S → (∀ w, w ∈ fr R x → Lt w θ) →
            inC x g R = true → Wmax x := by
        intro θ R g wg hga S good
        exact coeff_induction Wmax S good wmax_zero wmax_one (fun hn => wmax_K _ hn)
          (fun hw h1 h2 => wmax_add hw h1 h2) (fun hw h => wmax_om _ h hw)
          (fun hw he h => (MIH _ h (lt_of_lt_of_leY hw.xi.2.1 wg wa he hga)).1 _ hw)
          (fun hw he hπ h => (MIH _ h (lt_of_lt_of_leY hw.psi.2.2.2.1 wg wa he hga)).2 _ hπ hw)
      refine ⟨fun n hw => ?_, fun π hπ hw => ?_⟩
      · -- `Ξ_n(a)`
        have hn1 := hw.xi.1
        have wK := FYNF.K' hn1
        have hXK : Lt (.Xi n a) (.K n) := (lt_K_iffY hw hn1).mpr (Nat.le_refl _)
        have hnα := nr_specY _ hw
        have bound : ∀ x w, Hull (.Xi n a) Wmax x → Wmax w → Lt w (.Xi n a) → ¬ Lt w x →
            Wmax x := fun x w hx hW hwlt hn =>
          wmax_bounded hw hx hW (le_of_not_ltY (wmax_wf hW) hx.wf_of hn)
            (lt_transY (wmax_wf hW) hw hnα.1 hwlt hnα.2.2)
        refine wmax_of_good ⟨Hull.xi hw hXK (wmax_hull ha hw), ?_⟩
        intro β1
        induction β1 using size_induction with
        | h β1 LIH =>
          intro hβ hβlt
          have below : ∀ x, FYNF x → Lt x β1 → Lt x (.Xi n a) :=
            fun x wx h => lt_transY wx hβ.wf_of hw h hβlt
          cases hβ with
          | zero => exact wmax_zero
          | one => exact wmax_one
          | K hj => exact wmax_K _ hj
          | mem hX _ _ => exact hX
          | plus hw₁ hb₁ hb₂ =>
            exact wmax_add hw₁
              (LIH _ (by size_omega) hb₁ (below _ hw₁.plus.1 (lt_plus_leftY hw₁)))
              (LIH _ (by size_omega) hb₂ (below _ hw₁.plus.2.1 (lt_plus_rightY hw₁)))
          | om hw₁ hd =>
            exact wmax_om _ (LIH _ (by size_omega) hd (below _ hw₁.om.1 hw₁.om.2.2)) hw₁
          | @xi j d hw₁ hXKj hd =>
            have hjn : j = n := by
              have h1 := (lt_K_iffY hw hw₁.xi.1).mp hXKj
              have h2 := lev_le_of_lt_gen hβlt
              simp only [lev] at h1 h2
              omega
            subst hjn
            by_cases hda : d = a
            · subst hda
              exact absurd hβlt (Lt.irrefl _)
            rcases (ff_xiY hw₁ hw hda).mp hβlt with ⟨hdlt, hfr⟩ | ⟨-, w, hwfr, hwn⟩
            · have hdW : Wmax d := coeff hw₁.xi.2.1 (Or.inr hdlt) _
                (fun x hx hxθ hs => LIH x hs hx hxθ) d hd (by size_omega) hfr hw₁.xi.2.2.2.2
              exact (MIH d hdW hdlt).1 _ hw₁
            · exact bound _ w (Hull.xi hw₁ hXKj hd) (fr_wmax wK a ha w hwfr)
                (FYOrder.k2x hw w hwfr) hwn
          | @psi κ d hw₁ hσ hκ hd =>
            rcases hw₁.psi.2.1 with ⟨c', rfl, -⟩ | ⟨m, q, rfl⟩
            · exact absurd hβlt (Lt.asymmY hw hw₁ ((lt_OF_psiOm (Or.inl ⟨n, a, rfl⟩) hw hw₁).mpr
                ((lt_OF_omG (Or.inl ⟨n, a, rfl⟩) hw hw₁.psiOm.1).mp hσ)))
            · have hmn : m = n := by
                have h1 := lev_le_of_lt_gen hσ
                have h2 := lev_le_of_lt_gen hβlt
                simp only [lev] at h1 h2
                omega
              subst hmn
              obtain ⟨-, w, hwfr, hwn⟩ := wit_psi_xi hw₁ hw rfl hβlt hσ
              exact bound _ w (Hull.psi hw₁ hσ hκ hd) (fr_wmax wK a ha w hwfr)
                (FYOrder.k2x hw w hwfr) hwn
      · -- `Ψ^0_π(a)`
        have wπ := hw.psi.2.2.1
        have hπa := hw.psi.2.2.2.2.2
        have hnα := nr_specY _ hw
        have hγπ := lt_psi_targetY hw
        have bound : ∀ x w, Hull (.Psi .zero π a) Wmax x → Wmax w → Lt w (.Psi .zero π a) →
            ¬ Lt w x → Wmax x := fun x w hx hW hwlt hn =>
          wmax_bounded hw hx hW (le_of_not_ltY (wmax_wf hW) hx.wf_of hn)
            (lt_transY (wmax_wf hW) hw hnα.1 hwlt hnα.2.2)
        refine wmax_of_good ⟨Hull.psi hw hγπ (wmax_hull hπ hw) (wmax_hull ha hw), ?_⟩
        intro β1
        induction β1 using size_induction with
        | h β1 LIH =>
          intro hβ hβlt
          have good : ∀ x, Hull (.Psi .zero π a) Wmax x → Lt x (.Psi .zero π a) →
              x.size < β1.size → Wmax x := fun x hx hxθ hs => LIH x hs hx hxθ
          have below : ∀ x, FYNF x → Lt x β1 → Lt x (.Psi .zero π a) :=
            fun x wx h => lt_transY wx hβ.wf_of hw h hβlt
          cases hβ with
          | zero => exact wmax_zero
          | one => exact wmax_one
          | K hj => exact wmax_K _ hj
          | mem hX _ _ => exact hX
          | plus hw₁ hb₁ hb₂ =>
            exact wmax_add hw₁
              (LIH _ (by size_omega) hb₁ (below _ hw₁.plus.1 (lt_plus_leftY hw₁)))
              (LIH _ (by size_omega) hb₂ (below _ hw₁.plus.2.1 (lt_plus_rightY hw₁)))
          | om hw₁ hd =>
            exact wmax_om _ (LIH _ (by size_omega) hd (below _ hw₁.om.1 hw₁.om.2.2)) hw₁
          | @xi j d hw₁ hK hd =>
            rcases hw.psi.2.1 with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
            · exact wmax_bounded hw (Hull.xi hw₁ hK hd) (wmax_om_arg hπ)
                (Or.inr ((lt_OF_psiOm (Or.inl ⟨j, d, rfl⟩) hw₁ hw).mp hβlt))
                (lt_transY hw.psiOm.1 hw hnα.1 (FYOrder.cx hw) hnα.2.2)
            · have hjn : j = n := by
                have h1 := lev_le_of_lt_gen hβlt
                have h2 := (lt_K_iffY hw hw₁.xi.1).mp hK
                simp only [lev] at h1 h2
                omega
              subst hjn
              have wd := hw₁.xi.2.1
              have wp := wπ.xi.2.1
              have hn' := (lt_xi_psiY (π := .Xi j p) (n := j) rfl).mp hβlt
              rw [lt_psi_xiY (π := .Xi j p) (n := j) rfl] at hn'
              have hdπ : Lt (.Xi j d) (.Xi j p) := by
                cases e : cmp (Tm.Xi j p) (Tm.Xi j d) with
                | lt => exact absurd (Or.inl (by rw [e]; decide)) hn'
                | eq => exact absurd (Or.inl (by rw [e]; decide)) hn'
                | gt => exact lt_of_gtY wπ hw₁ e
              by_cases hda : Lt d a
              · have hC : inC d a (.Psi .zero (.Xi j p) a) = true := by
                  cases e : inC d a (Tm.Psi .zero (.Xi j p) a)
                  · exact absurd (Or.inr ⟨hda, e⟩) hn'
                  · rfl
                have hdW : Wmax d := coeff wa (Or.inl rfl) _ good d hd (by size_omega)
                  (fun w hw' => (fr_spec hw').2) hC
                exact (MIH d hdW hda).1 _ hw₁
              · have hpa : Lt p a := ((inC_xi_iff.mp hπa).resolve_left (Lt.irrefl _)).2
                have hpd : Lt p d := lt_of_lt_of_leY wp wa wd hpa (le_of_not_ltY wd wa hda)
                have hdp : d ≠ p := fun e => by subst e; exact Lt.irrefl _ hpd
                rcases (ff_xiY hw₁ wπ hdp).mp hdπ with ⟨hdp', -⟩ | ⟨-, w, hwfr, hwn⟩
                · exact absurd hdp' (Lt.asymmY wp wd hpd)
                · have hwπ := FYOrder.k2x wπ w hwfr
                  have hw' : w ∈ fr (.Xi j p) (.Xi j p) := by
                    rw [fr]
                    simp only [Lt.irrefl, ↓reduceIte]
                    exact fr_sub (FYNF.K' wπ.xi.1) wπ
                      (Or.inr ((lt_K_iffY wπ wπ.xi.1).mpr (Nat.le_refl _))) wp hwfr hwπ
                  exact bound _ w (Hull.xi hw₁ hK hd) (fr_wmax wπ _ hπ w hw')
                    (FYOrder.k2t hw w hw') hwn
          | @psi κ d hw₁ hσ hκ hd =>
            have wκ := hw₁.psi.2.2.1
            have wd := hw₁.psi.2.2.2.1
            have hl : lev κ = lev π := by
              have h1 := lev_le_of_lt_gen hσ
              have h2 := lev_le_of_lt_gen hβlt
              simp only [lev] at h1 h2
              omega
            rcases triY wκ wπ with hκπ | e | hπκ
            · obtain ⟨w, hwfr, hwn⟩ := wit_psi_psi hw₁ hw hl hβlt hσ hκπ
              rcases hwfr with hwfr | hwfr
              · exact bound _ w (Hull.psi hw₁ hσ hκ hd) (fr_wmax wπ a ha w hwfr)
                  (FYOrder.k2 hw w hwfr) hwn
              · exact bound _ w (Hull.psi hw₁ hσ hκ hd) (fr_wmax wπ π hπ w hwfr)
                  (FYOrder.k2t hw w hwfr) hwn
            · subst e
              by_cases hda : d = a
              · subst hda
                exact absurd hβlt (Lt.irrefl _)
              rcases (ff_psiY hw₁ hw hda).mp hβlt with ⟨hdlt, hfr⟩ | ⟨-, w, hwfr, hwn⟩
              · have hdW : Wmax d := coeff wd (Or.inr hdlt) _ good d hd (by size_omega) hfr
                  hw₁.psi.2.2.2.2.1
                exact (MIH d hdW hdlt).2 _ hπ hw₁
              · exact bound _ w (Hull.psi hw₁ hσ hκ hd) (fr_wmax wκ a ha w hwfr)
                  (FYOrder.k2 hw w hwfr) hwn
            · rcases (lt_psi_psiY hl hβlt.ne).mp hβlt with
                h1 | ⟨-, hβπ, (⟨hda, hdC, hκC⟩ | ⟨had, hn⟩)⟩
              · exact absurd hσ h1
              · have hdW : Wmax d := coeff wa (Or.inl rfl) _ good d hd (by size_omega)
                  (fun w hw' => (fr_spec hw').2) hdC
                have hκW : Wmax κ := coeff wa (Or.inl rfl) _ good κ hκ (by size_omega)
                  (fun w hw' => (fr_spec hw').2) hκC
                exact (MIH d hdW hda).2 _ hκW hw₁
              · obtain ⟨w, hwfr, hwn⟩ := wit_c2 hw₁ hw (le_of_ne_gtY wa wd had) hβπ hn
                rcases hwfr with hwfr | hwfr
                · exact bound _ w (Hull.psi hw₁ hσ hκ hd) (fr_wmax wπ a ha w hwfr)
                    (FYOrder.k2 hw w hwfr) hwn
                · exact bound _ w (Hull.psi hw₁ hσ hκ hd) (fr_wmax wπ π hπ w hwfr)
                    (FYOrder.k2t hw w hwfr) hwn
  intro a ha
  exact key a (wmax_acc ha) ha

/-- `FY` の標準形は全て最大区別集合に入る -/
theorem wmax_of_FYNF : ∀ t : Tm, FYNF t → Wmax t
  | .zero, _ => wmax_zero
  | .one, _ => wmax_one
  | .K _, h => wmax_K _ h.k
  | .plus a b, h => wmax_add h (wmax_of_FYNF a h.plus.1) (wmax_of_FYNF b h.plus.2.1)
  | .Om a, h => wmax_om a (wmax_of_FYNF a h.om.1) h
  | .Xi _ a, h => (wmax_coll a (wmax_of_FYNF a h.xi.2.1)).1 _ h
  | .Psi _ p a, h => by
    obtain ⟨rfl, -, hp, ha, -, -⟩ := h.psi
    exact (wmax_coll a (wmax_of_FYNF a ha)).2 p (wmax_of_FYNF p hp) h

end RTKA.WFY

namespace RTKA

open WFY

variable [FYOrder]

theorem acc_FY {t : Tm} (ht : FYNF t) : Acc (fun u v => FYNF u ∧ Lt u v) t := by
  have key : ∀ t, Acc (Rel Wmax) t → Acc (fun u v => FYNF u ∧ Lt u v) t := by
    intro t hacc
    induction hacc with
    | intro t _ ih => exact Acc.intro t (fun u hu => ih u ⟨wmax_of_FYNF u hu.1, hu.2⟩)
  exact key t (wmax_acc (wmax_of_FYNF t ht))

/-- 順序の仮定 `FYOrder` の下で、`FY` の標準形の上の `<` は整礎 -/
theorem wellFounded_FY : WellFounded (fun a b : {t : Tm // FYNF t} => Lt a.1 b.1) := by
  constructor
  rintro ⟨t, ht⟩
  have key : ∀ t, Acc (fun u v => FYNF u ∧ Lt u v) t → ∀ ht : FYNF t,
      Acc (fun a b : {t : Tm // FYNF t} => Lt a.1 b.1) ⟨t, ht⟩ := by
    intro t h
    induction h with
    | intro t _ ih =>
      intro ht
      exact Acc.intro _ (fun ⟨u, hu⟩ hlt => ih u ⟨hu, hlt⟩ hu)
  exact key t (acc_FY ht) ht

end RTKA
