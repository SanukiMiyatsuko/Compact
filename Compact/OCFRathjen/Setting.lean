import Compact.OCFRathjen.Club

/-! 基数の設定：`K_1 < K_2 < ⋯`、`Λ = sup K_n`、`Ω_ξ`。

* `K_n`（`n ≥ 1`）は正則で、正則基数の極限（弱到達不能）であることだけを課す（`Setting`）。
  弱コンパクト性（`WeaklyCompactCard`：非可算正則で分割性 `PartitionProp`）は `Setting` に含めず、
  `WeaklyCompact.lean` で弱コンパクト基数の列から `Setting` と `StationaryHyp`（`Eval.lean`）を導く。
* `Ω_ξ` は `{0} ∪ closure R` の数え上げ。`Ω_0 = 0`、`Ω_{ξ+1}` は正則（`Om_succ_R`）で、
  `Ω` は `Λ` 未満で狭義増加かつ連続、`Ω_{K_n} = K_n`。 -/

namespace OCF.Rathjen

universe u

open Ordinal

noncomputable section

/-! ### `Ω` -/

/-- `{0} ∪ closure R`（`0` と非可算基数） -/
def CardSet (ξ : Ordinal.{u}) : Prop := ξ = 0 ∨ closure R ξ

/-! ### 弱コンパクト性 -/

/-- `f` は `H` 上で一様な色を持つ。 -/
def Homogeneous (f : Ordinal.{u} → Ordinal.{u} → Bool) (H : Ordinal.{u} → Prop) : Prop :=
  ∃ c, ∀ x y, H x → H y → x < y → f x y = c

/-- すべての二色彩色に対して、非有界な一様部分集合がある。 -/
def PartitionProp (κ : Ordinal.{u}) : Prop :=
  ∀ f, ∃ H, (∀ x, H x → x < κ) ∧ Unbounded κ H ∧ Homogeneous f H

/-- The carrier point whose initial segment has order type `x`. -/
noncomputable def pointBelow (κ x : Ordinal.{u}) (hx : x < κ) :
    (representative κ).Carrier :=
  Classical.choose (initial_surjective κ x hx)

theorem pointBelow_spec {κ x : Ordinal.{u}} (hx : x < κ) :
    x = type ((representative κ).below (pointBelow κ x hx)) :=
  Classical.choose_spec (initial_surjective κ x hx)

/-- Strict lexicographic order on binary functions restricted to an ordinal. -/
def LexBelow (δ : Ordinal.{u}) (a b : Ordinal.{u} → Bool) : Prop :=
  ∃ ξ, ξ < δ ∧ a ξ = false ∧ b ξ = true ∧ ∀ η, η < ξ → a η = b η

/-- Two binary functions that differ below `δ` are comparable in lexicographic
order. -/
theorem lexBelow_total_of_diff {δ : Ordinal.{u}} {a b : Ordinal.{u} → Bool}
    (hdiff : ∃ ξ, ξ < δ ∧ a ξ ≠ b ξ) : LexBelow δ a b ∨ LexBelow δ b a := by
  classical
  obtain ⟨ξ, hP, hmin⟩ := Ordinal.exists_min
    (fun x => x < δ ∧ a x ≠ b x) hdiff
  have hξ : ξ < δ := hP.1
  have hneq : a ξ ≠ b ξ := hP.2
  have hbefore : ∀ η, η < ξ → a η = b η := by
    intro η hη
    by_cases heq : a η = b η
    · exact heq
    · exact False.elim (hmin η hη ⟨lt_trans η ξ δ hη hξ, heq⟩)
  cases ha : a ξ with
  | false =>
    cases hb : b ξ with
    | false => exact False.elim (hneq (by simp [ha, hb]))
    | true => exact Or.inl ⟨ξ, hξ, ha, hb, hbefore⟩
  | true =>
    cases hb : b ξ with
    | false => exact Or.inr ⟨ξ, hξ, hb, ha, fun η hη => (hbefore η hη).symm⟩
    | true => exact False.elim (hneq (by simp [ha, hb]))

/-- If two functions are both zero at and above `δ`, then any distinct pair
differs below `δ` and is lexicographically comparable there. -/
theorem lexBelow_total_of_supported {δ : Ordinal.{u}} {a b : Ordinal.{u} → Bool}
    (ha : ∀ ξ, δ ≤ ξ → a ξ = false) (hb : ∀ ξ, δ ≤ ξ → b ξ = false)
    (hne : a ≠ b) : LexBelow δ a b ∨ LexBelow δ b a := by
  classical
  have hdiff : ∃ ξ, ξ < δ ∧ a ξ ≠ b ξ := by
    apply Classical.byContradiction
    intro hn
    apply hne
    funext ξ
    cases lt_or_le ξ δ with
    | inl hξ =>
      by_cases heq : a ξ = b ξ
      · exact heq
      · exact False.elim (hn ⟨ξ, hξ, heq⟩)
    | inr hξ => rw [ha ξ hξ, hb ξ hξ]
  exact lexBelow_total_of_diff hdiff

/-- A lexicographic comparison whose first-difference coordinate lies past
`ε` restricts to the same comparison below `ε`, provided the values at `ε`
already point in the opposite direction. -/
theorem lexBelow_shrink {δ ε : Ordinal.{u}} {a b : Ordinal.{u} → Bool}
    (h : LexBelow δ a b) (hε : ε < δ)
    (ha : a ε = true) (hb : b ε = false) : LexBelow ε a b := by
  obtain ⟨ξ, hξ, hax, hbx, hbefore⟩ := h
  have hξε : ξ < ε := by
    apply lt_of_not_le
    intro hle
    cases hle with
    | inl hlt =>
      have heq := hbefore ε hlt
      have hbad : true = false := by
        calc
          true = a ε := ha.symm
          _ = b ε := heq
          _ = false := hb
      cases hbad
    | inr heq =>
      subst ε
      have hbad : true = false := by
        calc
          true = a ξ := ha.symm
          _ = false := hax
      cases hbad
  exact ⟨ξ, hξε, hax, hbx, fun η hη => hbefore η hη⟩

/-- Lexicographic comparisons are preserved by replacing either function with
one that agrees below the comparison bound. -/
theorem lexBelow_congr {δ : Ordinal.{u}} {a b c d : Ordinal.{u} → Bool}
    (hab : ∀ ξ, ξ < δ → a ξ = b ξ) (hcd : ∀ ξ, ξ < δ → c ξ = d ξ)
    (h : LexBelow δ a c) : LexBelow δ b d := by
  obtain ⟨ξ, hξ, hax, hcx, hbefore⟩ := h
  have hbx : b ξ = false := by rw [← hab ξ hξ, hax]
  have hdx : d ξ = true := by rw [← hcd ξ hξ, hcx]
  refine ⟨ξ, hξ, hbx, hdx, ?_⟩
  intro η hη
  rw [← hab η (lt_trans η ξ δ hη hξ), hbefore η hη,
    hcd η (lt_trans η ξ δ hη hξ)]

/-- The strict lexicographic relation is transitive. -/
theorem lexBelow_trans {δ : Ordinal.{u}} {a b c : Ordinal.{u} → Bool}
    (hab : LexBelow δ a b) (hbc : LexBelow δ b c) : LexBelow δ a c := by
  obtain ⟨ξ, hξ, hax, hbx, habefore⟩ := hab
  obtain ⟨η, hη, hby, hcy, hbcbefore⟩ := hbc
  rcases lt_total ξ η with hξη | heq | hηξ
  · refine ⟨ξ, hξ, hax, ?_, ?_⟩
    · have hbcξ := hbcbefore ξ hξη
      calc
        c ξ = b ξ := hbcξ.symm
        _ = true := hbx
    · intro ζ hζ
      calc
        a ζ = b ζ := habefore ζ hζ
        _ = c ζ := hbcbefore ζ (lt_trans ζ ξ η hζ hξη)
  · subst η
    have hbad : true = false := by
      calc
        true = b ξ := hbx.symm
        _ = false := hby
    cases hbad
  · refine ⟨η, hη, ?_, hcy, ?_⟩
    · have habη := habefore η hηξ
      calc
        a η = b η := habη
        _ = false := hby
    · intro ζ hζ
      calc
        a ζ = b ζ := habefore ζ (lt_trans ζ η ξ hζ hηξ)
        _ = c ζ := hbcbefore ζ hζ

/-- If the first difference is not below `ε`, the two functions agree below
`ε`; otherwise their strict comparison already appears there. -/
theorem lexBelow_restrict_or_agree {δ ε : Ordinal.{u}}
    {a b : Ordinal.{u} → Bool} (h : LexBelow δ a b) :
    LexBelow ε a b ∨ (∀ ξ, ξ < ε → a ξ = b ξ) := by
  obtain ⟨ξ, hξ, hax, hbx, hbefore⟩ := h
  cases lt_or_le ξ ε with
  | inl hξε => exact Or.inl ⟨ξ, hξε, hax, hbx, hbefore⟩
  | inr hle =>
    right
    intro η hη
    exact hbefore η (lt_of_lt_of_le hη hle)

/-- A strict lexicographic comparison cannot have `true` on the left and
`false` on the right at `ε` when the functions agree below `ε`. -/
theorem lexBelow_not_true_false {δ ε : Ordinal.{u}} {a b : Ordinal.{u} → Bool}
    (h : LexBelow δ a b)
    (hprefix : ∀ ξ, ξ < ε → a ξ = b ξ)
    (ha : a ε = true) (hb : b ε = false) : False := by
  obtain ⟨ξ, hξ, hax, hbx, hbefore⟩ := h
  cases lt_total ξ ε with
  | inl hξε =>
    have heq := hprefix ξ hξε
    have hbad : false = true := by
      calc
        false = a ξ := hax.symm
        _ = b ξ := heq
        _ = true := hbx
    cases hbad
  | inr hge =>
    cases hge with
    | inl heq =>
      subst ε
      have hbad : false = true := by
        calc
          false = a ξ := hax.symm
          _ = true := ha
      cases hbad
    | inr hεξ =>
      have heq := hbefore ε hεξ
      have hbad : true = false := by
        calc
          true = a ε := ha.symm
          _ = b ε := heq
          _ = false := hb
      cases hbad

/-- Agreement on a coordinate initial segment. -/
def AgreeBelow (δ : Ordinal.{u}) (a b : Ordinal.{u} → Bool) : Prop :=
  ∀ ξ, ξ < δ → a ξ = b ξ

/-- The non-strict lexicographic order, identifying functions that agree below
the bound. -/
def LexLe (δ : Ordinal.{u}) (a b : Ordinal.{u} → Bool) : Prop :=
  LexBelow δ a b ∨ AgreeBelow δ a b

theorem lexBelow_irrefl {δ : Ordinal.{u}} {a : Ordinal.{u} → Bool} :
    ¬ LexBelow δ a a := by
  rintro ⟨ξ, hξ, hfalse, htrue, _⟩
  have hbad : false = true := hfalse.symm.trans htrue
  cases hbad

theorem agreeBelow_symm {δ : Ordinal.{u}} {a b : Ordinal.{u} → Bool}
    (h : AgreeBelow δ a b) : AgreeBelow δ b a :=
  fun ξ hξ => (h ξ hξ).symm

theorem agreeBelow_trans {δ : Ordinal.{u}} {a b c : Ordinal.{u} → Bool}
    (hab : AgreeBelow δ a b) (hbc : AgreeBelow δ b c) : AgreeBelow δ a c :=
  fun ξ hξ => (hab ξ hξ).trans (hbc ξ hξ)

theorem lexLe_refl {δ : Ordinal.{u}} (a : Ordinal.{u} → Bool) : LexLe δ a a :=
  Or.inr (fun _ _ => rfl)

theorem lexLe_trans {δ : Ordinal.{u}} {a b c : Ordinal.{u} → Bool}
    (hab : LexLe δ a b) (hbc : LexLe δ b c) : LexLe δ a c := by
  cases hab with
  | inl hab =>
    cases hbc with
    | inl hbc => exact Or.inl (lexBelow_trans hab hbc)
    | inr hbc =>
      exact Or.inl (lexBelow_congr (fun _ _ => rfl) hbc hab)
  | inr hab =>
    cases hbc with
    | inl hbc =>
      exact Or.inl (lexBelow_congr (agreeBelow_symm hab) (fun _ _ => rfl) hbc)
    | inr hbc => exact Or.inr (agreeBelow_trans hab hbc)

theorem lexLe_antisymm {δ : Ordinal.{u}} {a b : Ordinal.{u} → Bool}
    (hab : LexLe δ a b) (hba : LexLe δ b a) : AgreeBelow δ a b := by
  cases hab with
  | inl hab =>
    cases hba with
    | inl hba => exact False.elim (lexBelow_irrefl (lexBelow_trans hab hba))
    | inr hba =>
      have hbad := lexBelow_congr (fun _ _ => rfl) hba hab
      exact False.elim (lexBelow_irrefl hbad)
  | inr hab =>
    cases hba with
    | inl hba =>
      have hbad := lexBelow_congr (fun _ _ => rfl) hab hba
      exact False.elim (lexBelow_irrefl hbad)
    | inr _hba => exact hab

theorem lexLe_of_le {δ : Ordinal.{u}} {a b : Ordinal.{u} → Bool}
    (h : LexBelow δ a b) : LexLe δ a b := Or.inl h

theorem lexLe_restrict {δ ε : Ordinal.{u}} {a b : Ordinal.{u} → Bool}
    (h : LexBelow δ a b) : LexLe ε a b := by
  cases lexBelow_restrict_or_agree h with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr h

noncomputable def lexBelowCoord {δ : Ordinal.{u}} {a b : Ordinal.{u} → Bool}
    (h : LexBelow δ a b) : Ordinal.{u} := Classical.choose h

theorem lexBelowCoord_spec {δ : Ordinal.{u}} {a b : Ordinal.{u} → Bool}
    (h : LexBelow δ a b) :
    lexBelowCoord h < δ ∧ a (lexBelowCoord h) = false ∧
      b (lexBelowCoord h) = true ∧
      ∀ η, η < lexBelowCoord h → a η = b η := Classical.choose_spec h

/-- A nondecreasing sequence in the initial-segment lex order either has an
unbounded fiber or contains a strictly increasing subsequence of full regular
length. -/
theorem lexLe_unbounded_fiber_or_chain {κ δ : Ordinal.{u}}
    (hκ : IsRegular κ) (g : Ordinal.{u} → Ordinal.{u} → Bool)
    (hmono : ∀ i j, i < κ → j < κ → i < j → LexLe δ (g i) (g j)) :
    (∃ p, Unbounded κ (fun i => i < κ ∧ AgreeBelow δ (g i) (g p))) ∨
    (∃ s : Ordinal.{u} → (Ordinal.{u} → Bool),
      ∀ i j, i < κ → j < κ → i < j → LexBelow δ (s i) (s j)) := by
  classical
  let A : Ordinal.{u} → Prop := fun i =>
    i < κ ∧ ∀ j, j < i → ¬ AgreeBelow δ (g j) (g i)
  by_cases hA : Unbounded κ A
  · right
    let e : Ordinal.{u} → Ordinal.{u} := enum A
    have he := enum_below_regular hκ hA
    refine ⟨fun i => g (e i), ?_⟩
    intro i j hi hj hij
    have hiκ := (he i hi).2
    have hjκ := (he j hj).2
    have hij' := (he j hj).1.lt hij
    have horder := hmono (e i) (e j) hiκ hjκ hij'
    cases horder with
    | inl hstrict => exact hstrict
    | inr heq =>
      have hnew : A (e j) := (he j hj).1.mem
      exact False.elim (hnew.2 (e i) hij' heq)
  · left
    have hbound : ∃ b, b < κ ∧ ∀ i, i < κ → A i → i ≤ b := by
      apply Classical.byContradiction
      intro hn
      have hA' : Unbounded κ A := by
        intro η hη
        have hnot : ¬ ∀ i, i < κ → A i → i ≤ η := by
          intro hle
          exact hn ⟨η, hη, hle⟩
        have hex : ∃ i, i < κ ∧ A i ∧ ¬ i ≤ η := by
          apply Classical.byContradiction
          intro h
          apply hnot
          intro i hi hAi
          by_cases hle : i ≤ η
          · exact hle
          · exact False.elim (h ⟨i, hi, hAi, hle⟩)
        obtain ⟨i, hi, hAi, hnotle⟩ := hex
        exact ⟨i, hAi, lt_of_not_le hnotle, hi⟩
      exact hA hA'
    obtain ⟨b, hb, hbA⟩ := hbound
    have hmonoLE : ∀ i j, i < κ → j < κ → i ≤ j → LexLe δ (g i) (g j) := by
      intro i j hi hj hij
      cases hij with
      | inl hlt => exact hmono i j hi hj hlt
      | inr heq => subst j; exact lexLe_refl _
    have heventual : ∀ i, b < i → i < κ → AgreeBelow δ (g b) (g i) := by
      intro i hbi hiκ
      have hnotNew : ¬ A i := fun hAi => not_lt_of_le (hbA i hiκ hAi) hbi
      have hprevious : ∃ j, j < i ∧ AgreeBelow δ (g j) (g i) := by
        apply Classical.byContradiction
        intro hn
        apply hnotNew
        refine ⟨hiκ, ?_⟩
        intro j hji
        intro heq
        exact hn ⟨j, hji, heq⟩
      obtain ⟨j, ⟨hj, hji⟩, hmin⟩ :=
        Ordinal.exists_min (fun j => j < i ∧ AgreeBelow δ (g j) (g i)) hprevious
      have hjκ : j < κ := lt_trans j i κ hj hiκ
      have hnewj : A j := by
        refine ⟨hjκ, ?_⟩
        intro k hkj heqkj
        apply hmin k hkj
        exact ⟨lt_trans k j i hkj hj, agreeBelow_trans heqkj hji⟩
      have hjb : j ≤ b := hbA j hjκ hnewj
      have hjb' : LexLe δ (g j) (g b) := hmonoLE j b hjκ hb hjb
      have hbj : LexLe δ (g b) (g j) := by
        have hbj' : LexLe δ (g b) (g i) := hmono b i hb hiκ hbi
        have hij' : LexLe δ (g i) (g j) := Or.inr (agreeBelow_symm hji)
        exact lexLe_trans hbj' hij'
      have heqjb : AgreeBelow δ (g j) (g b) := lexLe_antisymm hjb' hbj
      exact agreeBelow_trans (agreeBelow_symm heqjb) hji
    refine ⟨b, ?_⟩
    intro η hη
    cases lt_or_le η b with
    | inl hηb =>
      let i := succ b
      have hiκ : i < κ := hκ.1.2 b hb
      have hbi : b < i := lt_succ_self b
      exact ⟨i, ⟨hiκ, agreeBelow_symm (heventual i hbi hiκ)⟩,
        lt_trans η b i hηb hbi, hiκ⟩
    | inr hbe =>
      let i := succ η
      have hiκ : i < κ := hκ.1.2 η hη
      have hbi : b < i := lt_of_le_of_lt hbe (lt_succ_self η)
      exact ⟨i, ⟨hiκ, agreeBelow_symm (heventual i hbi hiκ)⟩,
        lt_succ_self η, hiκ⟩

/-- A regular ordinal has no strictly monotone sequence of binary functions
in lexicographic order when the coordinate length is smaller. -/
theorem no_long_lexBelow_inc {κ : Ordinal.{u}} (hκ : IsRegular κ) :
    ∀ δ, δ < κ → ¬ ∃ s : Ordinal.{u} → (Ordinal.{u} → Bool),
      ∀ i j, i < κ → j < κ → i < j → LexBelow δ (s i) (s j) := by
  intro δ hδκ
  induction δ using lt_wellFounded.induction with
  | h δ ih =>
    intro hchain
    classical
    obtain ⟨s, hs⟩ := hchain
    let d : Ordinal.{u} → Ordinal.{u} := fun i =>
      if hi : i < κ then
        lexBelowCoord (hs i (succ i) hi (hκ.1.2 i hi) (lt_succ_self i))
      else 0
    have hdlt : ∀ i, i < κ → d i < δ := by
      intro i hi
      simp only [d, dite_eq_left hi]
      exact (lexBelowCoord_spec (hs i (succ i) hi (hκ.1.2 i hi)
        (lt_succ_self i))).1
    obtain ⟨ε, hεδ, hI⟩ := exists_unbounded_fiber hκ hδκ d hdlt
    let I : Ordinal.{u} → Prop := fun i => i < κ ∧ d i = ε
    let e : Ordinal.{u} → Ordinal.{u} := enum I
    have he := enum_below_regular hκ hI
    have hprefixMono : ∀ i j, i < κ → j < κ → i < j →
        LexLe ε (s (e i)) (s (e j)) := by
      intro i j hi hj hij
      have hie : e i < κ := (he i hi).2
      have hje : e j < κ := (he j hj).2
      have hij' := (he j hj).1.lt hij
      exact lexLe_restrict (hs (e i) (e j) hie hje hij')
    have hnoSmall : ¬ ∃ t : Ordinal.{u} → (Ordinal.{u} → Bool),
        ∀ i j, i < κ → j < κ → i < j → LexBelow ε (t i) (t j) :=
      ih ε hεδ (lt_trans ε δ κ hεδ hδκ)
    have hfiber := lexLe_unbounded_fiber_or_chain hκ (fun i => s (e i)) hprefixMono
    have hpref : ∃ p, Unbounded κ
        (fun i => i < κ ∧ AgreeBelow ε (s (e i)) (s (e p))) := by
      cases hfiber with
      | inl h => exact h
      | inr h => exact False.elim (hnoSmall h)
    obtain ⟨p, hpre⟩ := hpref
    obtain ⟨i, hiMem, hi0, hiκ⟩ := hpre 0 hκ.pos
    have hsiκ : succ i < κ := hκ.1.2 i hiκ
    obtain ⟨j, hjMem, hij, hjκ⟩ := hpre (succ i) hsiκ
    have hisucc : i < succ i := lt_succ_self i
    have hise : e i < e (succ i) := (he (succ i) hsiκ).1.lt hisucc
    have hsuccLe : succ (e i) ≤ e (succ i) := succ_le_of_lt hise
    have hesuccj : e (succ i) < e j := (he j hjκ).1.lt hij
    have hstep : succ (e i) < e j := lt_of_le_of_lt hsuccLe hesuccj
    have hieκ : e i < κ := (he i hiκ).2
    have hjeκ : e j < κ := (he j hjκ).2
    have hsuccieκ : succ (e i) < κ := hκ.1.2 (e i) hieκ
    have hiI : I (e i) := (he i hiκ).1.mem
    have hjI : I (e j) := (he j hjκ).1.mem
    have hdi : d (e i) = ε := hiI.2
    have hdj : d (e j) = ε := hjI.2
    have hfirsti : LexBelow δ (s (e i)) (s (succ (e i))) :=
      hs (e i) (succ (e i)) hieκ hsuccieκ (lt_succ_self _)
    have hfirstj : LexBelow δ (s (e j)) (s (succ (e j))) :=
      hs (e j) (succ (e j)) hjeκ (hκ.1.2 (e j) hjeκ) (lt_succ_self _)
    have hcoordi : lexBelowCoord hfirsti = ε := by
      simpa [d, hieκ] using hdi
    have hcoordj : lexBelowCoord hfirstj = ε := by
      simpa [d, hjeκ] using hdj
    obtain ⟨_, hfalsei, htruei, hbeforei⟩ := lexBelowCoord_spec hfirsti
    obtain ⟨_, hfalsej, htruej, _⟩ := lexBelowCoord_spec hfirstj
    rw [hcoordi] at hfalsei htruei hbeforei
    rw [hcoordj] at hfalsej htruej
    have hpi : AgreeBelow ε (s (e i)) (s (e p)) := hiMem.2
    have hpj : AgreeBelow ε (s (e j)) (s (e p)) := hjMem.2
    have hpreij : AgreeBelow ε (s (e i)) (s (e j)) :=
      agreeBelow_trans hpi (agreeBelow_symm hpj)
    have hpresuccj : AgreeBelow ε (s (succ (e i))) (s (e j)) :=
      agreeBelow_trans (agreeBelow_symm hbeforei) hpreij
    have hbad := lexBelow_not_true_false (hs (succ (e i)) (e j) hsuccieκ hjeκ hstep)
      hpresuccj htruei hfalsej
    exact hbad

theorem lexBelow_complement_reverse {δ : Ordinal.{u}} {a b : Ordinal.{u} → Bool}
    (h : LexBelow δ b a) :
    LexBelow δ (fun ξ => Bool.not (a ξ)) (fun ξ => Bool.not (b ξ)) := by
  obtain ⟨ξ, hξ, hbξ, haξ, hbefore⟩ := h
  refine ⟨ξ, hξ, ?_, ?_, ?_⟩
  · simp [haξ]
  · simp [hbξ]
  · intro η hη
    change Bool.not (a η) = Bool.not (b η)
    exact congrArg Bool.not (hbefore η hη).symm

/-- The corresponding assertion for a strictly decreasing lexicographic
sequence follows by complementing every bit. -/
theorem no_long_lexBelow_dec {κ : Ordinal.{u}} (hκ : IsRegular κ) :
    ∀ δ, δ < κ → ¬ ∃ s : Ordinal.{u} → (Ordinal.{u} → Bool),
      ∀ i j, i < κ → j < κ → i < j → LexBelow δ (s j) (s i) := by
  intro δ hδκ hchain
  obtain ⟨s, hs⟩ := hchain
  apply no_long_lexBelow_inc hκ δ hδκ
  refine ⟨fun i ξ => Bool.not (s i ξ), ?_⟩
  intro i j hi hj hij
  exact lexBelow_complement_reverse (hs i j hi hj hij)

/-- `f` preserves ordinal order on `H` when compared by `ltX`. -/
def OrderMonotoneOn (κ : Ordinal.{u}) (H : Ordinal.{u} → Prop)
    {X : Type u} (ltX : X → X → Prop) (f : (representative κ).Carrier → X) : Prop :=
  ∀ x y (_hx : H x) (_hy : H y) (hxκ : x < κ) (hyκ : y < κ) (_hxy : x < y),
    ltX (f (pointBelow κ x hxκ)) (f (pointBelow κ y hyκ))

/-- `f` reverses ordinal order on `H` when compared by `ltX`. -/
def OrderAntitoneOn (κ : Ordinal.{u}) (H : Ordinal.{u} → Prop)
    {X : Type u} (ltX : X → X → Prop) (f : (representative κ).Carrier → X) : Prop :=
  ∀ x y (_hx : H x) (_hy : H y) (hxκ : x < κ) (hyκ : y < κ) (_hxy : x < y),
    ltX (f (pointBelow κ y hyκ)) (f (pointBelow κ x hxκ))

/-- The pair partition property turns an injection into a pairwise-comparable
relation into an unbounded subset on which the relation is uniformly oriented. -/
theorem PartitionProp.orient {κ : Ordinal.{u}} (hpart : PartitionProp κ)
    {X : Type u} (ltX : X → X → Prop)
    (htotal : ∀ a b, a ≠ b → ltX a b ∨ ltX b a)
    (f : (representative κ).Carrier → X) (hf : ∀ x y, f x = f y → x = y) :
    ∃ H, (∀ x, H x → x < κ) ∧ Unbounded κ H ∧
      (OrderMonotoneOn κ H ltX f ∨ OrderAntitoneOn κ H ltX f) := by
  classical
  let point : (x : Ordinal.{u}) → x < κ → (representative κ).Carrier :=
    fun x hx => Classical.choose (initial_surjective κ x hx)
  let coloring : Ordinal.{u} → Ordinal.{u} → Bool := fun x y =>
    if hx : x < κ then
      if hy : y < κ then
        if ltX (f (point x hx)) (f (point y hy)) then false else true
      else false
    else false
  obtain ⟨H, hHκ, hHunb, hHhom⟩ := hpart coloring
  obtain ⟨c, hc⟩ := hHhom
  refine ⟨H, hHκ, hHunb, ?_⟩
  cases c with
  | false =>
    left
    intro x y hx hy hxκ hyκ hxy
    have hcolor := hc x y hx hy hxy
    by_cases hlt : ltX (f (point x hxκ)) (f (point y hyκ))
    · exact hlt
    · simp [coloring, hxκ, hyκ, hlt] at hcolor
  | true =>
    right
    intro x y hx hy hxκ hyκ hxy
    have hcolor := hc x y hx hy hxy
    have hnot : ¬ ltX (f (point x hxκ)) (f (point y hyκ)) := by
      intro hlt
      simp [coloring, hxκ, hyκ, hlt] at hcolor
    have hpoint_ne : point x hxκ ≠ point y hyκ := by
      intro heq
      have hxrep := Classical.choose_spec (initial_surjective κ x hxκ)
      have hyrep := Classical.choose_spec (initial_surjective κ y hyκ)
      have htype := congrArg (fun z => type ((representative κ).below z)) heq
      have hxy_eq : x = y := hxrep.trans (htype.trans hyrep.symm)
      exact (ne_of_lt hxy) hxy_eq
    cases htotal (f (point x hxκ)) (f (point y hyκ)) (fun heq =>
        hpoint_ne (hf _ _ heq)) with
    | inl hlt => exact False.elim (hnot hlt)
    | inr hgt => exact hgt

/-- The partition property at a regular ordinal rules out injections into
binary sequences of any shorter coordinate length. -/
theorem WeaklyCompactCard.no_injective_bool_sequences {κ δ : Ordinal.{u}}
    (hκ : R κ ∧ PartitionProp κ) (hδ : δ < κ)
    (f : (representative κ).Carrier → ((representative δ).Carrier → Bool))
    (hf : ∀ x y, f x = f y → x = y) : False := by
  classical
  let lift : ((representative δ).Carrier → Bool) → (Ordinal.{u} → Bool) := fun a ξ =>
    if hξ : ξ < δ then a (pointBelow δ ξ hξ) else false
  have hlift_inj : ∀ a b, lift a = lift b → a = b := by
    intro a b hab
    funext y
    let ξ := type ((representative δ).below y)
    have hξ : ξ < δ := initial_lt δ y
    have hpoint : pointBelow δ ξ hξ = y := by
      apply initial_injective δ
      dsimp [ξ]
      exact (pointBelow_spec hξ).symm
    have hEval := congrFun hab ξ
    simp [lift, hξ] at hEval
    rw [hpoint] at hEval
    exact hEval
  have hlift_supp : ∀ a ξ, δ ≤ ξ → lift a ξ = false := by
    intro a ξ hξ
    have hnot : ¬ ξ < δ := not_lt_of_le hξ
    simp [lift, hnot]
  let f' : (representative κ).Carrier → (representative δ).Carrier → Bool := f
  have hf' : ∀ x y, f' x = f' y → x = y := hf
  let ltX : ((representative δ).Carrier → Bool) →
      ((representative δ).Carrier → Bool) → Prop := fun a b =>
    LexBelow δ (lift a) (lift b)
  have htotal : ∀ a b, a ≠ b → ltX a b ∨ ltX b a := by
    intro a b hne
    have hne' : lift a ≠ lift b := fun he => hne (hlift_inj a b he)
    exact lexBelow_total_of_supported (hlift_supp a) (hlift_supp b) hne'
  obtain ⟨H, _hHκ, hHunb, hOrient⟩ :=
    PartitionProp.orient (κ := κ) hκ.2 (X := (representative δ).Carrier → Bool)
      ltX htotal f' hf'
  have he := enum_below_regular hκ.1.2 hHunb
  let e : Ordinal.{u} → Ordinal.{u} := enum H
  let g : Ordinal.{u} → (Ordinal.{u} → Bool) := fun i =>
    if hi : i < κ then lift (f (pointBelow κ (e i) (he i hi).2)) else fun _ => false
  have hinc : ∃ s : Ordinal.{u} → (Ordinal.{u} → Bool),
      ∀ i j, i < κ → j < κ → i < j → LexBelow δ (s i) (s j) := by
    cases hOrient with
    | inl hm =>
      refine ⟨g, ?_⟩
      intro i j hi hj hij
      have hie := (he i hi).2
      have hje := (he j hj).2
      have hij' := (he j hj).1.lt hij
      have hstrict := hm (e i) (e j) (he i hi).1.mem (he j hj).1.mem hie hje hij'
      simpa [g, hi, hj] using hstrict
    | inr hm =>
      have hdec : ∃ s : Ordinal.{u} → (Ordinal.{u} → Bool),
          ∀ i j, i < κ → j < κ → i < j → LexBelow δ (s j) (s i) := by
        refine ⟨g, ?_⟩
        intro i j hi hj hij
        have hie := (he i hi).2
        have hje := (he j hj).2
        have hij' := (he j hj).1.lt hij
        have hstrict := hm (e i) (e j) (he i hi).1.mem (he j hj).1.mem hie hje hij'
        simpa [g, hi, hj] using hstrict
      exact False.elim (no_long_lexBelow_dec hκ.1.2 δ hδ hdec)
  exact no_long_lexBelow_inc hκ.1.2 δ hδ hinc

/-- The graph of a well-order transported by an injection into an ordinal
carrier, with diagonal pairs marking which carrier points are in its image. -/
def OrdinalImageRelation {α β : Ordinal.{u}}
    (e : (representative α).Carrier → (representative β).Carrier)
    (x y : (representative β).Carrier) : Prop :=
  (x = y ∧ ∃ a, e a = x) ∨
    ∃ a b, e a = x ∧ e b = y ∧ (representative α).lt a b

theorem ordinalImageRelation_diag_iff {α β : Ordinal.{u}}
    {e : (representative α).Carrier → (representative β).Carrier}
    (he : ∀ a b, e a = e b → a = b) (x : (representative β).Carrier) :
    OrdinalImageRelation e x x ↔ ∃ a, e a = x := by
  constructor
  · intro h
    cases h with
    | inl h => exact h.2
    | inr h =>
      obtain ⟨a, b, hax, hbx, hab⟩ := h
      have hab' : a = b := he a b (hax.trans hbx.symm)
      subst b
      exact False.elim ((representative α).irrefl a hab)
  · intro h
    exact Or.inl ⟨rfl, h⟩

theorem ordinalImageRelation_on_image_iff {α β : Ordinal.{u}}
    {e : (representative α).Carrier → (representative β).Carrier}
    (he : ∀ a b, e a = e b → a = b) (a b : (representative α).Carrier) :
    OrdinalImageRelation e (e a) (e b) ↔
      a = b ∨ (representative α).lt a b := by
  constructor
  · intro h
    cases h with
    | inl h => exact Or.inl (he a b h.1)
    | inr h =>
      obtain ⟨x, y, hxa, hyb, hxy⟩ := h
      have hxa' : x = a := he x a hxa
      have hyb' : y = b := he y b hyb
      subst x
      subst y
      exact Or.inr hxy
  · intro h
    cases h with
    | inl h => subst b; exact Or.inl ⟨rfl, ⟨a, rfl⟩⟩
    | inr h => exact Or.inr ⟨a, b, rfl, rfl, h⟩

/-- Equality of two transported well-order graphs forces equality of their
order types. -/
theorem ordinalImageRelation_eq_type {α α' β : Ordinal.{u}}
    {e : (representative α).Carrier → (representative β).Carrier}
    {e' : (representative α').Carrier → (representative β).Carrier}
    (he : ∀ a b, e a = e b → a = b) (he' : ∀ a b, e' a = e' b → a = b)
    (hrel : ∀ x y, OrdinalImageRelation e x y ↔ OrdinalImageRelation e' x y) :
    α = α' := by
  classical
  have hactive (x : (representative β).Carrier) :
      (∃ a, e a = x) ↔ (∃ a, e' a = x) := by
    constructor
    · intro hx
      exact (ordinalImageRelation_diag_iff he' x).mp
        ((hrel x x).mp ((ordinalImageRelation_diag_iff he x).mpr hx))
    · intro hx
      exact (ordinalImageRelation_diag_iff he x).mp
        ((hrel x x).mpr ((ordinalImageRelation_diag_iff he' x).mpr hx))
  let toFun : (representative α).Carrier → (representative α').Carrier := fun a =>
    Classical.choose ((hactive (e a)).mp ⟨a, rfl⟩)
  let invFun : (representative α').Carrier → (representative α).Carrier := fun a =>
    Classical.choose ((hactive (e' a)).mpr ⟨a, rfl⟩)
  have hto : ∀ a, e' (toFun a) = e a := fun a =>
    Classical.choose_spec ((hactive (e a)).mp ⟨a, rfl⟩)
  have hinv : ∀ a, e (invFun a) = e' a := fun a =>
    Classical.choose_spec ((hactive (e' a)).mpr ⟨a, rfl⟩)
  have hleft : ∀ a, invFun (toFun a) = a := by
    intro a
    apply he
    calc
      e (invFun (toFun a)) = e' (toFun a) := hinv (toFun a)
      _ = e a := hto a
  have hright : ∀ a, toFun (invFun a) = a := by
    intro a
    apply he'
    calc
      e' (toFun (invFun a)) = e (invFun a) := hto (invFun a)
      _ = e' a := hinv a
  have hlt : ∀ a b, (representative α').lt (toFun a) (toFun b) ↔
      (representative α).lt a b := by
    intro a b
    constructor
    · intro hab
      have hrSource := (ordinalImageRelation_on_image_iff he' (toFun a) (toFun b)).mpr
        (Or.inr hab)
      have hr' : OrdinalImageRelation e' (e a) (e b) := by
        simpa only [hto a, hto b] using hrSource
      cases (ordinalImageRelation_on_image_iff he a b).mp ((hrel _ _).mpr hr') with
      | inl heq =>
        subst b
        exact False.elim ((representative α').irrefl (toFun a) hab)
      | inr h => exact h
    · intro hab
      have hr := (ordinalImageRelation_on_image_iff he a b).mpr (Or.inr hab)
      have hrSource := (hrel _ _).mp hr
      have hr' : OrdinalImageRelation e' (e' (toFun a)) (e' (toFun b)) := by
        rw [hto a, hto b]
        exact hrSource
      cases (ordinalImageRelation_on_image_iff he' (toFun a) (toFun b)).mp hr' with
      | inl heq =>
        have heq' : e a = e b := by
          calc
            e a = e' (toFun a) := (hto a).symm
            _ = e' (toFun b) := congrArg e' heq
            _ = e b := hto b
        have heq'' := he a b heq'
        subst b
        exact False.elim ((representative α).irrefl a hab)
      | inr h => exact h
  let eIso : WellOrder.Iso (representative α) (representative α') := {
    toFun := toFun
    invFun := invFun
    left_inv := hleft
    right_inv := hright
    lt_iff := hlt }
  simpa only [type_representative] using type_eq_of_iso eIso

noncomputable def ordinalPairCode (β : Ordinal.{u})
    (x y : (representative β).Carrier) : Ordinal.{u} :=
  mul β (type ((representative β).below x)) +
    type ((representative β).below y)

theorem ordinalPairCode_lt (β : Ordinal.{u}) (x y : (representative β).Carrier) :
    ordinalPairCode β x y < mul β β :=
  mul_pair_lt (initial_lt β x) (initial_lt β y)

theorem ordinalPairCode_injective {β : Ordinal.{u}}
    {x x' y y' : (representative β).Carrier}
    (h : ordinalPairCode β x y = ordinalPairCode β x' y') : x = x' ∧ y = y' := by
  have hp := mul_pair_inj (initial_lt β y) (initial_lt β y') h
  exact ⟨initial_injective β x x' hp.1, initial_injective β y y' hp.2⟩

/-- Encode a transported well-order graph as a binary function on the
ordinal-sized set of pairs of carrier points. -/
noncomputable def ordinalImageRelationCode {α β : Ordinal.{u}}
    (e : (representative α).Carrier → (representative β).Carrier)
    (z : (representative (mul β β)).Carrier) : Bool := by
  classical
  exact if h : ∃ x y, OrdinalImageRelation e x y ∧
      ordinalPairCode β x y = type ((representative (mul β β)).below z) then true else false

theorem ordinalImageRelationCode_eval {α β : Ordinal.{u}}
    {e : (representative α).Carrier → (representative β).Carrier}
    (x y : (representative β).Carrier) :
    ordinalImageRelationCode e
      (pointBelow (mul β β) (ordinalPairCode β x y) (ordinalPairCode_lt β x y)) = true ↔
      OrdinalImageRelation e x y := by
  classical
  let z := pointBelow (mul β β) (ordinalPairCode β x y) (ordinalPairCode_lt β x y)
  have hz : type ((representative (mul β β)).below z) = ordinalPairCode β x y :=
    (pointBelow_spec (ordinalPairCode_lt β x y)).symm
  constructor
  · intro hcode
    by_cases hxy : OrdinalImageRelation e x y
    · exact hxy
    · have hex : ¬ ∃ a b, OrdinalImageRelation e a b ∧
          ordinalPairCode β a b = type ((representative (mul β β)).below z) := by
        rintro ⟨a, b, hab, hpair⟩
        have hp := ordinalPairCode_injective (β := β) (hpair.trans hz)
        cases hp with
        | intro hxa hyb => subst a; subst b; exact hxy hab
      simp [ordinalImageRelationCode, z, hex] at hcode
  · intro hxy
    have hex : ∃ a b, OrdinalImageRelation e a b ∧
        ordinalPairCode β a b = type ((representative (mul β β)).below z) :=
      ⟨x, y, hxy, hz.symm⟩
    simp [ordinalImageRelationCode, z, hex]

theorem ordinalImageRelationCode_eq_rel {α α' β : Ordinal.{u}}
    {e : (representative α).Carrier → (representative β).Carrier}
    {e' : (representative α').Carrier → (representative β).Carrier}
    (hcode : ordinalImageRelationCode e = ordinalImageRelationCode e') :
    ∀ x y, OrdinalImageRelation e x y ↔ OrdinalImageRelation e' x y := by
  intro x y
  have hvalue := congrFun hcode
    (pointBelow (mul β β) (ordinalPairCode β x y) (ordinalPairCode_lt β x y))
  have hvalue' : (ordinalImageRelationCode e
      (pointBelow (mul β β) (ordinalPairCode β x y) (ordinalPairCode_lt β x y)) = true) ↔
      (ordinalImageRelationCode e'
      (pointBelow (mul β β) (ordinalPairCode β x y) (ordinalPairCode_lt β x y)) = true) := by
    rw [hvalue]
  constructor
  · intro hxy
    exact (ordinalImageRelationCode_eval x y).mp
      (hvalue'.mp ((ordinalImageRelationCode_eval x y).mpr hxy))
  · intro hxy'
    exact (ordinalImageRelationCode_eval x y).mp
      (hvalue'.mpr ((ordinalImageRelationCode_eval x y).mpr hxy'))

/-- Encode every ordinal below a Hartogs ordinal by the graph of an injected
copy into the smaller ordinal. -/
noncomputable def hartogsRelationCode (β : Ordinal.{u}) :
    (representative (hartogs (representative β).Carrier)).Carrier →
      (representative (mul β β)).Carrier → Bool := by
  classical
  let θ := hartogs (representative β).Carrier
  let embed : (x : (representative θ).Carrier) →
      (representative (type ((representative θ).below x))).Carrier →
        (representative β).Carrier := fun x =>
    Classical.choose (injective_of_lt_hartogs (initial_lt θ x))
  exact fun x => ordinalImageRelationCode (embed x)

/-- Distinct ordinal types below a Hartogs ordinal induce distinct binary
codes on the set of pairs from the target. -/
theorem hartogsRelationCode_injective (β : Ordinal.{u})
    {x y : (representative (hartogs (representative β).Carrier)).Carrier}
    (hcode : hartogsRelationCode β x = hartogsRelationCode β y) : x = y := by
  classical
  let θ := hartogs (representative β).Carrier
  let embed : (x : (representative θ).Carrier) →
      (representative (type ((representative θ).below x))).Carrier →
        (representative β).Carrier := fun z =>
    Classical.choose (injective_of_lt_hartogs (initial_lt θ z))
  have hembed (z : (representative θ).Carrier) :
      ∀ a b, embed z a = embed z b → a = b :=
    Classical.choose_spec (injective_of_lt_hartogs (initial_lt θ z))
  have hrel := ordinalImageRelationCode_eq_rel hcode
  have htype := ordinalImageRelation_eq_type (hembed x) (hembed y) hrel
  exact initial_injective θ x y htype

/-- A weakly compact ordinal is a strict upper bound for the Hartogs ordinal
of each smaller ordinal.  The partition property codes each ordinal below
Hartogs by its embedded order relation; the number of pairs below `β × β` is
still below a regular `κ`. -/
theorem weaklyCompact_hartogs_rep_lt {κ β : Ordinal.{u}}
    (hκ : R κ ∧ PartitionProp κ) (hβ : β < κ) :
    hartogs (representative β).Carrier < κ := by
  classical
  let θ := hartogs (representative β).Carrier
  have hθ := hκ.1.2.hartogs_bounds hβ
  have hδ : mul β β < κ := hκ.1.2.mul_lt hβ hβ
  cases lt_or_le θ κ with
  | inl h => exact h
  | inr hκθ =>
    have hθκ : θ = κ := le_antisymm hθ.2 hκθ
    have htype : type (representative κ) = θ := by
      rw [type_representative]
      exact hθκ.symm
    let iso := representativeOrderIso (representative κ) htype
    let f : (representative κ).Carrier →
        ((representative (mul β β)).Carrier → Bool) :=
      fun x => hartogsRelationCode β (iso.toFun x)
    have hf : ∀ x y, f x = f y → x = y := by
      intro x y hxy
      have hIso : iso.toFun x = iso.toFun y := hartogsRelationCode_injective β hxy
      have hinv := congrArg iso.invFun hIso
      simpa only [iso.left_inv] using hinv
    exact False.elim (WeaklyCompactCard.no_injective_bool_sequences hκ hδ f hf)

/-- 正則な `κ` の中では、任意の非有界集合へ制限しても分割性が保たれる。 -/
theorem PartitionProp.refine_unbounded {κ : Ordinal.{u}} (hκ : R κ)
    (hpart : PartitionProp κ) {A : Ordinal.{u} → Prop} (hA : Unbounded κ A)
    (f : Ordinal.{u} → Ordinal.{u} → Bool) :
    ∃ H, (∀ x, H x → A x) ∧ Unbounded κ H ∧ Homogeneous f H := by
  have henum : ∀ α, α < κ → EnumDef A α ∧ enum A α < κ :=
    enum_below_regular hκ.2 (fun η hη => hA η hη)
  have hcofinal : ∀ η, η < κ → ∃ α, α < κ ∧ η < enum A α := by
    intro η hη
    apply Classical.byContradiction
    intro hn
    have hb : ∀ β, β < κ → enum A β ≤ η := by
      intro β hβ
      exact le_of_not_lt (fun hlt => hn (Exists.intro β (And.intro hβ hlt)))
    obtain ⟨a, haA, hηa, haκ⟩ := hA η hη
    have hdef : EnumDef A κ := ⟨a, haA, fun β hβ => lt_of_le_of_lt (hb β hβ) hηa⟩
    have hk : κ ≤ enum A κ := hdef.le_enum
    have ha : enum A κ ≤ a := enum_le_of haA (fun β hβ => lt_of_le_of_lt (hb β hβ) hηa)
    exact not_lt_of_le (le_trans hk ha) haκ
  let g : Ordinal.{u} → Ordinal.{u} → Bool := fun x y => f (enum A x) (enum A y)
  obtain ⟨H₀, hH₀κ, hH₀unb, hH₀hom⟩ := hpart g
  obtain ⟨c, hc⟩ := hH₀hom
  refine ⟨fun z => ∃ x, H₀ x ∧ z = enum A x, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact (henum x (hH₀κ x hx)).1.mem
  · intro η hη
    obtain ⟨α, hακ, hηα⟩ := hcofinal η hη
    obtain ⟨x, hx, hαx, hxκ⟩ := hH₀unb α hακ
    have hαx' : enum A α < enum A x := (henum x hxκ).1.lt hαx
    exact ⟨enum A x, ⟨x, hx, rfl⟩, lt_trans η (enum A α) (enum A x) hηα hαx',
      (henum x hxκ).2⟩
  · refine ⟨c, ?_⟩
    intro x y hx hy hxy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have habκ : b < κ := hH₀κ b hb
    have hba : a < b := ((henum b habκ).1.lt_iff (henum a (hH₀κ a ha)).1).mp hxy
    exact hc a b ha hb hba

/-- The order-orientation consequence remains valid inside any unbounded subset
of `κ`. -/
theorem PartitionProp.orient_unbounded {κ : Ordinal.{u}} (hκ : R κ)
    (hpart : PartitionProp κ) {A : Ordinal.{u} → Prop}
    (hAκ : ∀ x, A x → x < κ) (hA : Unbounded κ A)
    {X : Type u} (ltX : X → X → Prop)
    (htotal : ∀ a b, a ≠ b → ltX a b ∨ ltX b a)
    (f : (representative κ).Carrier → X) (hf : ∀ x y, f x = f y → x = y) :
    ∃ H, (∀ x, H x → A x) ∧ Unbounded κ H ∧
      (OrderMonotoneOn κ H ltX f ∨ OrderAntitoneOn κ H ltX f) := by
  classical
  let point : (x : Ordinal.{u}) → x < κ → (representative κ).Carrier :=
    fun x hx => Classical.choose (initial_surjective κ x hx)
  let coloring : Ordinal.{u} → Ordinal.{u} → Bool := fun x y =>
    if hx : x < κ then
      if hy : y < κ then
        if ltX (f (point x hx)) (f (point y hy)) then false else true
      else false
    else false
  obtain ⟨H, hHA, hHunb, hHhom⟩ := hpart.refine_unbounded hκ hA coloring
  have hHκ : ∀ x, H x → x < κ := fun x hx => hAκ x (hHA x hx)
  obtain ⟨c, hc⟩ := hHhom
  refine ⟨H, hHA, hHunb, ?_⟩
  cases c with
  | false =>
    left
    intro x y hx hy hxκ hyκ hxy
    have hcolor := hc x y hx hy hxy
    by_cases hlt : ltX (f (point x hxκ)) (f (point y hyκ))
    · exact hlt
    · simp [coloring, hxκ, hyκ, hlt] at hcolor
  | true =>
    right
    intro x y hx hy hxκ hyκ hxy
    have hcolor := hc x y hx hy hxy
    have hnot : ¬ ltX (f (point x hxκ)) (f (point y hyκ)) := by
      intro hlt
      simp [coloring, hxκ, hyκ, hlt] at hcolor
    have hpoint_ne : point x hxκ ≠ point y hyκ := by
      intro heq
      have hxrep := Classical.choose_spec (initial_surjective κ x hxκ)
      have hyrep := Classical.choose_spec (initial_surjective κ y hyκ)
      have htype := congrArg (fun z => type ((representative κ).below z)) heq
      have hxy_eq : x = y := hxrep.trans (htype.trans hyrep.symm)
      exact (ne_of_lt hxy) hxy_eq
    cases htotal (f (point x hxκ)) (f (point y hyκ)) (fun heq =>
        hpoint_ne (hf _ _ heq)) with
    | inl hlt => exact False.elim (hnot hlt)
    | inr hgt => exact hgt

/-- 非可算正則性と二分割性を満たす順序数。 -/
def WeaklyCompactCard (κ : Ordinal.{u}) : Prop := R κ ∧ PartitionProp κ

/-- 定常集合の内部でも、指定した彩色に関する非有界な一様集合を取れる。 -/
theorem WeaklyCompactCard.refine_stationary {κ : Ordinal.{u}} (hκ : WeaklyCompactCard κ)
    {S : Ordinal.{u} → Prop} (hS : Stationary κ S)
    (f : Ordinal.{u} → Ordinal.{u} → Bool) :
    ∃ H, (∀ x, H x → S x) ∧ Unbounded κ H ∧ Homogeneous f H :=
  hκ.2.refine_unbounded hκ.1 (hS.unbounded hκ.1) f

/-- On a stationary set, weak compactness yields an unbounded subset whose
injected order is monotone or reversed. -/
theorem WeaklyCompactCard.orient_stationary {κ : Ordinal.{u}}
    (hκ : WeaklyCompactCard κ) {S : Ordinal.{u} → Prop} (hS : Stationary κ S)
    {X : Type u} (ltX : X → X → Prop)
    (htotal : ∀ a b, a ≠ b → ltX a b ∨ ltX b a)
    (f : (representative κ).Carrier → X) (hf : ∀ x y, f x = f y → x = y) :
    ∃ H, (∀ x, H x → S x) ∧ Unbounded κ H ∧
      (OrderMonotoneOn κ H ltX f ∨ OrderAntitoneOn κ H ltX f) := by
  have hS' : Unbounded κ (fun x => S x ∧ x < κ) := by
    intro η hη
    cases hS.unbounded hκ.1 η hη with
    | intro ξ hξ => exact ⟨ξ, ⟨hξ.1, hξ.2.2⟩, hξ.2.1, hξ.2.2⟩
  obtain ⟨H, hHA, hHunb, hOrient⟩ :=
    hκ.2.orient_unbounded hκ.1 (fun x hx => hx.2) hS' ltX htotal f hf
  exact ⟨H, (fun x hx => (hHA x hx).1), hHunb, hOrient⟩

/-- 仮定 `h` が列挙する第 `n+1` 番目の弱コンパクト基数。 -/
noncomputable def weaklyCompactAt (n : Nat) : Ordinal.{u} :=
  enum.{u} WeaklyCompactCard (ordNat.{u} (n + 1))

/-- `h` によって列挙された各順序数は弱コンパクト性を満たす。 -/
theorem weaklyCompactAt_spec (h : ∀ n : Nat,
    EnumDef.{u} WeaklyCompactCard.{u} (ordNat.{u} n)) (n : Nat) :
    WeaklyCompactCard.{u} (weaklyCompactAt.{u} n) :=
  (h (n + 1)).mem

/-- The fixed enumeration hypothesis alone excludes an injection from an
enumerated weakly compact ordinal into binary strings of any shorter length. -/
theorem weaklyCompactAt_no_injective_bool_sequences
    (h : ∀ n : Nat, EnumDef.{u} WeaklyCompactCard.{u} (ordNat.{u} n))
    (n : Nat) {δ : Ordinal.{u}} (hδ : δ < weaklyCompactAt.{u} n)
    (f : (representative (weaklyCompactAt.{u} n)).Carrier →
      ((representative δ).Carrier → Bool))
    (hf : ∀ x y, f x = f y → x = y) : False :=
  WeaklyCompactCard.no_injective_bool_sequences
    ⟨(weaklyCompactAt_spec h n).1, (weaklyCompactAt_spec h n).2⟩ hδ f hf

/-- The fixed enumeration hypothesis alone places every smaller ordinal's
Hartogs ordinal below the corresponding weakly compact ordinal. -/
theorem weaklyCompactAt_hartogs_lt
    (h : ∀ n : Nat, EnumDef.{u} WeaklyCompactCard.{u} (ordNat.{u} n))
    (n : Nat) {β : Ordinal.{u}} (hβ : β < weaklyCompactAt.{u} n) :
    hartogs (representative β).Carrier < weaklyCompactAt.{u} n :=
  weaklyCompact_hartogs_rep_lt
    ⟨(weaklyCompactAt_spec h n).1, (weaklyCompactAt_spec h n).2⟩ hβ

/-- The Hartogs bounds already proved from `h` produce regular ordinals
arbitrarily high below each enumerated weakly compact ordinal, provided the
ordinary pairing maps on ordinal representatives are available. -/
theorem weaklyCompactAt_inacc_of_pairing
    (h : ∀ n : Nat, EnumDef.{u} WeaklyCompactCard.{u} (ordNat.{u} n))
    (pairing : ∀ β : Ordinal.{u}, omega ≤ β →
      ∃ pair : (representative β).Carrier × (representative β).Carrier →
        (representative β).Carrier, ∀ a b, pair a = pair b → a = b)
    (n : Nat) (η : Ordinal.{u}) (hη : η < weaklyCompactAt.{u} n) :
    ∃ ρ, R ρ ∧ η < ρ ∧ ρ < weaklyCompactAt.{u} n := by
  classical
  let κ := weaklyCompactAt.{u} n
  let β := if η < omega then omega else η
  have hωβ : omega ≤ β := by
    by_cases hηω : η < omega
    · simp [β, hηω]
      exact OCF.Ordinal.le_refl omega
    · simp [β, hηω]
      exact (not_lt_iff_le η omega).mp hηω
  have hηβ : η ≤ β := by
    by_cases hηω : η < omega
    · simp [β, hηω]
      exact Or.inl hηω
    · simp [β, hηω]
      exact Or.inr rfl
  have hβκ : β < κ := by
    by_cases hηω : η < omega
    · simp [β, hηω, κ]
      exact (weaklyCompactAt_spec h n).1.1
    · simp [β, hηω, κ]
      exact hη
  obtain ⟨pair, hpair⟩ := pairing β hωβ
  have hβθ : β < hartogs (representative β).Carrier := by
    apply lt_hartogs_of_injective β (fun x => x)
    intro x y hxy
    exact hxy
  have hθκ : hartogs (representative β).Carrier < κ :=
    weaklyCompactAt_hartogs_lt h n hβκ
  have hωθ : omega < hartogs (representative β).Carrier :=
    lt_of_le_of_lt hωβ hβθ
  have hθlim : IsLimit (hartogs (representative β).Carrier) :=
    hartogs_isLimit_of_omega_lt hωθ
  have hθreg : IsRegular (hartogs (representative β).Carrier) :=
    hartogs_regular_of_pair_injective hθlim pair hpair
  refine ⟨hartogs (representative β).Carrier, ⟨hωθ, hθreg⟩,
    lt_of_le_of_lt hηβ hβθ, ?_⟩
  simpa [κ] using hθκ

theorem weaklyCompactAt_R (h : ∀ n : Nat,
    EnumDef.{u} WeaklyCompactCard.{u} (ordNat.{u} n)) (n : Nat) :
    R (weaklyCompactAt.{u} n) := (weaklyCompactAt_spec h n).1

theorem weaklyCompactAt_partition (h : ∀ n : Nat,
    EnumDef.{u} WeaklyCompactCard.{u} (ordNat.{u} n)) (n : Nat) :
    PartitionProp (weaklyCompactAt.{u} n) := (weaklyCompactAt_spec h n).2

/-- A weakly compact ordinal from `h` has the uniform-orientation consequence
for every pairwise-comparable relation on an injected copy of its carrier. -/
theorem weaklyCompactAt_orient
    (h : ∀ n : Nat, EnumDef.{u} WeaklyCompactCard.{u} (ordNat.{u} n)) (n : Nat)
    {X : Type u} (ltX : X → X → Prop)
    (htotal : ∀ a b, a ≠ b → ltX a b ∨ ltX b a)
    (f : (representative (weaklyCompactAt.{u} n)).Carrier → X)
    (hf : ∀ x y, f x = f y → x = y) :
    ∃ H, (∀ x, H x → x < weaklyCompactAt.{u} n) ∧
      Unbounded (weaklyCompactAt.{u} n) H ∧
      (OrderMonotoneOn (weaklyCompactAt.{u} n) H ltX f ∨
        OrderAntitoneOn (weaklyCompactAt.{u} n) H ltX f) :=
  (weaklyCompactAt_partition h n).orient ltX htotal f hf

/-- The hypothesis `h` also gives the order-orientation consequence within any
stationary subset of an enumerated weakly compact ordinal. -/
theorem weaklyCompactAt_orient_stationary
    (h : ∀ n : Nat, EnumDef.{u} WeaklyCompactCard.{u} (ordNat.{u} n)) (n : Nat)
    {S : Ordinal.{u} → Prop} (hS : Stationary (weaklyCompactAt.{u} n) S)
    {X : Type u} (ltX : X → X → Prop)
    (htotal : ∀ a b, a ≠ b → ltX a b ∨ ltX b a)
    (f : (representative (weaklyCompactAt.{u} n)).Carrier → X)
    (hf : ∀ x y, f x = f y → x = y) :
    ∃ H, (∀ x, H x → S x) ∧ Unbounded (weaklyCompactAt.{u} n) H ∧
      (OrderMonotoneOn (weaklyCompactAt.{u} n) H ltX f ∨
        OrderAntitoneOn (weaklyCompactAt.{u} n) H ltX f) :=
  (weaklyCompactAt_spec h n).orient_stationary hS ltX htotal f hf

/-- `h` から得られる各段階で、定常集合の中に一様部分集合を取る。 -/
theorem weaklyCompactAt_refine_stationary
    (h : ∀ n : Nat, EnumDef.{u} WeaklyCompactCard.{u} (ordNat.{u} n)) (n : Nat)
    {S : Ordinal.{u} → Prop} (hS : Stationary (weaklyCompactAt.{u} n) S)
    (f : Ordinal.{u} → Ordinal.{u} → Bool) :
    ∃ H, (∀ x, H x → S x) ∧ Unbounded (weaklyCompactAt.{u} n) H ∧ Homogeneous f H :=
  (weaklyCompactAt_spec h n).refine_stationary hS f

/-- `h` の列挙は狭義単調である。 -/
theorem weaklyCompactAt_lt (h : ∀ n : Nat,
    EnumDef.{u} WeaklyCompactCard.{u} (ordNat.{u} n)) (n : Nat) :
    weaklyCompactAt.{u} n < weaklyCompactAt.{u} (n + 1) :=
  (h (n + 2)).lt (ordNat_lt (Nat.lt_succ_self (n + 1)))

/-- `h` だけから得られる、弱コンパクト基数の狭義増加列。 -/
structure WeaklyCompactSequence : Type (u + 1) where
  value : Nat → Ordinal.{u}
  weaklyCompact : ∀ n, WeaklyCompactCard (value n)
  increasing : ∀ n, value n < value (n + 1)

/-- 列挙仮定 `h` の標準列。 -/
noncomputable def weaklyCompactSequenceFromEnum
    (h : ∀ n : Nat, EnumDef.{u} WeaklyCompactCard.{u} (ordNat.{u} n)) :
    WeaklyCompactSequence.{u} where
  value := weaklyCompactAt.{u}
  weaklyCompact := weaklyCompactAt_spec h
  increasing := weaklyCompactAt_lt h

/-- `Ω_ξ`：`CardSet` の数え上げ（`Ω_0 = 0`、`Ω_1` は最初の非可算正則基数） -/
def Om : Ordinal.{u} → Ordinal.{u} := enum CardSet

theorem cardSet_limClosed : LimClosed (CardSet.{u}) := by
  intro ξ hξ
  apply Or.inr
  apply closure_limClosed R ξ
  apply And.intro hξ.1
  intro η hη
  cases hξ.2 η hη with
  | intro β hβ =>
    cases hβ.1 with
    | inl h0 => rw [h0] at hβ; exact absurd hβ.2.1 (not_lt_zero η)
    | inr hc => exact Exists.intro β (And.intro hc hβ.2)

theorem Om_zero : Om (0 : Ordinal.{u}) = 0 := by
  exact (le_zero_iff _).mp (enum_le_of (X := CardSet) (Or.inl rfl)
    (fun β hβ => absurd hβ (not_lt_zero β)))

/-! ### 弱コンパクト基数の列 -/

/-- 弱コンパクト基数の列 `K_1 < K_2 < ⋯` についての仮定（`Kseq n` が `K_{n+1}`） -/
class Setting : Type (u + 1) where
  Kseq : Nat → Ordinal.{u}
  Kseq_R : ∀ n, R (Kseq n)
  Kseq_lt : ∀ n, Kseq n < Kseq (n + 1)
  Kseq_inacc : ∀ n η, η < Kseq n → ∃ ρ, R ρ ∧ η < ρ ∧ ρ < Kseq n

variable [Setting.{u}]

/-- `K_0 = 0`、`K_{n+1} = Kseq n` -/
def K : Nat → Ordinal.{u}
  | 0 => 0
  | n + 1 => Setting.Kseq n

def Λ : Ordinal.{u} := sup (fun n : ULift.{u} Nat => K n.down)

theorem K_succ (n : Nat) : K.{u} (n + 1) = Setting.Kseq n := rfl

theorem K_zero : K.{u} 0 = 0 := rfl

theorem R_K {n : Nat} (h : 1 ≤ n) : R (K.{u} n) := by
  cases n with
  | zero => exact absurd h (by decide)
  | succ n => exact Setting.Kseq_R n

theorem K_lt_K_succ (n : Nat) : K.{u} n < K (n + 1) := by
  cases n with
  | zero => exact lt_of_le_of_lt (zero_le _) (lt_trans _ _ _ zero_lt_omega (Setting.Kseq_R 0).1)
  | succ n => exact Setting.Kseq_lt n

theorem K_lt {m n : Nat} (h : m < n) : K.{u} m < K n := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ n ih =>
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with
    | inl h' => exact lt_trans _ _ _ (ih h') (K_lt_K_succ n)
    | inr h' => rw [h']; exact K_lt_K_succ n

theorem K_le {m n : Nat} (h : m ≤ n) : K.{u} m ≤ K n := by
  cases Nat.lt_or_eq_of_le h with
  | inl h' => exact Or.inl (K_lt h')
  | inr h' => rw [h']; exact le_refl _

theorem K_lt_iff {m n : Nat} : K.{u} m < K n ↔ m < n := by
  apply Iff.intro
  · intro h
    cases Nat.lt_or_ge m n with
    | inl h' => exact h'
    | inr h' => exact absurd h (not_lt_of_le (K_le h'))
  · exact K_lt

theorem K_inj {m n : Nat} (h : K.{u} m = K n) : m = n := by
  cases Nat.lt_trichotomy m n with
  | inl h' => exact absurd h (ne_of_lt (K_lt h'))
  | inr h' =>
    cases h' with
    | inl h' => exact h'
    | inr h' => exact absurd h (ne_of_gt (K_lt h'))

theorem K_le_Λ (n : Nat) : K.{u} n ≤ Λ :=
  le_sup (fun k : ULift.{u} Nat => K k.down) (ULift.up n)

theorem K_lt_Λ (n : Nat) : K.{u} n < Λ :=
  lt_of_lt_of_le (K_lt_K_succ n) (K_le_Λ (n + 1))

theorem lt_Λ_iff (α : Ordinal.{u}) : α < Λ ↔ ∃ n, α < K n := by
  apply Iff.intro
  · intro h
    cases (lt_sup_iff _ α).mp h with
    | intro n hn => exact Exists.intro n.down hn
  · intro h
    cases h with
    | intro n hn => exact lt_trans _ _ _ hn (K_lt_Λ n)

theorem omega_lt_K {n : Nat} (h : 1 ≤ n) : omega < K.{u} n := (R_K h).1

/-- `K_n`（`n ≥ 1`）未満の正則基数は非有界 -/
theorem K_inacc {n : Nat} (h : 1 ≤ n) (η : Ordinal.{u}) (hη : η < K n) :
    ∃ ρ, R ρ ∧ η < ρ ∧ ρ < K n := by
  cases n with
  | zero => exact absurd h (by decide)
  | succ n => exact Setting.Kseq_inacc n η hη

/-! ### `Ω`（続き） -/

theorem cardSet_unbounded_K {n : Nat} (h : 1 ≤ n) :
    ∀ η, η < K.{u} n → ∃ ξ, CardSet ξ ∧ η < ξ ∧ ξ < K n := by
  intro η hη
  cases K_inacc h η hη with
  | intro ρ hρ => exact Exists.intro ρ (And.intro (Or.inr (subset_closure hρ.1)) hρ.2)

theorem Om_def_lt_K {n : Nat} (h : 1 ≤ n) {α : Ordinal.{u}} (hα : α < K n) :
    EnumDef CardSet α ∧ Om α < K n :=
  enum_below_regular (R_K h).2 (cardSet_unbounded_K h) α hα

theorem Om_def {α : Ordinal.{u}} (hα : α < Λ) : EnumDef CardSet α := by
  cases (lt_Λ_iff α).mp hα with
  | intro n hn =>
    cases n with
    | zero => exact absurd hn (not_lt_zero α)
    | succ n => exact (Om_def_lt_K (Nat.succ_le_succ (Nat.zero_le n)) hn).1

theorem Om_lt_K {n : Nat} (h : 1 ≤ n) {α : Ordinal.{u}} (hα : α < K n) : Om α < K n :=
  (Om_def_lt_K h hα).2

theorem Om_lt_Λ {α : Ordinal.{u}} (hα : α < Λ) : Om α < Λ := by
  cases (lt_Λ_iff α).mp hα with
  | intro n hn =>
    cases n with
    | zero => exact absurd hn (not_lt_zero α)
    | succ n =>
      exact lt_trans _ _ _ (Om_lt_K (Nat.succ_le_succ (Nat.zero_le n)) hn) (K_lt_Λ _)

theorem Om_K {n : Nat} (h : 1 ≤ n) : Om (K.{u} n) = K n :=
  (enum_fixed_regular (R_K h).2 (cardSet_unbounded_K h) (Or.inr (subset_closure (R_K h)))).2

theorem Om_lt_Om {α β : Ordinal.{u}} (hαβ : α < β) (hβ : β < Λ) : Om α < Om β :=
  (Om_def hβ).lt hαβ

theorem Om_lt_Om_iff {α β : Ordinal.{u}} (hα : α < Λ) (hβ : β < Λ) : Om α < Om β ↔ α < β :=
  (Om_def hβ).lt_iff (Om_def hα)

theorem Om_inj {α β : Ordinal.{u}} (hα : α < Λ) (hβ : β < Λ) (h : Om α = Om β) : α = β :=
  (Om_def hα).inj (Om_def hβ) h

theorem le_Om {α : Ordinal.{u}} (hα : α < Λ) : α ≤ Om α := (Om_def hα).le_enum

theorem cardSet_Om {α : Ordinal.{u}} (hα : α < Λ) : CardSet (Om α) := (Om_def hα).mem

/-- `Ω_{β+1}` は正則 -/
theorem Om_succ_R {β : Ordinal.{u}} (hβ : succ β < Λ) : R (Om (succ β)) := by
  have hdef := Om_def hβ
  have hβdef : EnumDef CardSet β := hdef.of_le (le_of_lt (lt_succ_self β))
  have hlt : Om β < Om (succ β) := hdef.lt (lt_succ_self β)
  cases hdef.mem with
  | inl h0 => exact absurd h0 (ne_of_gt (lt_of_le_of_lt (zero_le _) hlt))
  | inr hc =>
    cases (closure_iff R _).mp hc with
    | inl hR => exact hR
    | inr hlp =>
      cases hlp.2 _ hlt with
      | intro ρ hρ =>
        have hle : Om (succ β) ≤ ρ :=
          enum_le_of (X := CardSet) (Or.inr (subset_closure hρ.1))
            (fun γ hγ => lt_of_le_of_lt (hβdef.le_of_le (le_of_lt_succ hγ)) hρ.2.1)
        exact absurd hρ.2.2 (not_lt_of_le hle)

/-- `Ω` は極限で連続 -/
theorem Om_limit {l : Ordinal.{u}} (hl : IsLimit l) (hlΛ : l < Λ) : Om l = supLt l Om :=
  (enum_limit cardSet_limClosed hl (fun _ hβ => Om_def (lt_trans _ _ _ hβ hlΛ))).2

end
end OCF.Rathjen
