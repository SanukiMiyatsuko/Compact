import Compact.Additive
import Compact.OCFRathjen.Ordinal

/-! 基数の設定：`K_1 < K_2 < ⋯`、`Λ = sup K_n`、`Ω_ξ`。

* `K_n`（`n ≥ 1`）は正則で、正則基数の極限（弱到達不能）であることだけを課す（`Setting`）。
  弱コンパクト性（`WeaklyCompactCard`：非可算正則で分割性 `PartitionProp`）は `Setting` に含めず、
  `Complete.lean` で弱コンパクト基数の列から `Setting` と `StationaryHyp` を導く。
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

/-- 非可算正則性と二分割性を満たす順序数。 -/
def WeaklyCompactCard (κ : Ordinal.{u}) : Prop := R κ ∧ PartitionProp κ

/-- 仮定 `h` が列挙する第 `n+1` 番目の弱コンパクト基数。 -/
noncomputable def weaklyCompactAt (n : Nat) : Ordinal.{u} :=
  enum.{u} WeaklyCompactCard (ordNat.{u} (n + 1))

/-- `h` によって列挙された各順序数は弱コンパクト性を満たす。 -/
theorem weaklyCompactAt_spec (h : ∀ n : Nat,
    EnumDef.{u} WeaklyCompactCard.{u} (ordNat.{u} n)) (n : Nat) :
    WeaklyCompactCard.{u} (weaklyCompactAt.{u} n) :=
  (h (n + 1)).mem

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

/-- `h` の列挙は狭義単調である。 -/
theorem weaklyCompactAt_lt (h : ∀ n : Nat,
    EnumDef.{u} WeaklyCompactCard.{u} (ordNat.{u} n)) (n : Nat) :
    weaklyCompactAt.{u} n < weaklyCompactAt.{u} (n + 1) :=
  (h (n + 2)).lt (ordNat_lt (Nat.lt_succ_self (n + 1)))

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
  exact (le_zero_iff _).mp (enum_le (X := CardSet) (Or.inl rfl)
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
          enum_le (X := CardSet) (Or.inr (subset_closure hρ.1))
            (fun γ hγ => lt_of_le_of_lt (hβdef.le_of_le (le_of_lt_succ hγ)) hρ.2.1)
        exact absurd hρ.2.2 (not_lt_of_le hle)

/-- `Ω` は極限で連続 -/
theorem Om_limit {l : Ordinal.{u}} (hl : IsLimit l) (hlΛ : l < Λ) : Om l = supLt l Om :=
  (enum_limit cardSet_limClosed hl (fun _ hβ => Om_def (lt_trans _ _ _ hβ hlΛ))).2

/-! ## `C(α, β)`・`M^α`・`Ξ_m(α)`・`Ψ^ξ_π(α)` の定義（Rathjen, *Proof theory of reflection*, Def. 4.8 の加法版）。

`α` についての再帰で、段 `α` に次をまとめて定める（`Stage`）。

* `C(α, β)`：`β ∪ {1} ∪ {K_m}` を `+`、`Ω`（引数 `< Λ`）、`Ξ_m(ξ)`（`0 < ξ < α`）、
  `Ψ^ξ_π(δ)`（`ξ ≤ δ < α`、`π ∈ Reg`）で閉じたもの（`K_0 = 0` も入る）。
* `M^0 = Lim ∩ Λ`。`α > 0` なら
  `M^α = {π ∈ Reg : C(α, π) ∩ K(π) ⊆ π ∧ α ∈ C(α, π) ∧ ∀ ξ ∈ C(α, π) ∩ α, M^ξ は π で定常}`。
* `Ξ_m(α) = min({π ∈ M^α : K_{m-1} < π < K_m} ∪ {K_m})`。
* `Ψ^ξ_π(α) = min({ρ ∈ M^ξ ∩ π : C(α, ρ) ∩ π ⊆ ρ ∧ π, α ∈ C(α, ρ)} ∪ {π})`（`ξ ≤ α`。`ξ > α` なら `π`）。

`C(α, β)` は自然数で段階を付けた帰納的定義 `StageC` の和で、`|C(α, β)| < π`（`C_small`）の証明に段階を使う。 -/

/-- `Reg`：`Λ` 未満の非可算正則基数で、どの `K_n` とも等しくないもの -/
def IsReg (π : Ordinal.{u}) : Prop := R π ∧ π < Λ ∧ ∀ n, π ≠ K n

/-- `K(π)`：`π` より大きい最小の `K_n` -/
def Kabove (π : Ordinal.{u}) : Ordinal.{u} := least (fun κ => (∃ n, κ = K n) ∧ π < κ)

/-- 段 `α` で定まるもの -/
structure Stage : Type (u + 1) where
  /-- `C β x`：`x ∈ C(α, β)` -/
  C : Ordinal.{u} → Ordinal.{u} → Prop
  /-- `M^α` -/
  M : Ordinal.{u} → Prop
  /-- `Ξ_m(α)` -/
  Xi : Nat → Ordinal.{u}
  /-- `Ψ^ξ_π(α)` -/
  Psi : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}

/-- `C(α, β)` の段階 `n` の元 -/
inductive StageC (α : Ordinal.{u}) (prev : (γ : Ordinal.{u}) → γ < α → Stage.{u})
    (β : Ordinal.{u}) : Nat → Ordinal.{u} → Prop where
  | lt (n : Nat) (γ : Ordinal.{u}) (h : γ < β) : StageC α prev β n γ
  | one (n : Nat) : StageC α prev β n (succ 0)
  | kc (n m : Nat) : StageC α prev β n (K m)
  | add (n : Nat) (x y : Ordinal.{u}) (hx : StageC α prev β n x) (hy : StageC α prev β n y) :
      StageC α prev β (n + 1) (x + y)
  | om (n : Nat) (x : Ordinal.{u}) (hΛ : x < Λ) (hx : StageC α prev β n x) :
      StageC α prev β (n + 1) (Om x)
  | xi (n m : Nat) (x : Ordinal.{u}) (hpos : 0 < x) (hα : x < α) (hx : StageC α prev β n x) :
      StageC α prev β (n + 1) ((prev x hα).Xi m)
  | psi (n : Nat) (ξ π δ : Ordinal.{u}) (hα : δ < α) (hξδ : ξ ≤ δ) (hπ : IsReg π)
      (hξ : StageC α prev β n ξ) (hπC : StageC α prev β n π) (hδ : StageC α prev β n δ) :
      StageC α prev β (n + 1) ((prev δ hα).Psi ξ π)

open Classical in
/-- 段 `α` での `M^ξ`（`ξ < α` なら前の段、`ξ = α` なら `Mcur`、`ξ > α` なら空） -/
def Mof (α : Ordinal.{u}) (prev : (γ : Ordinal.{u}) → γ < α → Stage.{u}) (Mcur : Ordinal.{u} → Prop)
    (ξ : Ordinal.{u}) : Ordinal.{u} → Prop :=
  if h : ξ < α then (prev ξ h).M else if ξ = α then Mcur else fun _ => False

omit [Setting] in
theorem Mof_lt {α ξ : Ordinal.{u}} (prev : (γ : Ordinal.{u}) → γ < α → Stage.{u})
    (Mcur : Ordinal.{u} → Prop) (h : ξ < α) : Mof α prev Mcur ξ = (prev ξ h).M := by
  unfold Mof
  rw [dite_eq_left h]

omit [Setting] in
theorem Mof_self {α : Ordinal.{u}} (prev : (γ : Ordinal.{u}) → γ < α → Stage.{u})
    (Mcur : Ordinal.{u} → Prop) : Mof α prev Mcur α = Mcur := by
  unfold Mof
  rw [dite_eq_right (lt_irrefl α), ite_eq_left rfl]

omit [Setting] in
theorem Mof_gt {α ξ : Ordinal.{u}} (prev : (γ : Ordinal.{u}) → γ < α → Stage.{u})
    (Mcur : Ordinal.{u} → Prop) (h : α < ξ) : Mof α prev Mcur ξ = fun _ => False := by
  unfold Mof
  rw [dite_eq_right (lt_asymm h), ite_eq_right (ne_of_gt h)]

open Classical in
def makeStage (α : Ordinal.{u}) (prev : (γ : Ordinal.{u}) → γ < α → Stage.{u}) : Stage.{u} :=
  let C : Ordinal.{u} → Ordinal.{u} → Prop := fun β x => ∃ n, StageC α prev β n x
  let M : Ordinal.{u} → Prop := fun ρ =>
    if α = 0 then IsLimit ρ ∧ ρ < Λ
    else IsReg ρ ∧ (∀ x, C ρ x → x < Kabove ρ → x < ρ) ∧ C ρ α ∧
      ∀ ξ (h : ξ < α), C ρ ξ → Stationary ρ (prev ξ h).M
  { C := C
    M := M
    Xi := fun m => least (fun π => (M π ∧ K (m - 1) < π ∧ π < K m) ∨ π = K m)
    Psi := fun ξ π => least (fun ρ =>
      (Mof α prev M ξ ρ ∧ ρ < π ∧ (∀ x, C ρ x → x < π → x < ρ) ∧ C ρ π ∧ C ρ α) ∨ ρ = π) }

def stages : Ordinal.{u} → Stage.{u} := lt_wellFounded.fix makeStage

theorem stages_eq (α : Ordinal.{u}) : stages α = makeStage α (fun γ _ => stages γ) :=
  WellFounded.fix_eq lt_wellFounded makeStage α

/-- `x ∈ C(α, β)` の段階 `n` -/
def Cn (α β : Ordinal.{u}) (n : Nat) (x : Ordinal.{u}) : Prop :=
  StageC α (fun γ _ => stages γ) β n x

/-- `x ∈ C(α, β)` -/
def C (α β x : Ordinal.{u}) : Prop := ∃ n, Cn α β n x

/-- `ρ ∈ M^α` -/
def M (α ρ : Ordinal.{u}) : Prop := (stages α).M ρ

/-- `Ξ_m(α)` -/
def Xi (m : Nat) (α : Ordinal.{u}) : Ordinal.{u} := (stages α).Xi m

/-- `Ψ^ξ_π(α)` -/
def Psi (ξ π α : Ordinal.{u}) : Ordinal.{u} := (stages α).Psi ξ π

/-! ### 定義の展開 -/

open Classical in
theorem M_zero_iff (ρ : Ordinal.{u}) : M 0 ρ ↔ IsLimit ρ ∧ ρ < Λ := by
  unfold M
  rw [stages_eq 0]
  show (if (0 : Ordinal.{u}) = 0 then _ else _) ↔ _
  rw [ite_eq_left rfl]

open Classical in
theorem M_pos_iff {α : Ordinal.{u}} (hα : α ≠ 0) (ρ : Ordinal.{u}) :
    M α ρ ↔ IsReg ρ ∧ (∀ x, C α ρ x → x < Kabove ρ → x < ρ) ∧ C α ρ α ∧
      ∀ ξ, ξ < α → C α ρ ξ → Stationary ρ (M ξ) := by
  unfold M
  rw [stages_eq α]
  show (if α = 0 then _ else _) ↔ _
  rw [ite_eq_right hα]
  exact Iff.rfl

theorem Xi_eq (m : Nat) (α : Ordinal.{u}) :
    Xi m α = least (fun π => (M α π ∧ K (m - 1) < π ∧ π < K m) ∨ π = K m) := by
  unfold Xi M
  rw [stages_eq α]
  rfl

theorem Psi_eq {ξ α : Ordinal.{u}} (hξ : ξ ≤ α) (π : Ordinal.{u}) :
    Psi ξ π α = least (fun ρ =>
      (M ξ ρ ∧ ρ < π ∧ (∀ x, C α ρ x → x < π → x < ρ) ∧ C α ρ π ∧ C α ρ α) ∨ ρ = π) := by
  cases hξ with
  | inl h =>
    unfold Psi
    rw [stages_eq α]
    show least (fun ρ => (Mof α (fun γ _ => stages γ) _ ξ ρ ∧ _) ∨ _) = _
    rw [Mof_lt _ _ h]
    rfl
  | inr h =>
    subst h
    unfold Psi M
    rw [stages_eq ξ]
    show least (fun ρ => (Mof ξ (fun γ _ => stages γ) _ ξ ρ ∧ _) ∨ _) = _
    rw [Mof_self]
    rfl

omit [Setting] in
theorem least_false_or_eq (Q : Ordinal.{u} → Prop) (π : Ordinal.{u}) :
    least (fun ρ => ((fun _ => False) ρ ∧ Q ρ) ∨ ρ = π) = π := by
  have hs := (least_spec (fun ρ => ((fun _ : Ordinal.{u} => False) ρ ∧ Q ρ) ∨ ρ = π)
    (Exists.intro π (Or.inr rfl))).1
  cases hs with
  | inl hf => exact absurd hf.1 id
  | inr he => exact he

theorem Psi_eq_of_lt {ξ α : Ordinal.{u}} (hξ : α < ξ) (π : Ordinal.{u}) : Psi ξ π α = π := by
  unfold Psi
  rw [stages_eq α]
  show least (fun ρ => (Mof α (fun γ _ => stages γ) _ ξ ρ ∧ _) ∨ _) = _
  rw [Mof_gt _ _ hξ]
  exact least_false_or_eq _ π

/-! ### `C(α, β)` の構成子 -/

theorem Cn_lt (α β : Ordinal.{u}) (n : Nat) {x : Ordinal.{u}} (h : x < β) : Cn α β n x :=
  StageC.lt n x h

theorem Cn_one (α β : Ordinal.{u}) (n : Nat) : Cn α β n (succ 0) := StageC.one n

theorem Cn_K (α β : Ordinal.{u}) (n m : Nat) : Cn α β n (K m) := StageC.kc n m

theorem Cn_zero (α β : Ordinal.{u}) (n : Nat) : Cn α β n 0 := Cn_K α β n 0

theorem Cn_succ {α β : Ordinal.{u}} {n : Nat} {x : Ordinal.{u}} (h : Cn α β n x) :
    Cn α β (n + 1) x := by
  have hadd : Cn α β (n + 1) (x + 0) := StageC.add n x 0 h (Cn_zero α β n)
  rw [add_zero] at hadd
  exact hadd

theorem Cn_mono {α β : Ordinal.{u}} {n m : Nat} (hnm : n ≤ m) {x : Ordinal.{u}} (h : Cn α β n x) :
    Cn α β m x := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact Cn_succ ih

theorem C_lt {α β x : Ordinal.{u}} (h : x < β) : C α β x := Exists.intro 0 (Cn_lt α β 0 h)

theorem C_one (α β : Ordinal.{u}) : C α β (succ 0) := Exists.intro 0 (Cn_one α β 0)

theorem C_K (α β : Ordinal.{u}) (m : Nat) : C α β (K m) := Exists.intro 0 (Cn_K α β 0 m)

theorem C_zero (α β : Ordinal.{u}) : C α β 0 := C_K α β 0

theorem C_add {α β x y : Ordinal.{u}} (hx : C α β x) (hy : C α β y) : C α β (x + y) := by
  cases hx with
  | intro n hn =>
    cases hy with
    | intro m hm =>
      exact Exists.intro (max n m + 1) (StageC.add (max n m) x y
        (Cn_mono (Nat.le_max_left n m) hn) (Cn_mono (Nat.le_max_right n m) hm))

theorem C_Om {α β x : Ordinal.{u}} (hΛ : x < Λ) (hx : C α β x) : C α β (Om x) := by
  cases hx with
  | intro n hn => exact Exists.intro (n + 1) (StageC.om n x hΛ hn)

theorem C_Xi {α β x : Ordinal.{u}} (m : Nat) (hpos : 0 < x) (hα : x < α) (hx : C α β x) :
    C α β (Xi m x) := by
  cases hx with
  | intro n hn => exact Exists.intro (n + 1) (StageC.xi n m x hpos hα hn)

theorem C_Psi {α β ξ π δ : Ordinal.{u}} (hα : δ < α) (hξδ : ξ ≤ δ) (hπ : IsReg π)
    (hξ : C α β ξ) (hπC : C α β π) (hδ : C α β δ) : C α β (Psi ξ π δ) := by
  cases hξ with
  | intro n hn =>
    cases hπC with
    | intro m hm =>
      cases hδ with
      | intro k hk =>
        refine Exists.intro (max n (max m k) + 1) (StageC.psi (max n (max m k)) ξ π δ hα hξδ hπ
          (Cn_mono (Nat.le_max_left _ _) hn)
          (Cn_mono (Nat.le_trans (Nat.le_max_left m k) (Nat.le_max_right _ _)) hm)
          (Cn_mono (Nat.le_trans (Nat.le_max_right m k) (Nat.le_max_right _ _)) hk))

/-! ### Lemma 4.11 (i)：単調性 -/

theorem Cn_mono_arg {α α' β : Ordinal.{u}} (hα : α ≤ α') {n : Nat} {x : Ordinal.{u}}
    (h : Cn α β n x) : Cn α' β n x := by
  unfold Cn at h ⊢
  induction h with
  | lt n γ hγ => exact StageC.lt n γ hγ
  | one n => exact StageC.one n
  | kc n m => exact StageC.kc n m
  | add n x y _ _ ihx ihy => exact StageC.add n x y ihx ihy
  | om n x hΛ _ ih => exact StageC.om n x hΛ ih
  | xi n m x hpos hxα _ ih => exact StageC.xi n m x hpos (lt_of_lt_of_le hxα hα) ih
  | psi n ξ π δ hδα hξδ hπ _ _ _ ihξ ihπ ihδ =>
    exact StageC.psi n ξ π δ (lt_of_lt_of_le hδα hα) hξδ hπ ihξ ihπ ihδ

theorem C_mono_arg {α α' β x : Ordinal.{u}} (hα : α ≤ α') (h : C α β x) : C α' β x := by
  cases h with
  | intro n hn => exact Exists.intro n (Cn_mono_arg hα hn)

theorem Cn_mono_base {α β β' : Ordinal.{u}} (hβ : β ≤ β') {n : Nat} {x : Ordinal.{u}}
    (h : Cn α β n x) : Cn α β' n x := by
  unfold Cn at h ⊢
  induction h with
  | lt n γ hγ => exact StageC.lt n γ (lt_of_lt_of_le hγ hβ)
  | one n => exact StageC.one n
  | kc n m => exact StageC.kc n m
  | add n x y _ _ ihx ihy => exact StageC.add n x y ihx ihy
  | om n x hΛ _ ih => exact StageC.om n x hΛ ih
  | xi n m x hpos hxα _ ih => exact StageC.xi n m x hpos hxα ih
  | psi n ξ π δ hδα hξδ hπ _ _ _ ihξ ihπ ihδ => exact StageC.psi n ξ π δ hδα hξδ hπ ihξ ihπ ihδ

theorem C_mono_base {α β β' x : Ordinal.{u}} (hβ : β ≤ β') (h : C α β x) : C α β' x := by
  cases h with
  | intro n hn => exact Exists.intro n (Cn_mono_base hβ hn)

/-! ### Lemma 4.11 (iii)：極限での連続性 -/

theorem Cn_limit {α β : Ordinal.{u}} (hβ : IsLimit β) {n : Nat} {x : Ordinal.{u}}
    (h : Cn α β n x) : ∃ η, η < β ∧ Cn α η n x := by
  unfold Cn at h
  induction h with
  | lt n γ hγ => exact Exists.intro (succ γ) (And.intro (hβ.succ_lt hγ) (StageC.lt n γ (lt_succ_self γ)))
  | one n => exact Exists.intro 0 (And.intro hβ.1 (StageC.one n))
  | kc n m => exact Exists.intro 0 (And.intro hβ.1 (StageC.kc n m))
  | add n x y _ _ ihx ihy =>
    cases ihx with
    | intro η₁ h₁ =>
      cases ihy with
      | intro η₂ h₂ =>
        exact Exists.intro (omax η₁ η₂) (And.intro (omax_lt h₁.1 h₂.1)
          (StageC.add n x y (Cn_mono_base (le_omax_left η₁ η₂) h₁.2)
            (Cn_mono_base (le_omax_right η₁ η₂) h₂.2)))
  | om n x hΛ _ ih =>
    cases ih with
    | intro η h => exact Exists.intro η (And.intro h.1 (StageC.om n x hΛ h.2))
  | xi n m x hpos hxα _ ih =>
    cases ih with
    | intro η h => exact Exists.intro η (And.intro h.1 (StageC.xi n m x hpos hxα h.2))
  | psi n ξ π δ hδα hξδ hπ _ _ _ ihξ ihπ ihδ =>
    cases ihξ with
    | intro η₁ h₁ =>
      cases ihπ with
      | intro η₂ h₂ =>
        cases ihδ with
        | intro η₃ h₃ =>
          refine Exists.intro (omax η₁ (omax η₂ η₃)) (And.intro
            (omax_lt h₁.1 (omax_lt h₂.1 h₃.1)) (StageC.psi n ξ π δ hδα hξδ hπ
              (Cn_mono_base (le_omax_left _ _) h₁.2)
              (Cn_mono_base (le_trans (le_omax_left η₂ η₃) (le_omax_right _ _)) h₂.2)
              (Cn_mono_base (le_trans (le_omax_right η₂ η₃) (le_omax_right _ _)) h₃.2)))

theorem C_limit {α β x : Ordinal.{u}} (hβ : IsLimit β) (h : C α β x) : ∃ η, η < β ∧ C α η x := by
  cases h with
  | intro n hn =>
    cases Cn_limit hβ hn with
    | intro η hη => exact Exists.intro η (And.intro hη.1 (Exists.intro n hη.2))

/-! ### `Ψ` と `Ξ` の基本的な性質（Lemma 4.11 (iv)(v)） -/

theorem Psi_le (ξ π α : Ordinal.{u}) : Psi ξ π α ≤ π := by
  cases le_or_lt ξ α with
  | inl h =>
    rw [Psi_eq h]
    exact least_le _ (Or.inr rfl)
  | inr h => rw [Psi_eq_of_lt h]; exact le_refl π

/-- `Ψ^ξ_π(α) < π` なら、`Ψ^ξ_π(α) ∈ M^ξ` で `C(α, Ψ^ξ_π(α)) ∩ π ⊆ Ψ^ξ_π(α)`、`π, α ∈ C(α, Ψ^ξ_π(α))` -/
theorem Psi_spec {ξ π α : Ordinal.{u}} (h : Psi ξ π α < π) :
    ξ ≤ α ∧ M ξ (Psi ξ π α) ∧ (∀ x, C α (Psi ξ π α) x → x < π → x < Psi ξ π α) ∧
      C α (Psi ξ π α) π ∧ C α (Psi ξ π α) α := by
  cases le_or_lt ξ α with
  | inr hlt => rw [Psi_eq_of_lt hlt] at h; exact absurd h (lt_irrefl π)
  | inl hle =>
    refine And.intro hle ?_
    have hs := (least_spec (fun ρ =>
      (M ξ ρ ∧ ρ < π ∧ (∀ x, C α ρ x → x < π → x < ρ) ∧ C α ρ π ∧ C α ρ α) ∨ ρ = π)
      (Exists.intro π (Or.inr rfl))).1
    rw [← Psi_eq hle] at hs
    cases hs with
    | inl hs => exact And.intro hs.1 hs.2.2
    | inr he => exact absurd he (ne_of_lt h)

/-- `Ψ^ξ_π(α)` は条件を満たす `ρ < π` 以下 -/
theorem Psi_le_of {ξ π α ρ : Ordinal.{u}} (hξ : ξ ≤ α) (hM : M ξ ρ) (hρ : ρ < π)
    (hC : ∀ x, C α ρ x → x < π → x < ρ) (hπ : C α ρ π) (hα : C α ρ α) : Psi ξ π α ≤ ρ := by
  rw [Psi_eq hξ]
  exact least_le _ (Or.inl ⟨hM, hρ, hC, hπ, hα⟩)

theorem Xi_le (m : Nat) (α : Ordinal.{u}) : Xi m α ≤ K m := by
  rw [Xi_eq]
  exact least_le _ (Or.inr rfl)

/-- `Ξ_m(α) < K_m` なら、`Ξ_m(α) ∈ M^α` で `K_{m-1} < Ξ_m(α)` -/
theorem Xi_spec {m : Nat} {α : Ordinal.{u}} (h : Xi m α < K m) :
    M α (Xi m α) ∧ K (m - 1) < Xi m α := by
  have hs := (least_spec (fun π => (M α π ∧ K (m - 1) < π ∧ π < K m) ∨ π = K m)
    (Exists.intro (K m) (Or.inr rfl))).1
  rw [← Xi_eq] at hs
  cases hs with
  | inl hs => exact And.intro hs.1 hs.2.1
  | inr he => exact absurd he (ne_of_lt h)

/-- `Ξ_m(α)` は条件を満たす `π` 以下 -/
theorem Xi_le_of {m : Nat} {α π : Ordinal.{u}} (hM : M α π) (h1 : K (m - 1) < π) (h2 : π < K m) :
    Xi m α ≤ π := by
  rw [Xi_eq]
  exact least_le _ (Or.inl ⟨hM, h1, h2⟩)

end

/-! ## `|C(α, β)| < π`（Lemma 4.11 (ii)）と、`Ψ^ξ_π(α) ∈ M^ξ ∩ π`（Prop. 4.16 の前半）。

* `C_small`：`π` が非可算正則で `β < π` なら `C(α, β)` は `π` 未満の個数。
* `C_bounded`：さらに `C(α, β) ∩ π` は `π` 未満の順序数で抑えられる。
* `Psi_lt`：`M^ξ` が `π` で定常で、`ξ ≤ α`、`ξ, π, α ∈ C(α, π)` なら `Ψ^ξ_π(α) < π`
  （`Psi_spec` と合わせて `Ψ^ξ_π(α) ∈ M^ξ ∩ π`）。 -/

noncomputable section

/-- 正則基数 `κ` 未満の小さい集合は `κ` 未満で抑えられる -/
theorem Small.bounded {κ : Ordinal.{u}} (hκ : IsRegular κ) {A : Ordinal.{u} → Prop}
    (h : Small κ A) (hA : ∀ x, A x → x < κ) : ∃ γ, γ < κ ∧ ∀ x, A x → x < γ := by
  classical
  cases h with
  | intro β hβ =>
    cases hβ.2 with
    | intro f hf =>
      let pre : Ordinal.{u} → Ordinal.{u} := fun ζ =>
        if h : ∃ x, A x ∧ f x = ζ then Classical.choose h else 0
      have hpre : ∀ x, A x → pre (f x) = x := by
        intro x hx
        have h : ∃ y, A y ∧ f y = f x := Exists.intro x (And.intro hx rfl)
        have e : pre (f x) = Classical.choose h := dite_eq_left h
        rw [e]
        have hs := Classical.choose_spec h
        exact hf.2 _ _ hs.1 hx hs.2
      have hpreκ : ∀ ζ, pre ζ < κ := by
        intro ζ
        by_cases h : ∃ x, A x ∧ f x = ζ
        · have e : pre ζ = Classical.choose h := dite_eq_left h
          rw [e]
          exact hA _ (Classical.choose_spec h).1
        · have e : pre ζ = 0 := dite_eq_right h
          rw [e]
          exact hκ.pos
      refine Exists.intro (supLt β (fun ζ => succ (pre ζ)))
        (And.intro (hκ.supLt_lt hβ.1 (fun ζ _ => hκ.1.succ_lt (hpreκ ζ))) ?_)
      intro x hx
      apply (lt_supLt_iff _ _ _).mpr
      refine Exists.intro (f x) (And.intro (hf.1 x hx) ?_)
      show x < succ (pre (f x))
      rw [hpre x hx]
      exact lt_succ_self x

variable [Setting.{u}]

/-! ### Lemma 4.11 (ii) -/

theorem Cn_zero_cases {α β x : Ordinal.{u}} (h : Cn α β 0 x) :
    x < β ∨ x = succ 0 ∨ ∃ m, x = K m := by
  unfold Cn at h
  cases h with
  | lt _ _ h => exact Or.inl h
  | one _ => exact Or.inr (Or.inl rfl)
  | kc _ m => exact Or.inr (Or.inr (Exists.intro m rfl))

theorem Cn_succ_cases {α β x : Ordinal.{u}} {n : Nat} (h : Cn α β (n + 1) x) :
    Cn α β n x ∨ (∃ y z, Cn α β n y ∧ Cn α β n z ∧ x = y + z) ∨
      (∃ y, Cn α β n y ∧ x = Om y) ∨
      (∃ y m, Cn α β n y ∧ x = Xi m y) ∨
      (∃ ξ π δ, Cn α β n ξ ∧ Cn α β n π ∧ Cn α β n δ ∧ x = Psi ξ π δ) := by
  unfold Cn at h
  cases h with
  | lt _ _ h => exact Or.inl (StageC.lt n x h)
  | one _ => exact Or.inl (StageC.one n)
  | kc _ m => exact Or.inl (StageC.kc n m)
  | add _ y z hy hz => exact Or.inr (Or.inl ⟨y, z, hy, hz, rfl⟩)
  | om _ y _ hy => exact Or.inr (Or.inr (Or.inl ⟨y, hy, rfl⟩))
  | xi _ m y _ _ hy => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨y, m, hy, rfl⟩)))
  | psi _ ξ π δ _ _ _ hξ hπ hδ => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ξ, π, δ, hξ, hπ, hδ, rfl⟩)))

theorem small_K {κ : Ordinal.{u}} (hω : omega < κ) : Small κ (fun x => ∃ m, x = K m) := by
  apply ((small_natOrd hω).image (fun y => K (natOf y))).mono
  intro x hx
  cases hx with
  | intro m hm =>
    refine Exists.intro (ordNat m) (And.intro (Exists.intro m rfl) ?_)
    rw [natOf_ordNat]
    exact hm

theorem Cn_small {π β : Ordinal.{u}} (hπ : R π) (hβ : β < π) (α : Ordinal.{u}) :
    ∀ n, Small π (Cn α β n) := by
  have hreg := hπ.2
  have hω := hπ.1
  intro n
  induction n with
  | zero =>
    have h1 : Small π (fun x => x = succ (0 : Ordinal.{u})) := by
      apply (small_natOrd hω).mono
      intro x hx
      exact Exists.intro 1 hx
    apply ((Small.union hreg (small_lt hβ) (Small.union hreg h1 (small_K hω)))).mono
    intro x hx
    exact Cn_zero_cases hx
  | succ n ih =>
    have hadd := Small.image2 hreg ih ih (fun y z => y + z)
    have hom := Small.image ih Om
    have hxi := Small.image2 hreg ih (small_natOrd hω) (fun y m => Xi (natOf m) y)
    have hpsi : Small π (fun x => ∃ ξ, Cn α β n ξ ∧
        (fun ξ x => ∃ p d, Cn α β n p ∧ Cn α β n d ∧ x = Psi ξ p d) ξ x) :=
      Small.iUnion hreg ih (fun ξ _ => Small.image2 hreg ih ih (fun p d => Psi ξ p d))
    apply (Small.union hreg ih (Small.union hreg hadd (Small.union hreg hom
      (Small.union hreg hxi hpsi)))).mono
    intro x hx
    cases Cn_succ_cases hx with
    | inl h => exact Or.inl h
    | inr h =>
      cases h with
      | inl h => exact Or.inr (Or.inl h)
      | inr h =>
        cases h with
        | inl h =>
          cases h with
          | intro y hy => exact Or.inr (Or.inr (Or.inl ⟨y, hy.1, hy.2⟩))
        | inr h =>
          cases h with
          | inl h =>
            cases h with
            | intro y hy =>
              cases hy with
              | intro m hm =>
                refine Or.inr (Or.inr (Or.inr (Or.inl ⟨y, ordNat m, hm.1, Exists.intro m rfl, ?_⟩)))
                rw [natOf_ordNat]
                exact hm.2
          | inr h =>
            cases h with
            | intro ξ h =>
              cases h with
              | intro p h =>
                cases h with
                | intro d h =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ξ, h.1, p, d, h.2.1, h.2.2.1, h.2.2.2⟩)))

/-- Lemma 4.11 (ii)：`|C(α, β)| < π` -/
theorem C_small {π β : Ordinal.{u}} (hπ : R π) (hβ : β < π) (α : Ordinal.{u}) :
    Small π (C α β) := by
  apply (Small.iUnion hπ.2 (small_natOrd hπ.1) (A := fun i x => Cn α β (natOf i) x)
    (fun i _ => Cn_small hπ hβ α (natOf i))).mono
  intro x hx
  cases hx with
  | intro n hn =>
    refine Exists.intro (ordNat n) (And.intro (Exists.intro n rfl) ?_)
    show Cn α β (natOf (ordNat n)) x
    rw [natOf_ordNat]
    exact hn

/-- `C(α, β) ∩ π` は `π` 未満で抑えられる -/
theorem C_bounded {π β : Ordinal.{u}} (hπ : R π) (hβ : β < π) (α : Ordinal.{u}) :
    ∃ γ, γ < π ∧ ∀ x, C α β x → x < π → x < γ := by
  cases Small.bounded hπ.2 ((C_small hπ hβ α).mono (A := fun x => C α β x ∧ x < π)
      (fun _ h => h.1)) (fun _ h => h.2) with
  | intro γ hγ => exact Exists.intro γ (And.intro hγ.1 (fun x hx hxπ => hγ.2 x (And.intro hx hxπ)))

/-! ### Prop. 4.16（前半） -/

/-- `C(α, ρ) ∩ π ⊆ ρ` となる `ρ`（`μ₀ < ρ < π`）は `π` で閉非有界 -/
theorem club_closedC {π : Ordinal.{u}} (hπ : R π) (α : Ordinal.{u}) {μ₀ : Ordinal.{u}}
    (hμ₀ : μ₀ < π) :
    Club π (fun ρ => μ₀ < ρ ∧ ∀ x, C α ρ x → x < π → x < ρ) := by
  classical
  apply And.intro
  · intro η hη
    -- `δ₀ = max(η, μ₀) + 1`、`δ_{n+1} = max(δ_n + 1, sup(C(α, δ_n) ∩ π))`
    let bnd : Ordinal.{u} → Ordinal.{u} := fun δ =>
      if h : δ < π then Classical.choose (C_bounded hπ h α) else 0
    have hbnd : ∀ δ, δ < π → bnd δ < π ∧ ∀ x, C α δ x → x < π → x < bnd δ := by
      intro δ hδ
      have e : bnd δ = Classical.choose (C_bounded hπ hδ α) := dite_eq_left hδ
      rw [e]
      exact Classical.choose_spec (C_bounded hπ hδ α)
    let s : Nat → Ordinal.{u} := fun n =>
      Nat.rec (succ (omax η μ₀)) (fun _ δ => omax (succ δ) (bnd δ)) n
    have hs0 : s 0 = succ (omax η μ₀) := rfl
    have hsS : ∀ n, s (n + 1) = omax (succ (s n)) (bnd (s n)) := fun _ => rfl
    have hsπ : ∀ n, s n < π := by
      intro n
      induction n with
      | zero => rw [hs0]; exact hπ.2.1.succ_lt (omax_lt hη hμ₀)
      | succ n ih =>
        rw [hsS]
        exact omax_lt (hπ.2.1.succ_lt ih) (hbnd _ ih).1
    have hs : ∀ n, s n < s (n + 1) := by
      intro n
      rw [hsS]
      exact lt_of_lt_of_le (lt_succ_self _) (le_omax_left _ _)
    let δs := omegaSup s
    have hδsπ : δs < π := omegaSup_lt hπ hsπ
    have hδslim : IsLimit δs := by
      apply And.intro (lt_of_le_of_lt (zero_le _) (lt_omegaSup hs 0))
      intro β hβ
      cases (lt_omegaSup_iff β).mp hβ with
      | intro n hn => exact lt_of_le_of_lt (succ_le_of_lt hn) (lt_omegaSup hs n)
    have hlt0 : omax η μ₀ < δs := lt_trans _ _ _ (lt_succ_self _) (lt_omegaSup hs 0)
    refine Exists.intro δs (And.intro (And.intro
      (lt_of_le_of_lt (le_omax_right η μ₀) hlt0) ?_)
      (And.intro (lt_of_le_of_lt (le_omax_left η μ₀) hlt0) hδsπ))
    intro x hx hxπ
    cases C_limit hδslim hx with
    | intro ζ hζ =>
      cases (lt_omegaSup_iff ζ).mp hζ.1 with
      | intro n hn =>
        have hxn : x < bnd (s n) := (hbnd _ (hsπ n)).2 x (C_mono_base (Or.inl hn) hζ.2) hxπ
        exact lt_trans _ _ _ hxn (lt_of_le_of_lt (by rw [hsS n]; exact le_omax_right _ _)
          (lt_omegaSup hs (n + 1)))
  · intro l hlπ hlp
    have hl : IsLimit l := by
      apply And.intro hlp.1
      intro β hβ
      cases hlp.2 β hβ with
      | intro γ hγ => exact lt_of_le_of_lt (succ_le_of_lt hγ.2.1) hγ.2.2
    apply And.intro
    · cases hlp.2 0 hlp.1 with
      | intro γ hγ => exact lt_trans _ _ _ hγ.1.1 hγ.2.2
    · intro x hx hxπ
      cases C_limit hl hx with
      | intro ζ hζ =>
        cases hlp.2 ζ hζ.1 with
        | intro ρ hρ =>
          exact lt_trans _ _ _ (hρ.1.2 x (C_mono_base (Or.inl hρ.2.1) hζ.2) hxπ) hρ.2.2

/-- Prop. 4.16（前半）：`M^ξ` が `π` で定常、`ξ ≤ α`、`ξ, π, α ∈ C(α, π)` なら `Ψ^ξ_π(α) < π` -/
theorem Psi_lt {ξ π α : Ordinal.{u}} (hπ : R π) (hstat : Stationary π (M ξ)) (hξα : ξ ≤ α)
    (hξ : C α π ξ) (hπC : C α π π) (hα : C α π α) : Psi ξ π α < π := by
  have hl := hπ.2.1
  cases C_limit hl hξ with
  | intro η₁ h₁ =>
    cases C_limit hl hπC with
    | intro η₂ h₂ =>
      cases C_limit hl hα with
      | intro η₃ h₃ =>
        let μ₀ := omax η₁ (omax η₂ η₃)
        have hμ₀ : μ₀ < π := omax_lt h₁.1 (omax_lt h₂.1 h₃.1)
        cases hstat _ (club_closedC hπ α hμ₀) with
        | intro ν hν =>
          have hle : ∀ η, η ≤ μ₀ → η ≤ ν := fun η h => le_trans h (Or.inl hν.2.1.1)
          apply lt_of_le_of_lt _ hν.1
          exact Psi_le_of hξα hν.2.2 hν.1 hν.2.1.2
            (C_mono_base (hle _ (le_trans (le_omax_left η₂ η₃) (le_omax_right _ _))) h₂.2)
            (C_mono_base (hle _ (le_trans (le_omax_right η₂ η₃) (le_omax_right _ _))) h₃.2)

/-! ## 記法系 `T⁺`（`Compact/Additive.lean` の `RTKA`）の項の値と、目標の定理の主張。

* `val`：項の値（`Ψ^ξ_π(α)` は `Psi ξ π α`、`Ξ_n(α)` は `Xi n α`）。
* `StationaryHyp`：Rathjen の Thm. 4.12 にあたる定常性。
  `1 ≤ n`、`0 < α ≤ K_n^+`、`α ∈ C(α, K_n)` なら `M^α` は `K_n` で定常。
* `CmpCorrect`：目標。標準形の項について `cmp` が値の大小と一致する。

`StationaryHyp → CmpCorrect` は `Correct.lean` の `cmpCorrect_of_stationaryHyp`。`StationaryHyp` は
`Complete.lean` の `stationaryHyp_of_wc` で弱コンパクト基数の列から導く。 -/

/-- 項の値 -/
def val : RTKA.Tm → Ordinal.{u}
  | .zero => 0
  | .one => succ 0
  | .K n => K n
  | .plus a b => val a + val b
  | .Om a => Om (val a)
  | .Xi n a => Xi n (val a)
  | .Psi xi pi a => Psi (val xi) (val pi) (val a)

theorem val_succK (n : Nat) : val.{u} (RTKA.succK n) = Om (K n + succ 0) := by
  simp only [RTKA.succK, val]

/-- Thm. 4.12 にあたる定常性（`K_n` が弱コンパクトなら成り立つ：`stationaryHyp_of_wc`）：
    `1 ≤ n`、`0 < α ≤ K_n^+`、`α ∈ C(α, K_n)` なら `M^α` は `K_n` で定常 -/
def StationaryHyp : Prop :=
  ∀ n, 1 ≤ n → ∀ α : Ordinal.{u}, 0 < α → α ≤ Om (K n + succ 0) → C α (K n) α →
    Stationary (K n) (M α)

/-- 目標：標準形の項について、`cmp` が値の大小・相等と一致する -/
def CmpCorrect : Prop :=
  ∀ a b : RTKA.Tm, RTKA.isNF a = true → RTKA.isNF b = true →
    (RTKA.lt a b = true ↔ val.{u} a < val b) ∧ (RTKA.cmp a b = .eq ↔ val.{u} a = val b)

/-- `M^α` が `K_m` で定常なら `K_{m-1} < Ξ_m(α) < K_m` で `Ξ_m(α) ∈ M^α` -/
theorem Xi_lt {m : Nat} (hm : 1 ≤ m) {α : Ordinal.{u}} (hstat : Stationary (K m) (M α)) :
    Xi m α < K m := by
  have hlt : K (m - 1) < K m := K_lt (Nat.sub_lt hm Nat.one_pos)
  cases hstat _ (club_gt (R_K hm) hlt) with
  | intro π hπ => exact lt_of_le_of_lt (Xi_le_of hπ.2.2 hπ.2.1 hπ.1) hπ.1

theorem Xi_mem {m : Nat} (hm : 1 ≤ m) {α : Ordinal.{u}} (hstat : Stationary (K m) (M α)) :
    M α (Xi m α) ∧ K (m - 1) < Xi m α ∧ Xi m α < K m :=
  let h := Xi_spec (Xi_lt hm hstat)
  ⟨h.1, h.2, Xi_lt hm hstat⟩

end

/-! ## `M^ξ` の定常性から `M^ξ` への所属を得る（Lemma 4.11 (vi)(vii)）。

* `M_of_stationary`（4.11 (vii)）：`π ∈ Reg` で `M^ξ` が `π` で定常なら `π ∈ M^ξ`。
* `M_of_M`（4.11 (vi)）：`π ∈ M^α` で `ξ ∈ C(α, π) ∩ α` なら `π ∈ M^ξ`。
* `Psi_not_stationary`, `Psi_not_M`（Prop. 4.16 後半）：`ξ > 0` で `Ψ^ξ_π(α) < π` なら、
  `M^ξ` は `Ψ^ξ_π(α)` で定常でなく、`β > ξ` について `Ψ^ξ_π(α) ∉ M^β`。

準備として、`K(ρ)` が `(K_{n-1}, K_n)` で一定であることと、閉非有界集合の極限点の集合が閉非有界であることを示す。 -/

noncomputable section

/-! ### 閉非有界集合の極限点 -/

/-- 閉非有界集合の極限点全体は閉非有界 -/
theorem Club.limitPoints {κ : Ordinal.{u}} (hκ : R κ) {U : Ordinal.{u} → Prop} (hU : Club κ U) :
    Club κ (IsLimitPoint U) := by
  apply And.intro
  · intro η hη
    let s : Nat → Ordinal.{u} := fun n => Nat.rec η (fun _ δ => nextAbove κ U hU.1 δ) n
    have hsS : ∀ n, s (n + 1) = nextAbove κ U hU.1 (s n) := fun _ => rfl
    have hsp : ∀ n, s n < κ ∧ U (s (n + 1)) ∧ s n < s (n + 1) := by
      intro n
      induction n with
      | zero =>
        have h := nextAbove_spec hU.1 hη
        exact ⟨hη, h.1, h.2.1⟩
      | succ n ih =>
        have h1 : s (n + 1) < κ := by rw [hsS n]; exact (nextAbove_spec hU.1 ih.1).2.2
        have h2 := nextAbove_spec hU.1 h1
        rw [hsS (n + 1)]
        exact ⟨h1, h2.1, h2.2.1⟩
    have hs : ∀ n, s n < s (n + 1) := fun n => (hsp n).2.2
    refine Exists.intro (omegaSup s) (And.intro (omegaSup_isLimitPoint hs (fun n => (hsp n).2.1))
      (And.intro (lt_omegaSup hs 0) (omegaSup_lt hκ (fun n => (hsp n).1))))
  · intro l _ hlp
    apply And.intro hlp.1
    intro η hη
    cases hlp.2 η hη with
    | intro ρ hρ =>
      cases hρ.1.2 η hρ.2.1 with
      | intro ζ hζ => exact Exists.intro ζ (And.intro hζ.1 (And.intro hζ.2.1 (lt_trans _ _ _ hζ.2.2 hρ.2.2)))

/-- `ρ` が `U` の極限点で `U` が `κ` で閉なら、`U` は `ρ` で閉非有界 -/
theorem Club.below {κ ρ : Ordinal.{u}} {U : Ordinal.{u} → Prop} (hU : Club κ U) (hρκ : ρ < κ)
    (hρ : IsLimitPoint U ρ) : Club ρ U := by
  apply And.intro
  · intro η hη
    cases hρ.2 η hη with
    | intro ζ hζ => exact Exists.intro ζ hζ
  · intro l hl hlp
    exact hU.2 l (lt_trans _ _ _ hl hρκ) hlp

variable [Setting.{u}]

/-! ### `K(ρ)` -/

theorem exists_level_aux (π : Ordinal.{u}) :
    ∀ N, π < K N → ∃ n, π < K n ∧ ∀ m, m < n → K m ≤ π := by
  intro N
  induction N with
  | zero => intro h; exact absurd h (not_lt_zero π)
  | succ N ih =>
    intro h
    cases lt_or_le π (K N) with
    | inl h' => exact ih h'
    | inr h' =>
      refine Exists.intro (N + 1) (And.intro h ?_)
      intro m hm
      exact le_trans (K_le (Nat.le_of_lt_succ hm)) h'

/-- `π < Λ` なら `π < K_n` となる最小の `n` がある -/
theorem exists_level {π : Ordinal.{u}} (hπ : π < Λ) : ∃ n, π < K n ∧ ∀ m, m < n → K m ≤ π := by
  cases (lt_Λ_iff π).mp hπ with
  | intro N hN => exact exists_level_aux π N hN

theorem Kabove_eq {π : Ordinal.{u}} {n : Nat} (h1 : π < K n) (h2 : ∀ m, m < n → K m ≤ π) :
    Kabove π = K n := by
  have hP : (∃ k, K n = K k) ∧ π < K n := And.intro (Exists.intro n rfl) h1
  apply le_antisymm (least_le _ hP)
  apply le_of_not_lt
  intro hlt
  have hs := (least_spec (fun κ => (∃ k, κ = K k) ∧ π < κ) (Exists.intro _ hP)).1
  cases hs.1 with
  | intro k hk =>
    have hltk : K k < K n := by rw [← hk]; exact hlt
    have hπk : π < K k := by rw [← hk]; exact hs.2
    exact absurd hπk (not_lt_of_le (h2 k (K_lt_iff.mp hltk)))

/-- `π ∈ Reg` なら `K_{n-1} < π < K_n`（`1 ≤ n`）となる `n` があり、`K(π) = K_n` -/
theorem IsReg.level {π : Ordinal.{u}} (hπ : IsReg π) :
    ∃ n, 1 ≤ n ∧ K (n - 1) < π ∧ π < K n ∧ Kabove π = K n := by
  cases exists_level hπ.2.1 with
  | intro n hn =>
    cases n with
    | zero => exact absurd hn.1 (not_lt_zero π)
    | succ n =>
      have hle : K n ≤ π := hn.2 n (Nat.lt_succ_self n)
      have hlt : K n < π := lt_of_le_of_ne hle (fun e => hπ.2.2 n e.symm)
      exact ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), hlt, hn.1, Kabove_eq hn.1 hn.2⟩

/-- `K_{n-1} ≤ ρ < K_n` なら `K(ρ) = K_n` -/
theorem Kabove_eq_of_between {ρ : Ordinal.{u}} {n : Nat} (h1 : K (n - 1) ≤ ρ)
    (h2 : ρ < K n) : Kabove ρ = K n := by
  apply Kabove_eq h2
  intro m hm
  exact le_trans (K_le (Nat.le_sub_one_of_lt hm)) h1

/-! ### Lemma 4.11 (vi)(vii) -/

/-- Lemma 4.11 (vii)：`π ∈ Reg` で `M^ξ` が `π` で定常なら `π ∈ M^ξ` -/
theorem M_of_stationary {ξ π : Ordinal.{u}} (hπ : IsReg π) (hstat : Stationary π (M ξ)) :
    M ξ π := by
  have hR := hπ.1
  cases eq_zero_or_pos ξ with
  | inl h0 =>
    subst h0
    exact (M_zero_iff π).mpr (And.intro hR.2.1 hπ.2.1)
  | inr hpos =>
    have hξ0 : ξ ≠ 0 := ne_of_gt hpos
    cases hπ.level with
    | intro n hn =>
      have hunb := hstat.unbounded hR
      -- `M^ξ ∩ (η, π)` の元は `M^ξ` の性質をもつ
      have hMρ : ∀ ρ, M ξ ρ → IsReg ρ ∧ (∀ x, C ξ ρ x → x < Kabove ρ → x < ρ) ∧ C ξ ρ ξ ∧
          ∀ η, η < ξ → C ξ ρ η → Stationary ρ (M η) := fun ρ h => (M_pos_iff hξ0 ρ).mp h
      apply (M_pos_iff hξ0 π).mpr
      refine ⟨hπ, ?_, ?_, ?_⟩
      · intro x hx hxK
        cases C_limit hR.2.1 hx with
        | intro η hη =>
          cases hunb (omax η (K (n - 1))) (omax_lt hη.1 hn.2.1) with
          | intro ρ hρ =>
            have hKρ : Kabove ρ = K n :=
              Kabove_eq_of_between (le_trans (le_omax_right _ _) (Or.inl hρ.2.1))
                (lt_trans _ _ _ hρ.2.2 hn.2.2.1)
            have hxρ := (hMρ ρ hρ.1).2.1 x
              (C_mono_base (le_trans (le_omax_left _ _) (Or.inl hρ.2.1)) hη.2)
              (by rw [hKρ, ← hn.2.2.2]; exact hxK)
            exact lt_trans _ _ _ hxρ hρ.2.2
      · cases hunb 0 hR.2.pos with
        | intro ρ hρ => exact C_mono_base (Or.inl hρ.2.2) (hMρ ρ hρ.1).2.2.1
      · intro η hηξ hηC U hU
        cases C_limit hR.2.1 hηC with
        | intro ε hε =>
          cases hstat _ (Club.inter hR (Club.limitPoints hR hU) (club_gt hR hε.1)) with
          | intro ρ hρ =>
            have hρM := hMρ ρ hρ.2.2
            have hstatρ := hρM.2.2.2 η hηξ (C_mono_base (Or.inl hρ.2.1.2) hε.2)
            cases hstatρ U (Club.below hU hρ.1 hρ.2.1.1) with
            | intro ζ hζ => exact Exists.intro ζ (And.intro (lt_trans _ _ _ hζ.1 hρ.1) hζ.2)

/-- Lemma 4.11 (vi)：`π ∈ M^α` で `ξ ∈ C(α, π) ∩ α` なら `π ∈ M^ξ` -/
theorem M_of_M {α ξ π : Ordinal.{u}} (h : M α π) (hξα : ξ < α) (hξ : C α π ξ) : M ξ π := by
  have hα0 : α ≠ 0 := ne_of_gt (lt_of_le_of_lt (zero_le ξ) hξα)
  have hM := (M_pos_iff hα0 π).mp h
  exact M_of_stationary hM.1 (hM.2.2.2 ξ hξα hξ)

/-! ### Prop. 4.16（後半） -/

/-! ## The weak-compact reflection step in Rathjen's Theorem 4.12.

`StageReflectionAt n` is the local reflection statement needed at `K n`.  The
induction below derives `StationaryHyp` from those reflection statements.
`StageReflectionAt` itself is proved from the partition property of `K n`
(`PartitionProp`) by `stageReflectionAt_of_partition` in `Reflection.lean`, and
`Complete.lean` puts the two together.
-/

/-- The reflection conclusion required at stage `n` in Theorem 4.12. -/
def StageReflectionAt (n : Nat) : Prop :=
  ∀ α, 0 < α → α ≤ Om (K n + succ 0) → C α (K n) α →
    (∀ β, β < α → 0 < β → β ≤ Om (K n + succ 0) → C β (K n) β →
      Stationary (K n) (M β)) →
    ∀ E, Club (K n) E →
      ∃ τ, τ < K n ∧ E τ ∧ IsReg τ ∧ C α τ α ∧
        (∀ x, C α τ x → x < Kabove τ → x < τ) ∧
        (∀ β, β < α → C α τ β → Stationary τ (M β))

/-- Rathjen's induction step: the local reflection conclusion at every `K n`
implies `StationaryHyp`. -/
theorem stationaryHyp_of_stageReflection
    (hreflect : ∀ n, 1 ≤ n → StageReflectionAt n) : StationaryHyp.{u} := by
  intro n hn α
  induction α using lt_wellFounded.induction with
  | h α ih =>
    intro hα0 hαK hC E hE
    cases hreflect n hn α hα0 hαK hC ih E hE with
    | intro τ hτ =>
      exact ⟨τ, hτ.1, hτ.2.1,
        (M_pos_iff (ne_of_gt hα0) τ).mpr
          ⟨hτ.2.2.1, hτ.2.2.2.2.1, hτ.2.2.2.1, hτ.2.2.2.2.2⟩⟩

end
end OCF.Rathjen
