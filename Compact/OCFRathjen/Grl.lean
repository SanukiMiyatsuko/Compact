import Compact.OCFRathjen.Ultra

/-! 反射補題（GRL）：`κ` が `R κ ∧ PartitionProp κ` で、`S c`（`c < κ`）がすべて `κ` で定常、
`E` が `κ` の club なら、`E` に属する正則な `τ < κ` で、すべての `c < τ` について `S c` が
`τ` で定常となるものがある。

方針：`PartitionProp` から得た収束集合 `H`（`Ultra.lean`）上で、`NN` な語のうち `lessH` に
関して最小の `f₀` を取り、`f₀(x)`（`x ∈ H` が十分大きい）が求める `τ` になることを示す。 -/

namespace OCF.Rathjen

universe u

open Ordinal

set_option linter.unusedSectionVars false

noncomputable section

/-! ### 非正則順序数の共終列 -/

theorem cofinalFrom_self {θ : Ordinal.{u}} (hlim : IsLimit θ) : CofinalFrom θ θ := by
  let f : (representative θ).Carrier → Ordinal.{u} := fun x =>
    type ((representative θ).below x)
  have hlt : ∀ x, f x < θ := fun x => initial_lt θ x
  have hsup : sup f = θ := by
    apply le_antisymm
    · apply (sup_le_iff f θ).mpr
      intro x
      exact Or.inl (hlt x)
    · apply (not_lt_iff_le (sup f) θ).mp
      intro hsupθ
      let ξ := sup f
      have hξθ : ξ < θ := by simpa [ξ] using hsupθ
      obtain ⟨x, hx⟩ := initial_surjective θ (succ ξ) (hlim.2 ξ hξθ)
      have hvalue : f x = succ ξ := by simpa [f] using hx.symm
      have hle : succ ξ ≤ sup f := by
        simpa only [hvalue] using le_sup f x
      have hle' : succ ξ ≤ ξ := by simpa [ξ] using hle
      exact lt_irrefl ξ (lt_of_lt_of_le (lt_succ_self ξ) hle')
  exact ⟨f, hlt, hsup⟩

/-- `ω` より大きい非正則順序数には、より短い共終列がある -/
theorem nr_data {y : Ordinal.{u}} (hω : omega < y) (hnr : ¬ R y) :
    ∃ δ, δ < y ∧ ∃ hf : Ordinal.{u} → Ordinal.{u}, (∀ ξ, ξ < δ → hf ξ < y) ∧
      ∀ η, η < y → ∃ ξ, ξ < δ ∧ η ≤ hf ξ := by
  classical
  have hy0 : y ≠ 0 := ne_of_gt (lt_of_le_of_lt (zero_le _) hω)
  rcases zero_or_succ_or_limit y with h0 | ⟨β, hβ⟩ | hlim
  · exact absurd h0 hy0
  · refine ⟨succ 0, ?_, fun _ => β, ?_, ?_⟩
    · exact lt_trans _ _ _ (ordNat_lt_omega 1 : (succ 0 : Ordinal.{u}) < omega) hω
    · intro ξ _
      rw [hβ]
      exact lt_succ_self β
    · intro η hη
      rw [hβ] at hη
      exact ⟨0, lt_succ_self 0, le_of_lt_succ hη⟩
  · have hcf : cf y ≠ y := fun h => hnr ⟨hω, hlim, h⟩
    have hcofy : CofinalFrom y y := cofinalFrom_self hlim
    have hle : cf y ≤ y := least_le _ hcofy
    have hlt : cf y < y := by
      cases hle with
      | inl h => exact h
      | inr h => exact absurd h hcf
    have hcfspec : CofinalFrom (cf y) y := (least_spec (fun β => CofinalFrom β y) ⟨y, hcofy⟩).1
    obtain ⟨f₀, hf₀lt, hf₀sup⟩ := hcfspec
    refine ⟨cf y, hlt, fun ξ => if h : ξ < cf y then f₀ (pointBelow (cf y) ξ h) else 0, ?_, ?_⟩
    · intro ξ hξ
      dsimp only
      rw [dite_eq_left hξ]
      exact hf₀lt _
    · intro η hη
      rw [← hf₀sup] at hη
      obtain ⟨x, hx⟩ := (lt_sup_iff f₀ η).mp hη
      have hξ : type ((representative (cf y)).below x) < cf y := initial_lt (cf y) x
      have hpt : pointBelow (cf y) (type ((representative (cf y)).below x)) hξ = x :=
        initial_injective (cf y) _ _ (pointBelow_spec hξ).symm
      refine ⟨type ((representative (cf y)).below x), hξ, ?_⟩
      dsimp only
      rw [dite_eq_left hξ, hpt]
      exact Or.inl hx

/-- 非正則：`ω` より大きく正則でない -/
def NRp (y : Ordinal.{u}) : Prop := omega < y ∧ ¬ R y

open Classical in
/-- 共終列の長さ -/
def dlF (y : Ordinal.{u}) : Ordinal.{u} :=
  if h : NRp y then Classical.choose (nr_data h.1 h.2) else 0

open Classical in
/-- 共終列 -/
def hhF (y ξ : Ordinal.{u}) : Ordinal.{u} :=
  if h : NRp y then
    (if ξ < dlF y then Classical.choose (Classical.choose_spec (nr_data h.1 h.2)).2 ξ else 0)
  else 0

theorem nr_spec {y : Ordinal.{u}} (h : NRp y) :
    dlF y < y ∧ (∀ ξ, ξ < dlF y → hhF y ξ < y) ∧
      ∀ η, η < y → ∃ ξ, ξ < dlF y ∧ η ≤ hhF y ξ := by
  classical
  have hd : dlF y = Classical.choose (nr_data h.1 h.2) := dite_eq_left h
  have hs := Classical.choose_spec (nr_data h.1 h.2)
  have hs2 := Classical.choose_spec hs.2
  have hh : ∀ ξ, ξ < dlF y → hhF y ξ = Classical.choose hs.2 ξ := by
    intro ξ hξ
    have e : hhF y ξ = (if ξ < dlF y then Classical.choose hs.2 ξ else 0) := dite_eq_left h
    rw [e, ite_eq_left hξ]
  rw [hd]
  refine ⟨hs.1, ?_, ?_⟩
  · intro ξ hξ
    rw [← hd] at hξ
    rw [hh ξ hξ]
    exact hs2.1 ξ (by rw [hd] at hξ; exact hξ)
  · intro η hη
    obtain ⟨ξ, hξ, hle⟩ := hs2.2 η hη
    have hξ' : ξ < dlF y := by rw [hd]; exact hξ
    exact ⟨ξ, hξ, by rw [hh ξ hξ']; exact hle⟩

theorem dlF_le (y : Ordinal.{u}) : dlF y ≤ y := by
  by_cases h : NRp y
  · exact Or.inl (nr_spec h).1
  · have e : dlF y = 0 := dite_eq_right h
    rw [e]
    exact zero_le _

theorem hhF_le (y ξ : Ordinal.{u}) : hhF y ξ ≤ y := by
  classical
  by_cases h : NRp y
  · by_cases hξ : ξ < dlF y
    · exact Or.inl ((nr_spec h).2.1 ξ hξ)
    · have e : hhF y ξ = 0 := by
        have e0 : hhF y ξ = (if ξ < dlF y then Classical.choose
          (Classical.choose_spec (nr_data h.1 h.2)).2 ξ else 0) := dite_eq_left h
        rw [e0, ite_eq_right hξ]
      rw [e]
      exact zero_le _
  · have e : hhF y ξ = 0 := dite_eq_right h
    rw [e]
    exact zero_le _

/-! ### `E` の上限関数 -/

open Classical in
/-- `sup (E ∩ y)`（`F ξ = if E ξ then ξ else 0` の `y` 未満での上限） -/
def gEF (E : Ordinal.{u} → Prop) (y : Ordinal.{u}) : Ordinal.{u} :=
  supLt y (fun ξ => if E ξ then ξ else 0)

theorem gEF_le (E : Ordinal.{u} → Prop) (y : Ordinal.{u}) : gEF E y ≤ y := by
  classical
  apply (supLt_le_iff y _ y).mpr
  intro ξ hξ
  by_cases h : E ξ
  · rw [ite_eq_left h]; exact Or.inl hξ
  · rw [ite_eq_right h]; exact zero_le _

theorem le_gEF {E : Ordinal.{u} → Prop} {ε y : Ordinal.{u}} (hE : E ε) (hεy : ε < y) :
    ε ≤ gEF E y := by
  classical
  have := le_supLt y (fun ξ => if E ξ then ξ else 0) hεy
  rw [ite_eq_left hE] at this
  exact this

theorem gEF_lt {κ : Ordinal.{u}} {E : Ordinal.{u} → Prop} (hE : ClosedBelow κ E)
    {y : Ordinal.{u}} (hyκ : y < κ) (hy0 : 0 < y) (hnE : ¬ E y) : gEF E y < y := by
  classical
  rcases zero_or_succ_or_limit y with h0 | ⟨z, hz⟩ | hlim
  · rw [h0] at hy0; exact absurd hy0 (lt_irrefl 0)
  · have hz' : gEF E y ≤ z := by
      apply (supLt_le_iff y _ z).mpr
      intro ξ hξ
      have hξz : ξ ≤ z := le_of_lt_succ (by rw [← hz]; exact hξ)
      by_cases h : E ξ
      · rw [ite_eq_left h]; exact hξz
      · rw [ite_eq_right h]; exact zero_le _
    exact lt_of_le_of_lt hz' (by rw [hz]; exact lt_succ_self z)
  · have hnlp : ¬ IsLimitPoint E y := fun hlp => hnE (hE y hyκ hlp)
    have hex : ∃ η, η < y ∧ ∀ β, E β → η < β → ¬ β < y := by
      apply Classical.byContradiction
      intro hno
      apply hnlp
      refine ⟨hy0, ?_⟩
      intro η hη
      apply Classical.byContradiction
      intro hn
      apply hno
      refine ⟨η, hη, ?_⟩
      intro β hβ hηβ hβy
      exact hn ⟨β, hβ, hηβ, hβy⟩
    obtain ⟨η, hηy, hη⟩ := hex
    have hle : gEF E y ≤ η := by
      apply (supLt_le_iff y _ η).mpr
      intro ξ hξ
      by_cases h : E ξ
      · rw [ite_eq_left h]
        apply le_of_not_lt
        intro hlt
        exact hη ξ h hlt hξ
      · rw [ite_eq_right h]; exact zero_le _
    exact lt_of_le_of_lt hle hηy

/-! ### 反射しない点のデータ -/

open Classical in
/-- `0` か `1` -/
def indO (p : Prop) : Ordinal.{u} := if p then succ 0 else 0

theorem zero_lt_indO {p : Prop} : (0 : Ordinal.{u}) < indO p ↔ p := by
  classical
  unfold indO
  by_cases h : p
  · rw [ite_eq_left h]; exact ⟨fun _ => h, fun _ => lt_succ_self 0⟩
  · rw [ite_eq_right h]; exact ⟨fun h0 => absurd h0 (lt_irrefl 0), fun hp => absurd hp h⟩

theorem indO_cases (p : Prop) : indO.{u} p = succ 0 ∨ indO p = 0 := by
  classical
  unfold indO
  by_cases h : p
  · exact Or.inl (ite_eq_left h)
  · exact Or.inr (ite_eq_right h)

variable (κ : Ordinal.{u}) (E : Ordinal.{u} → Prop) (S : Ordinal.{u} → Ordinal.{u} → Prop)

/-- 反射しない点：`E` に属し、正則で、`κ` 未満で、ある `S c` が定常でない -/
def BadAt (y : Ordinal.{u}) : Prop :=
  E y ∧ R y ∧ y < κ ∧ ¬ (∀ c, c < y → Stationary y (S c))

variable {κ E S}

theorem BadAt.data {y : Ordinal.{u}} (h : BadAt κ E S y) :
    ∃ c, c < y ∧ ∃ X, Club y X ∧ ∀ ξ, ξ < y → X ξ → ¬ S c ξ := by
  have h4 := h.2.2.2
  apply Classical.byContradiction
  intro hno
  apply h4
  intro c hc X hX
  apply Classical.byContradiction
  intro hn
  exact hno ⟨c, hc, X, hX, fun ξ hξ hXξ hSξ => hn ⟨ξ, hξ, hXξ, hSξ⟩⟩

variable (κ E S)

open Classical in
/-- 反射しない点 `y` での、定常でない `S c` の添字 `c` -/
def cwF (y : Ordinal.{u}) : Ordinal.{u} :=
  if h : BadAt κ E S y then Classical.choose h.data else 0

open Classical in
/-- 反射しない点 `y` での、`S (cwF y)` と交わらない club -/
def DF (y : Ordinal.{u}) : Ordinal.{u} → Prop :=
  if h : BadAt κ E S y then Classical.choose (Classical.choose_spec h.data).2 else fun _ => False

variable {κ E S}

theorem BadAt.spec {y : Ordinal.{u}} (h : BadAt κ E S y) :
    cwF κ E S y < y ∧ Club y (DF κ E S y) ∧
      ∀ ξ, ξ < y → DF κ E S y ξ → ¬ S (cwF κ E S y) ξ := by
  have e1 : cwF κ E S y = Classical.choose h.data := dite_eq_left h
  have e2 : DF κ E S y = Classical.choose (Classical.choose_spec h.data).2 := dite_eq_left h
  rw [e1, e2]
  have hs := Classical.choose_spec h.data
  have hs2 := Classical.choose_spec hs.2
  exact ⟨hs.1, hs2.1, hs2.2⟩

theorem cwF_le (y : Ordinal.{u}) : cwF κ E S y ≤ y := by
  by_cases h : BadAt κ E S y
  · exact Or.inl h.spec.1
  · have e : cwF κ E S y = 0 := dite_eq_right h
    rw [e]
    exact zero_le _

variable (κ E S)

open Classical in
/-- `D y` の `η` より大きい元の一つ -/
def nxF (η y : Ordinal.{u}) : Ordinal.{u} :=
  if h : ∃ ξ, ξ < y ∧ DF κ E S y ξ ∧ η < ξ then Classical.choose h else 0

variable {κ E S}

theorem nxF_spec {η y : Ordinal.{u}} (h : ∃ ξ, ξ < y ∧ DF κ E S y ξ ∧ η < ξ) :
    nxF κ E S η y < y ∧ DF κ E S y (nxF κ E S η y) ∧ η < nxF κ E S η y := by
  have e : nxF κ E S η y = Classical.choose h := dite_eq_left h
  rw [e]
  exact Classical.choose_spec h

theorem nxF_le (η y : Ordinal.{u}) : nxF κ E S η y ≤ y := by
  by_cases h : ∃ ξ, ξ < y ∧ DF κ E S y ξ ∧ η < ξ
  · exact Or.inl (nxF_spec h).1
  · have e : nxF κ E S η y = 0 := dite_eq_right h
    rw [e]
    exact zero_le _

/-! ### 生成関数の族 -/

variable (κ E S)

/-- 生成関数：種類 `k`、パラメータ `ξ`、引数 `y` -/
def GG : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u}
  | 0, _, y => gEF E y
  | 1, _, y => indO (E y)
  | 2, _, y => indO (R y)
  | 3, _, y => indO (∀ c, c < y → Stationary y (S c))
  | 4, _, y => dlF y
  | 5, ξ, y => hhF y ξ
  | 6, _, y => cwF κ E S y
  | 7, ξ, y => nxF κ E S ξ y
  | _, _, y => y

variable {κ E S}

theorem GG_le (k : Nat) (ξ y : Ordinal.{u}) : GG κ E S k ξ y ≤ y ∨ GG κ E S k ξ y = succ 0 := by
  match k with
  | 0 => exact Or.inl (gEF_le E y)
  | 1 =>
    rcases indO_cases (E y) with h | h
    · exact Or.inr h
    · exact Or.inl (by show indO (E y) ≤ y; rw [h]; exact zero_le _)
  | 2 =>
    rcases indO_cases (R y) with h | h
    · exact Or.inr h
    · exact Or.inl (by show indO (R y) ≤ y; rw [h]; exact zero_le _)
  | 3 =>
    rcases indO_cases (∀ c, c < y → Stationary y (S c)) with h | h
    · exact Or.inr h
    · exact Or.inl (by show indO (∀ c, c < y → Stationary y (S c)) ≤ y; rw [h]; exact zero_le _)
  | 4 => exact Or.inl (dlF_le y)
  | 5 => exact Or.inl (hhF_le y ξ)
  | 6 => exact Or.inl (cwF_le y)
  | 7 => exact Or.inl (nxF_le ξ y)
  | n + 8 => exact Or.inl (le_refl y)

theorem GG_lt {κ : Ordinal.{u}} (hκ : R κ) (k : Nat) (ξ y : Ordinal.{u}) (hy : y < κ) :
    GG κ E S k ξ y < κ := by
  rcases GG_le (κ := κ) (E := E) (S := S) k ξ y with h | h
  · exact lt_of_le_of_lt h hy
  · rw [h]
    exact lt_trans _ _ _ (ordNat_lt_omega 1 : (succ 0 : Ordinal.{u}) < omega) hκ.1

/-! ### 最小の語 `f₀` の性質 -/

theorem evalW_lt {κ : Ordinal.{u}} (hκ : R κ) {E : Ordinal.{u} → Prop}
    {S : Ordinal.{u} → Ordinal.{u} → Prop} :
    ∀ w x, x < κ → evalW (GG κ E S) w x < κ := by
  intro w
  induction w with
  | nil => intro x hx; exact hx
  | cons g w ih =>
    intro x hx
    obtain ⟨k, ξ⟩ := g
    exact GG_lt hκ k ξ _ (ih x hx)

/-- 収束集合・最小の語などのデータ -/
structure Setup (κ : Ordinal.{u}) (E : Ordinal.{u} → Prop)
    (S : Ordinal.{u} → Ordinal.{u} → Prop) where
  H : Ordinal.{u} → Prop
  hc : Conv κ H
  w : List (Nat × Ordinal.{u})
  hw : Valid κ w
  hNN : NN κ H (evalW (GG κ E S) w)
  hmin : ∀ w', Valid κ w' → NN κ H (evalW (GG κ E S) w') →
    ¬ lessH κ H (evalW (GG κ E S) w') (evalW (GG κ E S) w)
  hdec : ∀ w', Valid κ w' → ∀ α, α < κ →
    Ev κ H (fun x => α < evalW (GG κ E S) w' x) ∨
      Ev κ H (fun x => ¬ α < evalW (GG κ E S) w' x)

namespace Setup

variable (T : Setup κ E S)

include T

/-- 最小の語が表す関数 -/
def f (x : Ordinal.{u}) : Ordinal.{u} := evalW (GG κ E S) T.w x

theorem pos : (0 : Ordinal.{u}) < κ := T.hc.reg.2.1.1

theorem fgt {α : Ordinal.{u}} (hα : α < κ) : Ev κ T.H (fun x => α < T.f x) := T.hNN α hα

theorem flt : Ev κ T.H (fun x => T.f x < κ) :=
  ⟨0, T.pos, fun x hx _ => evalW_lt T.hc.reg T.w x (T.hc.sub x hx)⟩

/-- 生成関数を `f` に合成した関数が `f` より小さいなら、最終的に定数 -/
theorem const (k : Nat) (ξ : Ordinal.{u}) (hξ : ξ < κ)
    (h : Ev κ T.H (fun x => GG κ E S k ξ (T.f x) < T.f x)) :
    ∃ γ, γ < κ ∧ Ev κ T.H (fun x => GG κ E S k ξ (T.f x) = γ) := by
  have hv : Valid κ ((k, ξ) :: T.w) := Valid.cons hξ T.hw
  apply eventually_const T.hc (g := evalW (GG κ E S) ((k, ξ) :: T.w))
  · intro hn
    exact T.hmin _ hv hn h
  · exact T.hdec _ hv

/-- 指示関数の生成関数について、`p (f x)` は最終的に決定される -/
theorem dec_ind (k : Nat) (ξ : Ordinal.{u}) (hξ : ξ < κ) (p : Ordinal.{u} → Prop)
    (hk : ∀ y, GG κ E S k ξ y = indO (p y)) :
    Ev κ T.H (fun x => p (T.f x)) ∨ Ev κ T.H (fun x => ¬ p (T.f x)) := by
  have hv : Valid κ ((k, ξ) :: T.w) := Valid.cons hξ T.hw
  rcases T.hdec _ hv 0 T.pos with h | h
  · left
    refine Ev.mono (fun x hx => ?_) h
    have h0 : (0 : Ordinal.{u}) < indO (p (T.f x)) := by
      rw [← hk]
      exact hx
    exact zero_lt_indO.mp h0
  · right
    refine Ev.mono (fun x hx hp => hx ?_) h
    show (0 : Ordinal.{u}) < GG κ E S k ξ (T.f x)
    rw [hk]
    exact zero_lt_indO.mpr hp

/-- (A) `f(x) ∈ E` が最終的に成り立つ -/
theorem fE (hE : Club κ E) : Ev κ T.H (fun x => E (T.f x)) := by
  rcases T.dec_ind 1 0 T.pos E (fun y => rfl) with h | h
  · exact h
  · exfalso
    have hreg : Ev κ T.H (fun x => GG κ E S 0 0 (T.f x) < T.f x) := by
      refine Ev.mono ?_ (h.and ((T.fgt T.pos).and T.flt))
      rintro x ⟨hnE, h0, hκ'⟩
      exact gEF_lt hE.2 hκ' h0 hnE
    obtain ⟨γ, hγκ, hγ⟩ := T.const 0 0 T.pos hreg
    obtain ⟨ε, hεE, hγε, hεκ⟩ := hE.1 γ hγκ
    obtain ⟨x, _, _, _, hx1, hx2⟩ := Ev.exists_pt T.hc (hγ.and (T.fgt hεκ)) T.pos
    have h1 : ε ≤ gEF E (T.f x) := le_gEF hεE hx2
    have hx1' : gEF E (T.f x) = γ := hx1
    rw [hx1'] at h1
    exact lt_irrefl _ (lt_of_lt_of_le hγε h1)

/-- (B) `f(x)` は最終的に正則 -/
theorem fR : Ev κ T.H (fun x => R (T.f x)) := by
  rcases T.dec_ind 2 0 T.pos R (fun y => rfl) with h | h
  · exact h
  · exfalso
    have hω : Ev κ T.H (fun x => omega < T.f x) := T.fgt T.hc.reg.1
    have hNR : Ev κ T.H (fun x => NRp (T.f x)) :=
      Ev.mono (fun x hx => ⟨hx.2, hx.1⟩) (h.and hω)
    have h1 : Ev κ T.H (fun x => GG κ E S 4 0 (T.f x) < T.f x) :=
      Ev.mono (fun x hx => (nr_spec hx).1) hNR
    obtain ⟨γ, hγκ, hγ⟩ := T.const 4 0 T.pos h1
    have h3 : ∀ ξ, ξ < γ → ∃ β, β < κ ∧ Ev κ T.H (fun x => GG κ E S 5 ξ (T.f x) = β) := by
      intro ξ hξ
      have hξκ : ξ < κ := lt_trans _ _ _ hξ hγκ
      apply T.const 5 ξ hξκ
      refine Ev.mono ?_ (hNR.and hγ)
      rintro x ⟨hx, hdl⟩
      have hdl' : dlF (T.f x) = γ := hdl
      exact (nr_spec hx).2.1 ξ (by rw [hdl']; exact hξ)
    classical
    let β' : Ordinal.{u} → Ordinal.{u} := fun ξ =>
      if h : ξ < γ then Classical.choose (h3 ξ h) else 0
    have hβ' : ∀ ξ, ξ < γ → β' ξ < κ ∧ Ev κ T.H (fun x => GG κ E S 5 ξ (T.f x) = β' ξ) := by
      intro ξ hξ
      have e : β' ξ = Classical.choose (h3 ξ hξ) := dite_eq_left hξ
      rw [e]
      exact Classical.choose_spec (h3 ξ hξ)
    have hsupκ : supLt γ β' < κ := T.hc.reg.2.supLt_lt hγκ (fun ξ hξ => (hβ' ξ hξ).1)
    have hall := Ev.all T.hc.reg hγκ (Q := fun ξ x => GG κ E S 5 ξ (T.f x) = β' ξ)
      (fun ξ hξ => (hβ' ξ hξ).2)
    have hsucc : succ (supLt γ β') < κ := T.hc.reg.2.1.succ_lt hsupκ
    obtain ⟨x, _, _, _, ⟨⟨hNRx, hdlx⟩, hallx⟩, hgtx⟩ :=
      Ev.exists_pt T.hc (((hNR.and hγ).and hall).and (T.fgt hsucc)) T.pos
    have hdl' : dlF (T.f x) = γ := hdlx
    have hle : succ (supLt γ β') ≤ supLt γ β' := by
      obtain ⟨ξ, hξ, hηξ⟩ := (nr_spec hNRx).2.2 _ hgtx
      rw [hdl'] at hξ
      have e : hhF (T.f x) ξ = β' ξ := hallx ξ hξ
      rw [e] at hηξ
      exact le_trans hηξ (le_supLt γ β' hξ)
    exact lt_irrefl _ (lt_of_lt_of_le (lt_succ_self _) hle)

/-- (C) `f(x)` は最終的にすべての `S c`（`c < f(x)`）を定常に保つ -/
theorem fRefl (hE : Club κ E) (hS : ∀ c, c < κ → Stationary κ (S c)) :
    Ev κ T.H (fun x => ∀ c, c < T.f x → Stationary (T.f x) (S c)) := by
  rcases T.dec_ind 3 0 T.pos (fun y => ∀ c, c < y → Stationary y (S c)) (fun y => rfl) with h | h
  · exact h
  · exfalso
    have hBad : Ev κ T.H (fun x => BadAt κ E S (T.f x)) :=
      Ev.mono (fun x hx => ⟨hx.1.1, hx.1.2, hx.2.1, hx.2.2⟩)
        (((T.fE hE).and T.fR).and (T.flt.and h))
    have h1 : Ev κ T.H (fun x => GG κ E S 6 0 (T.f x) < T.f x) :=
      Ev.mono (fun x hx => hx.spec.1) hBad
    obtain ⟨c₀, hc₀κ, hc₀⟩ := T.const 6 0 T.pos h1
    have hnx : ∀ η, η < κ → ∃ ξ, ξ < κ ∧ Ev κ T.H (fun x => GG κ E S 7 η (T.f x) = ξ) := by
      intro η hη
      have h2 : Ev κ T.H (fun x => GG κ E S 7 η (T.f x) < T.f x) := by
        refine Ev.mono ?_ (hBad.and (T.fgt hη))
        rintro x ⟨hb, hηx⟩
        obtain ⟨ξ, hξ1, hξ2, hξ3⟩ := hb.spec.2.1.1 η hηx
        exact (nxF_spec ⟨ξ, hξ3, hξ1, hξ2⟩).1
      exact T.const 7 η hη h2
    let Ds : Ordinal.{u} → Prop := fun ξ => ξ < κ ∧ Ev κ T.H (fun x => DF κ E S (T.f x) ξ)
    have hClub : Club κ Ds := by
      constructor
      · intro η hη
        obtain ⟨ξ₀, hξ₀κ, hξ₀⟩ := hnx η hη
        have hspec : Ev κ T.H (fun x => DF κ E S (T.f x) ξ₀ ∧ η < ξ₀) := by
          refine Ev.mono ?_ ((hBad.and (T.fgt hη)).and hξ₀)
          rintro x ⟨⟨hb, hηx⟩, hnx'⟩
          obtain ⟨ξ, hξ1, hξ2, hξ3⟩ := hb.spec.2.1.1 η hηx
          have hs := nxF_spec (κ := κ) (E := E) (S := S) ⟨ξ, hξ3, hξ1, hξ2⟩
          have hnx'' : nxF κ E S η (T.f x) = ξ₀ := hnx'
          rw [hnx''] at hs
          exact ⟨hs.2.1, hs.2.2⟩
        obtain ⟨x, _, _, _, hx⟩ := Ev.exists_pt T.hc hspec T.pos
        exact ⟨ξ₀, ⟨hξ₀κ, Ev.mono (fun x hx => hx.1) hspec⟩, hx.2, hξ₀κ⟩
      · intro l hlκ hlp
        refine ⟨hlκ, ?_⟩
        classical
        let ξf : Ordinal.{u} → Ordinal.{u} := fun η =>
          if h : η < l then Classical.choose (hlp.2 η h) else 0
        have hξf : ∀ η, η < l → Ds (ξf η) ∧ η < ξf η ∧ ξf η < l := by
          intro η hη
          have e : ξf η = Classical.choose (hlp.2 η hη) := dite_eq_left hη
          rw [e]
          exact Classical.choose_spec (hlp.2 η hη)
        have hall := Ev.all T.hc.reg hlκ (Q := fun η x => DF κ E S (T.f x) (ξf η))
          (fun η hη => (hξf η hη).1.2)
        refine Ev.mono ?_ ((hBad.and (T.fgt hlκ)).and hall)
        rintro x ⟨⟨hb, hlx⟩, hallx⟩
        exact hb.spec.2.1.2 l hlx
          ⟨hlp.1, fun η hη => ⟨ξf η, hallx η hη, (hξf η hη).2.1, (hξf η hη).2.2⟩⟩
    obtain ⟨ξ, hξκ, hξD, hξS⟩ := hS c₀ hc₀κ Ds hClub
    obtain ⟨x, _, _, _, ⟨hb, hcw⟩, hD, hxξ⟩ :=
      Ev.exists_pt T.hc ((hBad.and hc₀).and (hξD.2.and (T.fgt hξκ))) T.pos
    have hcw' : cwF κ E S (T.f x) = c₀ := hcw
    exact hb.spec.2.2 ξ hxξ hD (by rw [hcw']; exact hξS)

end Setup

/-- 反射補題（GRL） -/
theorem grl {κ : Ordinal.{u}} (hκ : R κ) (hpart : PartitionProp κ)
    {E : Ordinal.{u} → Prop} (hE : Club κ E)
    {S : Ordinal.{u} → Ordinal.{u} → Prop} (hS : ∀ c, c < κ → Stationary κ (S c)) :
    ∃ τ, τ < κ ∧ E τ ∧ R τ ∧ ∀ c, c < τ → Stationary τ (S c) := by
  obtain ⟨H, hc, hdec⟩ := exists_H_words hκ hpart (GG κ E S)
  obtain ⟨w, hw, hNN, hmin⟩ := exists_minimal_word hc (GG κ E S)
  let T : Setup κ E S := ⟨H, hc, w, hw, hNN, hmin, hdec⟩
  obtain ⟨x, _, _, _, ⟨hxE, hxR⟩, hxS, hxκ⟩ :=
    Ev.exists_pt hc (((T.fE hE).and T.fR).and ((T.fRefl hE hS).and T.flt)) T.pos
  exact ⟨T.f x, hxκ, hxE, hxR, hxS⟩

end
end OCF.Rathjen
