import Compact.OCFRathjen.Setting

/-! Hessenberg の定理：無限順序数 `β` の台集合 `X` について `X × X → X` の単射がある。

`weaklyCompactAt_inacc_of_pairing`（後続の正則基数の存在）に必要な
`pairing_of_omega_le` を、公理を使わずに示す。

* `ω` では `(a, b) ↦ 2^a (2b+1)`。
* `β > ω` では、`β` が小さい無限順序数 `γ` に単射で入るなら `γ` の対関数を使い、
  そうでなければ（`β` は基数）`max` と、各 `max` の殻の中の鍵で定まる Gödel 順序の
  順序型を使う。殻は `ν < β` に単射で入るので、Hartogs 数 `≤ β` から
  各始切片の順序型は `β` 未満。 -/

namespace OCF.Rathjen

universe u

open Ordinal

set_option linter.unusedSectionVars false

noncomputable section

/-! ### 自然数の対関数 -/

def natPair (a b : Nat) : Nat := 2 ^ a * (2 * b + 1)

theorem two_pow_succ_mul (k c : Nat) : 2 ^ (k + 1) * c = 2 * (2 ^ k * c) := by
  rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]

theorem natPair_inj {a b a' b' : Nat} (h : natPair a b = natPair a' b') : a = a' ∧ b = b' := by
  induction a generalizing a' with
  | zero =>
    cases a' with
    | zero =>
      simp only [natPair, Nat.pow_zero, Nat.one_mul] at h
      omega
    | succ a' =>
      exfalso
      simp only [natPair, Nat.pow_zero, Nat.one_mul] at h
      rw [two_pow_succ_mul] at h
      generalize 2 ^ a' * (2 * b' + 1) = x at h
      omega
  | succ a ih =>
    cases a' with
    | zero =>
      exfalso
      simp only [natPair, Nat.pow_zero, Nat.one_mul] at h
      rw [two_pow_succ_mul] at h
      generalize 2 ^ a * (2 * b + 1) = x at h
      omega
    | succ a' =>
      simp only [natPair] at h
      rw [two_pow_succ_mul, two_pow_succ_mul] at h
      have h2 : natPair a b = natPair a' b' := by
        simp only [natPair]
        omega
      have := ih h2
      omega

/-! ### 順序数レベルの単射な対関数 -/

/-- `β` 未満の順序数の対から `β` 未満の順序数への単射。 -/
def PairInj (β : Ordinal.{u}) : Prop :=
  ∃ g : Ordinal.{u} → Ordinal.{u} → Ordinal.{u},
    (∀ a b, a < β → b < β → g a b < β) ∧
    ∀ a b a' b', a < β → b < β → a' < β → b' < β → g a b = g a' b' → a = a' ∧ b = b'

theorem pointBelow_inj {κ x y : Ordinal.{u}} {hx : x < κ} {hy : y < κ}
    (h : pointBelow κ x hx = pointBelow κ y hy) : x = y :=
  (pointBelow_spec hx).trans
    ((congrArg (fun z => type ((representative κ).below z)) h).trans (pointBelow_spec hy).symm)

theorem below_type_injective (A : WellOrder.{u}) {a b : A.Carrier}
    (h : type (A.below a) = type (A.below b)) : a = b := by
  cases iso_of_type_eq h with
  | intro e => exact WellOrder.eq_of_below_iso A a b e

theorem type_lt_hartogs_of_injective {X : Type u} (A : WellOrder.{u}) (f : A.Carrier → X)
    (hf : ∀ a b, f a = f b → a = b) : type A < hartogs X := by
  have h := subOrder_type_lt_hartogs (SubOrder.image A f hf)
  rw [SubOrder.type_image_eq] at h
  exact h

/-- 台集合の間の単射を、順序数レベルの単射に読み替える。 -/
theorem ordInj_of_carrierInj {β γ : Ordinal.{u}}
    (f : (representative β).Carrier → (representative γ).Carrier)
    (hf : ∀ x y, f x = f y → x = y) :
    ∃ e : Ordinal.{u} → Ordinal.{u}, (∀ a, a < β → e a < γ) ∧
      ∀ a b, a < β → b < β → e a = e b → a = b := by
  classical
  refine ⟨fun a => if ha : a < β then
    type ((representative γ).below (f (pointBelow β a ha))) else 0, ?_, ?_⟩
  · intro a ha
    dsimp only
    rw [dite_eq_left ha]
    exact initial_lt γ _
  · intro a b ha hb h
    dsimp only at h
    rw [dite_eq_left ha, dite_eq_left hb] at h
    exact pointBelow_inj (hf _ _ (initial_injective γ _ _ h))

theorem pairInj_of_pairing {β : Ordinal.{u}}
    (pair : (representative β).Carrier × (representative β).Carrier → (representative β).Carrier)
    (hpair : ∀ a b, pair a = pair b → a = b) : PairInj β := by
  classical
  refine ⟨fun a b => if ha : a < β then (if hb : b < β then
      type ((representative β).below (pair (pointBelow β a ha, pointBelow β b hb))) else 0)
      else 0, ?_, ?_⟩
  · intro a b ha hb
    dsimp only
    rw [dite_eq_left ha, dite_eq_left hb]
    exact initial_lt β _
  · intro a b a' b' ha hb ha' hb' h
    dsimp only at h
    rw [dite_eq_left ha, dite_eq_left hb, dite_eq_left ha', dite_eq_left hb'] at h
    have h2 := hpair _ _ (initial_injective β _ _ h)
    exact ⟨pointBelow_inj (hx := ha) (hy := ha') (congrArg Prod.fst h2),
      pointBelow_inj (hx := hb) (hy := hb') (congrArg Prod.snd h2)⟩

theorem pairing_of_pairInj {β : Ordinal.{u}} (h : PairInj β) :
    ∃ pair : (representative β).Carrier × (representative β).Carrier → (representative β).Carrier,
      ∀ a b, pair a = pair b → a = b := by
  obtain ⟨g, hgβ, hginj⟩ := h
  refine ⟨fun p => pointBelow β (g (type ((representative β).below p.1))
      (type ((representative β).below p.2)))
      (hgβ _ _ (initial_lt β p.1) (initial_lt β p.2)), ?_⟩
  intro p q hpq
  have h1 := hginj _ _ _ _ (initial_lt β p.1) (initial_lt β p.2) (initial_lt β q.1)
    (initial_lt β q.2) (pointBelow_inj hpq)
  exact Prod.ext (initial_injective β _ _ h1.1) (initial_injective β _ _ h1.2)

theorem eq_of_natOf_eq {x y : Ordinal.{u}} (hx : x < omega) (hy : y < omega)
    (h : natOf x = natOf y) : x = y := by
  obtain ⟨n, rfl⟩ := (lt_omega_iff x).mp hx
  obtain ⟨k, rfl⟩ := (lt_omega_iff y).mp hy
  rw [natOf_ordNat, natOf_ordNat] at h
  rw [h]

theorem pairInj_omega : PairInj (omega : Ordinal.{u}) := by
  refine ⟨fun a b => ordNat (natPair (natOf a) (natOf b)), ?_, ?_⟩
  · intro a b _ _
    exact ordNat_lt_omega _
  · intro a b a' b' ha hb ha' hb' h
    have h2 := natPair_inj (ordNat_injective h)
    exact ⟨eq_of_natOf_eq ha ha' h2.1, eq_of_natOf_eq hb hb' h2.2⟩

/-! ### 辞書式の整列順序 -/

/-- 単射な鍵 `p ↦ (m p, h p)` から辞書式に定まる整列順序。 -/
def lexKeyOrder {X : Type u} (m h : X → Ordinal.{u})
    (hinj : ∀ p q, m p = m q → h p = h q → p = q) : WellOrder.{u} where
  Carrier := X
  lt p q := m p < m q ∨ (m p = m q ∧ h p < h q)
  irrefl p := by
    rintro (hlt | ⟨_, hlt⟩)
    · exact lt_irrefl _ hlt
    · exact lt_irrefl _ hlt
  trans p q r hpq hqr := by
    rcases hpq with hpq | ⟨hm1, hh1⟩
    · rcases hqr with hqr | ⟨hm2, _⟩
      · exact Or.inl (lt_trans _ _ _ hpq hqr)
      · exact Or.inl (by rw [← hm2]; exact hpq)
    · rcases hqr with hqr | ⟨hm2, hh2⟩
      · exact Or.inl (by rw [hm1]; exact hqr)
      · exact Or.inr ⟨hm1.trans hm2, lt_trans _ _ _ hh1 hh2⟩
  total p q := by
    rcases lt_total (m p) (m q) with h1 | h1 | h1
    · exact Or.inl (Or.inl h1)
    · rcases lt_total (h p) (h q) with h2 | h2 | h2
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · exact Or.inr (Or.inl (hinj p q h1 h2))
      · exact Or.inr (Or.inr (Or.inr ⟨h1.symm, h2⟩))
    · exact Or.inr (Or.inr (Or.inl h1))
  wellFounded := by
    have key : ∀ μ η, ∀ p : X, m p = μ → h p = η →
        Acc (fun p q : X => m p < m q ∨ (m p = m q ∧ h p < h q)) p := by
      intro μ
      induction μ using lt_wellFounded.induction with
      | h μ ihμ =>
        intro η
        induction η using lt_wellFounded.induction with
        | h η ihη =>
          intro p hpμ hpη
          refine Acc.intro p (fun q hq => ?_)
          rcases hq with hq | ⟨hqm, hqh⟩
          · exact ihμ (m q) (by rw [← hpμ]; exact hq) (h q) q rfl rfl
          · exact ihη (h q) (by rw [← hpη]; exact hqh) q (hqm.trans hpμ) rfl
    exact ⟨fun p => key (m p) (h p) p rfl rfl⟩

/-! ### 基数の場合（Gödel 順序） -/

/-- Hessenberg の定理の核：`β` が `ω` より大きく、より小さい無限順序数への単射を持たないなら、
`β` 未満の対から `β` 未満への単射がある（`ν < β` の無限順序数 `ν` では対関数があるとする）。 -/
theorem pairInj_of_card {β : Ordinal.{u}} (hωβ : omega < β) (hlim : IsLimit β)
    (hIH : ∀ ν, omega ≤ ν → ν < β → PairInj ν)
    (hcard : ∀ ν, omega ≤ ν → ν < β → ¬ ∃ e : Ordinal.{u} → Ordinal.{u},
      (∀ a, a < β → e a < ν) ∧ ∀ a b, a < β → b < β → e a = e b → a = b) :
    PairInj β := by
  classical
  let G0 : Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Ordinal.{u} := fun ν =>
    if h : omega ≤ ν ∧ ν < β then Classical.choose (hIH ν h.1 h.2) else fun _ _ => 0
  have hG0 : ∀ ν, omega ≤ ν → ν < β →
      (∀ a b, a < ν → b < ν → G0 ν a b < ν) ∧
      ∀ a b a' b', a < ν → b < ν → a' < ν → b' < ν →
        G0 ν a b = G0 ν a' b' → a = a' ∧ b = b' := by
    intro ν h1 h2
    have e : G0 ν = Classical.choose (hIH ν h1 h2) := dite_eq_left ⟨h1, h2⟩
    rw [e]
    exact Classical.choose_spec (hIH ν h1 h2)
  let P : Type u := (representative β).Carrier × (representative β).Carrier
  let rk : (representative β).Carrier → Ordinal.{u} := fun x => type ((representative β).below x)
  let mx : P → Ordinal.{u} := fun p => omax (rk p.1) (rk p.2)
  let nu : Ordinal.{u} → Ordinal.{u} := fun m => omax (succ m) omega
  let hk : P → Ordinal.{u} := fun p => G0 (nu (mx p)) (rk p.1) (rk p.2)
  have hrkβ : ∀ x, rk x < β := fun x => initial_lt β x
  have hrk_inj : ∀ x y, rk x = rk y → x = y := fun x y h => initial_injective β x y h
  have hmx_lt : ∀ p, mx p < β := fun p => omax_lt (hrkβ p.1) (hrkβ p.2)
  have hnu_ge : ∀ m, omega ≤ nu m := fun m => le_omax_right _ _
  have hnu_lt : ∀ m, m < β → nu m < β := fun m hm => omax_lt (hlim.succ_lt hm) hωβ
  have hnu_gt : ∀ m, m < nu m := fun m => lt_of_lt_of_le (lt_succ_self m) (le_omax_left _ _)
  have hrk1 : ∀ p : P, rk p.1 < nu (mx p) := fun p =>
    lt_of_le_of_lt (le_omax_left _ _) (hnu_gt _)
  have hrk2 : ∀ p : P, rk p.2 < nu (mx p) := fun p =>
    lt_of_le_of_lt (le_omax_right _ _) (hnu_gt _)
  have hinj : ∀ p q : P, mx p = mx q → hk p = hk q → p = q := by
    intro p q hm hh
    have hnuq : nu (mx q) = nu (mx p) := by rw [hm]
    have hq1 : rk q.1 < nu (mx p) := by rw [← hnuq]; exact hrk1 q
    have hq2 : rk q.2 < nu (mx p) := by rw [← hnuq]; exact hrk2 q
    have hkq : hk q = G0 (nu (mx p)) (rk q.1) (rk q.2) := by
      show G0 (nu (mx q)) (rk q.1) (rk q.2) = _
      rw [hnuq]
    have hh' : G0 (nu (mx p)) (rk p.1) (rk p.2) = G0 (nu (mx p)) (rk q.1) (rk q.2) :=
      hh.trans hkq
    have hspec := hG0 (nu (mx p)) (hnu_ge _) (hnu_lt _ (hmx_lt p))
    have h2 := hspec.2 _ _ _ _ (hrk1 p) (hrk2 p) hq1 hq2 hh'
    exact Prod.ext (hrk_inj _ _ h2.1) (hrk_inj _ _ h2.2)
  let G : WellOrder.{u} := lexKeyOrder mx hk hinj
  have hbound : ∀ p : P, type (G.below p) < β := by
    intro p
    have hν1 : omega ≤ nu (mx p) := hnu_ge _
    have hν2 : nu (mx p) < β := hnu_lt _ (hmx_lt p)
    have hspec := hG0 (nu (mx p)) hν1 hν2
    have hlow : ∀ q : (G.below p).Carrier,
        rk q.1.1 < nu (mx p) ∧ rk q.1.2 < nu (mx p) := by
      intro q
      have hq : mx q.1 ≤ mx p := by
        rcases q.2 with h | ⟨h, _⟩
        · exact le_of_lt h
        · exact Or.inr h
      exact ⟨lt_of_le_of_lt (le_trans (le_omax_left _ _) hq) (hnu_gt _),
        lt_of_le_of_lt (le_trans (le_omax_right _ _) hq) (hnu_gt _)⟩
    let F : (G.below p).Carrier → (representative (nu (mx p))).Carrier := fun q =>
      pointBelow (nu (mx p)) (G0 (nu (mx p)) (rk q.1.1) (rk q.1.2))
        (hspec.1 _ _ (hlow q).1 (hlow q).2)
    have hF : ∀ q q', F q = F q' → q = q' := by
      intro q q' h
      have h1 := pointBelow_inj h
      have h2 := hspec.2 _ _ _ _ (hlow q).1 (hlow q).2 (hlow q').1 (hlow q').2 h1
      exact Subtype.ext (Prod.ext (hrk_inj _ _ h2.1) (hrk_inj _ _ h2.2))
    have h1 : type (G.below p) < hartogs (representative (nu (mx p))).Carrier :=
      type_lt_hartogs_of_injective _ F hF
    have h2 : hartogs (representative (nu (mx p))).Carrier ≤ β := by
      apply le_of_not_lt
      intro hlt
      obtain ⟨f, hf⟩ :=
        (lt_hartogs_iff_injective (representative (nu (mx p))).Carrier β).mp hlt
      exact hcard _ hν1 hν2 (ordInj_of_carrierInj f hf)
    exact lt_of_lt_of_le h1 h2
  apply pairInj_of_pairing (fun p : P => pointBelow β (type (G.below p)) (hbound p))
  intro p q hpq
  exact below_type_injective G (pointBelow_inj hpq)

/-! ### Hessenberg の定理 -/

/-- 無限順序数 `β` について、`β` 未満の順序数の対から `β` 未満への単射がある。 -/
theorem pairInj_of_omega_le : ∀ β : Ordinal.{u}, omega ≤ β → PairInj β := by
  intro β
  induction β using lt_wellFounded.induction with
  | h β ih =>
    intro hωβ
    rcases hωβ with hlt | heq
    · by_cases hsmall : ∃ γ, omega ≤ γ ∧ γ < β ∧ ∃ e : Ordinal.{u} → Ordinal.{u},
          (∀ a, a < β → e a < γ) ∧ ∀ a b, a < β → b < β → e a = e b → a = b
      · obtain ⟨γ, hγω, hγβ, e, he1, he2⟩ := hsmall
        obtain ⟨g, hg1, hg2⟩ := ih γ hγβ hγω
        refine ⟨fun a b => g (e a) (e b), ?_, ?_⟩
        · intro a b ha hb
          exact lt_trans _ _ _ (hg1 _ _ (he1 a ha) (he1 b hb)) hγβ
        · intro a b a' b' ha hb ha' hb' h
          have h2 := hg2 _ _ _ _ (he1 a ha) (he1 b hb) (he1 a' ha') (he1 b' hb') h
          exact ⟨he2 a a' ha ha' h2.1, he2 b b' hb hb' h2.2⟩
      · have hlim : IsLimit β := by
          rcases zero_or_succ_or_limit β with h0 | ⟨δ, hδ⟩ | hl
          · rw [h0] at hlt
            exact absurd hlt (not_lt_zero _)
          · exfalso
            subst hδ
            have hωδ : omega ≤ δ := (lt_succ_iff_le omega δ).mp hlt
            obtain ⟨f, hf⟩ := exists_injective_succ_into_of_omega_le hωδ
            exact hsmall ⟨δ, hωδ, lt_succ_self δ, ordInj_of_carrierInj f hf⟩
          · exact hl
        exact pairInj_of_card hlt hlim (fun ν hν hνβ => ih ν hνβ hν)
          (fun ν hν hνβ hn => hsmall ⟨ν, hν, hνβ, hn⟩)
    · rw [← heq]
      exact pairInj_omega

/-- (A) `β ≥ ω` の台集合上の単射な対関数。 -/
theorem pairing_of_omega_le (β : Ordinal.{u}) (hβ : omega ≤ β) :
    ∃ pair : (representative β).Carrier × (representative β).Carrier →
      (representative β).Carrier, ∀ a b, pair a = pair b → a = b :=
  pairing_of_pairInj (pairInj_of_omega_le β hβ)

/-! ## 分割性 `PartitionProp κ` から取り出す「収束集合」`H`。

`Ev κ H Q`：`H` の十分大きい元で常に `Q` が成り立つ。`H` が非有界なら `Ev` は κ 未満の
個数の合接について閉じたフィルターで、`exists_convergent` は κ 個の性質それぞれについて
`Ev` が決定される `H` を与える（順序付け補題 `PartitionProp.orient` のみを使う）。 -/

/-- `H` の十分大きい元（`κ` 未満の点より先）で常に `Q` -/
def Ev (κ : Ordinal.{u}) (H : Ordinal.{u} → Prop) (Q : Ordinal.{u} → Prop) : Prop :=
  ∃ x₀, x₀ < κ ∧ ∀ x, H x → x₀ < x → Q x

/-- `H` は `κ` 未満の非有界集合で、`κ` は非可算正則 -/
structure Conv (κ : Ordinal.{u}) (H : Ordinal.{u} → Prop) : Prop where
  reg : R κ
  sub : ∀ x, H x → x < κ
  unb : Unbounded κ H

namespace Ev

variable {κ : Ordinal.{u}} {H : Ordinal.{u} → Prop}

theorem mono {Q Q' : Ordinal.{u} → Prop} (h : ∀ x, Q x → Q' x) (hQ : Ev κ H Q) : Ev κ H Q' := by
  cases hQ with
  | intro x₀ hx => exact ⟨x₀, hx.1, fun x hH hlt => h x (hx.2 x hH hlt)⟩

theorem and {Q Q' : Ordinal.{u} → Prop} (h : Ev κ H Q) (h' : Ev κ H Q') :
    Ev κ H (fun x => Q x ∧ Q' x) := by
  cases h with
  | intro a ha =>
    cases h' with
    | intro b hb =>
      refine ⟨omax a b, omax_lt ha.1 hb.1, fun x hH hlt => ⟨?_, ?_⟩⟩
      · exact ha.2 x hH (lt_of_le_of_lt (le_omax_left a b) hlt)
      · exact hb.2 x hH (lt_of_le_of_lt (le_omax_right a b) hlt)

theorem of_all {Q : Ordinal.{u} → Prop} (h0 : 0 < κ) (h : ∀ x, Q x) : Ev κ H Q :=
  ⟨0, h0, fun x _ _ => h x⟩

theorem gt {α : Ordinal.{u}} (hα : α < κ) : Ev κ H (fun x => α < x) :=
  ⟨α, hα, fun _ _ h => h⟩

theorem exists_pt (hc : Conv κ H) {Q : Ordinal.{u} → Prop} (h : Ev κ H Q) {η : Ordinal.{u}}
    (hη : η < κ) : ∃ x, H x ∧ η < x ∧ x < κ ∧ Q x := by
  cases h with
  | intro x₀ hx =>
    cases hc.unb (omax x₀ η) (omax_lt hx.1 hη) with
    | intro ξ hξ =>
      exact ⟨ξ, hξ.1, lt_of_le_of_lt (le_omax_right x₀ η) hξ.2.1, hξ.2.2,
        hx.2 ξ hξ.1 (lt_of_le_of_lt (le_omax_left x₀ η) hξ.2.1)⟩

theorem all (hκ : R κ) {δ : Ordinal.{u}} (hδ : δ < κ) {Q : Ordinal.{u} → Ordinal.{u} → Prop}
    (h : ∀ i, i < δ → Ev κ H (Q i)) : Ev κ H (fun x => ∀ i, i < δ → Q i x) := by
  classical
  let x₀ : Ordinal.{u} → Ordinal.{u} := fun i =>
    if hi : i < δ then Classical.choose (h i hi) else 0
  have hx₀ : ∀ i (hi : i < δ), x₀ i < κ ∧ ∀ x, H x → x₀ i < x → Q i x := by
    intro i hi
    have e : x₀ i = Classical.choose (h i hi) := dite_eq_left hi
    rw [e]
    exact Classical.choose_spec (h i hi)
  refine ⟨supLt δ x₀, hκ.2.supLt_lt hδ (fun i hi => (hx₀ i hi).1), ?_⟩
  intro x hH hlt i hi
  exact (hx₀ i hi).2 x hH (lt_of_le_of_lt (le_supLt δ x₀ hi) hlt)

end Ev

/-! ### 収束集合 -/

/-- 命題の（古典的な）真理値 -/
def bit (p : Prop) : Bool := @decide p (Classical.propDecidable p)

theorem bit_eq_true {p : Prop} : bit p = true ↔ p := by
  unfold bit
  exact @decide_eq_true_iff p (Classical.propDecidable p)

theorem bit_eq_false {p : Prop} : bit p = false ↔ ¬ p := by
  unfold bit
  exact @decide_eq_false_iff_not p (Classical.propDecidable p)

/-- 二値関数の辞書式順序（最初の相違点）と、同じ関数の間では台の順序 -/
def lexX (W : WellOrder.{u}) (a b : (W.Carrier → Bool) × W.Carrier) : Prop :=
  (∃ q, (∀ q', W.lt q' q → a.1 q' = b.1 q') ∧ a.1 q = false ∧ b.1 q = true) ∨
    (a.1 = b.1 ∧ W.lt a.2 b.2)

theorem lexX_total (W : WellOrder.{u}) (a b : (W.Carrier → Bool) × W.Carrier) (hab : a ≠ b) :
    lexX W a b ∨ lexX W b a := by
  classical
  by_cases h : a.1 = b.1
  · have h2 : a.2 ≠ b.2 := fun e => hab (Prod.ext h e)
    rcases W.total a.2 b.2 with hl | he | hr
    · exact Or.inl (Or.inr ⟨h, hl⟩)
    · exact absurd he h2
    · exact Or.inr (Or.inr ⟨h.symm, hr⟩)
  · have hex : ∃ q, a.1 q ≠ b.1 q := by
      apply Classical.byContradiction
      intro hne
      exact h (funext (fun q => Classical.byContradiction (fun hq => hne ⟨q, hq⟩)))
    obtain ⟨q, hq, hmin⟩ := WellOrder.exists_min W (fun q => a.1 q ≠ b.1 q) hex
    have hbefore : ∀ q', W.lt q' q → a.1 q' = b.1 q' :=
      fun q' hq' => Classical.byContradiction (fun hne => hmin q' hq' hne)
    cases ha : a.1 q with
    | false =>
      cases hb : b.1 q with
      | false => exact absurd (ha.trans hb.symm) hq
      | true => exact Or.inl (Or.inl ⟨q, hbefore, ha, hb⟩)
    | true =>
      cases hb : b.1 q with
      | false => exact Or.inr (Or.inl ⟨q, fun q' h' => (hbefore q' h').symm, hb, ha⟩)
      | true => exact absurd (ha.trans hb.symm) hq

theorem lexX_no_dec (W : WellOrder.{u}) {a b : (W.Carrier → Bool) × W.Carrier}
    (hab : lexX W a b) {q₀ : W.Carrier} (hag : ∀ q', W.lt q' q₀ → a.1 q' = b.1 q') :
    ¬ (a.1 q₀ = true ∧ b.1 q₀ = false) := by
  intro hh
  have h1 := hh.1
  have h2 := hh.2
  rcases hab with ⟨q, hq, ha, hb⟩ | ⟨he, _⟩
  · rcases W.total q q₀ with hl | he | hr
    · have := hag q hl
      rw [ha, hb] at this
      exact absurd this (by decide)
    · rw [he, h1] at ha
      exact absurd ha (by decide)
    · have := hq q₀ hr
      rw [h1, h2] at this
      exact absurd this (by decide)
  · rw [he] at h1
    rw [h1] at h2
    exact absurd h2 (by decide)

/-- `PartitionProp κ` から、`κ` 個の性質それぞれが最終的に決定される非有界集合が得られる -/
theorem exists_convergent {κ : Ordinal.{u}} (hκ : R κ) (hpart : PartitionProp κ)
    (P : Ordinal.{u} → Ordinal.{u} → Prop) :
    ∃ H, Conv κ H ∧ ∀ c, c < κ → Ev κ H (P c) ∨ Ev κ H (fun x => ¬ P c x) := by
  classical
  let chi : (representative κ).Carrier → (representative κ).Carrier → Bool := fun p q =>
    bit (P (type ((representative κ).below q)) (type ((representative κ).below p)))
  obtain ⟨H, hHκ, hHu, hor⟩ := hpart.orient (lexX (representative κ)) (lexX_total (representative κ))
    (fun p => (chi p, p)) (fun p p' h => congrArg Prod.snd h)
  refine ⟨H, ⟨hκ, hHκ, hHu⟩, ?_⟩
  have pt_ord : ∀ {x : Ordinal.{u}} (hx : x < κ),
      type ((representative κ).below (pointBelow κ x hx)) = x :=
    fun hx => (pointBelow_spec hx).symm
  have chi_pt : ∀ {x c : Ordinal.{u}} (hx : x < κ) (hc : c < κ),
      chi (pointBelow κ x hx) (pointBelow κ c hc) = bit (P c x) := by
    intro x c hx hc
    show bit (P (type ((representative κ).below (pointBelow κ c hc)))
      (type ((representative κ).below (pointBelow κ x hx)))) = _
    rw [pt_ord hx, pt_ord hc]
  have key : ∀ c, c < κ → ∃ v : Bool, Ev κ H (fun x => bit (P c x) = v) := by
    intro c
    induction c using lt_wellFounded.induction with
    | h c ih =>
      intro hcκ
      let v : Ordinal.{u} → Bool := fun c' =>
        if h : c' < c then Classical.choose (ih c' h (lt_trans _ _ _ h hcκ)) else false
      have hv : ∀ c', c' < c → Ev κ H (fun x => bit (P c' x) = v c') := by
        intro c' h
        have e : v c' = Classical.choose (ih c' h (lt_trans _ _ _ h hcκ)) := dite_eq_left h
        rw [e]
        exact Classical.choose_spec (ih c' h (lt_trans _ _ _ h hcκ))
      obtain ⟨x₀, hx₀κ, hx₀⟩ := Ev.all hκ hcκ hv
      have hag : ∀ x y (hx : H x) (hy : H y), x₀ < x → x₀ < y →
          ∀ q', (representative κ).lt q' (pointBelow κ c hcκ) →
            chi (pointBelow κ x (hHκ x hx)) q' = chi (pointBelow κ y (hHκ y hy)) q' := by
        intro x y hx hy hx0 hy0 q' hq'
        have hc' : type ((representative κ).below q') < c := by
          have h1 := (initial_lt_iff κ q' (pointBelow κ c hcκ)).mpr hq'
          rw [pt_ord hcκ] at h1
          exact h1
        have hc'κ : type ((representative κ).below q') < κ := lt_trans _ _ _ hc' hcκ
        have e : pointBelow κ (type ((representative κ).below q')) hc'κ = q' :=
          initial_injective κ _ _ (pt_ord hc'κ)
        rw [← e, chi_pt (hHκ x hx) hc'κ, chi_pt (hHκ y hy) hc'κ,
          hx₀ x hx hx0 _ hc', hx₀ y hy hy0 _ hc']
      rcases hor with hm | ha
      · have hnd : ∀ x y, H x → H y → x₀ < x → x < y →
            ¬ (bit (P c x) = true ∧ bit (P c y) = false) := by
          intro x y hx hy hx0 hxy hh
          have hxκ := hHκ x hx
          have hyκ := hHκ y hy
          have hlex := hm x y hx hy hxκ hyκ hxy
          apply lexX_no_dec (representative κ) hlex
            (hag x y hx hy hx0 (lt_trans _ _ _ hx0 hxy))
          constructor
          · show chi (pointBelow κ x hxκ) (pointBelow κ c hcκ) = true
            rw [chi_pt hxκ hcκ]
            exact hh.1
          · show chi (pointBelow κ y hyκ) (pointBelow κ c hcκ) = false
            rw [chi_pt hyκ hcκ]
            exact hh.2
        by_cases hex : ∃ x₁, H x₁ ∧ x₀ < x₁ ∧ bit (P c x₁) = true
        · obtain ⟨x₁, hx1, hx10, hx1t⟩ := hex
          refine ⟨true, x₁, hHκ x₁ hx1, ?_⟩
          intro y hy hy1
          match h : bit (P c y) with
          | true => rfl
          | false => exact absurd ⟨hx1t, h⟩ (hnd x₁ y hx1 hy hx10 hy1)
        · refine ⟨false, x₀, hx₀κ, ?_⟩
          intro y hy hy0
          match h : bit (P c y) with
          | false => rfl
          | true => exact absurd ⟨y, hy, hy0, h⟩ hex
      · have hnd : ∀ x y, H x → H y → x₀ < x → x < y →
            ¬ (bit (P c x) = false ∧ bit (P c y) = true) := by
          intro x y hx hy hx0 hxy hh
          have hxκ := hHκ x hx
          have hyκ := hHκ y hy
          have hlex := ha x y hx hy hxκ hyκ hxy
          apply lexX_no_dec (representative κ) hlex
            (fun q' hq' => (hag x y hx hy hx0 (lt_trans _ _ _ hx0 hxy) q' hq').symm)
          constructor
          · show chi (pointBelow κ y hyκ) (pointBelow κ c hcκ) = true
            rw [chi_pt hyκ hcκ]
            exact hh.2
          · show chi (pointBelow κ x hxκ) (pointBelow κ c hcκ) = false
            rw [chi_pt hxκ hcκ]
            exact hh.1
        by_cases hex : ∃ x₁, H x₁ ∧ x₀ < x₁ ∧ bit (P c x₁) = false
        · obtain ⟨x₁, hx1, hx10, hx1t⟩ := hex
          refine ⟨false, x₁, hHκ x₁ hx1, ?_⟩
          intro y hy hy1
          match h : bit (P c y) with
          | false => rfl
          | true => exact absurd ⟨hx1t, h⟩ (hnd x₁ y hx1 hy hx10 hy1)
        · refine ⟨true, x₀, hx₀κ, ?_⟩
          intro y hy hy0
          match h : bit (P c y) with
          | true => rfl
          | false => exact absurd ⟨y, hy, hy0, h⟩ hex
  intro c hc
  obtain ⟨v, hv⟩ := key c hc
  cases v with
  | true => exact Or.inl (Ev.mono (fun x hx => bit_eq_true.mp hx) hv)
  | false => exact Or.inr (Ev.mono (fun x hx => bit_eq_false.mp hx) hv)

/-! ### 語（生成関数の合成）-/

/-- 生成関数 `G k ξ`（種類 `k`、パラメータ `ξ`）の合成による関数 -/
def evalW (G : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u}) :
    List (Nat × Ordinal.{u}) → Ordinal.{u} → Ordinal.{u}
  | [], x => x
  | (k, ξ) :: w, x => G k ξ (evalW G w x)

/-- 語のパラメータがすべて `κ` 未満 -/
def Valid (κ : Ordinal.{u}) (w : List (Nat × Ordinal.{u})) : Prop :=
  ∀ g, g ∈ w → g.2 < κ

theorem Valid.nil (κ : Ordinal.{u}) : Valid κ [] := by
  intro g hg
  exact absurd hg (by simp)

theorem Valid.cons {κ : Ordinal.{u}} {k : Nat} {ξ : Ordinal.{u}} {w : List (Nat × Ordinal.{u})}
    (hξ : ξ < κ) (hw : Valid κ w) : Valid κ ((k, ξ) :: w) := by
  intro g hg
  rcases List.mem_cons.mp hg with h | h
  · rw [h]; exact hξ
  · exact hw g h

theorem Valid.tail {κ : Ordinal.{u}} {g : Nat × Ordinal.{u}} {w : List (Nat × Ordinal.{u})}
    (h : Valid κ (g :: w)) : Valid κ w :=
  fun g' hg' => h g' (List.mem_cons_of_mem g hg')

/-- 語の符号化 -/
def codeW (pair : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}) :
    List (Nat × Ordinal.{u}) → Ordinal.{u}
  | [] => 0
  | (k, ξ) :: w => succ (pair (pair (ordNat k) ξ) (codeW pair w))

theorem codeW_lt {κ : Ordinal.{u}} (hκ : R κ) {pair : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}}
    (hp : ∀ a b, a < κ → b < κ → pair a b < κ) :
    ∀ w, Valid κ w → codeW pair w < κ := by
  intro w
  induction w with
  | nil => intro _; exact hκ.2.1.1
  | cons g w ih =>
    intro hv
    obtain ⟨k, ξ⟩ := g
    have hξ : ξ < κ := hv (k, ξ) (List.mem_cons_self ..)
    have h1 : pair (ordNat k) ξ < κ := hp _ _ (lt_trans _ _ _ (ordNat_lt_omega k) hκ.1) hξ
    exact hκ.2.1.succ_lt (hp _ _ h1 (ih hv.tail))

theorem codeW_inj {κ : Ordinal.{u}} (hκ : R κ) {pair : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}}
    (hp : ∀ a b, a < κ → b < κ → pair a b < κ)
    (hi : ∀ a b a' b', a < κ → b < κ → a' < κ → b' < κ → pair a b = pair a' b' →
      a = a' ∧ b = b') :
    ∀ w w', Valid κ w → Valid κ w' → codeW pair w = codeW pair w' → w = w' := by
  intro w
  induction w with
  | nil =>
    intro w' _ hw' e
    cases w' with
    | nil => rfl
    | cons g w' =>
      obtain ⟨k, ξ⟩ := g
      exact absurd e.symm (succ_ne_zero _)
  | cons g w ih =>
    intro w' hv hw' e
    obtain ⟨k, ξ⟩ := g
    cases w' with
    | nil => exact absurd e (succ_ne_zero _)
    | cons g' w' =>
      obtain ⟨k', ξ'⟩ := g'
      have hξ : ξ < κ := hv (k, ξ) (List.mem_cons_self ..)
      have hξ' : ξ' < κ := hw' (k', ξ') (List.mem_cons_self ..)
      have hω : ∀ m : Nat, ordNat.{u} m < κ := fun m => lt_trans _ _ _ (ordNat_lt_omega m) hκ.1
      have h1 : pair (ordNat k) ξ < κ := hp _ _ (hω k) hξ
      have h1' : pair (ordNat k') ξ' < κ := hp _ _ (hω k') hξ'
      have e1 : pair (pair (ordNat k) ξ) (codeW pair w) =
          pair (pair (ordNat k') ξ') (codeW pair w') := succ_inj e
      obtain ⟨e2, e3⟩ := hi _ _ _ _ h1 (codeW_lt hκ hp w hv.tail) h1' (codeW_lt hκ hp w' hw'.tail) e1
      obtain ⟨e4, e5⟩ := hi _ _ _ _ (hω k) hξ (hω k') hξ' e2
      have e6 := ih w' hv.tail hw'.tail e3
      rw [ordNat_injective e4, e5, e6]

/-- 各語 `w` と `α < κ` について、`α < w(x)` が最終的に決定される非有界集合 -/
theorem exists_H_words {κ : Ordinal.{u}} (hκ : R κ) (hpart : PartitionProp κ)
    (G : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u}) :
    ∃ H, Conv κ H ∧ ∀ w, Valid κ w → ∀ α, α < κ →
      Ev κ H (fun x => α < evalW G w x) ∨ Ev κ H (fun x => ¬ α < evalW G w x) := by
  obtain ⟨pair, hp, hi⟩ := pairInj_of_omega_le κ (Or.inl hκ.1)
  obtain ⟨H, hc, hdec⟩ := exists_convergent hκ hpart
    (fun c x => ∃ w α, Valid κ w ∧ α < κ ∧ pair (codeW pair w) α = c ∧ α < evalW G w x)
  refine ⟨H, hc, ?_⟩
  intro w hw α hα
  have hcw := codeW_lt hκ hp w hw
  have hcκ : pair (codeW pair w) α < κ := hp _ _ hcw hα
  have iff : ∀ x, (∃ w' α', Valid κ w' ∧ α' < κ ∧ pair (codeW pair w') α' = pair (codeW pair w) α ∧
      α' < evalW G w' x) ↔ α < evalW G w x := by
    intro x
    constructor
    · rintro ⟨w', α', hw', hα', he, hlt⟩
      obtain ⟨e1, e2⟩ := hi _ _ _ _ (codeW_lt hκ hp w' hw') hα' hcw hα he
      have := codeW_inj hκ hp hi w' w hw' hw e1
      rw [← this, ← e2]
      exact hlt
    · intro h
      exact ⟨w, α, hw, hα, rfl, h⟩
  rcases hdec _ hcκ with h | h
  · exact Or.inl (Ev.mono (fun x hx => (iff x).mp hx) h)
  · exact Or.inr (Ev.mono (fun x hx hlt => hx ((iff x).mpr hlt)) h)

/-! ### 最小元 -/

/-- `g < f` が最終的に成り立つ -/
def lessH (κ : Ordinal.{u}) (H : Ordinal.{u} → Prop) (g f : Ordinal.{u} → Ordinal.{u}) : Prop :=
  Ev κ H (fun x => g x < f x)

/-- 任意の `α < κ` について `α < f x` が最終的に成り立つ -/
def NN (κ : Ordinal.{u}) (H : Ordinal.{u} → Prop) (f : Ordinal.{u} → Ordinal.{u}) : Prop :=
  ∀ α, α < κ → Ev κ H (fun x => α < f x)

theorem lessH_wf {κ : Ordinal.{u}} {H : Ordinal.{u} → Prop} (hc : Conv κ H) :
    WellFounded (lessH κ H) := by
  classical
  apply WellFounded.intro
  intro a
  apply Classical.byContradiction
  intro ha
  have step : ∀ b, ¬ Acc (lessH κ H) b → ∃ c, lessH κ H c b ∧ ¬ Acc (lessH κ H) c := by
    intro b hb
    apply Classical.byContradiction
    intro hne
    apply hb
    apply Acc.intro
    intro c hcb
    apply Classical.byContradiction
    intro hnc
    exact hne ⟨c, hcb, hnc⟩
  let s : Nat → {b // ¬ Acc (lessH κ H) b} := fun n =>
    Nat.rec ⟨a, ha⟩ (fun _ b => ⟨Classical.choose (step b.1 b.2),
      (Classical.choose_spec (step b.1 b.2)).2⟩) n
  have hs : ∀ n, lessH κ H (s (n + 1)).1 (s n).1 := fun n =>
    (Classical.choose_spec (step (s n).1 (s n).2)).1
  have hall := Ev.all hc.reg (δ := omega) hc.reg.1
    (Q := fun i x => (s (natOf i + 1)).1 x < (s (natOf i)).1 x)
    (fun i _ => hs (natOf i))
  obtain ⟨x₀, hx₀κ, hx₀⟩ := hall
  obtain ⟨x, hxH, hxx₀, _, _⟩ := Ev.exists_pt hc (Ev.of_all hc.reg.2.1.1 (fun _ => True.intro)) hx₀κ
  have hdesc : ∀ n, (s (n + 1)).1 x < (s n).1 x := by
    intro n
    have := hx₀ x hxH hxx₀ (ordNat n) (ordNat_lt_omega n)
    rw [natOf_ordNat] at this
    exact this
  obtain ⟨t, ht, htmin⟩ := Ordinal.exists_min (fun t => ∃ n, t = (s n).1 x) ⟨(s 0).1 x, 0, rfl⟩
  obtain ⟨m, hm⟩ := ht
  exact htmin _ (by rw [hm]; exact hdesc m) ⟨m + 1, rfl⟩

theorem wf_has_min {α : Type v} {r : α → α → Prop} (hwf : WellFounded r) (s : α → Prop)
    (h : ∃ a, s a) : ∃ a, s a ∧ ∀ x, s x → ¬ r x a := by
  obtain ⟨a₀, ha₀⟩ := h
  induction a₀ using hwf.induction with
  | _ a ih =>
    by_cases hb : ∃ b, s b ∧ r b a
    · obtain ⟨b, hb1, hb2⟩ := hb
      exact ih b hb2 hb1
    · exact ⟨a, ha₀, fun x hx hxa => hb ⟨x, hx, hxa⟩⟩

/-- `NN` な語の中で `lessH` に関して最小のものがある -/
theorem exists_minimal_word {κ : Ordinal.{u}} {H : Ordinal.{u} → Prop} (hc : Conv κ H)
    (G : Nat → Ordinal.{u} → Ordinal.{u} → Ordinal.{u}) :
    ∃ w, Valid κ w ∧ NN κ H (evalW G w) ∧
      ∀ w', Valid κ w' → NN κ H (evalW G w') → ¬ lessH κ H (evalW G w') (evalW G w) := by
  have hne : ∃ f : Ordinal.{u} → Ordinal.{u}, ∃ w, Valid κ w ∧ NN κ H (evalW G w) ∧
      f = evalW G w :=
    ⟨evalW G [], [], Valid.nil κ, fun α hα => Ev.gt hα, rfl⟩
  obtain ⟨f, ⟨w, hw, hn, hfw⟩, hmin⟩ := wf_has_min (lessH_wf hc)
    (fun f => ∃ w, Valid κ w ∧ NN κ H (evalW G w) ∧ f = evalW G w) hne
  refine ⟨w, hw, hn, ?_⟩
  intro w' hw' hn' hless
  apply hmin (evalW G w') ⟨w', hw', hn', rfl⟩
  rw [hfw]
  exact hless

/-- 決定済みで `NN` でない関数は最終的に定数 -/
theorem eventually_const {κ : Ordinal.{u}} {H : Ordinal.{u} → Prop} (hc : Conv κ H)
    {g : Ordinal.{u} → Ordinal.{u}} (hng : ¬ NN κ H g)
    (hdec : ∀ α, α < κ → Ev κ H (fun x => α < g x) ∨ Ev κ H (fun x => ¬ α < g x)) :
    ∃ γ, γ < κ ∧ Ev κ H (fun x => g x = γ) := by
  classical
  have hα : ∃ α, α < κ ∧ ¬ Ev κ H (fun x => α < g x) := by
    apply Classical.byContradiction
    intro hno
    apply hng
    intro α hακ
    apply Classical.byContradiction
    intro hn
    exact hno ⟨α, hακ, hn⟩
  obtain ⟨α, hακ, hα⟩ := hα
  have hαle : Ev κ H (fun x => ¬ α < g x) := by
    rcases hdec α hακ with h | h
    · exact absurd h hα
    · exact h
  obtain ⟨γ, hγ, hγmin⟩ := Ordinal.exists_min (fun δ => Ev κ H (fun x => ¬ δ < g x)) ⟨α, hαle⟩
  have hγα : γ ≤ α := by
    apply le_of_not_lt
    intro hlt
    exact hγmin α hlt hαle
  have hγκ : γ < κ := lt_of_le_of_lt hγα hακ
  refine ⟨γ, hγκ, ?_⟩
  have hbelow : ∀ δ, δ < γ → Ev κ H (fun x => δ < g x) := by
    intro δ hδ
    rcases hdec δ (lt_trans _ _ _ hδ hγκ) with h | h
    · exact h
    · exact absurd h (hγmin δ hδ)
  have hall := Ev.all hc.reg hγκ hbelow
  refine Ev.mono ?_ (hγ.and hall)
  intro x hx
  apply le_antisymm
  · exact le_of_not_lt hx.1
  · apply le_of_not_lt
    intro hlt
    exact lt_irrefl _ (hx.2 (g x) hlt)

/-! ## 反射補題（GRL）：`κ` が `R κ ∧ PartitionProp κ` で、`S c`（`c < κ`）がすべて `κ` で定常、
`E` が `κ` の club なら、`E` に属する正則な `τ < κ` で、すべての `c < τ` について `S c` が
`τ` で定常となるものがある。

方針：`PartitionProp` から得た収束集合 `H` 上で、`NN` な語のうち `lessH` に
関して最小の `f₀` を取り、`f₀(x)`（`x ∈ H` が十分大きい）が求める `τ` になることを示す。 -/

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

/-! ## 構造補題 (B3')：`α ≤ Ω_{K_n+1}` のとき、`x ∈ C(α, K_n)` かつ `x < α` なら `x ∈ C(x, K_n)`。

`α > Ω_{K_n+1}` では成り立たない（`Ψ^0_{K_n^+}(K_n^+) ∈ C(α, K_n)` だが `C(Ψ^0_{K_n^+}(K_n^+), K_n)` には
入らない。`Complete.lean`）。 -/

noncomputable section

variable [Setting.{u}]

/-- `K n` より大きい正則順序数は `Ω_{K n + 1}` 以上 -/
theorem Om_succ_le_of_R {n : Nat} (hn : 1 ≤ n) {π : Ordinal.{u}} (hπ : R π) (hlt : K n < π) :
    Om (K n + succ 0) ≤ π := by
  rw [add_one_eq_succ]
  apply enum_le (X := CardSet) (Or.inr (subset_closure hπ))
  intro γ hγ
  have hγle : γ ≤ K n := le_of_lt_succ hγ
  have h1 : Om γ ≤ K n := by
    cases hγle with
    | inl h =>
      have := Om_lt_Om h (K_lt_Λ n)
      rw [Om_K hn] at this
      exact Or.inl this
    | inr h => rw [h, Om_K hn]; exact le_refl _
  exact lt_of_le_of_lt h1 hlt

theorem K_add_one_lt_Λ (n : Nat) : K.{u} n + succ 0 < Λ := by
  rw [add_one_eq_succ]
  have hl : IsLimit (K.{u} (n + 1)) := (R_K (Nat.succ_le_succ (Nat.zero_le n))).2.1
  exact lt_trans _ _ _ (hl.succ_lt (K_lt_K_succ n)) (K_lt_Λ (n + 1))

/-- (B3')：`x ∈ C(α, K n)`、`x < α ≤ Ω_{K n + 1}` なら `x ∈ C(x, K n)` -/
theorem C_self_of_lt {n : Nat} (hn : 1 ≤ n) {α : Ordinal.{u}} (hα : α ≤ Om (K n + succ 0))
    {k : Nat} {x : Ordinal.{u}} (h : Cn α (K n) k x) : x < α → C x (K n) x := by
  unfold Cn at h
  induction h with
  | lt k γ hγ => intro _; exact C_lt hγ
  | one k => intro _; exact C_one _ _
  | kc k m => intro _; exact C_K _ _ m
  | add k y z hy hz ihy ihz =>
    intro hlt
    exact C_add (C_mono_arg (le_add y z) (ihy (lt_of_le_of_lt (le_add y z) hlt)))
      (C_mono_arg (right_le_add y z) (ihz (lt_of_le_of_lt (right_le_add y z) hlt)))
  | om k y hΛ hy ih =>
    intro hlt
    have hy' : y ≤ Om y := le_Om hΛ
    exact C_Om hΛ (C_mono_arg hy' (ih (lt_of_le_of_lt hy' hlt)))
  | xi k m y hpos hyα hy ih =>
    show Xi m y < α → C (Xi m y) (K n) (Xi m y)
    intro hlt
    cases Xi_le m y with
    | inr heq => rw [heq]; exact C_K _ _ m
    | inl hlt' =>
      have hsp := Xi_spec hlt'
      have hreg : IsReg (Xi m y) := ((M_pos_iff (ne_of_gt hpos) _).mp hsp.1).1
      by_cases hm : m ≤ n
      · exact C_lt (lt_of_lt_of_le hlt' (K_le hm))
      · exfalso
        have hnm : n ≤ m - 1 := by omega
        have h1 : K n < Xi m y := lt_of_le_of_lt (K_le hnm) hsp.2
        have h2 := Om_succ_le_of_R hn hreg.1 h1
        exact lt_irrefl _ (lt_of_lt_of_le (lt_of_lt_of_le hlt hα) h2)
  | psi k ξ π δ hδα hξδ hπ hξ hπC hδ ihξ ihπ ihδ =>
    show Psi ξ π δ < α → C (Psi ξ π δ) (K n) (Psi ξ π δ)
    intro hlt
    by_cases hX : Psi ξ π δ < K n
    · exact C_lt hX
    · have hKX : K n ≤ Psi ξ π δ := le_of_not_lt hX
      have hπR : R π := hπ.1
      cases Psi_le ξ π δ with
      | inr heq =>
        exfalso
        have hKπ : K n < π := by
          cases hKX with
          | inl h => rw [heq] at h; exact h
          | inr h => exact absurd (h.trans heq).symm (hπ.2.2 n)
        have h2 := Om_succ_le_of_R hn hπR hKπ
        have hπα : π < α := by rw [← heq]; exact hlt
        exact lt_irrefl π (lt_of_lt_of_le (lt_of_lt_of_le hπα hα) h2)
      | inl hlt' =>
        have hsp := Psi_spec hlt'
        have hKπ : K n < π := lt_of_le_of_lt hKX hlt'
        have h2 := Om_succ_le_of_R hn hπR hKπ
        have hπeq : π = Om (K n + succ 0) := by
          apply le_antisymm _ h2
          apply le_of_not_lt
          intro hlt2
          have hC : C δ (Psi ξ π δ) (Om (K n + succ 0)) :=
            C_Om (K_add_one_lt_Λ n) (C_add (C_K _ _ n) (C_one _ _))
          have := hsp.2.2.1 _ hC hlt2
          exact lt_irrefl _ (lt_of_lt_of_le (lt_trans _ _ _ this hlt) hα)
        have hδπ : δ < π := by rw [hπeq]; exact lt_of_lt_of_le hδα hα
        have hδX : δ < Psi ξ π δ := hsp.2.2.1 δ hsp.2.2.2.2 hδπ
        have hξα : ξ < α := lt_of_le_of_lt hξδ hδα
        have c1 : C (Psi ξ π δ) (K n) ξ :=
          C_mono_arg (le_trans hξδ (Or.inl hδX)) (ihξ hξα)
        have c2 : C (Psi ξ π δ) (K n) δ := C_mono_arg (Or.inl hδX) (ihδ hδα)
        have c3 : C (Psi ξ π δ) (K n) π := by
          rw [hπeq]; exact C_Om (K_add_one_lt_Λ n) (C_add (C_K _ _ n) (C_one _ _))
        exact C_Psi hδX hξδ hπ c1 c3 c2

theorem C_self_of_C {n : Nat} (hn : 1 ≤ n) {α x : Ordinal.{u}} (hα : α ≤ Om (K n + succ 0))
    (hx : C α (K n) x) (hxα : x < α) : C x (K n) x := by
  cases hx with
  | intro k hk => exact C_self_of_lt hn hα hk hxα

/-! ## `α < Ω_{K n + 1}` から `K n` への単射（Hartogs）、`C(α, K n)` から `K n` への単射（`exists_inj_C`）、
閉包点の club。 -/

/-- `α < Ω_{K n + 1}` なら、`α` から `K n` への（順序数としての）単射がある -/
theorem exists_inj_of_lt_Om_succ {n : Nat} (hn : 1 ≤ n) {α : Ordinal.{u}}
    (hα : α < Om (K n + succ 0)) :
    ∃ j : Ordinal.{u} → Ordinal.{u}, (∀ β, β < α → j β < K n) ∧
      ∀ β β', β < α → β' < α → j β = j β' → β = β' := by
  classical
  let κ := K.{u} n
  have hκR : R κ := R_K hn
  let X := (representative κ).Carrier
  obtain ⟨pair, hpair⟩ := pairing_of_omega_le κ (Or.inl hκR.1)
  have hκθ : κ < hartogs X := lt_hartogs_of_injective κ (fun x => x) (fun x y h => h)
  have hωθ : omega < hartogs X := lt_trans _ _ _ hκR.1 hκθ
  have hθlim : IsLimit (hartogs X) := hartogs_isLimit_of_omega_lt hωθ
  have hθreg : IsRegular (hartogs X) := hartogs_regular_of_pair_injective hθlim pair hpair
  have hθR : R (hartogs X) := ⟨hωθ, hθreg⟩
  have h2 := Om_succ_le_of_R hn hθR hκθ
  have hαθ : α < hartogs X := lt_of_lt_of_le hα h2
  obtain ⟨f, hf⟩ := injective_of_lt_hartogs hαθ
  let j : Ordinal.{u} → Ordinal.{u} := fun β =>
    if h : β < α then type ((representative κ).below (f (pointBelow α β h))) else 0
  have hj : ∀ β (h : β < α), j β = type ((representative κ).below (f (pointBelow α β h))) :=
    fun β h => dite_eq_left h
  refine ⟨j, ?_, ?_⟩
  · intro β h
    rw [hj β h]
    exact initial_lt κ _
  · intro β β' h h' e
    rw [hj β h, hj β' h'] at e
    have e1 := initial_injective κ _ _ e
    have e2 := hf _ _ e1
    exact pointBelow_inj e2

/-- `K n < Ω_{K n + 1}` -/
theorem K_lt_Om_succK {n : Nat} (hn : 1 ≤ n) : K.{u} n < Om (K n + succ 0) := by
  have h := Om_lt_Om (by rw [add_one_eq_succ]; exact lt_succ_self (K.{u} n)) (K_add_one_lt_Λ n)
  rw [Om_K hn] at h
  exact h

/-- `Ω_{K n + 1}` は非可算正則 -/
theorem R_Om_succK (n : Nat) : R (Om (K.{u} n + succ 0)) := by
  rw [add_one_eq_succ]
  exact Om_succ_R (by rw [← add_one_eq_succ]; exact K_add_one_lt_Λ n)

/-- `C(α, K n)` から `K n` への単射（`|C(α, K n)| < Ω_{K n + 1}` による。`α` には制限が無い） -/
theorem exists_inj_C {n : Nat} (hn : 1 ≤ n) (α : Ordinal.{u}) :
    ∃ j : Ordinal.{u} → Ordinal.{u}, (∀ β, j β < K n) ∧
      ∀ β β', C α (K n) β → C α (K n) β' → j β = j β' → β = β' := by
  classical
  obtain ⟨γ, hγ, f, hf, hfinj⟩ := C_small (R_Om_succK n) (K_lt_Om_succK hn) α
  obtain ⟨j₀, hj₀κ, hj₀inj⟩ := exists_inj_of_lt_Om_succ hn hγ
  refine ⟨fun β => if C α (K n) β then j₀ (f β) else 0, ?_, ?_⟩
  · intro β
    by_cases hβ : C α (K n) β
    · dsimp only
      rw [ite_eq_left hβ]
      exact hj₀κ _ (hf β hβ)
    · dsimp only
      rw [ite_eq_right hβ]
      exact (R_K hn).2.pos
  · intro β β' hβ hβ' e
    dsimp only at e
    rw [ite_eq_left hβ, ite_eq_left hβ'] at e
    exact hfinj β β' hβ hβ' (hj₀inj _ _ (hf β hβ) (hf β' hβ') e)

theorem Club.congr {κ : Ordinal.{u}} {X Y : Ordinal.{u} → Prop} (h : ∀ ρ, X ρ ↔ Y ρ)
    (hX : Club κ X) : Club κ Y := by
  have e : X = Y := funext (fun ρ => propext (h ρ))
  rw [← e]
  exact hX

/-- 吸収される集合 `Q ρ` が単調・連続・有界なら、`Q ρ ∩ κ ⊆ ρ` となる `ρ` は club -/
theorem club_absorb {κ : Ordinal.{u}} (hκ : R κ) (Q : Ordinal.{u} → Ordinal.{u} → Prop)
    (hmono : ∀ ρ ρ' y, ρ ≤ ρ' → Q ρ y → Q ρ' y)
    (hcont : ∀ l y, IsLimit l → Q l y → ∃ ρ, ρ < l ∧ Q ρ y)
    (hbdd : ∀ ρ, ρ < κ → ∃ γ, γ < κ ∧ ∀ y, Q ρ y → y < κ → y < γ)
    {μ₀ : Ordinal.{u}} (hμ₀ : μ₀ < κ) :
    Club κ (fun ρ => μ₀ < ρ ∧ ∀ y, Q ρ y → y < κ → y < ρ) := by
  classical
  apply And.intro
  · intro η hη
    let bnd : Ordinal.{u} → Ordinal.{u} := fun δ =>
      if h : δ < κ then Classical.choose (hbdd δ h) else 0
    have hbnd : ∀ δ, δ < κ → bnd δ < κ ∧ ∀ y, Q δ y → y < κ → y < bnd δ := by
      intro δ hδ
      have e : bnd δ = Classical.choose (hbdd δ hδ) := dite_eq_left hδ
      rw [e]
      exact Classical.choose_spec (hbdd δ hδ)
    let s : Nat → Ordinal.{u} := fun n =>
      Nat.rec (succ (omax η μ₀)) (fun _ δ => omax (succ δ) (bnd δ)) n
    have hs0 : s 0 = succ (omax η μ₀) := rfl
    have hsS : ∀ n, s (n + 1) = omax (succ (s n)) (bnd (s n)) := fun _ => rfl
    have hsκ : ∀ n, s n < κ := by
      intro n
      induction n with
      | zero => rw [hs0]; exact hκ.2.1.succ_lt (omax_lt hη hμ₀)
      | succ n ih =>
        rw [hsS]
        exact omax_lt (hκ.2.1.succ_lt ih) (hbnd _ ih).1
    have hs : ∀ n, s n < s (n + 1) := by
      intro n
      rw [hsS]
      exact lt_of_lt_of_le (lt_succ_self _) (le_omax_left _ _)
    let δs := omegaSup s
    have hδsκ : δs < κ := omegaSup_lt hκ hsκ
    have hδslim : IsLimit δs := by
      apply And.intro (lt_of_le_of_lt (zero_le _) (lt_omegaSup hs 0))
      intro β hβ
      cases (lt_omegaSup_iff β).mp hβ with
      | intro n hn => exact lt_of_le_of_lt (succ_le_of_lt hn) (lt_omegaSup hs n)
    have hlt0 : omax η μ₀ < δs := lt_trans _ _ _ (lt_succ_self _) (lt_omegaSup hs 0)
    refine Exists.intro δs (And.intro (And.intro
      (lt_of_le_of_lt (le_omax_right η μ₀) hlt0) ?_)
      (And.intro (lt_of_le_of_lt (le_omax_left η μ₀) hlt0) hδsκ))
    intro y hy hyκ
    cases hcont δs y hδslim hy with
    | intro ζ hζ =>
      cases (lt_omegaSup_iff ζ).mp hζ.1 with
      | intro n hn =>
        have hyn : y < bnd (s n) :=
          (hbnd _ (hsκ n)).2 y (hmono ζ (s n) y (Or.inl hn) hζ.2) hyκ
        exact lt_trans _ _ _ hyn (lt_of_le_of_lt (by rw [hsS n]; exact le_omax_right _ _)
          (lt_omegaSup hs (n + 1)))
  · intro l hlκ hlp
    have hl : IsLimit l := by
      apply And.intro hlp.1
      intro β hβ
      cases hlp.2 β hβ with
      | intro γ hγ => exact lt_of_le_of_lt (succ_le_of_lt hγ.2.1) hγ.2.2
    apply And.intro
    · cases hlp.2 0 hlp.1 with
      | intro γ hγ => exact lt_trans _ _ _ hγ.1.1 hγ.2.2
    · intro y hy hyκ
      cases hcont l y hl hy with
      | intro ζ hζ =>
        cases hlp.2 ζ hζ.1 with
        | intro ρ hρ =>
          exact lt_trans _ _ _ (hρ.1.2 y (hmono ζ ρ y (Or.inl hρ.2.1) hζ.2) hyκ) hρ.2.2

/-- `j[C(α, ρ) ∩ α] ⊆ ρ` となる `ρ` は club -/
theorem club_j {n : Nat} (hn : 1 ≤ n) {α : Ordinal.{u}} {j : Ordinal.{u} → Ordinal.{u}}
    (hjκ : ∀ β, β < α → j β < K n) {μ₀ : Ordinal.{u}} (hμ₀ : μ₀ < K n) :
    Club (K n) (fun ρ => μ₀ < ρ ∧ ∀ x, C α ρ x → x < α → j x < ρ) := by
  have hκ : R (K n) := R_K hn
  have hc := club_absorb hκ (fun ρ y => ∃ x, C α ρ x ∧ x < α ∧ y = j x) ?_ ?_ ?_ hμ₀
  · refine Club.congr (fun ρ => ?_) hc
    apply and_congr_right
    intro _
    constructor
    · intro h x hx hxα
      exact h (j x) ⟨x, hx, hxα, rfl⟩ (hjκ x hxα)
    · intro h y hy _
      cases hy with
      | intro x hx => rw [hx.2.2]; exact h x hx.1 hx.2.1
  · intro ρ ρ' y hρ hy
    cases hy with
    | intro x hx => exact ⟨x, C_mono_base hρ hx.1, hx.2⟩
  · intro l y hl hy
    cases hy with
    | intro x hx =>
      cases C_limit hl hx.1 with
      | intro η hη => exact ⟨η, hη.1, x, hη.2, hx.2⟩
  · intro ρ hρ
    have hsm : Small (K n) (fun y => ∃ x, (C α ρ x ∧ x < α) ∧ y = j x) :=
      ((C_small hκ hρ α).mono (A := fun x => C α ρ x ∧ x < α) (fun _ h => h.1)).image j
    have hb := Small.bounded hκ.2 hsm (A := fun y => ∃ x, (C α ρ x ∧ x < α) ∧ y = j x) (by
      intro y hy
      cases hy with
      | intro x hx => rw [hx.2]; exact hjκ x hx.1.2)
    cases hb with
    | intro γ hγ =>
      refine ⟨γ, hγ.1, ?_⟩
      intro y hy _
      cases hy with
      | intro x hx => exact hγ.2 y ⟨x, ⟨hx.1, hx.2.1⟩, hx.2.2⟩

/-! ## `K n`（`n ≥ 1`）が分割性を持つなら `StageReflectionAt n` が成り立つ。

`C(α, K n)` から `K n` への単射 `j`（`|C(α, K n)| < Ω_{K n + 1}`、`exists_inj_C`）で
`C(α, K n) ∩ α` を `K n` 個の定常集合 `M^β` の族として並べ、反射補題 `grl` を、四つの club
（`E`、`C(α,ρ) ∩ K n ⊆ ρ`、`j[C(α,ρ) ∩ α] ⊆ ρ`、`ρ > max(K(n-1), η₀)`）の共通部分に適用する。
`α ≤ Ω_{K n + 1}` は (B3')（`C_self_of_C`）で `C(α, K n) ∩ α` の元に帰納法の仮定を使うためだけに要る。 -/

theorem stageReflectionAt_of_partition {n : Nat} (hn : 1 ≤ n) (hpart : PartitionProp (K.{u} n)) :
    StageReflectionAt.{u} n := by
  intro α hα0 hαΩ hCα hIH E hE
  have hκ : R (K.{u} n) := R_K hn
  obtain ⟨j, hjκ, hjinj⟩ := exists_inj_C hn α
  let S : Ordinal.{u} → Ordinal.{u} → Prop := fun c ρ =>
    ∀ β, β < α → 0 < β → C α (K n) β → j β = c → M β ρ
  have hS : ∀ c, c < K n → Stationary (K n) (S c) := by
    intro c _
    by_cases hex : ∃ β, β < α ∧ 0 < β ∧ C α (K n) β ∧ j β = c
    · obtain ⟨β₀, hβ₀α, hβ₀pos, hβ₀C, hβ₀c⟩ := hex
      have hst : Stationary (K n) (M β₀) :=
        hIH β₀ hβ₀α hβ₀pos (Or.inl (lt_of_lt_of_le hβ₀α hαΩ)) (C_self_of_C hn hαΩ hβ₀C hβ₀α)
      refine hst.mono ?_
      intro ρ _ hρ β _ _ hβC hβc
      have e : β = β₀ := hjinj β β₀ hβC hβ₀C (hβc.trans hβ₀c.symm)
      rw [e]
      exact hρ
    · refine (stationary_isLimit hκ).mono ?_
      intro ρ _ _ β hβα hβpos hβC hβc
      exact absurd ⟨β, hβα, hβpos, hβC, hβc⟩ hex
  obtain ⟨η₀, hη₀κ, hη₀⟩ := C_limit hκ.2.1 hCα
  have hn' : n - 1 < n := by omega
  have hK1 : K (n - 1) < K n := K_lt hn'
  have hμ₀ : omax (K (n - 1)) η₀ < K n := omax_lt hK1 hη₀κ
  have hE2 := club_closedC hκ α hμ₀
  have hE3 := club_j hn (α := α) (fun β _ => hjκ β) hμ₀
  have hEall := Club.inter hκ (Club.inter hκ hE hE2) hE3
  obtain ⟨τ, hτκ, ⟨⟨hτE, hτμ, hτcl⟩, _, hτj⟩, hτR, hτS⟩ := grl hκ hpart hEall hS
  have hτpos : K (n - 1) < τ := lt_of_le_of_lt (le_omax_left _ _) hτμ
  have hη₀τ : η₀ ≤ τ := le_trans (le_omax_right _ _) (Or.inl hτμ)
  have hτΛ : τ < Λ := lt_trans _ _ _ hτκ (K_lt_Λ n)
  refine ⟨τ, hτκ, hτE, ?_, C_mono_base hη₀τ hη₀, ?_, ?_⟩
  · refine ⟨hτR, hτΛ, ?_⟩
    intro m hm
    by_cases hmn : m ≤ n - 1
    · have h1 : K m ≤ K (n - 1) := K_le hmn
      rw [hm] at hτpos
      exact lt_irrefl _ (lt_of_le_of_lt h1 hτpos)
    · have h1 : K n ≤ K m := K_le (by omega)
      rw [hm] at hτκ
      exact lt_irrefl _ (lt_of_lt_of_le hτκ h1)
  · intro x hx hxK
    rw [Kabove_eq_of_between (Or.inl hτpos) hτκ] at hxK
    exact hτcl x hx hxK
  · intro β hβα hβC
    by_cases hβ0 : β = 0
    · subst hβ0
      intro X hX
      cases stationary_isLimit hτR X hX with
      | intro ξ hξ =>
        exact ⟨ξ, hξ.1, hξ.2.1,
          (M_zero_iff ξ).mpr ⟨hξ.2.2, lt_trans _ _ _ hξ.1 hτΛ⟩⟩
    · have hβpos : 0 < β := by
        cases zero_le β with
        | inl h => exact h
        | inr h => exact absurd h.symm hβ0
      have hβC' : C α (K n) β := C_mono_base (Or.inl hτκ) hβC
      have hjβ : j β < τ := hτj β hβC hβα
      intro X hX
      cases hτS (j β) hjβ X hX with
      | intro ξ hξ => exact ⟨ξ, hξ.1, hξ.2.1, hξ.2.2 β hβα hβpos hβC' rfl⟩

end
end OCF.Rathjen
