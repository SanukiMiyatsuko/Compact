import Compact.OCFRathjen.Setting

/-! Hessenberg の定理：無限順序数 `β` の台集合 `X` について `X × X → X` の単射がある。

`Setting.lean` の `weaklyCompactAt_inacc_of_pairing`（後続の正則基数の存在）に必要な
`pairing_of_omega_le` を、公理を使わずに示す。

* `ω` では `(a, b) ↦ 2^a (2b+1)`。
* `β > ω` では、`β` が小さい無限順序数 `γ` に単射で入るなら `γ` の対関数を使い、
  そうでなければ（`β` は基数）`max` と、各 `max` の殻の中の鍵で定まる Gödel 順序の
  順序型を使う。殻は `ν < β` に単射で入るので、Hartogs 数 `≤ β` から
  各始切片の順序型は `β` 未満。 -/

namespace OCF.Rathjen

universe u

open Ordinal

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

end
end OCF.Rathjen
