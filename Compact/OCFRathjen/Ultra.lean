import Compact.OCFRathjen.Pairing

/-! 分割性 `PartitionProp κ` から取り出す「収束集合」`H`。

`Ev κ H Q`：`H` の十分大きい元で常に `Q` が成り立つ。`H` が非有界なら `Ev` は κ 未満の
個数の合接について閉じたフィルターで、`exists_convergent` は κ 個の性質それぞれについて
`Ev` が決定される `H` を与える（順序付け補題 `PartitionProp.orient` のみを使う）。 -/

namespace OCF.Rathjen

universe u

open Ordinal

set_option linter.unusedSectionVars false

noncomputable section

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

theorem absurd (hc : Conv κ H) {Q : Ordinal.{u} → Prop} (h : Ev κ H Q)
    (h' : Ev κ H (fun x => ¬ Q x)) : False := by
  cases exists_pt hc (h.and h') hc.reg.2.1.1 with
  | intro x hx => exact hx.2.2.2.2 hx.2.2.2.1

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

end
end OCF.Rathjen
