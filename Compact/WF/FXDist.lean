import Compact.WF.FXOrd

/-! 断片 `FX` の区別集合（Buchholz の distinguished sets を、Arai の最大区別集合の形で）。
Subsp の `OCF/Jaeger/Constructive/Distinguished.lean` と同じ構成で、項と順序を `FX` に替えたもの。

* `Hull α X` は `C^α(X)`：`{0, 1, K_n} ∪ (X ∩ α)` を `+`、`Ω`、`Ξ_n`（`α < K_n`）、`Ψ_{Ω_c}`（`α < Ω_c`）で
  閉じたもの。
* `WPart Y` は `Y` の整礎部分。
* `Dist X`：`X` は区別集合（`X` のある元以下の `α` について、`α` の次の正則項 `nr α` 未満では、`X` は
  `Hull α X` の整礎部分と一致する）。
* `Wmax` は区別集合全ての合併（`Prop` での非可述的な定義）、`Good α` は `α ∈ C^α(Wmax)` かつ
  `C^α(Wmax) ∩ α ⊆ Wmax`。

主な結果 `wmax_of_good_hyp`：`Good α` と拡張の仮定 `Hyp α` から新しい区別集合を作り、`α ∈ Wmax` を示す。 -/

namespace RTKA.WFX

open Tm

theorem size_induction {P : Tm → Prop} (h : ∀ t, (∀ s, s.size < t.size → P s) → P t)
    (t : Tm) : P t := by
  have key : ∀ n, ∀ t : Tm, t.size < n → P t := by
    intro n
    induction n with
    | zero => intro t ht; exact absurd ht (Nat.not_lt_zero _)
    | succ n ih => intro t ht; exact h t (fun s hs => ih s (by omega))
  exact key _ t (Nat.lt_succ_self _)

/-- 部分項の大きさの比較 -/
macro "size_omega" : tactic =>
  `(tactic| first | (simp only [Tm.size]; omega) | (simp only [Tm.size] at *; omega))

inductive Hull (α : Tm) (X : Tm → Prop) : Tm → Prop where
  | zero : Hull α X .zero
  | one : Hull α X .one
  | K {n : Nat} (hn : 1 ≤ n) : Hull α X (.K n)
  | mem {β : Tm} (hX : X β) (hw : FXNF β) (hβ : Lt β α) : Hull α X β
  | plus {a b : Tm} (hw : FXNF (.plus a b)) (ha : Hull α X a) (hb : Hull α X b) :
      Hull α X (.plus a b)
  | om {a : Tm} (hw : FXNF (.Om a)) (ha : Hull α X a) : Hull α X (.Om a)
  | xi {n : Nat} {a : Tm} (hw : FXNF (.Xi n a)) (hα : Lt α (.K n)) (ha : Hull α X a) :
      Hull α X (.Xi n a)
  | psi {c a : Tm} (hw : FXNF (.Psi .zero (.Om c) a)) (hα : Lt α (.Om c))
      (hσ : Hull α X (.Om c)) (ha : Hull α X a) : Hull α X (.Psi .zero (.Om c) a)

def Rel (Y : Tm → Prop) (x y : Tm) : Prop := Y x ∧ Lt x y

def WPart (Y : Tm → Prop) (β : Tm) : Prop := Y β ∧ Acc (Rel Y) β

def Dist (X : Tm → Prop) : Prop :=
  (∀ β, X β → FXNF β) ∧
    ∀ α, FXNF α → (∃ δ, X δ ∧ Le α δ) →
      ∀ β, (WPart (Hull α X) β ∧ Lt β (nr α)) ↔ (X β ∧ Lt β (nr α))

def Wmax (β : Tm) : Prop := ∃ X, Dist X ∧ X β

def Good (α : Tm) : Prop := Hull α Wmax α ∧ ∀ β, Hull α Wmax β → Lt β α → Wmax β

/-! ### 生成集合 -/

theorem Hull.wf_of {α : Tm} {X : Tm → Prop} {β : Tm} (h : Hull α X β) : FXNF β := by
  cases h with
  | zero => exact FXNF.zero
  | one => exact FXNF.one
  | K hn => exact FXNF.K' hn
  | mem _ hw _ => exact hw
  | plus hw _ _ => exact hw
  | om hw _ => exact hw
  | xi hw _ _ => exact hw
  | psi hw _ _ _ => exact hw

/-- 生成集合の元を構成子ごとに写す（元と、添字の条件を与えて） -/
theorem Hull.map {α β : Tm} {X Y : Tm → Prop}
    (hmem : ∀ γ, X γ → FXNF γ → Lt γ α → Hull β Y γ)
    (hreg : ∀ σ, FXNF σ → IsReg σ → Lt α σ → Lt β σ) {γ : Tm}
    (h : Hull α X γ) : Hull β Y γ := by
  induction h with
  | zero => exact Hull.zero
  | one => exact Hull.one
  | K hn => exact Hull.K hn
  | mem hX hw hlt => exact hmem _ hX hw hlt
  | plus hw _ _ iha ihb => exact Hull.plus hw iha ihb
  | om hw _ iha => exact Hull.om hw iha
  | xi hw hα _ iha => exact Hull.xi hw (hreg _ (FXNF.K' hw.xi.1) (IsReg.K _) hα) iha
  | psi hw hα _ _ ihσ iha =>
    exact Hull.psi hw (hreg _ hw.psi'.2.1 (IsReg.FXNF_psi hw) hα) ihσ iha

theorem Hull.mono {α : Tm} {X Y : Tm → Prop}
    (h : ∀ γ, X γ → FXNF γ → Lt γ α → Y γ) {β : Tm} (hb : Hull α X β) :
    Hull α Y β :=
  hb.map (fun γ hX hw hlt => Hull.mem (h γ hX hw hlt) hw hlt) (fun _ _ _ h => h)

theorem Hull.congr {α : Tm} {X Y : Tm → Prop}
    (h : ∀ γ, FXNF γ → Lt γ α → (X γ ↔ Y γ)) (β : Tm) :
    Hull α X β ↔ Hull α Y β :=
  ⟨Hull.mono (fun γ hX hw hlt => (h γ hw hlt).mp hX),
    Hull.mono (fun γ hY hw hlt => (h γ hw hlt).mpr hY)⟩

/-- `α` より大きい正則項は `nr α` 未満の全ての項より大きい -/
theorem lt_of_lt_nr {α β σ : Tm} (wα : FXNF α) (wβ : FXNF β) (wσ : FXNF σ)
    (hσR : IsReg σ) (h1 : Lt α σ) (h2 : Lt β (nr α)) : Lt β σ :=
  lt_of_lt_of_leX wβ (nr_spec α wα).1 wσ h2 (nr_least α wα σ wσ hσR h1)

/-- 次の正則項までの範囲でパラメタを上げる -/
theorem Hull.raise {α β : Tm} {X : Tm → Prop} (wα : FXNF α) (wβ : FXNF β)
    (h1 : Lt α β) (h2 : Lt β (nr α)) {γ : Tm} (hγ : Hull α X γ) :
    Hull β X γ :=
  hγ.map (fun _ hX hw hlt => Hull.mem hX hw (lt_trans_FX hw wα wβ hlt h1))
    (fun _ wσ hσR hσ => lt_of_lt_nr wα wβ wσ hσR hσ h2)

theorem Hull.lower_aux {X : Tm → Prop} (HX : ∀ γ, X γ → Hull γ X γ) {α : Tm}
    (wα : FXNF α) : ∀ γ β : Tm, FXNF β → Le α β → Hull β X γ →
      Hull α X γ ∨ (X γ ∧ Lt γ β) := by
  intro γ
  induction γ using size_induction with
  | h γ ih =>
    intro β wβ hαβ h
    have conv : ∀ c : Tm, c.size < γ.size → Hull β X c → Hull α X c := by
      intro c hc hcβ
      have wc := hcβ.wf_of
      refine (ih c hc β wβ hαβ hcβ).elim id (fun ⟨hXc, _⟩ => ?_)
      by_cases hca : Lt c α
      · exact Hull.mem hXc wc hca
      · exact (ih c hc c wc (le_of_not_ltX wc wα hca) (HX c hXc)).resolve_right
          (fun ⟨_, h⟩ => Lt.irrefl _ h)
    cases h with
    | zero => exact Or.inl Hull.zero
    | one => exact Or.inl Hull.one
    | K hn => exact Or.inl (Hull.K hn)
    | mem hX _ hlt => exact Or.inr ⟨hX, hlt⟩
    | plus hw ha hb =>
      exact Or.inl (Hull.plus hw (conv _ (by size_omega) ha) (conv _ (by size_omega) hb))
    | om hw ha => exact Or.inl (Hull.om hw (conv _ (by size_omega) ha))
    | xi hw hβK ha =>
      exact Or.inl (Hull.xi hw (lt_of_le_of_ltX wα wβ (FXNF.K' hw.xi.1) hαβ hβK)
        (conv _ (by size_omega) ha))
    | psi hw hβσ hσ ha =>
      exact Or.inl (Hull.psi hw (lt_of_le_of_ltX wα wβ hw.psi'.2.1 hαβ hβσ)
        (conv _ (by size_omega) hσ) (conv _ (by size_omega) ha))

/-- `α ≤ β` なら `C^β(X) ⊆ C^α(X)`（`X` の各元が自分の生成集合に入るとき） -/
theorem Hull.lower {X : Tm → Prop} (HX : ∀ γ, X γ → Hull γ X γ) {α β : Tm}
    (wα : FXNF α) (wβ : FXNF β) (hαβ : Le α β) {γ : Tm} (h : Hull β X γ) :
    Hull α X γ := by
  have wγ := h.wf_of
  refine (Hull.lower_aux HX wα γ β wβ hαβ h).elim id (fun ⟨hX, _⟩ => ?_)
  by_cases hγα : Lt γ α
  · exact Hull.mem hX wγ hγα
  · exact (Hull.lower_aux HX wα γ γ wγ (le_of_not_ltX wγ wα hγα) (HX γ hX)).resolve_right
      (fun ⟨_, h⟩ => Lt.irrefl _ h)

theorem Hull.sub_of_lt_nr {X : Tm → Prop} (HX : ∀ γ, X γ → Hull γ X γ) {β γ : Tm}
    (wβ : FXNF β) (wγ : FXNF γ) (h : Lt γ (nr β)) {x : Tm}
    (hx : Hull β X x) : Hull γ X x := by
  rcases triX wγ wβ with h' | rfl | h'
  · exact Hull.lower HX wγ wβ (Or.inr h') hx
  · exact hx
  · exact Hull.raise wβ wγ h' h hx

/-! ### 整礎部分 -/

theorem acc_of_below {Y Z : Tm → Prop} (hY : ∀ x, Y x → FXNF x) :
    ∀ β : Tm, Acc (Rel Z) β → FXNF β → (∀ x, Y x → Lt x β → Z x) →
      Acc (Rel Y) β := by
  intro β hacc
  induction hacc with
  | intro β _ ih =>
    intro wβ hb
    refine Acc.intro β ?_
    intro x hx
    exact ih x ⟨hb x hx.1 hx.2, hx.2⟩ (hY x hx.1)
      (fun x' hx' hx'x => hb x' hx' (lt_trans_FX (hY x' hx') (hY x hx.1) wβ hx'x hx.2))

theorem acc_sub {Y Z : Tm → Prop} (h : ∀ x, Y x → Z x) :
    ∀ β : Tm, Acc (Rel Z) β → Acc (Rel Y) β := by
  intro β hacc
  induction hacc with
  | intro β _ ih =>
    exact Acc.intro β (fun x hx => ih x ⟨h x hx.1, hx.2⟩)

theorem WPart.congr {Y Z : Tm → Prop} (h : ∀ x, Y x ↔ Z x) (β : Tm) :
    WPart Y β ↔ WPart Z β :=
  Iff.intro (fun hb => ⟨(h β).mp hb.1, acc_sub (fun x hx => (h x).mpr hx) β hb.2⟩)
    (fun hb => ⟨(h β).mpr hb.1, acc_sub (fun x hx => (h x).mp hx) β hb.2⟩)

theorem WPart.down {Y : Tm → Prop} {β γ : Tm} (hβ : WPart Y β) (hγ : Y γ)
    (h : Lt γ β) : WPart Y γ :=
  ⟨hγ, hβ.2.inv ⟨hγ, h⟩⟩

/-! ### 区別集合 -/

theorem Dist.mem_wf {X : Tm → Prop} (hX : Dist X) {β : Tm} (h : X β) : FXNF β :=
  hX.1 β h

theorem Dist.self {X : Tm → Prop} (hX : Dist X) {γ : Tm} (hγ : X γ) :
    WPart (Hull γ X) γ := by
  have wγ := hX.mem_wf hγ
  exact ((hX.2 γ wγ ⟨γ, hγ, Or.inl rfl⟩ γ).mpr ⟨hγ, (nr_spec γ wγ).2.2⟩).1

theorem Dist.self_hull {X : Tm → Prop} (hX : Dist X) {γ : Tm} (hγ : X γ) : Hull γ X γ :=
  (hX.self hγ).1

theorem Dist.hull {X : Tm → Prop} (hX : Dist X) {γ : Tm} (hγ : X γ) {β : Tm}
    (wβ : FXNF β) : Hull β X γ := by
  have wγ := hX.mem_wf hγ
  by_cases h : Lt γ β
  · exact Hull.mem hγ wγ h
  · exact Hull.lower (fun _ h => hX.self_hull h) wβ wγ (le_of_not_ltX wγ wβ h)
      (hX.self_hull hγ)

theorem Dist.acc {X : Tm → Prop} (hX : Dist X) {δ : Tm} (hδ : X δ) : Acc (Rel X) δ := by
  have wδ := hX.mem_wf hδ
  exact acc_of_below hX.1 δ (hX.self hδ).2 wδ
    (fun x hx hxδ => Hull.mem hx (hX.mem_wf hx) hxδ)

/-- 区別集合どうしの比較（`X` と `Y` に沿った二重の帰納法） -/
theorem dist_claim {X Y : Tm → Prop} (hX : Dist X) (hY : Dist Y) :
    ∀ δ, X δ → (∃ ε, Y ε ∧ Le δ ε) → Y δ ∧ (∀ ε, Y ε → Lt ε δ → X ε) := by
  have key : ∀ δ, Acc (Rel X) δ → X δ → (∃ ε, Y ε ∧ Le δ ε) →
      Y δ ∧ (∀ ε, Y ε → Lt ε δ → X ε) := by
    intro δ hacc
    induction hacc with
    | intro δ _ ihX =>
      intro hδ hδY
      obtain ⟨ε₀, hε₀, hδε₀⟩ := hδY
      have wδ := hX.mem_wf hδ
      have wε₀ := hY.mem_wf hε₀
      have s1 : ∀ x, X x → Lt x δ → Y x := fun x hx hxδ =>
        (ihX x ⟨hx, hxδ⟩ hx
          ⟨ε₀, hε₀, Or.inr (lt_of_lt_of_leX (hX.mem_wf hx) wδ wε₀ hxδ hδε₀)⟩).1
      have key2 : ∀ ε, Acc (Rel Y) ε → Y ε → Lt ε δ → X ε := by
        intro ε hacc'
        induction hacc' with
        | intro ε _ ihY =>
          intro hε hεδ
          have wε := hY.mem_wf hε
          have agree : ∀ γ, FXNF γ → Lt γ ε → (X γ ↔ Y γ) := fun γ wγ hγε =>
            Iff.intro (fun hγ => s1 γ hγ (lt_trans_FX wγ wε wδ hγε hεδ))
              (fun hγ => ihY γ ⟨hγ, hγε⟩ hγ (lt_trans_FX wγ wε wδ hγε hεδ))
          have hxε : WPart (Hull ε X) ε :=
            (WPart.congr (Hull.congr agree) ε).mpr (hY.self hε)
          exact ((hX.2 ε wε ⟨δ, hδ, Or.inr hεδ⟩ ε).mp ⟨hxε, (nr_spec ε wε).2.2⟩).1
      have s2 : ∀ ε, Y ε → Lt ε δ → X ε := fun ε hε => key2 ε (hY.acc hε) hε
      refine ⟨?_, s2⟩
      have agree : ∀ γ, FXNF γ → Lt γ δ → (X γ ↔ Y γ) := fun γ _ hγδ =>
        Iff.intro (fun hγ => s1 γ hγ hγδ) (fun hγ => s2 γ hγ hγδ)
      have hyδ : WPart (Hull δ Y) δ := (WPart.congr (Hull.congr agree) δ).mp (hX.self hδ)
      exact ((hY.2 δ wδ ⟨ε₀, hε₀, hδε₀⟩ δ).mp ⟨hyδ, (nr_spec δ wδ).2.2⟩).1
  intro δ hδ
  exact key δ (hX.acc hδ) hδ

theorem dist_agree {X Y : Tm → Prop} (hX : Dist X) (hY : Dist Y) {α : Tm}
    (wα : FXNF α) (hαX : ∃ δ, X δ ∧ Le α δ) (hαY : ∃ ε, Y ε ∧ Le α ε) :
    ∀ β, Lt β (nr α) → (X β ↔ Y β) := by
  obtain ⟨δ, hδ, hαδ⟩ := hαX
  obtain ⟨ε, hε, hαε⟩ := hαY
  have agree : ∀ γ, FXNF γ → Lt γ α → (X γ ↔ Y γ) := fun γ wγ hγα =>
    Iff.intro
      (fun hγ => (dist_claim hX hY γ hγ
        ⟨ε, hε, Or.inr (lt_of_lt_of_leX wγ wα (hY.mem_wf hε) hγα hαε)⟩).1)
      (fun hγ => (dist_claim hY hX γ hγ
        ⟨δ, hδ, Or.inr (lt_of_lt_of_leX wγ wα (hX.mem_wf hδ) hγα hαδ)⟩).1)
  have hc := Hull.congr agree
  intro β hβ
  exact Iff.intro
    (fun hb => ((hY.2 α wα ⟨ε, hε, hαε⟩ β).mp
      ⟨(WPart.congr hc β).mp ((hX.2 α wα ⟨δ, hδ, hαδ⟩ β).mpr ⟨hb, hβ⟩).1, hβ⟩).1)
    (fun hb => ((hX.2 α wα ⟨δ, hδ, hαδ⟩ β).mp
      ⟨(WPart.congr hc β).mpr ((hY.2 α wα ⟨ε, hε, hαε⟩ β).mpr ⟨hb, hβ⟩).1, hβ⟩).1)

/-! ### 最大区別集合 -/

theorem wmax_dist : Dist Wmax := by
  refine ⟨fun β hβ => hβ.elim (fun X h => h.1.mem_wf h.2), ?_⟩
  intro α wα hα β
  obtain ⟨δ, ⟨X₀, hX₀, hδ⟩, hαδ⟩ := hα
  have hnα := nr_spec α wα
  have agreeW : ∀ γ, Lt γ (nr α) → (Wmax γ ↔ X₀ γ) := by
    intro γ hγ
    refine Iff.intro ?_ (fun h => ⟨X₀, hX₀, h⟩)
    intro hW
    obtain ⟨Y, hY, hγY⟩ := hW
    have wγ := hY.mem_wf hγY
    by_cases hγα : Lt γ α
    · exact (dist_agree hX₀ hY wγ
        ⟨δ, hδ, Or.inr (lt_of_lt_of_leX wγ wα (hX₀.mem_wf hδ) hγα hαδ)⟩
        ⟨γ, hγY, Or.inl rfl⟩ γ (nr_spec γ wγ).2.2).mpr hγY
    · exact (dist_agree hX₀ hY wα ⟨δ, hδ, hαδ⟩ ⟨γ, hγY, le_of_not_ltX wγ wα hγα⟩ γ hγ).mpr hγY
  have hc : ∀ x, Hull α Wmax x ↔ Hull α X₀ x :=
    Hull.congr (fun γ wγ hγα => agreeW γ (lt_trans_FX wγ wα hnα.1 hγα hnα.2.2))
  rw [WPart.congr hc β, hX₀.2 α wα ⟨δ, hδ, hαδ⟩ β]
  exact Iff.intro (fun h => ⟨(agreeW β h.2).mpr h.1, h.2⟩)
    (fun h => ⟨(agreeW β h.2).mp h.1, h.2⟩)

theorem wmax_wf {β : Tm} (h : Wmax β) : FXNF β := wmax_dist.mem_wf h

theorem wmax_self {γ : Tm} (h : Wmax γ) : WPart (Hull γ Wmax) γ := wmax_dist.self h

theorem wmax_hull {γ : Tm} (h : Wmax γ) {β : Tm} (wβ : FXNF β) : Hull β Wmax γ :=
  wmax_dist.hull h wβ

theorem wmax_acc {δ : Tm} (h : Wmax δ) : Acc (Rel Wmax) δ := wmax_dist.acc h

theorem HW : ∀ γ, Wmax γ → Hull γ Wmax γ := fun _ h => wmax_dist.self_hull h

/-- `C^β(Wmax)` の元で、`β⁺` 未満の `Wmax` の元以下のものは `Wmax` に入る -/
theorem wmax_bounded {α β δ : Tm} (wβ : FXNF β) (hα : Hull β Wmax α) (hδ : Wmax δ)
    (hαδ : Le α δ) (hδβ : Lt δ (nr β)) : Wmax α := by
  have wδ := wmax_wf hδ
  have wα := hα.wf_of
  have hα' : Hull δ Wmax α := Hull.sub_of_lt_nr HW wβ wδ hδβ hα
  rcases hαδ with e | hlt
  · rw [e]
    exact hδ
  · have hw := WPart.down (wmax_self hδ) hα' hlt
    exact ((wmax_dist.2 δ wδ ⟨δ, hδ, Or.inl rfl⟩ α).mp
      ⟨hw, lt_trans_FX wα wδ (nr_spec δ wδ).1 hlt (nr_spec δ wδ).2.2⟩).1

theorem wmax_good {γ : Tm} (h : Wmax γ) : Good γ :=
  ⟨HW γ h, fun _ hβ hlt =>
    wmax_bounded (wmax_wf h) hβ h (Or.inr hlt) (nr_spec _ (wmax_wf h)).2.2⟩

theorem acc_hull_of_wmax {μ δ : Tm} (hδ : Wmax δ)
    (h : ∀ x, Hull μ Wmax x → Lt x δ → Wmax x) : Acc (Rel (Hull μ Wmax)) δ :=
  acc_of_below (fun _ hx => hx.wf_of) δ (wmax_acc hδ) (wmax_wf hδ) h

/-! ### `Wmax` の拡張 -/

/-- 拡張の仮定：`γ⁺ ≤ α` の `C^γ(Wmax)` の整礎部分（`γ⁺` 未満）は `Wmax` に入る -/
def Hyp (α : Tm) : Prop := ∀ γ, FXNF γ → Le (nr γ) α → ∀ β,
  WPart (Hull γ Wmax) β → Lt β (nr γ) → Wmax β

def Ext (α β : Tm) : Prop := WPart (Hull α Wmax) β ∧ Lt β (nr α)

theorem wmax_of_good_hyp {α : Tm} (hG : Good α) (hH : Hyp α) : Wmax α := by
  have wα := hG.1.wf_of
  have hnα := nr_spec α wα
  have accα : ∀ x, Wmax x → Lt x α → Acc (Rel (Hull α Wmax)) x := fun x hx hxα =>
    acc_hull_of_wmax hx (fun x' hx' hx'x =>
      hG.2 x' hx' (lt_trans_FX hx'.wf_of (wmax_wf hx) wα hx'x hxα))
  have agree : ∀ β, Lt β α → (Ext α β ↔ Wmax β) := fun β hβα =>
    ⟨fun hb => hG.2 β hb.1.1 hβα, fun hb => ⟨⟨Hull.mem hb (wmax_wf hb) hβα, accα β hb hβα⟩,
      lt_trans_FX (wmax_wf hb) wα hnα.1 hβα hnα.2.2⟩⟩
  have hYwf : ∀ β, Ext α β → FXNF β := fun β hb => hb.1.1.wf_of
  refine ⟨Ext α, ⟨hYwf, ?_⟩,
    ⟨⟨hG.1, Acc.intro α (fun x hx => accα x (hG.2 x hx.1 hx.2) hx.2)⟩, hnα.2.2⟩⟩
  intro γ wγ ⟨ε, hε, hγε⟩ β
  have hnγ := nr_spec γ wγ
  have hnγnα := nr_least γ wγ (nr α) hnα.1 hnα.2.1
    (lt_of_le_of_ltX wγ (hYwf ε hε) hnα.1 hγε hε.2)
  have split : Le (nr γ) α ∨ Lt α (nr γ) :=
    (triX hnγ.1 wα).elim (fun h => Or.inl (Or.inr h))
      (fun h => h.elim (fun e => Or.inl (Or.inl e)) Or.inr)
  rcases split with hle | hgt
  · have hγα : Lt γ α := lt_of_lt_of_leX wγ hnγ.1 wα hnγ.2.2 hle
    rw [WPart.congr (Hull.congr (fun x wx hxγ => agree x (lt_trans_FX wx wγ wα hxγ hγα))) β]
    constructor
    · intro hb
      exact ⟨(agree β (lt_of_lt_of_leX hb.1.1.wf_of hnγ.1 wα hb.2 hle)).mpr
        (hH γ wγ hle β hb.1 hb.2), hb.2⟩
    · intro hb
      have wb := hYwf β hb.1
      have hbW := (agree β (lt_of_lt_of_leX wb hnγ.1 wα hb.2 hle)).mp hb.1
      refine ⟨?_, hb.2⟩
      by_cases hβγ : Lt β γ
      · exact ⟨Hull.mem hbW wb hβγ, acc_hull_of_wmax hbW (fun x hx hxβ => wmax_bounded wb
          (Hull.lower HW wb wγ (Or.inr hβγ) hx) hbW (Or.inr hxβ) (nr_spec β wb).2.2)⟩
      · exact ((wmax_dist.2 γ wγ ⟨β, hbW, le_of_not_ltX wb wγ hβγ⟩ β).mpr ⟨hbW, hb.2⟩).1
  · have heqn : nr γ = nr α :=
      le_antisymmX hnγ.1 hnα.1 hnγnα (nr_least α wα (nr γ) hnγ.1 hnγ.2.1 hgt)
    have hc : ∀ x, Hull γ (Ext α) x ↔ Hull α Wmax x := by
      rcases triX wγ wα with hγα | rfl | hαγ
      · intro x
        rw [Hull.congr (fun x wx hxγ => agree x (lt_trans_FX wx wγ wα hxγ hγα)) x]
        exact ⟨Hull.raise wγ wα hγα hgt, Hull.lower HW wγ wα (Or.inr hγα)⟩
      · exact Hull.congr (fun x _ hxγ => agree x hxγ)
      · intro x
        exact ⟨Hull.map (fun _ hY _ _ => hY.1.1) (fun _ wσ _ h => lt_trans_FX wα wγ wσ hαγ h),
          Hull.map (fun _ hW hw hlt => Hull.mem ((agree _ hlt).mpr hW) hw
            (lt_trans_FX hw wα wγ hlt hαγ))
            (fun _ wσ hσR h => lt_of_lt_nr wα wγ wσ hσR h (by rw [← heqn]; exact hnγ.2.2))⟩
    rw [WPart.congr hc β, heqn]
    exact ⟨fun hb => ⟨⟨hb.1, hb.2⟩, hb.2⟩, fun hb => ⟨hb.1.1, hb.2⟩⟩

end RTKA.WFX
