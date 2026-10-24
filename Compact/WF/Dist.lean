import Compact.WF.F0Int

/-! 区別集合（Buchholz）の一般論（断片 `F0`）。

区間 `[κ, κ^+)` ごとに「その区間で到達可能と確かめた項」を積み上げた集合を区別集合と呼ぶ。

* `CS X κ`：`C^κ(X)`。`X ∩ κ` と定数から `+`・`Ω`・`Ψ_σ`（`σ > κ`）で生成される項。
* `WC X κ`：`C^κ(X)` の中で到達可能な項。
* `D X`：`X` は区別集合。`X` の元以下の各基数 `κ` について、`X` の区間 `κ^+` 未満の部分は
  `WC X κ` の区間 `κ^+` 未満の部分と一致する（`Bl κ t` が `t < κ^+`）。
* `W`：区別集合の合併。`D_W` で `W` 自身も区別集合、`acc_W` で `W` の元は `W` の中で到達可能。
* `one_step`：区別集合 `X` を基数 `α` の区間まで延ばす補題（Arai の Prop. 6.36 にあたる）。

Arai（arXiv 1506.05280）の §6 を手本にした。ただし条件を基数 `κ` の所でだけ課し、
`F0` の区間の構造（`F0Int.lean`）を使って議論を簡単にしている。 -/

namespace RTKA

open Tm

/-! ### 生成集合 `C^κ(X)` -/

/-- `t ∈ C^κ(X)`：`X ∩ κ` と定数から `+`・`Ω`・`Ψ_σ`（`σ > κ`）で生成される -/
def CS (X : Tm → Prop) (κ : Tm) : Tm → Prop
  | .zero => True
  | .one => True
  | .K _ => True
  | .plus a b => (Lt (.plus a b) κ ∧ X (.plus a b)) ∨ (CS X κ a ∧ CS X κ b)
  | .Om a => (Lt (.Om a) κ ∧ X (.Om a)) ∨ CS X κ a
  | .Xi n a => Lt (.Xi n a) κ ∧ X (.Xi n a)
  | .Psi s p a => (Lt (.Psi s p a) κ ∧ X (.Psi s p a)) ∨
      (Lt κ p ∧ CS X κ s ∧ CS X κ p ∧ CS X κ a)

theorem CS.base {X : Tm → Prop} {κ : Tm} : ∀ {t : Tm}, Lt t κ → X t → CS X κ t
  | .zero, _, _ | .one, _, _ | .K _, _, _ => trivial
  | .plus _ _, h, hx | .Om _, h, hx | .Psi _ _ _, h, hx => Or.inl ⟨h, hx⟩
  | .Xi _ _, h, hx => ⟨h, hx⟩

/-- `C^κ(X)` は `X ∩ κ` だけで決まる -/
theorem CS_congr {X Y : Tm → Prop} {κ : Tm} (h : ∀ t, Lt t κ → (X t ↔ Y t)) :
    ∀ t, CS X κ t ↔ CS Y κ t
  | .zero | .one | .K _ => Iff.rfl
  | .plus a b => by
    simp only [CS]
    rw [CS_congr h a, CS_congr h b]
    constructor
    · rintro (⟨h1, h2⟩ | h3)
      · exact Or.inl ⟨h1, (h _ h1).mp h2⟩
      · exact Or.inr h3
    · rintro (⟨h1, h2⟩ | h3)
      · exact Or.inl ⟨h1, (h _ h1).mpr h2⟩
      · exact Or.inr h3
  | .Om a => by
    simp only [CS]
    rw [CS_congr h a]
    constructor
    · rintro (⟨h1, h2⟩ | h3)
      · exact Or.inl ⟨h1, (h _ h1).mp h2⟩
      · exact Or.inr h3
    · rintro (⟨h1, h2⟩ | h3)
      · exact Or.inl ⟨h1, (h _ h1).mpr h2⟩
      · exact Or.inr h3
  | .Xi n a => by
    simp only [CS]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, (h _ h1).mp h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (h _ h1).mpr h2⟩
  | .Psi s p a => by
    simp only [CS]
    rw [CS_congr h s, CS_congr h p, CS_congr h a]
    constructor
    · rintro (⟨h1, h2⟩ | h3)
      · exact Or.inl ⟨h1, (h _ h1).mp h2⟩
      · exact Or.inr h3
    · rintro (⟨h1, h2⟩ | h3)
      · exact Or.inl ⟨h1, (h _ h1).mpr h2⟩
      · exact Or.inr h3

/-- `Ω_c > κ` なら `Ω_c ∈ C^κ(X)` は `c ∈ C^κ(X)` -/
theorem CS_om_iff {X : Tm → Prop} {κ c : Tm} (hκ : F0NF κ) (hc : F0NF (.Om c)) (h : Lt κ (.Om c)) :
    CS X κ (.Om c) ↔ CS X κ c := by
  simp only [CS]
  constructor
  · rintro (⟨h1, -⟩ | h2)
    · exact absurd h (Lt.asymm hc hκ h1)
    · exact h2
  · exact Or.inr

/-- `κ ≤ t` なら `t ∈ C^κ(X)` は生成されたもの -/
theorem CS_plus_of_le {X : Tm → Prop} {κ a b : Tm} (hκ : F0NF κ) (ht : F0NF (.plus a b))
    (hle : Le κ (.plus a b)) (h : CS X κ (.plus a b)) : CS X κ a ∧ CS X κ b := by
  rcases h with ⟨h1, -⟩ | h2
  · exact absurd h1 (not_lt_of_le hκ ht hle)
  · exact h2

theorem CS_om_of_le {X : Tm → Prop} {κ a : Tm} (hκ : F0NF κ) (ht : F0NF (.Om a))
    (hle : Le κ (.Om a)) (h : CS X κ (.Om a)) : CS X κ a := by
  rcases h with ⟨h1, -⟩ | h2
  · exact absurd h1 (not_lt_of_le hκ ht hle)
  · exact h2

theorem CS_psi_of_le {X : Tm → Prop} {κ s p a : Tm} (hκ : F0NF κ) (ht : F0NF (.Psi s p a))
    (hle : Le κ (.Psi s p a)) (h : CS X κ (.Psi s p a)) :
    Lt κ p ∧ CS X κ s ∧ CS X κ p ∧ CS X κ a := by
  rcases h with ⟨h1, -⟩ | h2
  · exact absurd h1 (not_lt_of_le hκ ht hle)
  · exact h2

/-! ### 到達可能部分 -/

/-- `C^κ(X)` の中の `<` -/
def RC (X : Tm → Prop) (κ : Tm) (u v : Tm) : Prop := F0NF u ∧ CS X κ u ∧ Lt u v

/-- `C^κ(X)` の中で到達可能 -/
def WC (X : Tm → Prop) (κ : Tm) (t : Tm) : Prop := F0NF t ∧ CS X κ t ∧ Acc (RC X κ) t

/-- `X` の中の `<` -/
def RX (X : Tm → Prop) (u v : Tm) : Prop := X u ∧ Lt u v

/-- `t < κ^+`（`t` の区間が `κ` の区間以下） -/
def Bl (κ t : Tm) : Prop := Le (ix t) (ix κ)

/-- `κ ≤ X`（`X` に `κ` 以上の元がある） -/
def Ge (X : Tm → Prop) (κ : Tm) : Prop := ∃ x, X x ∧ Le κ x

theorem WC_congr {X Y : Tm → Prop} {κ : Tm} (h : ∀ t, Lt t κ → (X t ↔ Y t)) (t : Tm) :
    WC X κ t ↔ WC Y κ t := by
  have e : RC X κ = RC Y κ := by
    funext u v
    unfold RC
    rw [CS_congr h u]
  unfold WC
  rw [e, CS_congr h t]

/-- 到達可能性の移し替え -/
theorem acc_transfer {R S : Tm → Tm → Prop} (P : Tm → Prop) (hP : ∀ u v, S u v → P v → P u)
    (hRS : ∀ u v, S u v → P v → R u v) : ∀ a, Acc R a → P a → Acc S a := by
  intro a h
  induction h with
  | intro x _ ih =>
    intro hx
    exact Acc.intro x (fun u hu => ih u (hRS u x hu hx) (hP u x hu hx))

theorem Bl.of_le {κ s t : Tm} (hs : F0NF s) (ht : F0NF t) (hκ : F0NF κ) (h : Le s t) (hb : Bl κ t) :
    Bl κ s :=
  Le.trans (ix_F0NF hs) (ix_F0NF ht) (ix_F0NF hκ) (ix_le_ix' hs ht h) hb

theorem Bl.of_lt {κ t : Tm} (hκ : F0NF κ) (ht : F0NF t) (h : Lt t κ) : Bl κ t :=
  ix_le_ix ht hκ h

theorem Bl.self {t : Tm} : Bl t t := Le.refl _

/-! ### 区別集合 -/

/-- `X` は区別集合 -/
def D (X : Tm → Prop) : Prop :=
  (∀ t, X t → F0NF t) ∧
    ∀ κ, isCard κ → Ge X κ → ∀ t, F0NF t → Bl κ t → (X t ↔ WC X κ t)

theorem Ge.of_mem {X : Tm → Prop} {x : Tm} (hx : X x) : Ge X x := ⟨x, hx, Le.refl _⟩

theorem Ge.of_le {X : Tm → Prop} {κ μ : Tm} (hD : ∀ t, X t → F0NF t) (hκ : F0NF κ) (hμ : F0NF μ)
    (h : Le κ μ) (hg : Ge X μ) : Ge X κ := by
  obtain ⟨x, hx, hle⟩ := hg
  exact ⟨x, hx, Le.trans hκ hμ (hD x hx) h hle⟩

/-- 区別集合の元は区別集合の中で到達可能 -/
theorem D.acc {X : Tm → Prop} (hD : D X) {x : Tm} (hx : X x) : Acc (RX X) x := by
  have hxF := hD.1 x hx
  obtain ⟨hκ, hix⟩ := bot_card hxF
  have hW := (hD.2 (bot x) hκ ⟨x, hx, bot_le hxF⟩ x hxF (by unfold Bl; rw [hix]; exact Le.refl _)).mp hx
  refine acc_transfer (fun v => F0NF v ∧ Le v x) ?_ ?_ x hW.2.2 ⟨hxF, Le.refl _⟩
  · rintro u v ⟨hu, huv⟩ ⟨hv, hvx⟩
    exact ⟨hD.1 u hu, Or.inr (lt_of_lt_of_le (hD.1 u hu) hv hxF huv hvx)⟩
  · rintro u v ⟨hu, huv⟩ ⟨hv, hvx⟩
    have huF := hD.1 u hu
    have hux : Le u x := Or.inr (lt_of_lt_of_le huF hv hxF huv hvx)
    have hbl : Bl (bot x) u := by
      unfold Bl
      rw [hix]
      exact ix_le_ix' huF hxF hux
    exact ⟨huF, ((hD.2 (bot x) hκ ⟨x, hx, bot_le hxF⟩ u huF hbl).mp hu).2.1, huv⟩

/-- 二つの区別集合の合併の中の `<` -/
def RU (X Y : Tm → Prop) (u v : Tm) : Prop := (X u ∨ Y u) ∧ Lt u v

theorem union_acc_aux {X Y : Tm → Prop} (hX : D X) (hY : D Y) :
    ∀ x, Acc (RX X) x → X x → ∀ w, (X w ∨ Y w) → Le w x → Acc (RU X Y) w := by
  intro x hacc
  induction hacc with
  | intro x _ ihx =>
    intro hxX
    have hxF := hX.1 x hxX
    have hYle : ∀ w, Acc (RX Y) w → Y w → Le w x → Acc (RU X Y) w := by
      intro w hw
      induction hw with
      | intro w _ ihw =>
        intro hwY hwx
        have hwF := hY.1 w hwY
        refine Acc.intro w (fun v hv => ?_)
        obtain ⟨hv, hvw⟩ := hv
        have hvF : F0NF v := hv.elim (hX.1 v) (hY.1 v)
        have hvx : Lt v x := lt_of_lt_of_le hvF hwF hxF hvw hwx
        rcases hv with hv | hv
        · exact ihx v ⟨hv, hvx⟩ hv v (Or.inl hv) (Le.refl _)
        · exact ihw v ⟨hv, hvw⟩ hv (Or.inr hvx)
    intro w hw hwx
    rcases hwx with rfl | e
    · refine Acc.intro _ (fun v hv => ?_)
      obtain ⟨hv, hvw⟩ := hv
      rcases hv with hv | hv
      · exact ihx v ⟨hv, hvw⟩ hv v (Or.inl hv) (Le.refl _)
      · exact hYle v (hY.acc hv) hv (Or.inr hvw)
    · rcases hw with hw | hw
      · exact ihx w ⟨hw, e⟩ hw w (Or.inl hw) (Le.refl _)
      · exact hYle w (hY.acc hw) hw (Or.inr e)

/-- 二つの区別集合の合併の元は合併の中で到達可能 -/
theorem union_acc {X Y : Tm → Prop} (hX : D X) (hY : D Y) :
    ∀ u, (X u ∨ Y u) → Acc (RU X Y) u := by
  intro u hu
  rcases hu with hu | hu
  · exact union_acc_aux hX hY u (hX.acc hu) hu u (Or.inl hu) (Le.refl _)
  · have : ∀ w, Acc (RX Y) w → Y w → Acc (RU X Y) w := by
      intro w hw
      induction hw with
      | intro w _ ihw =>
        intro hwY
        refine Acc.intro w (fun v hv => ?_)
        obtain ⟨hv, hvw⟩ := hv
        rcases hv with hv | hv
        · exact union_acc_aux hX hY v (hX.acc hv) hv v (Or.inl hv) (Le.refl _)
        · exact ihw v ⟨hv, hvw⟩ hv
    exact this u (hY.acc hu) hu

/-- `X ∩ bot u = Y ∩ bot u` なら、`u ∈ X` で `u ≤ Y` のとき `u ∈ Y` -/
theorem D.step {X Y : Tm → Prop} (hX : D X) (hY : D Y) {u : Tm} (hu : X u) (hg : Ge Y u)
    (hag : ∀ t, Lt t (bot u) → (X t ↔ Y t)) : Y u := by
  have huF := hX.1 u hu
  obtain ⟨hκ, hix⟩ := bot_card huF
  have hbl : Bl (bot u) u := by unfold Bl; rw [hix]; exact Le.refl _
  have h1 := (hX.2 (bot u) hκ ⟨u, hu, bot_le huF⟩ u huF hbl).mp hu
  have hgY : Ge Y (bot u) := Ge.of_le hY.1 hκ.1 huF (bot_le huF) hg
  exact (hY.2 (bot u) hκ hgY u huF hbl).mpr ((WC_congr hag u).mp h1)

theorem D.compare_aux {X Y : Tm → Prop} (hX : D X) (hY : D Y) :
    ∀ u, Acc (RU X Y) u → (X u ∨ Y u) → (X u → Ge Y u → Y u) ∧ (Y u → Ge X u → X u) := by
  intro u hacc
  induction hacc with
  | intro u _ ih =>
    intro hu
    have huF : F0NF u := hu.elim (hX.1 u) (hY.1 u)
    have hbu := bot_le huF
    have hbF := bot_F0NF huF
    have hag : Ge X u → Ge Y u → ∀ t, Lt t (bot u) → (X t ↔ Y t) := by
      intro gX gY t ht
      constructor
      · intro htX
        have htF := hX.1 t htX
        have htu : Lt t u := lt_of_lt_of_le htF hbF huF ht hbu
        exact (ih t ⟨Or.inl htX, htu⟩ (Or.inl htX)).1 htX (Ge.of_le hY.1 htF huF (Or.inr htu) gY)
      · intro htY
        have htF := hY.1 t htY
        have htu : Lt t u := lt_of_lt_of_le htF hbF huF ht hbu
        exact (ih t ⟨Or.inr htY, htu⟩ (Or.inr htY)).2 htY (Ge.of_le hX.1 htF huF (Or.inr htu) gX)
    exact ⟨fun hxu gY => D.step hX hY hxu gY (hag (Ge.of_mem hxu) gY),
      fun hyu gX => D.step hY hX hyu gX (fun t ht => (hag gX (Ge.of_mem hyu) t ht).symm)⟩

/-- 比較可能性：二つの区別集合は、両方に `z` 以上の元があれば `z` 未満で一致する -/
theorem D.agree {X Y : Tm → Prop} (hX : D X) (hY : D Y) {z : Tm} (hz : F0NF z)
    (gX : Ge X z) (gY : Ge Y z) : ∀ t, Lt t z → (X t ↔ Y t) := by
  intro t ht
  constructor
  · intro htX
    have htF := hX.1 t htX
    exact (D.compare_aux hX hY t (union_acc hX hY t (Or.inl htX)) (Or.inl htX)).1 htX
      (Ge.of_le hY.1 htF hz (Or.inr ht) gY)
  · intro htY
    have htF := hY.1 t htY
    exact (D.compare_aux hX hY t (union_acc hX hY t (Or.inr htY)) (Or.inr htY)).2 htY
      (Ge.of_le hX.1 htF hz (Or.inr ht) gX)

/-- 二つの区別集合は、両方に基数 `κ` 以上の元があれば `κ^+` 未満で一致する -/
theorem D.agreeBl {X Y : Tm → Prop} (hX : D X) (hY : D Y) {κ : Tm} (hκ : isCard κ)
    (gX : Ge X κ) (gY : Ge Y κ) : ∀ t, F0NF t → Bl κ t → (X t ↔ Y t) := by
  intro t ht hb
  rw [hX.2 κ hκ gX t ht hb, hY.2 κ hκ gY t ht hb]
  exact WC_congr (D.agree hX hY hκ.1 gX gY) t

/-! ### 最大の区別集合 -/

/-- 区別集合の合併 -/
def W (t : Tm) : Prop := ∃ X, D X ∧ X t

theorem W.nf {t : Tm} (h : W t) : F0NF t := by
  obtain ⟨X, hX, ht⟩ := h
  exact hX.1 t ht

theorem W.of_D {X : Tm → Prop} (hX : D X) {t : Tm} (h : X t) : W t := ⟨X, hX, h⟩

/-- `W` は区別集合 -/
theorem D_W : D W := by
  refine ⟨fun t h => h.nf, ?_⟩
  rintro κ hκ ⟨w, ⟨X0, hX0, hw⟩, hκw⟩ t ht hb
  have g0 : Ge X0 κ := ⟨w, hw, hκw⟩
  have hag : ∀ s, F0NF s → Bl κ s → (W s ↔ X0 s) := by
    intro s hs hbs
    constructor
    · rintro ⟨Z, hZ, hsZ⟩
      obtain ⟨hμ, hix⟩ := bot_card hs
      have hμκ : Le (bot s) κ := (card_le_iff hμ hκ).mpr (by rw [hix]; exact hbs)
      have gZ : Ge Z (bot s) := ⟨s, hsZ, bot_le hs⟩
      have g0' : Ge X0 (bot s) := Ge.of_le hX0.1 hμ.1 hκ.1 hμκ g0
      exact (D.agreeBl hX0 hZ hμ g0' gZ s hs (by unfold Bl; rw [hix]; exact Le.refl _)).mpr hsZ
    · intro h
      exact ⟨X0, hX0, h⟩
  have hag' : ∀ s, Lt s κ → (W s ↔ X0 s) := by
    intro s hs
    constructor
    · intro h
      exact (hag s h.nf (Bl.of_lt hκ.1 h.nf hs)).mp h
    · intro h
      exact ⟨X0, hX0, h⟩
  rw [hag t ht hb, hX0.2 κ hκ g0 t ht hb]
  exact (WC_congr hag' t).symm

/-- `W` の元は `W` の中で到達可能 -/
theorem acc_W {x : Tm} (h : W x) : Acc (RX W) x := D_W.acc h

/-! ### 区別集合の性質 -/

/-- `κ ≤ μ` で `X ∩ μ` が `C^κ(X)` に入るなら `C^μ(X) ⊆ C^κ(X)` -/
theorem CS_mono_down {X : Tm → Prop} {κ μ : Tm} (hκ : F0NF κ) (hμ : F0NF μ) (hle : Le κ μ)
    (h : ∀ v, Lt v μ → X v → CS X κ v) : ∀ t, F0NF t → CS X μ t → CS X κ t
  | .zero, _, _ | .one, _, _ | .K _, _, _ => trivial
  | .plus a b, ht, hc => by
    rcases hc with ⟨h1, h2⟩ | ⟨ha, hb⟩
    · exact h _ h1 h2
    · exact Or.inr ⟨CS_mono_down hκ hμ hle h a ht.plus.1 ha,
        CS_mono_down hκ hμ hle h b ht.plus.2.1 hb⟩
  | .Om a, ht, hc => by
    rcases hc with ⟨h1, h2⟩ | ha
    · exact h _ h1 h2
    · exact Or.inr (CS_mono_down hκ hμ hle h a ht.om.1 ha)
  | .Xi _ _, ht, _ => (ht.not_xi).elim
  | .Psi s p a, ht, hc => by
    obtain ⟨rfl, c, rfl, hcF, -, haF, -⟩ := ht.psi
    rcases hc with ⟨h1, h2⟩ | ⟨hp, -, hpc, ha⟩
    · exact h _ h1 h2
    · exact Or.inr ⟨lt_of_le_of_lt hκ hμ hcF hle hp, trivial,
        CS_mono_down hκ hμ hle h _ hcF hpc, CS_mono_down hκ hμ hle h a haF ha⟩

theorem D.mem_CS_aux {X : Tm → Prop} (hD : D X) :
    ∀ x, Acc (RX X) x → X x → ∀ κ, isCard κ → CS X κ x := by
  intro x hacc
  induction hacc with
  | intro x _ ih =>
    intro hx κ hκ
    have hxF := hD.1 x hx
    rcases le_or_lt hκ.1 hxF with hle | hlt
    · obtain ⟨hμ, hix⟩ := bot_card hxF
      have hbl : Bl (bot x) x := by unfold Bl; rw [hix]; exact Le.refl _
      have h1 := (hD.2 (bot x) hμ ⟨x, hx, bot_le hxF⟩ x hxF hbl).mp hx
      refine CS_mono_down hκ.1 hμ.1 (card_le_bot hκ hxF hle) ?_ x hxF h1.2.1
      intro v hv hvX
      exact ih v ⟨hvX, lt_of_lt_of_le (hD.1 v hvX) hμ.1 hxF hv (bot_le hxF)⟩ hvX κ hκ
    · exact CS.base hlt hx

/-- 区別集合の元は全ての基数 `κ` について `C^κ(X)` に入る -/
theorem D.mem_CS {X : Tm → Prop} (hD : D X) {x : Tm} (hx : X x) {κ : Tm} (hκ : isCard κ) :
    CS X κ x :=
  D.mem_CS_aux hD x (hD.acc hx) hx κ hκ

/-- 区別集合の元 `w` より小さい `C^{bot w}(X)` の元は `X` に入る -/
theorem D.mem_of_CS_lt {X : Tm → Prop} (hD : D X) {w u : Tm} (hw : X w) (hu : F0NF u)
    (hc : CS X (bot w) u) (hlt : Lt u w) : X u := by
  have hwF := hD.1 w hw
  obtain ⟨hμ, hix⟩ := bot_card hwF
  have g : Ge X (bot w) := ⟨w, hw, bot_le hwF⟩
  have h1 := (hD.2 (bot w) hμ g w hwF (by unfold Bl; rw [hix]; exact Le.refl _)).mp hw
  have hbl : Bl (bot w) u := by unfold Bl; rw [hix]; exact ix_le_ix hu hwF hlt
  exact (hD.2 (bot w) hμ g u hu hbl).mpr ⟨hu, hc, h1.2.2.inv ⟨hu, hc, hlt⟩⟩

/-! ### 1 段の拡張 -/

/-- 区別集合 `X` を基数 `α` の区間まで延ばす：`α ∈ C^α(X)`、`C^α(X) ∩ α ⊆ X`、
    `α` より下の基数 `μ` で `X` が `μ^+` 未満の到達可能部分と一致するなら、
    `Y = WC X α ∩ α^+` は区別集合で `α` を含む（Arai の Prop. 6.36） -/
theorem one_step {X : Tm → Prop} {α : Tm} (hD : D X) (hα : isCard α)
    (G1 : CS X α α) (G2 : ∀ t, F0NF t → Lt t α → CS X α t → X t)
    (GC : ∀ μ, isCard μ → Lt μ α → ∀ t, F0NF t → Bl μ t → (X t ↔ WC X μ t)) :
    D (fun t => Bl α t ∧ WC X α t) ∧ WC X α α := by
  have hαF := hα.1
  have accX : ∀ t, X t → Lt t α → Acc (RC X α) t := by
    intro t ht hlt
    have htF := hD.1 t ht
    refine acc_transfer (fun v => F0NF v ∧ Le v t) ?_ ?_ t (hD.acc ht) ⟨htF, Le.refl _⟩
    · rintro u v ⟨hu, -, huv⟩ ⟨hv, hvt⟩
      exact ⟨hu, Or.inr (lt_of_lt_of_le hu hv htF huv hvt)⟩
    · rintro u v ⟨hu, hcu, huv⟩ ⟨hv, hvt⟩
      have hut : Lt u t := lt_of_lt_of_le hu hv htF huv hvt
      exact ⟨G2 u hu (lt_trans_F0 hu htF hαF hut hlt) hcu, huv⟩
  have YX : ∀ t, Lt t α → ((Bl α t ∧ WC X α t) ↔ X t) := by
    intro t hlt
    constructor
    · rintro ⟨-, htF, hc, -⟩
      exact G2 t htF hlt hc
    · intro ht
      have htF := hD.1 t ht
      exact ⟨Bl.of_lt hαF htF hlt, htF, CS.base hlt ht, accX t ht hlt⟩
  have hWα : WC X α α :=
    ⟨hαF, G1, Acc.intro α (fun u ⟨hu, hcu, hlt⟩ => accX u (G2 u hu hlt hcu) hlt)⟩
  refine ⟨⟨fun t ht => ht.2.1, ?_⟩, hWα⟩
  rintro μ hμ ⟨y, ⟨hyα, hyW⟩, hμy⟩ t ht hb
  have hyF := hyW.1
  have hμα : Le μ α := by
    rw [card_le_iff hμ hα]
    exact Le.trans (ix_F0NF hμ.1) (ix_F0NF hyF) (ix_F0NF hαF) (ix_le_ix' hμ.1 hyF hμy) hyα
  rcases hμα with e | hlt
  · subst e
    rw [WC_congr YX t]
    exact ⟨fun h => h.2, fun h => ⟨hb, h⟩⟩
  · have htα : Lt t α := by
      apply ix_lt_ix ht hαF
      exact lt_of_le_of_lt (ix_F0NF ht) (ix_F0NF hμ.1) (ix_F0NF hαF) hb
        ((card_lt_iff hμ hα).mp hlt)
    have hag : ∀ s, Lt s μ → ((Bl α s ∧ WC X α s) ↔ X s) := by
      intro s hs
      constructor
      · intro h
        exact (YX s (lt_trans_F0 h.2.1 hμ.1 hαF hs hlt)).mp h
      · intro h
        exact (YX s (lt_trans_F0 (hD.1 s h) hμ.1 hαF hs hlt)).mpr h
    show (Bl α t ∧ WC X α t) ↔ WC (fun t => Bl α t ∧ WC X α t) μ t
    rw [YX t htα, WC_congr hag t]
    exact GC μ hμ hlt t ht hb

/-- `one_step` の仮定の下で `α ∈ W` -/
theorem W.of_one_step {X : Tm → Prop} {α : Tm} (hD : D X) (hα : isCard α)
    (G1 : CS X α α) (G2 : ∀ t, F0NF t → Lt t α → CS X α t → X t)
    (GC : ∀ μ, isCard μ → Lt μ α → ∀ t, F0NF t → Bl μ t → (X t ↔ WC X μ t)) : W α := by
  obtain ⟨hY, hα'⟩ := one_step hD hα G1 G2 GC
  exact ⟨_, hY, Bl.self, hα'⟩

end RTKA
