import Compact.WF.FXColl

/-! 崩壊項どうしの比較を前線で書き直したもの（断片 `FX`）。

同じ正則項 `R` の崩壊項 `x = col(α)`、`y = col(β)` について

  `x < y` ⟺ (`α < β` かつ `α` の前線が全て `y` 未満) または (`β < α` かつ `β` の前線のどれかが `x` 以上)。

これは再帰的経路順序と同じ形で、比較は部分項どうしの比較に帰着する。仮定（`R` 以上の節点が
相手より小さくない、引数の大小が推移的）は、推移性を示している途中の有限集合の上で確かめる。 -/

namespace RTKA

open Tm

/-- 前線の各節点が `C(g, d)` に入ることは、崩壊の性質があれば `d` 未満と同値 -/
theorem fr_inC_iff {R x g d : Tm} (hcoll : ∀ w, w ∈ fr R x → inC w g d = true → Lt w d) :
    (∀ w, w ∈ fr R x → inC w g d = true) ↔ (∀ w, w ∈ fr R x → Lt w d) :=
  ⟨fun h w hw => hcoll w hw (h w hw), fun h w hw => inC_of_lt_node (fr_node hw) (h w hw)⟩

/-- 前線のどれかが `C(g, d)` に入らないことは、崩壊の性質があれば、どれかが `d` 未満でないことと同値 -/
theorem fr_inC_false_iff {R x g d : Tm} (hcoll : ∀ w, w ∈ fr R x → inC w g d = true → Lt w d) :
    (¬ ∀ w, w ∈ fr R x → inC w g d = true) ↔ (∃ w, w ∈ fr R x ∧ ¬ Lt w d) := by
  rw [fr_inC_iff hcoll]
  constructor
  · exact exists_of_not_forall_mem _
  · rintro ⟨w, hw, hn⟩ h
    exact hn (h w hw)

/-- 同じ区間の `Ψ_c` どうしの比較の前線による言い換え -/
theorem ff_psi {c α β : Tm} (hx : FXNF (.Psi .zero (.Om c) α)) (hy : FXNF (.Psi .zero (.Om c) β))
    (hne : α ≠ β)
    (icx : ∀ g, inC (.Om c) g (.Psi .zero (.Om c) α) = true)
    (icy : ∀ g, inC (.Om c) g (.Psi .zero (.Om c) β) = true)
    (H1 : ∀ w, w ∈ subs α → ¬ Lt w (.Om c) → ¬ Lt w (.Psi .zero (.Om c) β))
    (H2 : ∀ w, w ∈ subs β → ¬ Lt w (.Om c) → ¬ Lt w (.Psi .zero (.Om c) α))
    (H3 : Lt α β → ∀ v, v ∈ subs α → Lt v α → Lt v β)
    (H4 : Lt β α → ∀ v, v ∈ subs β → Lt v β → Lt v α) :
    Lt (.Psi .zero (.Om c) α) (.Psi .zero (.Om c) β) ↔
      (Lt α β ∧ ∀ w, w ∈ fr (.Om c) α → Lt w (.Psi .zero (.Om c) β)) ∨
        (Lt β α ∧ ∃ w, w ∈ fr (.Om c) β ∧ ¬ Lt w (.Psi .zero (.Om c) α)) := by
  obtain ⟨-, c₁, hc₁, -, -, hαF, hαC, -⟩ := hx.psi
  cases hc₁
  obtain ⟨-, c₂, hc₂, -, -, hβF, hβC, -⟩ := hy.psi
  cases hc₂
  have collx : ∀ w, w ∈ fr (.Om c) β → inC w α (.Psi .zero (.Om c) α) = true →
      Lt w (.Psi .zero (.Om c) α) := fun w hw h =>
    coll_psi hx w (hβF.of_mem_subs (fr_spec hw).1) h (fr_spec hw).2
  have colly : ∀ w, w ∈ fr (.Om c) α → inC w β (.Psi .zero (.Om c) β) = true →
      Lt w (.Psi .zero (.Om c) β) := fun w hw h =>
    coll_psi hy w (hαF.of_mem_subs (fr_spec hw).1) h (fr_spec hw).2
  rw [lt_psi_same_iffX hx hy hne icx icy]
  constructor
  · rintro (⟨hab, h⟩ | ⟨hba, h⟩)
    · refine Or.inl ⟨hab, (fr_inC_iff colly).mp ?_⟩
      exact (inC_fr α hαC H1 (H3 hab)).mp h
    · refine Or.inr ⟨hba, (fr_inC_false_iff collx).mp ?_⟩
      intro h'
      rw [(inC_fr β hβC H2 (H4 hba)).mpr h'] at h
      cases h
  · rintro (⟨hab, h⟩ | ⟨hba, h⟩)
    · exact Or.inl ⟨hab, (inC_fr α hαC H1 (H3 hab)).mpr ((fr_inC_iff colly).mpr h)⟩
    · refine Or.inr ⟨hba, ?_⟩
      cases e : inC β α (Tm.Psi .zero (.Om c) α)
      · rfl
      · exact absurd ((inC_fr β hβC H2 (H4 hba)).mp e) ((fr_inC_false_iff collx).mpr h)

theorem lev_le_of_lt_gen {w y : Tm} (h : Lt w y) : lev w ≤ lev y := by
  apply Nat.le_of_not_lt
  intro hl
  have hw0 : w ≠ .zero := by intro e; subst e; simp [lev] at hl
  by_cases hy0 : y = .zero
  · subst hy0; exact not_lt_zero w h
  · cases hsw : summands w with
    | nil => exact absurd hsw (summands_ne_nil hw0)
    | cons x xs =>
      cases hsy : summands y with
      | nil => exact absurd hsy (summands_ne_nil hy0)
      | cons z zs =>
        unfold Lt at h
        rw [cmp_eq, hsw, hsy] at h
        have e : cmpP x z = .gt := cmpP_of_lev_gt (by rw [lev_head hsw, lev_head hsy]; exact hl)
        rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e] at h
        cases h

/-- `K_n` 以上の項は階 `n` の項より小さくない -/
theorem not_lt_of_not_lt_K {n : Nat} {w y : Tm} (hy : lev y = n)
    (h : ¬ Lt w (.K n)) : ¬ Lt w y := by
  intro h'
  have hl := lev_le_of_lt_gen h'
  exact h (lt_of_lev_lt' (by simp only [lev]; omega))

/-- 同じ階の `Ξ_n` どうしの比較の前線による言い換え -/
theorem ff_xi {n : Nat} {α β : Tm} (hx : FXNF (.Xi n α)) (hy : FXNF (.Xi n β)) (hne : α ≠ β)
    (H3 : Lt α β → ∀ v, v ∈ subs α → Lt v α → Lt v β)
    (H4 : Lt β α → ∀ v, v ∈ subs β → Lt v β → Lt v α) :
    Lt (.Xi n α) (.Xi n β) ↔
      (Lt α β ∧ ∀ w, w ∈ fr (.K n) α → Lt w (.Xi n β)) ∨
        (Lt β α ∧ ∃ w, w ∈ fr (.K n) β ∧ ¬ Lt w (.Xi n α)) := by
  obtain ⟨-, hαF, -, -, hαC⟩ := hx.xi
  obtain ⟨-, hβF, -, -, hβC⟩ := hy.xi
  have collx : ∀ w, w ∈ fr (.K n) β → inC w α (.Xi n α) = true → Lt w (.Xi n α) := fun w hw h =>
    coll_xi hx w (hβF.of_mem_subs (fr_spec hw).1) h (fr_spec hw).2
  have colly : ∀ w, w ∈ fr (.K n) α → inC w β (.Xi n β) = true → Lt w (.Xi n β) := fun w hw h =>
    coll_xi hy w (hαF.of_mem_subs (fr_spec hw).1) h (fr_spec hw).2
  have H1 : ∀ w, w ∈ subs α → ¬ Lt w (.K n) → ¬ Lt w (.Xi n β) := fun w hw h =>
    not_lt_of_not_lt_K rfl h
  have H2 : ∀ w, w ∈ subs β → ¬ Lt w (.K n) → ¬ Lt w (.Xi n α) := fun w hw h =>
    not_lt_of_not_lt_K rfl h
  rw [lt_xi_xi_same hαF hβF hne]
  constructor
  · rintro (⟨hab, h⟩ | ⟨hba, h⟩)
    · exact Or.inl ⟨hab, (fr_inC_iff colly).mp ((inC_fr α hαC H1 (H3 hab)).mp h)⟩
    · refine Or.inr ⟨hba, (fr_inC_false_iff collx).mp ?_⟩
      intro h'
      rw [(inC_fr β hβC H2 (H4 hba)).mpr h'] at h
      cases h
  · rintro (⟨hab, h⟩ | ⟨hba, h⟩)
    · exact Or.inl ⟨hab, (inC_fr α hαC H1 (H3 hab)).mpr ((fr_inC_iff colly).mpr h)⟩
    · refine Or.inr ⟨hba, ?_⟩
      cases e : inC β α (Tm.Xi n α)
      · rfl
      · exact absurd ((inC_fr β hβC H2 (H4 hba)).mp e) ((fr_inC_false_iff collx).mpr h)

/-- `Ψ_c(β)` と `Ξ_n(ξ)` の比較の前線による言い換え -/
theorem ff_kl {c β ξ : Tm} {n : Nat} (hX : FXNF (.Xi n ξ))
    (hl : lev c = n) (H : Lt ξ β → ∀ v, v ∈ subs ξ → Lt v ξ → Lt v β) :
    Lt (.Psi .zero (.Om c) β) (.Xi n ξ) ↔
      cmp c (.Xi n ξ) ≠ .gt ∨
        (Lt ξ β ∧ ∃ w, w ∈ fr (.K n) ξ ∧ inC w β (.Psi .zero (.Om c) β) = false) := by
  obtain ⟨-, hξF, -, -, hξC⟩ := hX.xi
  have H1 : ∀ w, w ∈ subs ξ → ¬ Lt w (.K n) → ¬ Lt w (.Psi .zero (.Om c) β) := fun w hw h =>
    not_lt_of_not_lt_K hl h
  rw [lt_psi_xi hl]
  constructor
  · rintro (h | ⟨hξβ, h⟩)
    · exact Or.inl h
    · refine Or.inr ⟨hξβ, ?_⟩
      have hn : ¬ ∀ w, w ∈ fr (.K n) ξ → inC w β (.Psi .zero (.Om c) β) = true := by
        intro h'
        rw [(inC_fr ξ hξC H1 (H hξβ)).mpr h'] at h
        cases h
      obtain ⟨w, hw, hw'⟩ := exists_of_not_forall_mem _ hn
      exact ⟨w, hw, by cases e : inC w β (Tm.Psi .zero (.Om c) β) <;> simp_all⟩
  · rintro (h | ⟨hξβ, w, hw, hw'⟩)
    · exact Or.inl h
    · refine Or.inr ⟨hξβ, ?_⟩
      cases e : inC ξ β (Tm.Psi .zero (.Om c) β)
      · rfl
      · have := (inC_fr ξ hξC H1 (H hξβ)).mp e w hw
        rw [hw'] at this
        cases this

end RTKA
