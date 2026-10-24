import Compact.WF.FXBasic
import Compact.WF.F0Int

/-! 崩壊項の前線と崩壊の性質（断片 `FX` の推移性の道具）。

崩壊項は `Ψ_c(γ) = Ψ^0_{Ω_c}(γ)`（正則項 `Ω_c`）と `Ξ_n(γ)`（正則項 `K_n`）。

* `fr R x`：`x` を `R` 以上の `Ψ`・`Ξ` の節点だけを通って辿ったとき、最初に出会う `R` 未満の節点の一覧（前線）。
* `inC_fr`：`R` 以上の節点の引数が小さいとき、`x ∈ C(g, d)` は前線の各節点が `C(g, d)` に入ることと同値。
* `coll_psi`・`coll_xi`：崩壊の性質 `C(γ, t) ∩ R ⊆ t`。推移性を使わず、項についての帰納法で示せる。
* `ff_psi`・`ff_xi`：同じ正則項の崩壊項どうしの比較を前線で書き直したもの（再帰的経路順序の形）。
* `ff_kl`：`Ψ_c(β)` と `Ξ_n(ξ)` の比較を前線で書き直したもの。 -/

namespace RTKA

open Tm

/-! ### 道具 -/

theorem lt_of_lev_lt' {a b : Tm} (h : lev a < lev b) : Lt a b := by
  have hb0 : b ≠ .zero := by intro e; subst e; simp [lev] at h
  by_cases ha0 : a = .zero
  · subst ha0
    exact zero_lt hb0
  · cases hsa : summands a with
    | nil => exact absurd hsa (summands_ne_nil ha0)
    | cons x xs =>
      cases hsb : summands b with
      | nil => exact absurd hsb (summands_ne_nil hb0)
      | cons y ys =>
        unfold Lt
        rw [cmp_eq, hsa, hsb]
        have e : cmpP x y = .lt := cmpP_of_lev_lt (by rw [lev_head hsa, lev_head hsb]; exact h)
        rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]

theorem lev_le_of_ltX {a b : Tm} (ha : FXNF a) (hb : FXNF b) (h : Lt a b) : lev a ≤ lev b :=
  Nat.le_of_not_lt (fun h' => Lt.asymmX ha hb h (lt_of_lev_lt' h'))

theorem lt_om_iffX {a b : Tm} (ha : FXNF a) (hb : FXNF b) : Lt (.Om a) (.Om b) ↔ Lt a b := by
  rcases Nat.lt_trichotomy (lev a) (lev b) with h | h | h
  · constructor
    · intro _; exact lt_of_lev_lt' h
    · intro _
      rw [lt_principal_iff rfl rfl, cmpP_of_lev_lt (by simp only [lev]; exact h)]
  · exact lt_om_om a b h
  · constructor
    · intro h'
      rw [lt_principal_iff rfl rfl, cmpP_of_lev_gt (by simp only [lev]; exact h)] at h'
      cases h'
    · intro h'; exact absurd (lt_of_lev_lt' h) (Lt.asymmX ha hb h')

theorem inC_xi_iff {n : Nat} {a g d : Tm} :
    inC (.Xi n a) g d = true ↔ Lt (.Xi n a) d ∨ (inC a g d = true ∧ Lt a g) := by
  rw [inC_xi]
  unfold Lt
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]

/-- 同じ区間の `Ψ` どうしの比較（`Ω_c ∈ C` を使って簡単にしたもの） -/
theorem lt_psi_same_iffX {c α β : Tm} (hx : FXNF (.Psi .zero (.Om c) α))
    (hy : FXNF (.Psi .zero (.Om c) β)) (hne : α ≠ β)
    (icx : ∀ g, inC (.Om c) g (.Psi .zero (.Om c) α) = true)
    (icy : ∀ g, inC (.Om c) g (.Psi .zero (.Om c) β) = true) :
    Lt (.Psi .zero (.Om c) α) (.Psi .zero (.Om c) β) ↔
      (Lt α β ∧ inC α β (.Psi .zero (.Om c) β) = true) ∨
        (Lt β α ∧ inC β α (.Psi .zero (.Om c) α) = false) := by
  obtain ⟨-, c₁, hc₁, -, -, hαF, -, -⟩ := hx.psi
  obtain ⟨-, c₂, hc₂, -, -, hβF, -, -⟩ := hy.psi
  rw [lt_psi_psi_same hne, icx, icy]
  have hβα : cmp β α ≠ .gt ↔ Lt β α := by
    constructor
    · intro h
      cases e : cmp β α with
      | lt => exact e
      | eq => exact absurd (eq_of_cmp_eq_FX hβF hαF e).symm hne
      | gt => exact absurd e h
    · intro h
      unfold Lt at h
      rw [h]
      decide
  rw [hβα]
  simp

/-- 有限の一覧の上の「全ては成り立たない」から反例を取り出す -/
theorem exists_of_not_forall_mem {P : Tm → Prop} [DecidablePred P] :
    ∀ l : List Tm, ¬ (∀ w, w ∈ l → P w) → ∃ w, w ∈ l ∧ ¬ P w
  | [], h => absurd (fun _ hw => absurd hw List.not_mem_nil) h
  | x :: xs, h => by
    by_cases hx : P x
    · obtain ⟨w, hw, hP⟩ := exists_of_not_forall_mem xs (fun h' => h (fun w hw => by
        rcases List.mem_cons.mp hw with e | e
        · subst e; exact hx
        · exact h' w e))
      exact ⟨w, List.mem_cons_of_mem _ hw, hP⟩
    · exact ⟨x, List.mem_cons_self, hx⟩

/-! ### 前線 -/

/-- 正則項 `R` についての前線 -/
def fr (R : Tm) : Tm → List Tm
  | .plus a b => fr R a ++ fr R b
  | .Om a => fr R a
  | .Xi m a => if Lt (.Xi m a) R then [.Xi m a] else fr R a
  | .Psi s p a => if Lt (.Psi s p a) R then [.Psi s p a] else fr R s ++ fr R p ++ fr R a
  | _ => []

theorem subs_plus_l {a b w : Tm} (h : w ∈ subs a) : w ∈ subs (.plus a b) :=
  subs_trans (by simp [subs, self_mem_subs]) h

theorem subs_plus_r {a b w : Tm} (h : w ∈ subs b) : w ∈ subs (.plus a b) :=
  subs_trans (by simp [subs, self_mem_subs]) h

theorem subs_om {a w : Tm} (h : w ∈ subs a) : w ∈ subs (.Om a) :=
  subs_trans (mem_subs_om a) h

theorem subs_xi {n : Nat} {a w : Tm} (h : w ∈ subs a) : w ∈ subs (.Xi n a) :=
  subs_trans (mem_subs_xi n a) h

theorem subs_psi_s {s p a w : Tm} (h : w ∈ subs s) : w ∈ subs (.Psi s p a) :=
  subs_trans (by simp [subs, self_mem_subs]) h

theorem subs_psi_p {s p a w : Tm} (h : w ∈ subs p) : w ∈ subs (.Psi s p a) :=
  subs_trans (by simp [subs, self_mem_subs]) h

theorem subs_psi_a {s p a w : Tm} (h : w ∈ subs a) : w ∈ subs (.Psi s p a) :=
  subs_trans (mem_subs_psi_a s p a) h

/-- 前線の元は部分項で `R` 未満 -/
theorem fr_spec {R : Tm} : ∀ {x w : Tm}, w ∈ fr R x → w ∈ subs x ∧ Lt w R
  | .zero, _, h | .one, _, h | .K _, _, h => by simp [fr] at h
  | .plus a b, w, h => by
    rw [fr, List.mem_append] at h
    rcases h with h | h
    · exact ⟨subs_plus_l (fr_spec h).1, (fr_spec h).2⟩
    · exact ⟨subs_plus_r (fr_spec h).1, (fr_spec h).2⟩
  | .Om a, w, h => by
    rw [fr] at h
    exact ⟨subs_om (fr_spec h).1, (fr_spec h).2⟩
  | .Xi m a, w, h => by
    rw [fr] at h
    by_cases hR : Lt (.Xi m a) R
    · simp only [hR, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact ⟨self_mem_subs _, hR⟩
    · simp only [hR, ↓reduceIte] at h
      exact ⟨subs_xi (fr_spec h).1, (fr_spec h).2⟩
  | .Psi s p a, w, h => by
    rw [fr] at h
    by_cases hR : Lt (.Psi s p a) R
    · simp only [hR, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact ⟨self_mem_subs _, hR⟩
    · simp only [hR, ↓reduceIte, List.mem_append] at h
      rcases h with (h | h) | h
      · exact ⟨subs_psi_s (fr_spec h).1, (fr_spec h).2⟩
      · exact ⟨subs_psi_p (fr_spec h).1, (fr_spec h).2⟩
      · exact ⟨subs_psi_a (fr_spec h).1, (fr_spec h).2⟩

/-- 前線による `C` への所属の言い換え：`R` 以上の節点が `d` 未満でなく、その引数が `g0` 未満
    （したがって `g` 未満）なら、`x ∈ C(g, d)` は前線の各節点が `C(g, d)` に入ることと同値 -/
theorem inC_fr {R g0 g d : Tm} : ∀ x : Tm, inC x g0 R = true →
    (∀ w, w ∈ subs x → ¬ Lt w R → ¬ Lt w d) →
    (∀ v, v ∈ subs x → Lt v g0 → Lt v g) →
    (inC x g d = true ↔ ∀ w, w ∈ fr R x → inC w g d = true)
  | .zero, _, _, _ => by simp [fr, inC_zero]
  | .one, _, _, _ => by simp [fr, inC_one]
  | .K n, _, _, _ => by simp [fr, inC_K]
  | .plus a b, h0, hd, hg => by
    rw [inC_plus, Bool.and_eq_true] at h0
    rw [inC_plus, Bool.and_eq_true, fr]
    rw [inC_fr a h0.1 (fun w hw => hd w (subs_plus_l hw)) (fun v hv => hg v (subs_plus_l hv)),
      inC_fr b h0.2 (fun w hw => hd w (subs_plus_r hw)) (fun v hv => hg v (subs_plus_r hv))]
    simp only [List.mem_append]
    constructor
    · rintro ⟨h1, h2⟩ w (hw | hw)
      · exact h1 w hw
      · exact h2 w hw
    · intro h
      exact ⟨fun w hw => h w (Or.inl hw), fun w hw => h w (Or.inr hw)⟩
  | .Om a, h0, hd, hg => by
    rw [inC_om] at h0
    rw [inC_om, fr]
    exact inC_fr a h0 (fun w hw => hd w (subs_om hw)) (fun v hv => hg v (subs_om hv))
  | .Xi m a, h0, hd, hg => by
    rw [fr]
    by_cases hR : Lt (.Xi m a) R
    · simp only [hR, ↓reduceIte]
      simp
    · simp only [hR, ↓reduceIte]
      rcases inC_xi_iff.mp h0 with h | ⟨ha, hlt⟩
      · exact absurd h hR
      have hnd := hd _ (self_mem_subs _) hR
      have hag : Lt a g := hg a (mem_subs_xi m a) hlt
      rw [inC_xi_iff, ← inC_fr a ha (fun w hw => hd w (subs_xi hw)) (fun v hv => hg v (subs_xi hv))]
      constructor
      · rintro (h | ⟨h, _⟩)
        · exact absurd h hnd
        · exact h
      · intro h
        exact Or.inr ⟨h, hag⟩
  | .Psi s p a, h0, hd, hg => by
    rw [fr]
    by_cases hR : Lt (.Psi s p a) R
    · simp only [hR, ↓reduceIte]
      simp
    · simp only [hR, ↓reduceIte]
      rcases inC_psi_iff.mp h0 with h | ⟨hp, hs, ha, hlt⟩
      · exact absurd h hR
      have hnd := hd _ (self_mem_subs _) hR
      have hag : Lt a g := hg a (mem_subs_psi_a s p a) hlt
      rw [inC_psi_iff,
        inC_fr p hp (fun w hw => hd w (subs_psi_p hw)) (fun v hv => hg v (subs_psi_p hv)),
        inC_fr s hs (fun w hw => hd w (subs_psi_s hw)) (fun v hv => hg v (subs_psi_s hv)),
        inC_fr a ha (fun w hw => hd w (subs_psi_a hw)) (fun v hv => hg v (subs_psi_a hv))]
      simp only [List.mem_append]
      constructor
      · rintro (h | ⟨h1, h2, h3, _⟩)
        · exact absurd h hnd
        · rintro w ((hw | hw) | hw)
          · exact h2 w hw
          · exact h1 w hw
          · exact h3 w hw
      · intro h
        exact Or.inr ⟨fun w hw => h w (Or.inl (Or.inr hw)), fun w hw => h w (Or.inl (Or.inl hw)),
          fun w hw => h w (Or.inr hw), hag⟩

end RTKA
