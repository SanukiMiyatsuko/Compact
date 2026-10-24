import Compact.WF.FYL5
import Compact.WF.FYWF

/-! 断片 `FY` の順序の性質（`FYOrder`）の証明と、`FY` の整列性（仮定なし）。

部分項で閉じた有限集合 `S` の要素数についての帰納法で `GoodY S` を示す（`lin_closedY`）。`S` から大きさ
最大の項 `t` を除いた `S'` について `GoodY S'` を仮定し、`t` の形で場合分けして、`t` の切断性・`t` と
`S'` の元の反対称性・`t` についての K2・K2T・K2X・CX を得る（`cut_omY`・`XiCtxY`・`PsiCtxY`）。 -/

namespace RTKA

open Tm

theorem GoodY.nil : GoodY [] :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ _ h => absurd h List.not_mem_nil, fun _ _ h => absurd h List.not_mem_nil,
    fun _ _ h => absurd h List.not_mem_nil, fun _ _ h => absurd h List.not_mem_nil⟩

/-- `S'` が反対称で、`t` が `S'` の全ての元と反対称なら、`S' ∪ {t}` は反対称 -/
theorem antiOn_extend {S S' : List Tm} {t : Tm} (hA : AntiOn S')
    (inS' : ∀ s, s ∈ S → s ≠ t → s ∈ S') (hT : ∀ z, z ∈ S' → AntiT t z) : AntiOn S := by
  intro a ha b hb
  by_cases ea : a = t <;> by_cases eb : b = t
  · subst ea; subst eb
    rw [cmp_self]
    exact ⟨rfl, fun _ => rfl⟩
  · subst ea
    exact hT b (inS' b hb eb)
  · subst eb
    obtain ⟨h1, -⟩ := hT a (inS' a ha ea)
    refine ⟨by rw [h1, Ordering.swap_swap], fun e => ?_⟩
    have := (hT a (inS' a ha ea)).2
    rw [h1] at e
    exact (this (swap_eq_eq e)).symm
  · exact hA a (inS' a ha ea) b (inS' b hb eb)

theorem lin_closedY : ∀ n, ∀ S : List Tm, S.length ≤ n →
    (∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S) → (∀ s, s ∈ S → FYNF s) → GoodY S := by
  intro n
  induction n with
  | zero =>
    intro S hl _ _
    have hS : S = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst hS
    exact GoodY.nil
  | succ n ih =>
    intro S hl hcl hNF
    by_cases hS0 : S = []
    · subst hS0
      exact GoodY.nil
    obtain ⟨t, htS, hmax⟩ := exists_max_size S hS0
    have hmem : ∀ s, s ∈ S.filter (fun s => s != t) ↔ s ∈ S ∧ s ≠ t := by
      intro s
      rw [List.mem_filter, bne_iff_ne]
    have hl' : (S.filter (fun s => s != t)).length ≤ n := by
      have := length_filter_ne_lt htS
      omega
    have hcl' : ∀ s, s ∈ S.filter (fun s => s != t) → ∀ r, r ∈ subs s →
        r ∈ S.filter (fun s => s != t) := by
      intro s hs r hr
      obtain ⟨hsS, hst⟩ := (hmem s).mp hs
      refine (hmem r).mpr ⟨hcl s hsS r hr, ?_⟩
      intro e
      subst e
      exact hst (eq_of_mem_subs_size hr (hmax s hsS)).symm
    have hNF' : ∀ s, s ∈ S.filter (fun s => s != t) → FYNF s := fun s hs =>
      hNF s ((hmem s).mp hs).1
    have G' := ih _ hl' hcl' hNF'
    have htF := hNF t htS
    have hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S.filter (fun s => s != t) := fun s hs hne =>
      (hmem s).mpr ⟨hcl t htS s hs, hne⟩
    have htS' : t ∉ S.filter (fun s => s != t) := fun h => ((hmem t).mp h).2 rfl
    have inS' : ∀ s, s ∈ S → s ≠ t → s ∈ S.filter (fun s => s != t) := fun s hs hne =>
      (hmem s).mpr ⟨hs, hne⟩
    -- `t` は `S'` を切断する
    have cut : CutT (S.filter (fun s => s != t)) t := by
      cases t with
      | zero => exact cut_botY G' htF (Or.inr rfl) hsub
      | one => exact cut_botY G' htF (Or.inl rfl) hsub
      | K _ => exact cut_botY G' htF (Or.inl rfl) hsub
      | plus a b =>
        exact G'.cut_of_principal htF hsub (fun _ _ htp => by simp [isPrincipal] at htp)
      | Om e => exact cut_omY G' htF hsub
      | Xi m γ => exact (XiCtxY.mk G' htF hsub htS').cut
      | Psi xi π γ =>
        obtain ⟨rfl, -⟩ := htF.psi
        exact (PsiCtxY.mk G' htF hsub htS').cut
    -- `t` は `S'` の全ての元と反対称
    have antiT : ∀ z, z ∈ S.filter (fun s => s != t) → AntiT t z := by
      cases t with
      | Psi xi π γ =>
        obtain ⟨rfl, -⟩ := htF.psi
        exact (PsiCtxY.mk G' htF hsub htS').anti
      | _ => exact G'.anti_new htF hsub htS' (fun _ _ _ _ e => by cases e)
    have hA := antiOn_extend G'.anti inS' antiT
    refine ⟨linOn_of_cutY hA G'.lin inS' cut, hA, hNF, hcl, ?_, ?_, ?_, ?_⟩
    · intro π γ hx
      by_cases e : Tm.Psi .zero π γ = t
      · subst e
        exact (PsiCtxY.mk G' htF hsub htS').k2
      · exact G'.k2 π γ (inS' _ hx e)
    · intro π γ hx
      by_cases e : Tm.Psi .zero π γ = t
      · subst e
        exact (PsiCtxY.mk G' htF hsub htS').k2t
      · exact G'.k2t π γ (inS' _ hx e)
    · intro m γ hx
      by_cases e : Tm.Xi m γ = t
      · subst e
        exact (XiCtxY.mk G' htF hsub htS').k2x
      · exact G'.k2x m γ (inS' _ hx e)
    · intro c γ hx
      by_cases e : Tm.Psi .zero (.Om c) γ = t
      · subst e
        exact (PsiCtxY.mk G' htF hsub htS').cx rfl
      · exact G'.cx c γ (inS' _ hx e)

/-- 三つの標準形の部分項全体は `GoodY` -/
theorem goodY3 {a b c : Tm} (ha : FYNF a) (hb : FYNF b) (hc : FYNF c) :
    GoodY (subs a ++ subs b ++ subs c) := by
  apply lin_closedY _ _ (Nat.le_refl _)
  · intro s hs r hr
    simp only [List.mem_append] at hs ⊢
    rcases hs with (hs | hs) | hs
    · exact Or.inl (Or.inl (subs_trans hs hr))
    · exact Or.inl (Or.inr (subs_trans hs hr))
    · exact Or.inr (subs_trans hs hr)
  · intro s hs
    simp only [List.mem_append] at hs
    rcases hs with (hs | hs) | hs
    · exact ha.of_mem_subs hs
    · exact hb.of_mem_subs hs
    · exact hc.of_mem_subs hs

theorem mem3_a (a b c : Tm) : a ∈ subs a ++ subs b ++ subs c := by simp [self_mem_subs]

theorem mem3_b (a b c : Tm) : b ∈ subs a ++ subs b ++ subs c := by simp [self_mem_subs]

theorem mem3_c (a b c : Tm) : c ∈ subs a ++ subs b ++ subs c := by simp [self_mem_subs]

/-- `FY` の標準形の上で順序の性質が成り立つ -/
instance instFYOrder : FYOrder where
  swap ha hb := (goodY3 ha hb hb).swap (mem3_a _ _ _) (mem3_b _ _ _)
  eq ha hb h := (goodY3 ha hb hb).eq (mem3_a _ _ _) (mem3_b _ _ _) h
  trans ha hb hc h1 h2 :=
    (goodY3 ha hb hc).trans (mem3_a _ _ _) (mem3_b _ _ _) (mem3_c _ _ _) h1 h2
  k2 h w hw := (goodY3 h h h).k2 _ _ (mem3_a _ _ _) w hw
  k2t h w hw := (goodY3 h h h).k2t _ _ (mem3_a _ _ _) w hw
  k2x h w hw := (goodY3 h h h).k2x _ _ (mem3_a _ _ _) w hw
  cx h := (goodY3 h h h).cx _ _ (mem3_a _ _ _)

/-- `FY` の標準形の上の `<` は整礎（仮定なし） -/
theorem wellFounded_FY_NF : WellFounded (fun a b : {t : Tm // FYNF t} => Lt a.1 b.1) :=
  wellFounded_FY

end RTKA
