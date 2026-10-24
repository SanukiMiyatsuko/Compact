import Compact.WF.FXXi

/-! 断片 `FX` の標準形の上で `<` が推移的であること（`lt_trans_FX`）。

部分項で閉じた有限集合 `S` の要素数についての帰納法で、不変条件 `GoodX S` を示す（`lin_closedX`）。
`S` から大きさ最大の項 `t` を除いた `S'` について `GoodX S'` を仮定し、`t` が `S'` を切断することを
`t` の形で場合分けして示す（`cut_om`・`PsiCtx.cut`・`XiCtx.cut`）。新しい項についての K2・KL などは
同じ場合分けの中で得る。 -/

namespace RTKA

open Tm

theorem GoodX.nil : GoodX [] :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ _ h => absurd h List.not_mem_nil,
    fun _ _ h => absurd h List.not_mem_nil, fun _ _ h => absurd h List.not_mem_nil,
    fun _ _ _ _ h => absurd h List.not_mem_nil, fun _ _ _ h => absurd h List.not_mem_nil⟩

/-- 切断性から推移性へ -/
theorem linOn_of_cut {S S' : List Tm} {t : Tm} (hNF : ∀ s, s ∈ S → FXNF s) (hLin : LinOn S')
    (inS' : ∀ s, s ∈ S → s ≠ t → s ∈ S') (cut : CutT S' t) : LinOn S := by
  intro a ha b hb c hc hab hbc
  have haF := hNF a ha
  have hbF := hNF b hb
  have hcF := hNF c hc
  by_cases eat : a = t <;> by_cases ebt : b = t <;> by_cases ect : c = t
  · subst eat; subst ebt; exact absurd hab (Lt.irrefl _)
  · subst eat; subst ebt; exact absurd hab (Lt.irrefl _)
  · subst eat; subst ect; exact absurd hbc (Lt.asymmX haF hbF hab)
  · subst eat
    rcases triX haF hcF with h | h | h
    · exact h
    · exact absurd h.symm ect
    · exact absurd hab (Lt.asymmX hbF haF (cut c b (inS' c hc ect) (inS' b hb ebt) hbc h))
  · subst ebt; subst ect; exact absurd hbc (Lt.irrefl _)
  · subst ebt
    rcases triX haF hcF with h | h | h
    · exact h
    · subst h; exact absurd hbc (Lt.asymmX haF hbF hab)
    · exact absurd hbc (Lt.asymmX hcF hbF (cut a c (inS' a ha eat) (inS' c hc ect) h hab))
  · subst ect
    exact cut b a (inS' b hb ebt) (inS' a ha eat) hab hbc
  · exact hLin a (inS' a ha eat) b (inS' b hb ebt) c (inS' c hc ect) hab hbc

theorem lin_closedX : ∀ n, ∀ S : List Tm, S.length ≤ n →
    (∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S) → (∀ s, s ∈ S → FXNF s) → GoodX S := by
  intro n
  induction n with
  | zero =>
    intro S hl _ _
    have hS : S = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst hS
    exact GoodX.nil
  | succ n ih =>
    intro S hl hcl hNF
    by_cases hS0 : S = []
    · subst hS0
      exact GoodX.nil
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
    have hNF' : ∀ s, s ∈ S.filter (fun s => s != t) → FXNF s := fun s hs =>
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
      | zero => exact cut_bot G' htF (Or.inr rfl) hsub
      | one => exact cut_bot G' htF (Or.inl rfl) hsub
      | K _ => exact cut_bot G' htF (Or.inl rfl) hsub
      | plus a b =>
        exact cut_of_principal G' htF hsub (fun _ _ htp => by simp [isPrincipal] at htp)
      | Om e => exact cut_om G' htF hsub
      | Xi m γ => exact (XiCtx.mk G' htF hsub htS').cut
      | Psi xi pi γ =>
        obtain ⟨rfl, c, rfl, -⟩ := htF.psi
        exact (PsiCtx.mk G' htF hsub htS').cut
    refine ⟨linOn_of_cut hNF G'.lin inS' cut, hNF, hcl, ?_, ?_, ?_, ?_, ?_⟩
    · intro c γ hx
      by_cases e : Tm.Psi .zero (.Om c) γ = t
      · subst e
        exact (PsiCtx.mk G' htF hsub htS').k2
      · exact G'.k2 c γ (inS' _ hx e)
    · intro m γ hx
      by_cases e : Tm.Xi m γ = t
      · subst e
        exact (XiCtx.mk G' htF hsub htS').k2x
      · exact G'.k2x m γ (inS' _ hx e)
    · intro c γ hx
      by_cases e : Tm.Psi .zero (.Om c) γ = t
      · subst e
        exact (PsiCtx.mk G' htF hsub htS').cx
      · exact G'.cx c γ (inS' _ hx e)
    · intro c β m ξ hψ hX hl
      by_cases e : Tm.Psi .zero (.Om c) β = t
      · subst e
        have hX' : Tm.Xi m ξ ∈ S.filter (fun s => s != Tm.Psi .zero (.Om c) β) :=
          inS' _ hX (by intro e; cases e)
        exact (PsiCtx.mk G' htF hsub htS').kl hX' hl
      · by_cases e' : Tm.Xi m ξ = t
        · subst e'
          exact (XiCtx.mk G' htF hsub htS').kl (inS' _ hψ e) hl
        · exact G'.kl c β m ξ (inS' _ hψ e) (inS' _ hX e') hl
    · intro c γ g hx
      by_cases e : Tm.Psi .zero (.Om c) γ = t
      · subst e
        exact (PsiCtx.mk G' htF hsub htS').ic g
      · exact G'.ic c γ g (inS' _ hx e)

/-- `FX` の標準形の上で `<` は推移的 -/
theorem lt_trans_FX {a b c : Tm} (ha : FXNF a) (hb : FXNF b) (hc : FXNF c)
    (h1 : Lt a b) (h2 : Lt b c) : Lt a c := by
  let S := subs a ++ subs b ++ subs c
  have hcl : ∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S := by
    intro s hs r hr
    simp only [S, List.mem_append] at hs ⊢
    rcases hs with (hs | hs) | hs
    · exact Or.inl (Or.inl (subs_trans hs hr))
    · exact Or.inl (Or.inr (subs_trans hs hr))
    · exact Or.inr (subs_trans hs hr)
  have hNF : ∀ s, s ∈ S → FXNF s := by
    intro s hs
    simp only [S, List.mem_append] at hs
    rcases hs with (hs | hs) | hs
    · exact ha.of_mem_subs hs
    · exact hb.of_mem_subs hs
    · exact hc.of_mem_subs hs
  have G := lin_closedX _ S (Nat.le_refl _) hcl hNF
  exact G.lin a (by simp [S, self_mem_subs]) b (by simp [S, self_mem_subs])
    c (by simp [S, self_mem_subs]) h1 h2

end RTKA
