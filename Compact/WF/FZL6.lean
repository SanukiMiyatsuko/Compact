import Compact.WF.FZL5
import Compact.WF.FZWF

/-! 断片 `FZ` の順序の性質（`FZOrder`）の証明と、`FZ` の整列性（仮定なし）。

部分項で閉じ、`Ψ^ξ_{Ξ_n(p)}(γ)`（`ξ ≠ 0`）を含めば `K_n^+` も含む有限集合 `S` の要素数についての帰納法で
`GoodY S` を示す（`lin_closedY`）。`S` から大きさ最大の項 `t` を除いた `S'` について `GoodY S'` を仮定し、
`t` の形で場合分けして、`t` の切断性・`t` と `S'` の元の反対称性・`t` についての K2・K2T・K2S・K2X・CX を
得る（`cut_omY`・`XiCtxY`・`PsiCtxY`）。 -/

namespace RTKA.Z

open Tm

theorem GoodY.nil : GoodY [] :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ _ _ h => absurd h List.not_mem_nil, fun _ _ _ h => absurd h List.not_mem_nil,
    fun _ _ _ h => absurd h List.not_mem_nil, fun _ _ h => absurd h List.not_mem_nil,
    fun _ _ h => absurd h List.not_mem_nil, fun _ _ _ _ h => absurd h List.not_mem_nil⟩

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

/-- `Ψ^ξ_{Ξ_n(p)}(γ)`（`ξ ≠ 0`）は `K_n^+` より大きい -/
theorem size_succK_lt {ξ γ p : Tm} {n : Nat} (hξ : ξ ≠ .zero) :
    (succK n).size < (Tm.Psi ξ (.Xi n p) γ).size := by
  have h1 : 1 ≤ ξ.size := Tm.size_pos ξ
  have h2 := Tm.size_pos p
  have h3 := Tm.size_pos γ
  cases ξ with
  | zero => exact absurd rfl hξ
  | _ => simp only [succK, Tm.size] at *; omega

theorem lin_closedY : ∀ n, ∀ S : List Tm, S.length ≤ n →
    (∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S) → (∀ s, s ∈ S → FZNF s) → SKOn S → GoodY S := by
  intro n
  induction n with
  | zero =>
    intro S hl _ _ _
    have hS : S = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst hS
    exact GoodY.nil
  | succ n ih =>
    intro S hl hcl hNF hsk
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
    have hNF' : ∀ s, s ∈ S.filter (fun s => s != t) → FZNF s := fun s hs =>
      hNF s ((hmem s).mp hs).1
    -- `K_n^+` は `t` でない（大きさが小さい）
    have skne : ∀ ξ m p γ, Tm.Psi ξ (.Xi m p) γ ∈ S → ξ ≠ .zero → succK m ≠ t :=
      fun ξ m p γ hψ hξ e => by
        have h1 := hmax _ hψ
        have h2 := size_succK_lt (γ := γ) (p := p) (n := m) hξ
        rw [e] at h2
        omega
    have hsk' : SKOn (S.filter (fun s => s != t)) := fun ξ m p γ hψ hξ =>
      (hmem _).mpr ⟨hsk ξ m p γ ((hmem _).mp hψ).1 hξ,
        skne ξ m p γ ((hmem _).mp hψ).1 hξ⟩
    have G' := ih _ hl' hcl' hNF' hsk'
    have htF := hNF t htS
    have hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S.filter (fun s => s != t) := fun s hs hne =>
      (hmem s).mpr ⟨hcl t htS s hs, hne⟩
    have htS' : t ∉ S.filter (fun s => s != t) := fun h => ((hmem t).mp h).2 rfl
    have inS' : ∀ s, s ∈ S → s ≠ t → s ∈ S.filter (fun s => s != t) := fun s hs hne =>
      (hmem s).mpr ⟨hs, hne⟩
    -- `Ψ` の文脈の `K_n^+` の条件
    have hskt : ∀ ξ π γ, t = .Psi ξ π γ → ∀ m p, π = .Xi m p → ξ ≠ .zero →
        succK m ∈ S.filter (fun s => s != t) := fun ξ π γ e m p hπ hξ => by
      subst hπ
      have hψ : Tm.Psi ξ (.Xi m p) γ ∈ S := e ▸ htS
      exact inS' _ (hsk ξ m p γ hψ hξ) (skne ξ m p γ hψ hξ)
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
      | Psi ξ π γ =>
        exact (PsiCtxY.mk G' htF hsub htS' (fun m p hπ hξ => hskt ξ π γ rfl m p hπ hξ)).cut
    -- `t` は `S'` の全ての元と反対称
    have antiT : ∀ z, z ∈ S.filter (fun s => s != t) → AntiT t z := by
      cases t with
      | Psi ξ π γ =>
        exact (PsiCtxY.mk G' htF hsub htS' (fun m p hπ hξ => hskt ξ π γ rfl m p hπ hξ)).anti
      | _ => exact G'.anti_new htF hsub htS' (fun _ _ _ _ _ _ e => by cases e)
    have hA := antiOn_extend G'.anti inS' antiT
    have ctx : ∀ ξ π γ, Tm.Psi ξ π γ = t → PsiCtxY (S.filter (fun s => s != t)) ξ π γ :=
      fun ξ π γ e => by
        subst e
        exact PsiCtxY.mk G' htF hsub htS' (fun m p hπ hξ => hskt ξ π γ rfl m p hπ hξ)
    refine ⟨linOn_of_cutY hA G'.lin inS' cut, hA, hNF, hcl, ?_, ?_, ?_, ?_, ?_, hsk⟩
    · intro ξ π γ hx
      by_cases e : Tm.Psi ξ π γ = t
      · have P := ctx ξ π γ e
        subst e
        exact P.k2
      · exact G'.k2 ξ π γ (inS' _ hx e)
    · intro ξ π γ hx
      by_cases e : Tm.Psi ξ π γ = t
      · have P := ctx ξ π γ e
        subst e
        exact P.k2t
      · exact G'.k2t ξ π γ (inS' _ hx e)
    · intro ξ π γ hx
      by_cases e : Tm.Psi ξ π γ = t
      · have P := ctx ξ π γ e
        subst e
        exact P.k2s
      · exact G'.k2s ξ π γ (inS' _ hx e)
    · intro m γ hx
      by_cases e : Tm.Xi m γ = t
      · subst e
        exact (XiCtxY.mk G' htF hsub htS').k2x
      · exact G'.k2x m γ (inS' _ hx e)
    · intro c γ hx
      by_cases e : Tm.Psi .zero (.Om c) γ = t
      · have P := ctx _ _ _ e
        subst e
        exact P.cx rfl
      · exact G'.cx c γ (inS' _ hx e)

/-! ### 有限集合の構成 -/

theorem FZNF.succK {n : Nat} (hn : 1 ≤ n) : FZNF (succK n) := by
  refine ⟨?_, rfl⟩
  have h1 : cmp (Tm.plus (.K n) .one) (.Om (.plus (.K n) .one)) = .lt := by
    rw [cmp_eq]
    simp only [summands]
    rw [cmpList_cons_cons_ne _ _ (by rw [cmpP.eq_def]; simp [lev]), cmpP.eq_def]
    simp [lev]
  have h2 : cmp .one (.K n) = .lt := by
    rw [cmp_principal rfl rfl, cmpP_of_lev_lt (by simp only [lev]; omega)]
  simp [_root_.RTKA.succK, isNF, lt, h1, h2, summands, hn, isPrincipal]

/-- `Ψ^ξ_{Ξ_n(p)}` に対して `K_n^+` の部分項を足す -/
def skx : Tm → List Tm
  | .Psi _ (.Xi n _) _ => subs (_root_.RTKA.succK n)
  | _ => []

/-- 部分項の一覧に `K_n^+` を足した有限集合 -/
def skClose (L : List Tm) : List Tm := L ++ L.flatMap skx

theorem skClose_good {L : List Tm} (hcl : ∀ s, s ∈ L → ∀ r, r ∈ subs s → r ∈ L)
    (hNF : ∀ s, s ∈ L → FZNF s) : GoodY (skClose L) := by
  apply lin_closedY _ _ (Nat.le_refl _)
  · intro s hs r hr
    simp only [skClose, List.mem_append, List.mem_flatMap] at hs ⊢
    rcases hs with hs | ⟨u, hu, hs⟩
    · exact Or.inl (hcl s hs r hr)
    · refine Or.inr ⟨u, hu, ?_⟩
      cases u with
      | Psi ξ π γ =>
        cases π with
        | Xi n p => simp only [skx] at hs ⊢; exact subs_trans hs hr
        | _ => simp [skx] at hs
      | _ => simp [skx] at hs
  · intro s hs
    simp only [skClose, List.mem_append, List.mem_flatMap] at hs
    rcases hs with hs | ⟨u, hu, hs⟩
    · exact hNF s hs
    · cases u with
      | Psi ξ π γ =>
        cases π with
        | Xi n p =>
          simp only [skx] at hs
          have hπF := (hNF _ (hcl _ hu (.Xi n p) (by simp [subs, self_mem_subs])))
          exact (FZNF.succK hπF.xi.1).of_mem_subs hs
        | _ => simp [skx] at hs
      | _ => simp [skx] at hs
  · intro ξ n p γ hψ _
    simp only [skClose, List.mem_append, List.mem_flatMap] at hψ ⊢
    rcases hψ with hψ | ⟨u, hu, hψ⟩
    · exact Or.inr ⟨_, hψ, by simp [skx, self_mem_subs]⟩
    · exfalso
      cases u with
      | Psi ξ' π' γ' =>
        cases π' with
        | Xi n' p' => simp [skx, _root_.RTKA.succK, subs] at hψ
        | _ => simp [skx] at hψ
      | _ => simp [skx] at hψ

/-- 三つの標準形の部分項全体（と `K_n^+`）は `GoodY` -/
theorem goodY3 {a b c : Tm} (ha : FZNF a) (hb : FZNF b) (hc : FZNF c) :
    GoodY (skClose (subs a ++ subs b ++ subs c)) := by
  apply skClose_good
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

theorem mem3_a (a b c : Tm) : a ∈ skClose (subs a ++ subs b ++ subs c) := by
  simp [skClose, self_mem_subs]

theorem mem3_b (a b c : Tm) : b ∈ skClose (subs a ++ subs b ++ subs c) := by
  simp [skClose, self_mem_subs]

theorem mem3_c (a b c : Tm) : c ∈ skClose (subs a ++ subs b ++ subs c) := by
  simp [skClose, self_mem_subs]

/-- `FZ` の標準形の上で順序の性質が成り立つ -/
instance instFZOrder : FZOrder where
  swap ha hb := (goodY3 ha hb hb).swap (mem3_a _ _ _) (mem3_b _ _ _)
  eq ha hb h := (goodY3 ha hb hb).eq (mem3_a _ _ _) (mem3_b _ _ _) h
  trans ha hb hc h1 h2 :=
    (goodY3 ha hb hc).trans (mem3_a _ _ _) (mem3_b _ _ _) (mem3_c _ _ _) h1 h2
  k2 h w hw := (goodY3 h h h).k2 _ _ _ (mem3_a _ _ _) w hw
  k2t h w hw := (goodY3 h h h).k2t _ _ _ (mem3_a _ _ _) w hw
  k2s h w hw := (goodY3 h h h).k2s _ _ _ (mem3_a _ _ _) w hw
  ms h := (goodY3 h h h).msS (mem3_a _ _ _)
  k2x h w hw := (goodY3 h h h).k2x _ _ (mem3_a _ _ _) w hw
  cx h := (goodY3 h h h).cx _ _ (mem3_a _ _ _)

/-- `FZ` の標準形の上の `<` は整礎（仮定なし） -/
theorem wellFounded_FZ_NF : WellFounded (fun a b : {t : Tm // FZNF t} => Lt a.1 b.1) :=
  wellFounded_FZ

end RTKA.Z
