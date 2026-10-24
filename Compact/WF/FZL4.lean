import Compact.WF.FZL3

/-! 断片 `FZ` の順序の性質の証明：新しい項が `t = Ψ^ξ_π(γ)` の場合の準備（`FYL4.lean` の `FZ` 版）。

`t` との非対称性を使わずに、比較を直接計算して示す。`FY` から増えるのは Mahlo 添字 `ξ` の扱い。

1. `GoodY.mi`（MI）：`Ψ^ξ_{Ξ_n(p)}(γ)` の `ξ` について `ξ ∈ C(ξ, Ξ_n(p))`。`ξ` の節点で `Ξ_n(p)` 以上のものは
   `K_n` 以上（`coll_xi0`）で、`ξ < p ≤ K_n^+` から目標は `K_n^+` 自身、引数はその節点未満になる。
2. `tb`・`tbge`・`below`・`tgt_contra`：`FY` と同じ。
3. `lemA`：`γ`・`π`・`ξ` の前線（`π` について）のどれか以下の `S` の元は `t` 未満（補題 A）。
4. `k2`・`k2t`・`k2s`・`cx`・`ms`（`ξ ∈ C(ξ, t)`）。 -/

namespace RTKA.Z

open Tm

/-! ### 道具 -/

theorem psiOm_lt_om_iff {c γ x : Tm} (hl : lev x = lev c) :
    Lt (.Psi .zero (.Om c) γ) (.Om x) ↔ ¬ Lt x c := by
  rw [lt_principal_iff rfl rfl, cmpP_psi0_om hl]
  unfold Lt
  cases cmp x c <;> simp

theorem OF_lt_om_iff {X x : Tm} (hX : IsOF X) (hl : lev x = lev X) :
    Lt X (.Om x) ↔ cmp x X = .gt := by
  rw [lt_principal_iff hX.principal rfl, cmpP_OF_om hX hl]
  cases cmp x X <;> simp

theorem IsTgt.principal {ρ : Tm} (h : IsTgt ρ) : isPrincipal ρ = true := by
  rcases h with ⟨c, rfl, -⟩ | ⟨n, r, rfl⟩ <;> rfl

theorem IsTgt.not_bot {ρ : Tm} (h : IsTgt ρ) : isBot ρ = false := by
  rcases h with ⟨c, rfl, -⟩ | ⟨n, r, rfl⟩ <;> rfl

theorem IsTgt.np {ρ : Tm} (h : IsTgt ρ) (σ κ β : Tm) : ρ ≠ .Psi σ κ β := by
  rcases h with ⟨c, rfl, -⟩ | ⟨n, r, rfl⟩ <;> intro e <;> cases e

theorem psiXiOF (ξ : Tm) (n : Nat) (r γ : Tm) : IsOF (.Psi ξ (.Xi n r) γ) := Or.inr ⟨ξ, n, r, γ, rfl⟩

namespace GoodY

variable {S : List Tm} (G : GoodY S)
include G

/-- `b < a + b`（`S` の中で） -/
theorem lt_plus_right : ∀ {a b : Tm}, Tm.plus a b ∈ S → Lt b (.plus a b)
  | a, b, hS => by
    have h := G.nf _ hS
    obtain ⟨-, hb, hap, hb0⟩ := h.plus
    have hbS := G.sub hS (show b ∈ subs (.plus a b) by simp [subs, self_mem_subs])
    have haS := G.sub hS (show a ∈ subs (.plus a b) by simp [subs, self_mem_subs])
    cases hs : summands b with
    | nil => exact absurd hs (summands_ne_nil hb0)
    | cons x xs =>
      have hxa := h.plus_head hs
      have hxm : x ∈ summands b := by rw [hs]; exact List.mem_cons_self
      have hx := summands_FZNF b hb x hxm
      have hxS := G.sub hbS (mem_subs_of_mem_summands hxm)
      have hxa' : cmpP x a ≠ .gt := by rwa [← cmp_principal hx.2 hap]
      unfold Lt
      rw [cmp_eq, hs, summands_plus, hs]
      cases e : cmpP x a with
      | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]
      | gt => exact absurd e hxa'
      | eq =>
        rw [cmpList_cons_cons_eq _ _ e]
        have hxe : x = a := G.eq_of_cmpP_eq hxS haS hx.2 hap e
        subst hxe
        cases b with
        | zero => exact absurd rfl hb0
        | plus p q =>
          rw [summands_plus, List.cons.injEq] at hs
          obtain ⟨rfl, hq⟩ := hs
          have := lt_plus_right hbS
          unfold Lt at this
          rw [cmp_eq, summands_plus] at this
          rwa [← hq]
        | _ =>
          simp only [summands, List.cons.injEq] at hs
          rw [← hs.2]
          exact cmpList_nil_cons _ _

/-- `z < c` なら `z + 1 ≤ c`（`S` の中で） -/
theorem succT_le {z c : Tm} (hcS : c ∈ S) (hsS : succT z ∈ S) (h : Lt z c) :
    Le (succT z) c := by
  refine G.le_of_ne_gt hsS hcS ?_
  rw [cmp_eq, summands_succT]
  unfold Lt at h
  rw [cmp_eq] at h
  exact cmpList_succ_ne_gtY _ _ (summands_FZNF c (G.nf c hcS)) h

/-- 階 `n + 1` の `Ω` の不動点は `K_n^+` より大きい -/
theorem succK_lt_OF {n : Nat} {X : Tm} (hX : IsOF X) (hXF : FZNF X) (hl : lev X = n + 1)
    (hK1S : Tm.plus (.K n) .one ∈ S)
    (hn : 1 ≤ n) : Lt (succK n) X := by
  have hKF : FZNF (.plus (.K n) .one) := G.nf _ hK1S
  refine (lt_om_OFG hX).mpr ((lt_plus_prin_iffY hKF hX.principal).mpr ?_)
  exact bot_ltY rfl (by simp only [lev]; omega) hX.principal
    (by rcases hX with ⟨m, a, rfl⟩ | ⟨ξ, m, p, a, rfl⟩ <;> rfl) hXF

/-- MI：`Ψ^ξ_{Ξ_n(p)}(γ)` の Mahlo 添字 `ξ` について `ξ ∈ C(ξ, Ξ_n(p))`（`K_n^+ ∈ S` のとき） -/
theorem mi {ξ γ p : Tm} {n : Nat} (ht : FZNF (.Psi ξ (.Xi n p) γ)) (hξS : ξ ∈ S)
    (hπS : Tm.Xi n p ∈ S) (hKS : succK n ∈ S) : inC ξ ξ (.Xi n p) = true := by
  have hπF := G.nf _ hπS
  obtain ⟨hn, -, -, hpK, -⟩ := hπF.xi
  have hpS := G.sub hπS (mem_subs_xi n p)
  have hK1S : Tm.plus (.K n) .one ∈ S := G.sub hKS (by simp [succK, subs])
  have hKnS : Tm.K n ∈ S := G.sub hK1S (by simp [subs])
  have hpKp : Le p (succK n) := G.le_of_ne_gt hpS hKS hpK
  obtain ⟨hξp, hξC⟩ : Lt ξ p ∧ inC ξ p (.Xi n p) = true := by
    rcases ht.psi.m with ⟨c, e, -⟩ | ⟨n', p', e, h1, h2⟩
    · cases e
    · cases e; exact ⟨h1, h2⟩
  have hξK : Lt ξ (succK n) := G.lt_of_lt_of_le hξS hpS hKS hξp hpKp
  -- 主張：`ξ` 以下の `S` の元 `x` について `x ∈ C(p, Ξ_n(p))` なら `x ∈ C(ξ, Ξ_n(p))`
  have key : ∀ N, ∀ x, x ∈ S → x.size ≤ N → Le x ξ → inC x p (.Xi n p) = true →
      inC x ξ (.Xi n p) = true := by
    intro N
    induction N with
    | zero => intro x _ h; exact absurd h (by have := Tm.size_pos x; omega)
    | succ N ih =>
      intro x hxS hs hxξ hx
      have hxF := G.nf _ hxS
      have hxK : Lt x (succK n) := G.lt_of_le_of_lt hxS hξS hKS hxξ hξK
      have hlx : lev x ≤ n + 1 := by
        have := lev_le_of_lt_gen hxK; simp only [succK, lev] at this; exact this
      cases x with
      | zero => exact inC_zero _ _
      | one => exact inC_one _ _
      | K m => exact inC_K m _ _
      | plus a b =>
        rw [inC_plus, Bool.and_eq_true] at hx ⊢
        obtain ⟨-, -, -, -⟩ := hxF.plus
        have haS := G.sub hxS (show a ∈ subs (.plus a b) by simp [subs, self_mem_subs])
        have hbS := G.sub hxS (show b ∈ subs (.plus a b) by simp [subs, self_mem_subs])
        exact ⟨ih a haS (by simp only [Tm.size] at hs; omega)
            (G.le_trans haS hxS hξS (Or.inr (lt_plus_leftY hxF)) hxξ) hx.1,
          ih b hbS (by simp only [Tm.size] at hs; omega)
            (G.le_trans hbS hxS hξS (Or.inr (G.lt_plus_right hxS)) hxξ) hx.2⟩
      | Om e =>
        rw [inC_om] at hx ⊢
        have heS := G.sub hxS (mem_subs_om e)
        exact ih e heS (by simp only [Tm.size] at hs; omega)
          (G.le_trans heS hxS hξS (Or.inr hxF.om.2.2) hxξ) hx
      | Xi m f =>
        refine inC_xi_iff.mpr (Or.inl ?_)
        rcases inC_xi_iff.mp hx with h | -
        · exact h
        simp only [lev] at hlx
        rcases Nat.lt_trichotomy m n with hm | hm | hm
        · exact lt_of_lev_lt' (by simp only [lev]; exact hm)
        · subst hm
          exact coll_xi0 hπF _ hxF hx ((lt_K_iffY hxF hn).mpr (Nat.le_refl _))
        · exfalso
          have hm' : m = n + 1 := by omega
          subst hm'
          exact G.asymm hKS hxS (G.succK_lt_OF (xiOF _ _) hxF rfl hK1S hn) hxK
      | Psi τ κ β =>
        by_cases hlt : Lt (.Psi τ κ β) (.Xi n p)
        · exact inC_psi_iff.mpr (Or.inl hlt)
        rcases inC_psi_iff.mp hx with h | ⟨hκ, hτ, hβ, hβp⟩
        · exact absurd h hlt
        have hP := hxF.psi
        have hlκ : lev κ = n + 1 := by
          simp only [lev] at hlx
          rcases Nat.lt_trichotomy (lev κ) n with h1 | h1 | h1
          · exact absurd (lt_of_lev_lt' (by simp only [lev]; exact h1)) hlt
          · exact absurd (coll_xi0 hπF _ hxF hx ((lt_K_iffY hxF hn).mpr
              (by simp only [lev]; omega))) hlt
          · omega
        rcases hP.m with ⟨c, rfl, rfl⟩ | ⟨m, q, rfl, -, -⟩
        · -- 目標は `Ω_c` で、`c = K_n + 1`
          have hcS := G.sub hxS (mem_subs_psi_c _ c β)
          have hβS := G.sub hxS (mem_subs_psi_a _ _ β)
          have hcF := G.nf _ hcS
          have hlc : lev c = n + 1 := hlκ
          have hKc : Lt (.K n) c := by
            rcases G.tri hKnS hcS with h | h | h
            · exact h
            · exact absurd h.symm (hP.piF.om_ne_k)
            · exfalso
              have := (lt_K_iffY hcF hn).mp h
              omega
          have hKc' : Le (.plus (.K n) .one) c := G.succT_le (z := .K n) hcS hK1S hKc
          have hcK : Le c (.plus (.K n) .one) := (G.lt_psi_omS hxS hK1S).mp hxK
          have hceq : c = .plus (.K n) .one := by
            rcases hcK with e | h
            · exact e
            · exact absurd h (G.not_lt_of_le hK1S hcS hKc')
          subst hceq
          have hβΩ : Lt β (.Om (.plus (.K n) .one)) :=
            G.lt_of_lt_of_le hβS hpS hKS hβp hpKp
          have hβx := G.coll_psiS hxS β hβS (G.inC_argS hxS) hβΩ
          have hβξ : Lt β ξ := G.lt_of_lt_of_le hβS hxS hξS hβx hxξ
          refine inC_psi_iff.mpr (Or.inr ⟨?_, inC_zero _ _, ?_, hβξ⟩)
          · simp [inC_om, inC_plus, inC_K, inC_one]
          · exact ih β hβS (by simp only [Tm.size] at hs; omega) (Or.inr hβξ) hβ
        · -- 目標が `Ξ_{n+1}(q)` なら `K_n^+` より大きい
          exfalso
          simp only [lev] at hlκ
          subst hlκ
          exact G.asymm hKS hxS (G.succK_lt_OF (psiXiOF _ _ _ _) hxF rfl hK1S hn) hxK
  exact key _ ξ hξS (Nat.le_refl _) (Or.inl rfl) hξC

/-- `S` の元 `Ψ^ξ_π(γ)` について `ξ ∈ C(ξ, π)` -/
theorem miS {ξ π γ : Tm} (ht : Tm.Psi ξ π γ ∈ S) : inC ξ ξ π = true := by
  have htF := G.nf _ ht
  rcases htF.psi.m with ⟨c, rfl, rfl⟩ | ⟨n, p, rfl, -, -⟩
  · exact inC_zero _ _
  · by_cases hξ : ξ = .zero
    · subst hξ; exact inC_zero _ _
    · exact G.mi htF (G.sub ht (by simp [subs, self_mem_subs]))
        (G.sub ht (by simp [subs, self_mem_subs])) (G.sk ξ n p γ ht hξ)

/-- `S` の元 `Ψ^ξ_π(γ)` について `ξ ∈ C(ξ, Ψ^ξ_π(γ))` -/
theorem msS {ξ π γ : Tm} (ht : Tm.Psi ξ π γ ∈ S) : inC ξ ξ (.Psi ξ π γ) = true :=
  inC_of_fr ξ (G.miS ht) (fun _ _ h => h)
    (fun w hw => inC_of_lt_node (fr_node hw) (G.k2s ξ π γ ht w hw))

end GoodY

/-- 新しい項 `t = Ψ^ξ_π(γ)` の文脈 -/
structure PsiCtxY (S : List Tm) (ξ π γ : Tm) : Prop where
  G : GoodY S
  ht : FZNF (.Psi ξ π γ)
  hsub : ∀ s, s ∈ subs (Tm.Psi ξ π γ) → s ≠ .Psi ξ π γ → s ∈ S
  htS : Tm.Psi ξ π γ ∉ S
  hsk : ∀ n p, π = .Xi n p → ξ ≠ .zero → succK n ∈ S

namespace PsiCtxY

variable {S : List Tm} {ξ π γ : Tm} (P : PsiCtxY S ξ π γ)
include P

theorem πS : π ∈ S :=
  P.hsub π (by simp [subs, self_mem_subs]) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))

theorem γS : γ ∈ S :=
  P.hsub γ (mem_subs_psi_a _ _ γ) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))

theorem ξS : ξ ∈ S :=
  P.hsub ξ (by simp [subs, self_mem_subs]) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))

theorem hT : IsTgt π := P.ht.psi.tgt

theorem πF : FZNF π := P.ht.psi.piF

theorem ne_of_mem {s : Tm} (hs : s ∈ S) : s ≠ .Psi ξ π γ := fun e => P.htS (e ▸ hs)

theorem lt_of_ne_gt {z : Tm} (hz : z ∈ S) (h : cmp z (.Psi ξ π γ) ≠ .gt) :
    Lt z (.Psi ξ π γ) :=
  P.G.lt_of_ne_gt_new P.ht P.hsub P.htS hz h

/-- `Ψ` でない主要項 `y` について `y < t ⟺ ¬ t < y` -/
theorem lt_iff_np {y : Tm} (hy : y ∈ S) (hyp : isPrincipal y = true)
    (hnp : ∀ σ κ β, y ≠ .Psi σ κ β) :
    Lt y (.Psi ξ π γ) ↔ ¬ Lt (.Psi ξ π γ) y := by
  have hs := P.G.swapP_new P.ht P.hsub hy rfl hyp
    (fun _ _ _ σ κ β _ e => absurd e (hnp σ κ β))
  have hne := (P.G.ne_new P.ht P.hsub P.htS y hy).1
  rw [cmp_principal hyp rfl, hs] at hne
  rw [lt_principal_iff hyp rfl, lt_principal_iff rfl hyp, hs]
  revert hne
  cases cmpP (Tm.Psi ξ π γ) y <;> decide

theorem tgt_lt {ρ : Tm} (hρS : ρ ∈ S) (hρT : IsTgt ρ) (h : ¬ Lt (.Psi ξ π γ) ρ) :
    Lt ρ (.Psi ξ π γ) :=
  (P.lt_iff_np hρS hρT.principal hρT.np).mpr h

theorem not_lt_tgt {ρ : Tm} (hρS : ρ ∈ S) (hρT : IsTgt ρ) (h : Lt ρ (.Psi ξ π γ)) :
    ¬ Lt (.Psi ξ π γ) ρ :=
  (P.lt_iff_np hρS hρT.principal hρT.np).mp h

/-- MI：`ξ ∈ C(ξ, π)` -/
theorem mi : inC ξ ξ π = true := by
  rcases P.ht.psi.m with ⟨c, rfl, rfl⟩ | ⟨n, p, rfl, -, -⟩
  · exact inC_zero _ _
  · by_cases hξ : ξ = .zero
    · subst hξ; exact inC_zero _ _
    · exact P.G.mi P.ht P.ξS P.πS (P.hsk n p rfl hξ)

/-! ### `S` の `Ψ` が `t` 未満になる条件 -/

theorem psi_lt_of_tgt {τ ρ α : Tm} (hq : Tm.Psi τ ρ α ∈ S) (hl : lev ρ = lev π)
    (h : ¬ Lt (.Psi ξ π γ) ρ) : Lt (.Psi τ ρ α) (.Psi ξ π γ) :=
  (lt_psi_psiY hl (P.ne_of_mem hq)).mpr (Or.inl h)

theorem psi_lt_of_c1 {τ ρ α : Tm} (hq : Tm.Psi τ ρ α ∈ S) (hl : lev ρ = lev π)
    (htρ : Lt (.Psi ξ π γ) ρ) (hqπ : Lt (.Psi τ ρ α) π) (hαγ : Lt α γ)
    (h1 : inC α γ (.Psi ξ π γ) = true) (h2 : inC τ γ (.Psi ξ π γ) = true)
    (h3 : inC ρ γ (.Psi ξ π γ) = true) :
    Lt (.Psi τ ρ α) (.Psi ξ π γ) :=
  (lt_psi_psiY hl (P.ne_of_mem hq)).mpr (Or.inr ⟨htρ, hqπ, Or.inl ⟨hαγ, h1, h2, h3⟩⟩)

theorem psi_lt_of_c2 {τ ρ α : Tm} (hq : Tm.Psi τ ρ α ∈ S) (hl : lev ρ = lev π)
    (htρ : Lt (.Psi ξ π γ) ρ) (hqπ : Lt (.Psi τ ρ α) π) (hγα : cmp γ α ≠ .gt)
    (hn : ¬ (inC γ α (.Psi τ ρ α) = true ∧ inC ξ α (.Psi τ ρ α) = true ∧
      inC π α (.Psi τ ρ α) = true)) :
    Lt (.Psi τ ρ α) (.Psi ξ π γ) :=
  (lt_psi_psiY hl (P.ne_of_mem hq)).mpr (Or.inr ⟨htρ, hqπ, Or.inr (Or.inl ⟨hγα, hn⟩)⟩)

theorem psi_lt_of_c3 {τ α : Tm} (hq : Tm.Psi τ π α ∈ S) (he : cmp α γ = .eq)
    (hτξ : Lt τ ξ) (hC : inC τ γ (.Psi ξ π γ) = true) :
    Lt (.Psi τ π α) (.Psi ξ π γ) :=
  (lt_psi_psiY rfl (P.ne_of_mem hq)).mpr (Or.inr ⟨lt_psi_targetY P.ht,
    lt_psi_targetY (P.G.nf _ hq), Or.inr (Or.inr (Or.inl ⟨he, rfl, hτξ, hC⟩))⟩)

theorem psi_lt_of_c4 {τ ρ α : Tm} (hq : Tm.Psi τ ρ α ∈ S) (hl : lev ρ = lev π)
    (htρ : Lt (.Psi ξ π γ) ρ) (hqπ : Lt (.Psi τ ρ α) π) (hξτ : Lt ξ τ)
    (hn : inC ξ τ (.Psi τ ρ α) = false) :
    Lt (.Psi τ ρ α) (.Psi ξ π γ) :=
  (lt_psi_psiY hl (P.ne_of_mem hq)).mpr (Or.inr ⟨htρ, hqπ, Or.inr (Or.inr (Or.inr ⟨hξτ, hn⟩))⟩)

/-- `Ξ_m(f) < t` の条件 -/
theorem xi_lt_t {m : Nat} {f : Tm} (hX : Tm.Xi m f ∈ S) (hl : lev π = m)
    (hXπ : Lt (.Xi m f) π)
    (hfr : Lt f γ → ∀ u, u ∈ fr (.K m) f → Lt u (.Psi ξ π γ)) :
    Lt (.Xi m f) (.Psi ξ π γ) := by
  have G := P.G
  have hfS := G.sub hX (mem_subs_xi m f)
  rw [lt_xi_psiY hl, lt_psi_xiY hl]
  rintro (h | ⟨hfγ, hn⟩)
  · apply h
    unfold Lt at hXπ
    rw [G.swap hX P.πS, hXπ]
    decide
  · rw [inC_of_fr f (G.nf _ hX).xi.2.2.2.2 (fun v hv h' => G.trans (G.sub hfS hv) hfS P.γS h' hfγ)
      (fun u hu => inC_of_lt_node (fr_node hu) (hfr hfγ u hu))] at hn
    cases hn

theorem xi_lt_t_inv {m : Nat} {f : Tm} (hX : Tm.Xi m f ∈ S) (hl : lev π = m)
    (h : Lt (.Xi m f) (.Psi ξ π γ)) :
    Lt (.Xi m f) π ∧ (Lt f γ → inC f γ (.Psi ξ π γ) = true) := by
  rw [lt_xi_psiY hl, lt_psi_xiY hl] at h
  refine ⟨P.G.lt_of_gt P.πS hX ?_, fun hfγ => ?_⟩
  · cases e : cmp π (Tm.Xi m f)
    · exact absurd (Or.inl (by rw [e]; decide)) h
    · exact absurd (Or.inl (by rw [e]; decide)) h
    · rfl
  · cases e : inC f γ (Tm.Psi ξ π γ)
    · exact absurd (Or.inr ⟨hfγ, e⟩) h
    · rfl

/-- `t` の引数・目標・Mahlo 添字の前線 -/
def InF (w : Tm) : Prop := w ∈ fr π γ ∨ w ∈ fr π π ∨ w ∈ fr π ξ

/-- 前線の証人：`γ ≤ g` で `γ`・`ξ`・`π` のどれかが `C(g, d)` に入らなければ、その前線に `d` 未満でない元がある -/
theorem wit {g d : Tm} (hg : Le γ g) (hgS : g ∈ S)
    (hn : ¬ (inC γ g d = true ∧ inC ξ g d = true ∧ inC π g d = true)) :
    ∃ w, (w ∈ fr π γ ∨ w ∈ fr π π ∨ w ∈ fr π ξ) ∧ ¬ Lt w d := by
  have G := P.G
  have hP := P.ht.psi
  cases e1 : inC γ g d
  · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hP.Ca
      (fun v hv h => G.lt_of_lt_of_le (G.sub P.γS hv) P.γS hgS h hg) e1
    exact ⟨w, Or.inl hw, hwn⟩
  · cases e2 : inC ξ g d
    · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hP.Cxi
        (fun v hv h => G.lt_of_lt_of_le (G.sub P.ξS hv) P.γS hgS h hg) e2
      exact ⟨w, Or.inr (Or.inr hw), hwn⟩
    · cases e3 : inC π g d
      · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hP.Cpi
          (fun v hv h => G.lt_of_lt_of_le (G.sub P.πS hv) P.γS hgS h hg) e3
        exact ⟨w, Or.inr (Or.inl hw), hwn⟩
      · exact absurd ⟨e1, e2, e3⟩ hn

/-- 前線の証人（(4) の形）：`ξ < τ` で `ξ ∉ C(τ, d)` なら、`ξ` の前線（`π` について）に `d` 未満でない元がある -/
theorem wit4 {τ d : Tm} (hτS : τ ∈ S) (hξτ : Lt ξ τ) (hn : inC ξ τ d = false) :
    ∃ w, w ∈ fr π ξ ∧ ¬ Lt w d :=
  wit_of_not_inC P.mi (fun v hv h => P.G.trans (P.G.sub P.ξS hv) P.ξS hτS h hξτ) hn

theorem F_spec {w : Tm} (hw : w ∈ fr π γ ∨ w ∈ fr π π ∨ w ∈ fr π ξ) : w ∈ S ∧ Lt w π := by
  rcases hw with hw | hw | hw
  · exact ⟨P.G.sub P.γS (fr_spec hw).1, (fr_spec hw).2⟩
  · exact ⟨P.G.sub P.πS (fr_spec hw).1, (fr_spec hw).2⟩
  · exact ⟨P.G.sub P.ξS (fr_spec hw).1, (fr_spec hw).2⟩

/-! ### `t` 未満の元は `π` 未満 -/

theorem tb_aux : ∀ N, ∀ z, z ∈ S → z.size ≤ N →
    (Lt z (.Psi ξ π γ) → Lt z π) ∧
      (isPrincipal z = true → ¬ Lt (.Psi ξ π γ) z → Lt z π) := by
  have G := P.G
  have hπp := P.hT.principal
  have hπb := P.hT.not_bot
  intro N
  induction N with
  | zero => intro z _ h; exact absurd h (by have := Tm.size_pos z; omega)
  | succ N ih =>
    have prin : ∀ y, y ∈ S → y.size ≤ N + 1 → isPrincipal y = true →
        (Lt y (.Psi ξ π γ) → Lt y π) ∧ (¬ Lt (.Psi ξ π γ) y → Lt y π) := by
      intro y hy hs hyp
      have hyF := G.nf y hy
      by_cases hl1 : lev y < lev π
      · exact ⟨fun _ => lt_of_lev_lt' hl1, fun _ => lt_of_lev_lt' hl1⟩
      by_cases hl2 : lev π < lev y
      · refine ⟨fun h => absurd (lev_le_of_lt_gen h) (by simp only [lev]; omega),
          fun h => absurd (lt_of_lev_lt' (by simp only [lev]; omega)) h⟩
      have hl : lev y = lev π := by omega
      by_cases hb : isBot y = true
      · have := bot_ltY hb (Nat.le_of_eq hl) hπp hπb P.πF
        exact ⟨fun _ => this, fun _ => this⟩
      rcases shape_FY3 hyF hyp (Bool.eq_false_iff.mpr hb) with
        ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨τ, ρ, δ, rfl⟩
      · have hx := G.sub hy (mem_subs_om x)
        have ihx := ih x hx (by simp only [Tm.size] at hs; omega)
        rcases P.ht.psi.m with ⟨c, rfl, rfl⟩ | ⟨n, r0, rfl, -, -⟩
        · have hcS := G.sub P.πS (mem_subs_om c)
          have hl' : lev x = lev c := hl
          refine ⟨fun h => (G.lt_om_iffS hx hcS).mpr ((lt_om_psiY P.ht).mp h), fun h => ?_⟩
          refine (G.lt_om_iffS hx hcS).mpr ?_
          by_cases hxc : Lt x c
          · exact hxc
          · exact absurd ((psiOm_lt_om_iff hl').mpr hxc) h
        · have hOF := psiXiOF ξ n r0 γ
          have hl' : lev x = lev (Tm.Psi ξ (.Xi n r0) γ) := hl
          refine ⟨fun h => (lt_om_OFG (xiOF _ _)).mpr (ihx.1 ((lt_om_OFG hOF).mp h)), fun h => ?_⟩
          refine (lt_om_OFG (xiOF _ _)).mpr (ihx.1 (P.lt_of_ne_gt hx ?_))
          intro e
          exact h ((OF_lt_om_iff hOF hl').mpr e)
      · have hl' : lev π = m := hl.symm
        have key : ¬ Lt (.Psi ξ π γ) (.Xi m f) → Lt (.Xi m f) π := fun h => by
          rw [lt_psi_xiY hl'] at h
          refine G.lt_of_gt P.πS hy ?_
          cases e : cmp π (Tm.Xi m f)
          · exact absurd (Or.inl (by rw [e]; decide)) h
          · exact absurd (Or.inl (by rw [e]; decide)) h
          · rfl
        exact ⟨fun h => key ((lt_xi_psiY hl').mp h), key⟩
      · have hyF' := hyF.psi
        have hρS : ρ ∈ S := G.sub hy (by simp [subs, self_mem_subs])
        have hl' : lev ρ = lev π := hl
        have hne := P.ne_of_mem hy
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rcases (lt_psi_psiY hl' hne).mp h with h' | ⟨-, h', -⟩
          · have := (ih ρ hρS (by simp only [Tm.size] at hs; omega)).2 hyF'.tgt.principal h'
            exact G.trans hy hρS P.πS (lt_psi_targetY hyF) this
          · exact h'
        · by_cases h' : Lt (.Psi τ ρ δ) π
          · exact h'
          · exact absurd ((lt_psi_psiY hl'.symm (fun e => hne e.symm)).mpr (Or.inl h')) h
    intro z hz hs
    have hzF := G.nf z hz
    refine ⟨fun hzt => ?_, fun hzp => (prin z hz hs hzp).2⟩
    cases hsz : summands z with
    | nil =>
      have : z = .zero := by cases z <;> simp_all [summands]
      subst this
      exact zero_lt (by rcases P.hT with ⟨c, rfl, -⟩ | ⟨n, r, rfl⟩ <;> intro e <;> cases e)
    | cons h rest =>
      have hmem : h ∈ summands z := by rw [hsz]; exact List.mem_cons_self
      have hhS := G.sub hz (mem_subs_of_mem_summands hmem)
      obtain ⟨-, hhp⟩ := summands_FZNF z hzF h hmem
      have hhs := size_le_of_mem_summands z h hmem
      have hht : Lt h (.Psi ξ π γ) :=
        (lt_principal_iff hhp rfl).mpr (cmpP_head_of_lt hsz rfl hzt)
      have := (prin h hhS (by omega) hhp).1 hht
      exact lt_of_head_lt hπp hsz ((lt_principal_iff hhp hπp).mp this)

/-- `t` 未満の `S` の元は `π` 未満 -/
theorem tb {z : Tm} (hz : z ∈ S) (h : Lt z (.Psi ξ π γ)) : Lt z π :=
  (P.tb_aux _ z hz (Nat.le_refl _)).1 h

/-- `t` が上にない主要項は `π` 未満 -/
theorem tbge {z : Tm} (hz : z ∈ S) (hzp : isPrincipal z = true)
    (h : ¬ Lt (.Psi ξ π γ) z) : Lt z π :=
  (P.tb_aux _ z hz (Nat.le_refl _)).2 hzp h

/-! ### `t < ρ ≤ v < π` の矛盾 -/

theorem tgt_contra {ρ v : Tm} (hρS : ρ ∈ S) (hρT : IsTgt ρ) (hl : lev ρ = lev π)
    (htρ : Lt (.Psi ξ π γ) ρ) (hvS : v ∈ S) (hρv : Le ρ v) (hvπ : Lt v π)
    (H : ∀ u, u ∈ S → u.size < ρ.size → Lt u v → Lt u (.Psi ξ π γ)) : False := by
  have G := P.G
  rcases hρT with ⟨d, rfl, -⟩ | ⟨m, r, rfl⟩
  · have hdS := G.sub hρS (mem_subs_om d)
    rcases P.ht.psi.m with ⟨c, rfl, rfl⟩ | ⟨n, r0, rfl, -, -⟩
    · have hl' : lev d = lev c := hl
      have hcS := G.sub P.πS (mem_subs_om c)
      exact (psiOm_lt_om_iff hl').mp htρ
        ((G.lt_om_iffS hdS hcS).mp (G.lt_of_le_of_lt hρS hvS P.πS hρv hvπ))
    · have hl' : lev d = lev (Tm.Psi ξ (.Xi n r0) γ) := hl
      have e := (OF_lt_om_iff (psiXiOF ξ n r0 γ) hl').mp htρ
      have hdv : Lt d v := G.lt_of_lt_of_le hdS hρS hvS (G.nf _ hρS).om.2.2 hρv
      have := H d hdS (by simp only [Tm.size]; omega) hdv
      unfold Lt at this
      rw [this] at e
      cases e
  · have hrS := G.sub hρS (mem_subs_xi m r)
    have hl' : lev π = m := hl.symm
    rcases (lt_psi_xiY hl').mp htρ with h | ⟨hrγ, hn⟩
    · apply h
      have := G.lt_of_le_of_lt hρS hvS P.πS hρv hvπ
      unfold Lt at this
      rw [G.swap hρS P.πS, this]
      decide
    · obtain ⟨u, hu, hun⟩ := wit_of_not_inC (G.nf _ hρS).xi.2.2.2.2
        (fun w hw h' => G.trans (G.sub hrS hw) hrS P.γS h' hrγ) hn
      have huS := G.sub hrS (fr_spec hu).1
      have := size_le_of_mem_subs (fr_spec hu).1
      exact hun (H u huS (by simp only [Tm.size]; omega)
        (G.lt_of_lt_of_le huS hρS hvS (G.k2x m r hρS u hu) hρv))

/-! ### `π = Ω_c` のとき：`c` 未満なら `t` 未満 -/

theorem below_aux {c : Tm} (hπ : π = .Om c) : ∀ N, ∀ v, v ∈ S → v.size ≤ N →
    Lt v c → Lt v (.Psi ξ π γ) := by
  subst hπ
  have hξ0 : ξ = .zero := P.ht.psiOm.2.2.2.2.2
  subst hξ0
  have G := P.G
  have hcS := G.sub P.πS (mem_subs_om c)
  have hcΩ : Lt c (.Om c) := P.πF.om.2.2
  intro N
  induction N with
  | zero => intro v _ h; exact absurd h (by have := Tm.size_pos v; omega)
  | succ N ih =>
    intro v hvS hs hvc
    have hvF := G.nf _ hvS
    cases hsv : summands v with
    | nil =>
      have : v = .zero := by cases v <;> simp_all [summands]
      subst this
      exact zero_lt (by intro e; cases e)
    | cons h rest =>
      have hmem : h ∈ summands v := by rw [hsv]; exact List.mem_cons_self
      have hhS := G.sub hvS (mem_subs_of_mem_summands hmem)
      obtain ⟨hhF, hhp⟩ := summands_FZNF v hvF h hmem
      have hhs := size_le_of_mem_summands v h hmem
      have hhc : Lt h c := G.lt_of_le_of_lt hhS hvS hcS (head_leY hvF hsv) hvc
      have IH : ∀ u, u ∈ S → u.size < h.size → Lt u c → Lt u (.Psi .zero (.Om c) γ) :=
        fun u hu hus huc => ih u hu (by omega) huc
      have hht : Lt h (.Psi .zero (.Om c) γ) := by
        have hl := lev_le_of_lt_gen hhc
        rcases Nat.lt_or_eq_of_le hl with hl | hl
        · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
        by_cases hb : isBot h = true
        · exact bot_ltY hb (by simp only [lev]; omega) rfl rfl P.ht
        rcases shape_FY4 hhF hhp (Bool.eq_false_iff.mpr hb) with
          ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨d, δ, rfl⟩ | ⟨τ, m, r, δ, rfl⟩
        · have hx := G.sub hhS (mem_subs_om x)
          exact (lt_om_psiY P.ht).mpr (G.trans hx hhS hcS hhF.om.2.2 hhc)
        · simp only [lev] at hl
          refine P.xi_lt_t hhS hl.symm (G.trans hhS hcS P.πS hhc hcΩ) (fun _ u hu => ?_)
          have hfS := G.sub hhS (mem_subs_xi m f)
          have huS := G.sub hfS (fr_spec hu).1
          have := size_le_of_mem_subs (fr_spec hu).1
          exact IH u huS (by simp only [Tm.size]; omega)
            (G.trans huS hhS hcS (G.k2x m f hhS u hu) hhc)
        · have hdS := G.sub hhS (mem_subs_psi_c _ d δ)
          have hdc := G.trans hdS hhS hcS (G.cx d δ hhS) hhc
          simp only [lev] at hl
          exact P.psi_lt_of_tgt hhS hl (fun h' => (psiOm_lt_om_iff hl).mp h' hdc)
        · simp only [lev] at hl
          have hρS : Tm.Xi m r ∈ S := G.sub hhS (by simp [subs])
          have hrS := G.sub hρS (mem_subs_xi m r)
          have hτS : τ ∈ S := G.sub hhS (by simp [subs, self_mem_subs])
          have hδS := G.sub hhS (mem_subs_psi_a _ _ δ)
          have hhπ : Lt (.Psi τ (.Xi m r) δ) (.Om c) := G.trans hhS hcS P.πS hhc hcΩ
          have hP := hhF.psi
          by_cases htρ' : ¬ Lt (.Psi .zero (.Om c) γ) (.Xi m r)
          · exact P.psi_lt_of_tgt hhS hl htρ'
          have htρ : Lt (.Psi .zero (.Om c) γ) (.Xi m r) := Decidable.of_not_not htρ'
          have hcρ : Lt c (.Xi m r) := by
            rcases (lt_psi_xiY (π := .Om c) hl.symm).mp htρ with h' | ⟨hrγ, hn⟩
            · rw [cmp_principal rfl rfl, cmpP_om_xi hl.symm] at h'
              rcases G.le_of_ne_gt hcS hρS h' with e | e
              · exfalso
                rcases P.hT with ⟨c', e', hsc⟩ | ⟨n', r', e'⟩
                · cases e'
                  rw [e] at hsc
                  simp [isSucc, summands] at hsc
                · cases e'
              · exact e
            · exfalso
              obtain ⟨u, hu, hun⟩ := wit_of_not_inC (G.nf _ hρS).xi.2.2.2.2
                (fun w hw h' => G.trans (G.sub hrS hw) hrS P.γS h' hrγ) hn
              have huS := G.sub hrS (fr_spec hu).1
              have := size_le_of_mem_subs (fr_spec hu).1
              exact hun (IH u huS (by simp only [Tm.size]; omega)
                (G.trans huS hhS hcS (G.k2t _ _ δ hhS u (G.fr_xi_sub hρS hu)) hhc))
          have frIH : ∀ x, x ∈ S → x.size < (Tm.Psi τ (.Xi m r) δ).size →
              (∀ w, w ∈ fr (.Xi m r) x → Lt w (.Psi τ (.Xi m r) δ)) →
              ∀ u, u ∈ fr (.Xi m r) x → inC u γ (.Psi .zero (.Om c) γ) = true :=
            fun x hx hxs hk u hu => by
              refine inC_of_lt_node (fr_node hu) ?_
              have huS := G.sub hx (fr_spec hu).1
              have := size_le_of_mem_subs (fr_spec hu).1
              exact IH u huS (by omega) (G.trans huS hhS hcS (hk u hu) hhc)
          rcases G.tri hδS P.γS with h' | h' | h'
          · refine P.psi_lt_of_c1 hhS hl htρ hhπ h' ?_ ?_ ?_
            · exact inC_of_fr δ hP.Ca (fun v hv hv' => G.trans (G.sub hδS hv) hδS P.γS hv' h')
                (frIH δ hδS (by simp only [Tm.size]; omega) (G.k2 _ _ δ hhS))
            · exact inC_of_fr τ hP.Cxi (fun v hv hv' => G.trans (G.sub hτS hv) hδS P.γS hv' h')
                (frIH τ hτS (by simp only [Tm.size]; omega) (G.k2s _ _ δ hhS))
            · exact inC_of_fr _ hP.Cpi (fun v hv hv' => G.trans (G.sub hρS hv) hδS P.γS hv' h')
                (frIH _ hρS (by simp only [Tm.size]; omega) (G.k2t _ _ δ hhS))
          all_goals
            refine P.psi_lt_of_c2 hhS hl htρ hhπ (ne_gt_of_le ?_) (fun ⟨_, _, hin⟩ => ?_)
            · first | exact Or.inl h'.symm | exact Or.inr h'
            · rw [inC_om] at hin
              exact G.asymm hcS hhS (G.coll_psiS hhS c hcS hin hcρ) hhc
      exact lt_of_head_lt rfl hsv ((lt_principal_iff hhp rfl).mp hht)

/-- `π = Ω_c` なら、`c` 未満の `S` の元は `t` 未満 -/
theorem below {c v : Tm} (hπ : π = .Om c) (hv : v ∈ S) (h : Lt v c) : Lt v (.Psi ξ π γ) :=
  P.below_aux hπ _ v hv (Nat.le_refl _) h

/-! ### 補題 A -/

/-- 補題 A の主要項の場合 -/
theorem lemA_head {h w : Tm} (hhS : h ∈ S) (hhp : isPrincipal h = true)
    (hw : w ∈ fr π γ ∨ w ∈ fr π π ∨ w ∈ fr π ξ) (hhw : Le h w)
    (IH : ∀ u, u ∈ S → u.size < h.size → Le u w → Lt u (.Psi ξ π γ)) :
    Lt h (.Psi ξ π γ) := by
  have G := P.G
  have hhF := G.nf _ hhS
  obtain ⟨hwS, hwπ⟩ := P.F_spec hw
  have hhπ : Lt h π := G.lt_of_le_of_lt hhS hwS P.πS hhw hwπ
  have hl := lev_le_of_lt_gen hhπ
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
  by_cases hb : isBot h = true
  · exact bot_ltY hb (by simp only [lev]; omega) rfl rfl P.ht
  rcases shape_FY3 hhF hhp (Bool.eq_false_iff.mpr hb) with ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨τ, ρ, δ, rfl⟩
  · have hx := G.sub hhS (mem_subs_om x)
    rcases P.ht.psi.m with ⟨c, rfl, rfl⟩ | ⟨n, r0, rfl, -, -⟩
    · have hcS := G.sub P.πS (mem_subs_om c)
      exact (lt_om_psiY P.ht).mpr ((G.lt_om_iffS hx hcS).mp hhπ)
    · exact (lt_om_OFG (psiXiOF _ _ _ _)).mpr (IH x hx (by simp only [Tm.size]; omega)
        (Or.inr (G.lt_of_lt_of_le hx hhS hwS hhF.om.2.2 hhw)))
  · simp only [lev] at hl
    refine P.xi_lt_t hhS hl.symm hhπ (fun _ u hu => ?_)
    have hfS := G.sub hhS (mem_subs_xi m f)
    have huS := G.sub hfS (fr_spec hu).1
    have := size_le_of_mem_subs (fr_spec hu).1
    exact IH u huS (by simp only [Tm.size]; omega)
      (Or.inr (G.lt_of_lt_of_le huS hhS hwS (G.k2x m f hhS u hu) hhw))
  · have hρS : ρ ∈ S := G.sub hhS (by simp [subs, self_mem_subs])
    have hτS : τ ∈ S := G.sub hhS (by simp [subs, self_mem_subs])
    have hδS := G.sub hhS (mem_subs_psi_a _ _ δ)
    have hP := hhF.psi
    have hl' : lev ρ = lev π := hl
    by_cases htρ' : ¬ Lt (.Psi ξ π γ) ρ
    · exact P.psi_lt_of_tgt hhS hl' htρ'
    have htρ : Lt (.Psi ξ π γ) ρ := Decidable.of_not_not htρ'
    have frIH : ∀ x, x ∈ S → x.size < (Tm.Psi τ ρ δ).size →
        (∀ u, u ∈ fr ρ x → Lt u (.Psi τ ρ δ)) →
        ∀ u, u ∈ fr ρ x → inC u γ (.Psi ξ π γ) = true :=
      fun x hx hxs hk u hu => by
        refine inC_of_lt_node (fr_node hu) ?_
        have huS := G.sub hx (fr_spec hu).1
        have := size_le_of_mem_subs (fr_spec hu).1
        exact IH u huS (by omega) (Or.inr (G.lt_of_lt_of_le huS hhS hwS (hk u hu) hhw))
    rcases G.tri hδS P.γS with h' | h' | h'
    · refine P.psi_lt_of_c1 hhS hl' htρ hhπ h' ?_ ?_ ?_
      · exact inC_of_fr δ hP.Ca (fun v hv hv' => G.trans (G.sub hδS hv) hδS P.γS hv' h')
          (frIH δ hδS (by simp only [Tm.size]; omega) (G.k2 _ _ δ hhS))
      · exact inC_of_fr τ hP.Cxi (fun v hv hv' => G.trans (G.sub hτS hv) hδS P.γS hv' h')
          (frIH τ hτS (by simp only [Tm.size]; omega) (G.k2s _ _ δ hhS))
      · exact inC_of_fr ρ hP.Cpi (fun v hv hv' => G.trans (G.sub hρS hv) hδS P.γS hv' h')
          (frIH ρ hρS (by simp only [Tm.size]; omega) (G.k2t _ _ δ hhS))
    all_goals
      -- `w < ρ`
      have hwρ : Lt w ρ := by
        rcases G.tri hwS hρS with e | e | e
        · exact e
        all_goals
          exfalso
          refine P.tgt_contra hρS hP.tgt hl' htρ hwS (by first | exact Or.inl e.symm | exact Or.inr e)
            hwπ (fun u hu hus huw => IH u hu (by simp only [Tm.size]; omega) (Or.inr huw))
      refine P.psi_lt_of_c2 hhS hl' htρ hhπ
        (ne_gt_of_le (by first | exact Or.inl h'.symm | exact Or.inr h'))
        (fun ⟨hin1, hin2, hin3⟩ => ?_)
      have hd : ∀ x, x ∈ S → ∀ w', w' ∈ subs x → ¬ Lt w' π →
          ¬ Lt w' (.Psi τ ρ δ) := fun x hx w' hw' hn hlt =>
        hn (G.trans (G.sub hx hw') hhS P.πS hlt hhπ)
      have hinw : inC w δ (.Psi τ ρ δ) = true := by
        rcases hw with hw | hw | hw
        · exact fr_of_inC γ (hd γ P.γS) hin1 w hw
        · exact fr_of_inC π (hd π P.πS) hin3 w hw
        · exact fr_of_inC ξ (hd ξ P.ξS) hin2 w hw
      exact G.not_lt_of_le hhS hwS hhw (G.coll_psiS hhS w hwS hinw hwρ)

/-- 補題 A：`γ`・`π`・`ξ` の前線のどれか以下の `S` の元は `t` 未満 -/
theorem lemA_aux : ∀ N, ∀ v, v ∈ S → v.size ≤ N →
    (∃ w, (w ∈ fr π γ ∨ w ∈ fr π π ∨ w ∈ fr π ξ) ∧ Le v w) → Lt v (.Psi ξ π γ) := by
  have G := P.G
  intro N
  induction N with
  | zero => intro v _ h; exact absurd h (by have := Tm.size_pos v; omega)
  | succ N ih =>
    intro v hvS hs ⟨w, hw, hvw⟩
    have hvF := G.nf _ hvS
    obtain ⟨hwS, -⟩ := P.F_spec hw
    cases hsv : summands v with
    | nil =>
      have : v = .zero := by cases v <;> simp_all [summands]
      subst this
      exact zero_lt (by intro e; cases e)
    | cons h rest =>
      have hmem : h ∈ summands v := by rw [hsv]; exact List.mem_cons_self
      have hhS := G.sub hvS (mem_subs_of_mem_summands hmem)
      obtain ⟨-, hhp⟩ := summands_FZNF v hvF h hmem
      have hhs := size_le_of_mem_summands v h hmem
      have hhw : Le h w := G.le_trans hhS hvS hwS (head_leY hvF hsv) hvw
      have hht := P.lemA_head hhS hhp hw hhw (fun u hu hus huw => ih u hu (by omega) ⟨w, hw, huw⟩)
      exact lt_of_head_lt rfl hsv ((lt_principal_iff hhp rfl).mp hht)

theorem lemA {v : Tm} (hv : v ∈ S)
    (h : ∃ w, (w ∈ fr π γ ∨ w ∈ fr π π ∨ w ∈ fr π ξ) ∧ Le v w) : Lt v (.Psi ξ π γ) :=
  P.lemA_aux _ v hv (Nat.le_refl _) h

/-- K2：`γ` の前線は全て `t` 未満 -/
theorem k2 : ∀ w, w ∈ fr π γ → Lt w (.Psi ξ π γ) := fun w hw =>
  P.lemA (P.F_spec (Or.inl hw)).1 ⟨w, Or.inl hw, Le.refl _⟩

/-- K2T：`π` の前線は全て `t` 未満 -/
theorem k2t : ∀ w, w ∈ fr π π → Lt w (.Psi ξ π γ) := fun w hw =>
  P.lemA (P.F_spec (Or.inr (Or.inl hw))).1 ⟨w, Or.inr (Or.inl hw), Le.refl _⟩

/-- K2S：`ξ` の前線は全て `t` 未満 -/
theorem k2s : ∀ w, w ∈ fr π ξ → Lt w (.Psi ξ π γ) := fun w hw =>
  P.lemA (P.F_spec (Or.inr (Or.inr hw))).1 ⟨w, Or.inr (Or.inr hw), Le.refl _⟩

theorem inC_arg : inC γ γ (.Psi ξ π γ) = true := inC_arg_of_k2 P.ht P.k2

theorem inC_tgt : inC π γ (.Psi ξ π γ) = true := inC_tgt_of_k2t P.ht P.k2t

theorem inC_mahlo : inC ξ γ (.Psi ξ π γ) = true := inC_mahlo_of_k2s P.ht P.k2s

/-- MS：`ξ ∈ C(ξ, t)` -/
theorem ms : inC ξ ξ (.Psi ξ π γ) = true :=
  inC_of_fr ξ P.mi (fun _ _ h => h) (fun w hw => inC_of_lt_node (fr_node hw) (P.k2s w hw))

/-- CX：`π = Ω_c` なら `c < t` -/
theorem cx {c : Tm} (hπ : π = .Om c) : Lt c (.Psi ξ π γ) := by
  have G := P.G
  have hΩS : Tm.Om c ∈ S := hπ ▸ P.πS
  have hcS := G.sub hΩS (mem_subs_om c)
  have hΩF := G.nf _ hΩS
  have hs : isSucc c = true := by
    rcases P.hT with ⟨c', e, hs⟩ | ⟨n, r, e⟩
    · rw [hπ] at e; cases e; exact hs
    · rw [hπ] at e; cases e
  have hlt : lev c = lev π := by rw [hπ]; rfl
  cases c with
  | one => exact bot_ltY rfl (Nat.le_of_eq hlt) rfl rfl P.ht
  | plus a b =>
    have hcF := G.nf _ hcS
    obtain ⟨-, -, hap, -⟩ := hcF.plus
    have haS := G.sub hcS (show a ∈ subs (.plus a b) by simp [subs, self_mem_subs])
    have haF := G.nf _ haS
    have hac : Lt a (.plus a b) := lt_plus_leftY hcF
    have haΩ : Lt a (.Om (.plus a b)) := G.trans haS hcS hΩS hac hΩF.om.2.2
    have hat : Lt a (.Psi ξ π γ) := by
      have hl : lev a = lev π := hlt
      by_cases hb : isBot a = true
      · exact bot_ltY hb (Nat.le_of_eq hl) rfl rfl P.ht
      rcases shape_FY3 haF hap (Bool.eq_false_iff.mpr hb) with
        ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨τ, ρ, δ, rfl⟩
      · have hx := G.sub haS (mem_subs_om x)
        have hxc := G.trans hx haS hcS haF.om.2.2 hac
        have ht' := P.ht
        rw [hπ] at ht' ⊢
        have hξ0 := ht'.psiOm.2.2.2.2.2
        subst hξ0
        exact (lt_om_psiY ht').mpr hxc
      · refine P.k2t _ ?_
        rw [hπ]
        simp [fr, haΩ]
      · refine P.k2t _ ?_
        rw [hπ]
        simp [fr, haΩ]
    exact lt_of_head_lt rfl (summands_plus a b) ((lt_principal_iff hap rfl).mp hat)
  | _ => simp [isSucc, summands] at hs

end PsiCtxY

end RTKA.Z
