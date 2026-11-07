import Compact.FS.FSNF

/-! 基本列の反復で得られる順序数項（NOT）と、可算な標準形全体の一致。

Subsp の `FundSys.NOT` と同じく、極限となる始点 `notBase n` から基本列 `t ↦ t[n]`（`n` は自然数）を繰り返して
得られる標準形を順序数項（`IsOT`）とし、その全体を `NOT` とする。

* 始点 `notBase n = Ψ^0_{Ω_1}(K_{n+1})`：可算な標準形で、共終数は `ω`（極限、`dom_notBase`）。可算な標準形の
  中で共終（可算な `t` は、`n` を部分項の階以上に取ると `Ψ^0_{Ω_1}(K_{n+1})` 未満、`lt_notBase`）。
* 可算な項の共終数は `0`・`1`・`ω` のいずれか（`dom_countable`）：正則項は全て `Ω_1` 以上なので
  （`om_one_le_reg`）、共終数が正則項 `σ` の項は `σ` 以上、すなわち非可算。
* `isOT_iff`：`IsOT t ⟺ t < Ω_1`。`NOT_eq`：`NOT` は可算な標準形全体 `{t : NF // t < Ω_1}` に等しい。
  `⊆` は基本列が項を増やさないことから、`⊇` は始点の共終性と、基本列の共終性・整列性による下への閉包から。
* `NOTFundLt_iff_lt`：基本列の一歩（`NOTStep`）の推移閉包は、項の順序と一致する。

Bachmann 性は使わない（基本列の降下・共終性と整列性 `wellFounded_isNF` だけを使う）。 -/

namespace RTKA.Fund

open Tm W

/-! ### 可算な項の共終数 -/

/-- 正則項は `Ω_1` 以上 -/
theorem om_one_le_reg {σ : Tm} (hσ : WNF σ) (h : RegTerm σ) : Le (.Om .one) σ := by
  rcases h with h | ⟨m, rfl⟩
  · rcases IsTgt.cases h hσ with ⟨c, rfl⟩ | hX
    · -- `Ω_c`（`c ≠ 0`）
      obtain ⟨hc, hc0, -⟩ := hσ.om
      exact le_om_of_leY WNF.one hc (one_leY hc hc0)
    · -- `Ω` の不動点 `X`：`1 < X` なので `Ω_1 < X`
      have h0 : σ ≠ .zero := by
        rintro rfl
        rcases hX with ⟨_, _, e⟩ | ⟨_, _, _, e, -, -⟩ <;> cases e
      rcases one_leY hσ h0 with e | h1
      · subst e
        rcases hX with ⟨_, _, e⟩ | ⟨_, _, _, e, -, -⟩ <;> cases e
      · exact Or.inr ((lt_om_OFG hX).mpr h1)
  · -- `K_m`：`K_m < Ω_1` なら `K_m < 1`、すなわち `K_m = 0` で矛盾
    have hm : 1 ≤ m := hσ.k
    refine le_of_not_ltY (WNF.K' hm) WNF.om_one fun h => ?_
    cases lt_oneY (WNF.K' hm) ((lt_K_omY hm WNF.one).mp h)

/-- 共終数が正則項の項は `Ω_1` 以上 -/
theorem om_one_le_of_big {t σ : Tm} (ht : WNF t) (h : dom t = .big σ) : Le (.Om .one) t := by
  obtain ⟨hU, hreg⟩ := seqI_dom_big ht h
  exact le_transY WNF.om_one hU.hσF ht (om_one_le_reg hU.hσF hreg) hU.hσle

/-- 可算な項の共終数は `0`・`1`・`ω` のいずれか -/
theorem dom_countable {t : Tm} (ht : WNF t) (hc : Lt t (.Om .one)) :
    dom t = .zero ∨ dom t = .one ∨ dom t = .omega := by
  cases hd : dom t with
  | zero => exact Or.inl rfl
  | one => exact Or.inr (Or.inl rfl)
  | omega => exact Or.inr (Or.inr rfl)
  | big σ => exact absurd hc (not_lt_of_leY WNF.om_one ht (om_one_le_of_big ht hd))

/-! ### 基本列の降下と共終性 -/

/-- `0` でない項の基本列の項は自分未満 -/
theorem fund_lt_of_ne_zero {t ξ : Tm} (ht : WNF t) (hξ : WNF ξ) (h0 : t ≠ .zero) :
    Lt (fund t ξ) t := by
  rw [fund_eq]
  cases hd : dom t with
  | zero => exact absurd ((dom_eq_zero_iff ht).mp hd) h0
  | one => exact pred_lt ht ((dom_eq_one_iff ht).mp hd)
  | omega => exact ((seqI_dom_nat ht hd).1.good _).2.1
  | big σ =>
    obtain ⟨hU, hreg⟩ := seqI_dom_big ht hd
    show Lt (fundBig t (if ltB ξ σ = true then ξ else zero)) t
    by_cases h : ltB ξ σ = true
    · rw [ite_eq_left h]
      exact (hU.good.1 ξ hξ (ltB_iff.mp h)).2
    · rw [ite_eq_right h]
      exact (hU.good.1 .zero WNF.zero (zero_lt hreg.ne_zero)).2

/-- 可算な項の基本列は下から共終：`b < a < Ω_1` なら `b ≤ a[n]` となる自然数 `n` がある -/
theorem fund_cof_countable {a b : Tm} (ha : WNF a) (hb : WNF b) (hc : Lt a (.Om .one)) (h : Lt b a) :
    ∃ n : Nat, Le b (fund a (ofNatT n)) := by
  rcases dom_countable ha hc with hd | hd | hd
  · rw [(dom_eq_zero_iff ha).mp hd] at h
    exact absurd h (Fund.not_lt_zero b)
  · refine ⟨0, ?_⟩
    rw [fund_of_dom_one _ hd]
    exact le_pred ha ((dom_eq_one_iff ha).mp hd) hb h
  · obtain ⟨n, hn⟩ := nf_omega_cof ⟨a, ha⟩ ⟨b, hb⟩ (domNF_omega.mpr hd) h
    exact ⟨n, nf_le.mp hn⟩

/-! ### 始点 -/

/-- 始点 `Ψ^0_{Ω_1}(K_{n+1})` -/
def notBase (n : Nat) : Tm := .Psi .zero (.Om .one) (.K (n + 1))

theorem wnf_notBase (n : Nat) : WNF (notBase n) :=
  wnf_psi0 WNF.om_one (Or.inl ⟨.one, rfl, rfl⟩) (WNF.K' (Nat.le_add_left 1 n)) (inC_K _ _ _)
    fun r hr => by simp [argR?] at hr

/-- 始点は可算 -/
theorem notBase_lt (n : Nat) : Lt (notBase n) (.Om .one) := lt_psi_targetY (wnf_notBase n)

/-- 始点は極限：共終数は `ω` -/
theorem dom_notBase (n : Nat) : dom (notBase n) = .omega := by
  rcases dom_countable (wnf_notBase n) (notBase_lt n) with hd | hd | hd
  · cases (dom_eq_zero_iff (wnf_notBase n)).mp hd
  · have hs := (dom_eq_one_iff (wnf_notBase n)).mp hd
    simp [notBase, isSucc, summands] at hs
  · exact hd

/-- 始点は可算な標準形の中で共終：可算な `t` は、`n` を部分項の階以上に取ると `Ψ^0_{Ω_1}(K_{n+1})` 未満
    （`t` の節点の引数は全て `K_{n+1}` 未満なので `t ∈ C(K_{n+1}, Ψ^0_{Ω_1}(K_{n+1}))`、崩壊の性質による） -/
theorem lt_notBase {t : Tm} (ht : WNF t) (hc : Lt t (.Om .one)) : Lt t (notBase (maxLevS [t])) := by
  have hM : 1 ≤ maxLevS [t] + 1 := Nat.le_add_left 1 _
  have hlt : ∀ v, v ∈ subs t → WNF v → Lt v (.K (maxLevS [t] + 1)) := fun v hv hvF =>
    (lt_K_iffY hvF hM).mpr (Nat.le_trans (lev_le_maxLevS List.mem_cons_self hv) (Nat.le_succ _))
  have hC : inC t (.K (maxLevS [t] + 1)) (notBase (maxLevS [t])) = true :=
    inC_of_args (fun s k a hs => hlt a (subs_trans hs (subs_psi_a (self_mem_subs a)))
        (ht.of_mem_subs hs).psi.aF)
      fun j b hs => hlt b (subs_trans hs (subs_xi (self_mem_subs b))) (ht.of_mem_subs hs).xi.2.1
  exact coll_psiY (wnf_notBase (maxLevS [t])) t ht hC hc

end RTKA.Fund

namespace RTKA

open Fund Tm W

/-! ### 順序数項（NOT） -/

/-- 始点（標準形） -/
def baseNF (n : Nat) : NF := ⟨notBase n, wnf_notBase n⟩

/-- 順序数項：始点 `notBase n` から基本列 `t ↦ t[n]`（`n` は自然数）の反復で得られる標準形
    （Subsp の `FundSys.IsOT`） -/
inductive IsOT : NF → Prop
  | base (n : Nat) : IsOT (baseNF n)
  | step (s : NF) : IsOT s → ∀ n : Nat, IsOT (fundNF s (ofNatNF n))

/-- 順序数項の全体（Subsp の `FundSys.NOT`） -/
def NOT := { s : NF // IsOT s }

/-- 始点は極限 -/
theorem domNF_baseNF (n : Nat) : domNF (baseNF n) = .omega := domNF_omega.mpr (dom_notBase n)

/-- 順序数項は可算 -/
theorem IsOT.lt_om {t : NF} (h : IsOT t) : Lt t.1 (.Om .one) := by
  induction h with
  | base n => exact notBase_lt n
  | step s _ n ih =>
    show Lt (fund s.1 (ofNatT n)) (.Om .one)
    by_cases h0 : s.1 = .zero
    · rw [h0, fund_zero]
      rw [h0] at ih
      exact ih
    · exact lt_transY (fund_wnf s.2 (wnf_ofNatT n)) s.2 WNF.om_one
        (fund_lt_of_ne_zero s.2 (wnf_ofNatT n) h0) ih

/-- 下への閉包：順序数項以下の標準形は順序数項（`a` についての整礎帰納。`b < a` なら、基本列の共終性から
    `b ≤ a[n] < a` となる `n` があり、`a[n]` は順序数項） -/
theorem IsOT.of_le {a : NF} (ha : IsOT a) : ∀ {b : NF}, Le b.1 a.1 → IsOT b := by
  refine WellFounded.induction (C := fun a : NF => IsOT a → ∀ {b : NF}, Le b.1 a.1 → IsOT b)
    wellFounded_isNF a ?_ ha
  intro a ih ha b hb
  rcases hb with e | hlt
  · rw [Subtype.ext e]
    exact ha
  · obtain ⟨n, hn⟩ := fund_cof_countable a.2 b.2 ha.lt_om hlt
    have ha0 : a.1 ≠ .zero := fun e => Fund.not_lt_zero b.1 (by rw [← e]; exact hlt)
    exact ih (fundNF a (ofNatNF n)) (fund_lt_of_ne_zero a.2 (wnf_ofNatT n) ha0) (.step a ha n) hn

/-- **NOT は可算な標準形全体と一致する**：`IsOT t ⟺ t < Ω_1` -/
theorem isOT_iff (t : NF) : IsOT t ↔ Lt t.1 (.Om .one) :=
  ⟨IsOT.lt_om, fun hc => (IsOT.base (maxLevS [t.1])).of_le (Or.inr (lt_notBase t.2 hc))⟩

/-- `NOT` は可算な標準形全体 `{t : NF // t < Ω_1}` に等しい -/
theorem NOT_eq : NOT = { t : NF // Lt t.1 (.Om .one) } :=
  congrArg Subtype (funext fun t => propext (isOT_iff t))

/-! ### 基本列による順序 -/

/-- 基本列の一歩：`a` は `b` の基本列の項（Subsp の `FundSys.NOTStep`） -/
def NOTStep (a b : NOT) : Prop := b.1.1 ≠ .zero ∧ ∃ n : Nat, a.1 = fundNF b.1 (ofNatNF n)

/-- 基本列の一歩の推移閉包（Subsp の `FundSys.NOTFundLt`） -/
abbrev NOTFundLt : NOT → NOT → Prop := Relation.TransGen NOTStep

/-- 基本列の項はもとの項より小さい（Subsp の `FundDesc`） -/
theorem NOT.fundDesc (b : NOT) (n : Nat) (hb : b.1.1 ≠ .zero) : fundNF b.1 (ofNatNF n) < b.1 :=
  fund_lt_of_ne_zero b.1.2 (wnf_ofNatT n) hb

/-- 基本列は下から共終（Subsp の `FundCofinal`） -/
theorem NOT.fundCofinal (a b : NOT) (h : b.1 < a.1) : ∃ n : Nat, b.1 ≤ fundNF a.1 (ofNatNF n) := by
  obtain ⟨n, hn⟩ := fund_cof_countable a.1.2 b.1.2 a.2.lt_om h
  exact ⟨n, nf_le.mpr hn⟩

/-- `NOT` の上の順序は整礎 -/
theorem NOT.wf : WellFounded (fun a b : NOT => a.1 < b.1) :=
  InvImage.wf (fun s : NOT => s.1) wellFounded_isNF

theorem NOTStep.lt {a b : NOT} (h : NOTStep a b) : a.1 < b.1 := by
  obtain ⟨hb, n, e⟩ := h
  rw [e]
  exact NOT.fundDesc b n hb

theorem NOTFundLt.lt {a b : NOT} (h : NOTFundLt a b) : a.1 < b.1 := by
  induction h with
  | single h => exact h.lt
  | @tail c d _ hcd ih => exact lt_transY a.1.2 c.1.2 d.1.2 ih hcd.lt

theorem NOTFundLt_of_lt (b : NOT) : ∀ a : NOT, a.1 < b.1 → NOTFundLt a b := by
  refine NOT.wf.induction (C := fun b : NOT => ∀ a : NOT, a.1 < b.1 → NOTFundLt a b) b ?_
  intro b ih a hab
  have hb0 : b.1.1 ≠ .zero := fun e => Fund.not_lt_zero a.1.1 (by rw [← e]; exact hab)
  obtain ⟨n, hn⟩ := NOT.fundCofinal b a hab
  let c : NOT := ⟨fundNF b.1 (ofNatNF n), .step _ b.2 n⟩
  have hstep : NOTStep c b := ⟨hb0, n, rfl⟩
  rcases nf_le.mp hn with e | h
  · have hac : a = c := Subtype.ext (Subtype.ext e)
    rw [hac]
    exact .single hstep
  · exact .tail (ih c hstep.lt a h) hstep

/-- **基本列の一歩の推移閉包と項の順序の一致**（Subsp の `FundSys.NOTFundLt_iff_lt`） -/
theorem NOTFundLt_iff_lt (a b : NOT) : NOTFundLt a b ↔ a.1 < b.1 :=
  ⟨NOTFundLt.lt, NOTFundLt_of_lt b a⟩

end RTKA
