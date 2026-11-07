import Compact.FS.Gap
import Compact.FS.Tgt

/-! 共終数が正則項の列の不変量（`BigUB`・`BigGap`）と、正則項自身の列（`reg`）。

`ω` 型の不変量と同じく、良さ・上界・梯子の上界・隙間を持つ。加えて対角化のために、添字が列の項の成分であること
（`lo`）、共終数が `t` の成分で `t` 以下の部分項であること（`hσC`・`hσle`・`hσs`）を持つ。

上界の仮定：

* `0 < g` は、`Ω_{e+1}[ξ] = Ψ^0_{Ω_{e+1}}(0) ⊕ ξ` の始点の引数 `0` のため。
* `BigOK σ g d` は、`Ξ_n(q)[ξ] = Ψ^0_{Ξ_n(q)}(q+1) ⊕ ξ` の始点の引数 `q + 1` のため（`g = q + 1` では本当に成り立たない）。

正則項 `σ` の列は `σ[ξ] = b ⊕ ξ`、`b = Ψ^0_σ(Y)`（`bigInv_tgt`）。梯子の上界は `above_coll` による：`b` より大きい `σ` 未満の
項には、見える位置に目標 `σ` で引数が `Y` 以上の節点がある。 -/

namespace RTKA.Fund

open Tm W

/-- 正則項 `σ` の列の始点が `C(g, d)` に入るための `g` の条件 -/
def BigOK (σ g d : Tm) : Prop :=
  Le σ d ∨ ∀ q, argR? σ = some q → Lt q g → Lt (succT q) g

theorem bigOK_none {σ g d : Tm} (h : argR? σ = none) : BigOK σ g d :=
  Or.inr fun q hq => by rw [h] at hq; cases hq

/-! ### 後者の判定 -/

theorem one_mem_of_isSucc {t : Tm} (h : isSucc t = true) : Tm.one ∈ summands t := by
  have e : (summands t).getLast? = some Tm.one := by simpa [isSucc] using h
  exact List.mem_of_getLast? e

theorem isSucc_of_one_mem : ∀ {t : Tm}, WNF t → Tm.one ∈ summands t → isSucc t = true
  | .zero, _, h => by simp [summands] at h
  | .one, _, _ => rfl
  | .K _, _, h | .Om _, _, h | .Xi _ _, _, h | .Psi _ _ _, _, h => by simp [summands] at h
  | .plus a b, ht, h => by
    obtain ⟨ha, hb, hap, hb0⟩ := ht.plus
    rw [isSucc_plus hb0]
    rw [summands_plus, List.mem_cons] at h
    rcases h with rfl | h
    · obtain ⟨h', rest, hsb⟩ := List.exists_cons_of_ne_nil (summands_ne_nil hb0)
      have h2 := WNF.plus_head ht hsb
      have hhm := (nfl_summands hb).1 h' (by rw [hsb]; exact List.mem_cons_self)
      have e : h' = .one := by
        rcases le_of_ne_gtY hhm.1 WNF.one h2 with e | h3
        · exact e
        · have e0 := lt_oneY hhm.1 h3
          rw [e0] at hhm
          cases hhm.2
      exact isSucc_of_one_mem hb (by rw [hsb, e]; exact List.mem_cons_self)
    · exact isSucc_of_one_mem hb h

theorem not_succ_oadd {a y : Tm} (ha : WNF a) (hy : WNF y) (hy0 : y ≠ .zero)
    (hs : ¬ isSucc y = true) : ¬ isSucc (oadd a y) = true := by
  intro h
  have hm := one_mem_of_isSucc h
  obtain ⟨h', rest, hsy⟩ := List.exists_cons_of_ne_nil (summands_ne_nil hy0)
  rw [summands_oadd hsy (nfl_principal (nfl_summands ha)) (nfl_principal (nfl_summands hy))] at hm
  rcases List.mem_append.mp hm with hm | hm
  · have h1 : leB h' .one = true := mem_takeWhile_imp' (p := fun s => leB h' s) hm
    rw [leB_iff] at h1
    have hhm := (nfl_summands hy).1 h' (by rw [hsy]; exact List.mem_cons_self)
    have e : h' = .one := by
      rcases le_of_ne_gtY hhm.1 WNF.one h1 with e | h3
      · exact e
      · have e0 := lt_oneY hhm.1 h3
        rw [e0] at hhm
        cases hhm.2
    exact hs (isSucc_of_one_mem hy (by rw [hsy, e]; exact List.mem_cons_self))
  · exact hs (isSucc_of_one_mem hy hm)

theorem not_succ_nsum {x y : Tm} (hx : WNF x) (hy : WNF y) (hxs : ¬ isSucc x = true)
    (hys : ¬ isSucc y = true) : ¬ isSucc (nsum x y) = true := by
  intro h
  have hm := one_mem_of_isSucc h
  rw [summands_nsum hx hy] at hm
  rcases List.mem_append.mp ((merge_perm _ _).mem_iff.mp hm) with h1 | h1
  · exact hxs (isSucc_of_one_mem hx h1)
  · exact hys (isSucc_of_one_mem hy h1)

theorem succT_le_of_lt {a b : Tm} (ha : WNF a) (hb : WNF b) (h : Lt a b) : Le (succT a) b :=
  le_of_not_ltY hb (succT_WNF ha) fun h' => not_lt_of_leY hb ha (le_of_lt_succT hb ha h') h

/-- 共終数が正則項 `σ` の列の不変量（隙間を除く） -/
structure BigUB (t σ : Tm) (s : SeqD) : Prop where
  good : BigGood t σ s
  /-- `t[ξ] = 0` なら `t` に真の部分項はない（`K_1` の始点） -/
  pos : ∀ ξ, WNF ξ → Lt ξ σ → s.big ξ = .zero → ∀ v, v ∈ subs t → v = t
  hσF : WNF σ
  hσle : Le σ t
  /-- 共終数は `t` の部分項 -/
  hσs : σ ∈ subs t
  /-- 共終数は `t` の成分 -/
  hσC : ∀ g d, WNF g → WNF d → inC t g d = true → inC σ g d = true
  /-- 上界 -/
  ub : ∀ g d ξ, WNF g → WNF d → WNF ξ → Lt ξ σ → Lt .zero g → BigOK σ g d → inC t g d = true →
    inC ξ g d = true → inC (s.big ξ) g d = true
  /-- 梯子の上界 -/
  ub2 : ∀ g d ξ η, WNF g → WNF d → WNF ξ → WNF η → Lt ξ η → Lt η σ →
    inC (s.big η) g d = true → inC ξ g d = true → inC (s.big ξ) g d = true
  /-- 添字は列の項の成分 -/
  lo : ∀ g d ξ, WNF d → WNF ξ → Lt ξ σ → inC (s.big ξ) g d = true → inC ξ g d = true
  /-- 主要項の列は、添字が後者でなければ後者でない -/
  ns : isPrincipal t = true → ∀ ξ, WNF ξ → Lt ξ σ → ¬ isSucc ξ = true → ¬ isSucc (s.big ξ) = true
  /-- 共終数が `K_m` で `t` が `K_m` より大きいなら、列の項は `K_m` 以上 -/
  lbK : ∀ m, σ = .K m → Lt (.K m) t → ∀ ξ, WNF ξ → Lt ξ σ → Le (.K m) (s.big ξ)
  /-- 共終数が `K_m` で `t` が `K_m⁺` より大きいなら、列の項は `K_m⁺` 以上 -/
  lbS : ∀ m, σ = .K m → Lt (succK m) t → ∀ ξ, WNF ξ → Lt ξ σ → Le (succK m) (s.big ξ)

/-- 隙間 -/
def BigGap (t σ : Tm) (s : SeqD) : Prop :=
  ∀ ξ, WNF ξ → Lt ξ σ → ∀ v, v ∈ subs t → v ≠ t → Lt v t → Lt v (s.big ξ)

/-- 隙間（等号つき）：和 `a + K_1` の `[0] = a` のため -/
def BigGapW (t σ : Tm) (s : SeqD) : Prop :=
  ∀ ξ, WNF ξ → Lt ξ σ → ∀ v, v ∈ subs t → v ≠ t → Lt v t → Le v (s.big ξ)

/-- 共終数が正則項 `σ` の列の不変量 -/
def BigInv (t σ : Tm) (s : SeqD) : Prop := BigUB t σ s ∧ BigGap t σ s

/-- 共終数が正則項 `σ` の列の不変量（隙間は等号つき） -/
def BigInvW (t σ : Tm) (s : SeqD) : Prop := BigUB t σ s ∧ BigGapW t σ s

theorem BigInv.weak {t σ : Tm} {s : SeqD} (h : BigInv t σ s) : BigInvW t σ s :=
  ⟨h.1, fun ξ hξ hξσ v hv hne hlt => Or.inr (h.2 ξ hξ hξσ v hv hne hlt)⟩

theorem oadd_ne_zero_left {b ξ : Tm} (hb : WNF b) (hξ : WNF ξ) (hb0 : b ≠ .zero) :
    oadd b ξ ≠ .zero := by
  intro e
  have h := le_oadd_left hb hξ
  rw [e] at h
  rcases h with h | h
  · exact hb0 h
  · exact not_lt_zero _ h

/-- 添字は `b ⊕ ξ` の成分 -/
theorem inC_of_oadd_right {b ξ g d : Tm} (hb : WNF b) (hξ : WNF ξ) (h : inC (oadd b ξ) g d = true) :
    inC ξ g d = true := by
  rw [inC_iff_summands hξ]
  intro s hsm
  exact inC_of_mem_summands (wnf_oadd hb hξ) h (mem_summands_oadd_right hb hξ hsm)

theorem IsTgt.principal {π : Tm} (h : IsTgt π) : isPrincipal π = true := by
  rcases h with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩ <;> rfl

theorem IsTgt.ne_K {π : Tm} (h : IsTgt π) (m : Nat) : π ≠ .K m := by
  rcases h with ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩ <;> intro e <;> cases e

/-- `K_m` は階が上の主要項未満 -/
theorem K_lt_of_lev {m : Nat} {y : Tm} (hy : WNF y) (hp : isPrincipal y = true) (hb : isBot y = false)
    (hl : m + 1 ≤ lev y) : Lt (.K m) y :=
  bot_ltY rfl hl hp hb hy

/-- 目標が `K_m` より大きい崩壊は `K_m` より大きい -/
theorem K_lt_psi {m : Nat} {ξ π A : Tm} (hy : WNF (.Psi ξ π A)) (h : Lt (.K m) π) :
    Lt (.K m) (.Psi ξ π A) :=
  K_lt_of_lev hy rfl rfl (lev_le_of_lt_gen h)

/-- `K_m⁺` は、`K_m` より大きい `Ω` の不動点の未満 -/
theorem succK_lt_of_OF {m : Nat} {y : Tm} (hm : 1 ≤ m) (hof : IsOF y) (hy : WNF y) (h : Lt (.K m) y) :
    Lt (succK m) y :=
  (lt_om_OFG hof).mpr (succT_lt_of_not_succ (WNF.K' hm) hy (not_succ_OF hof) h)

/-- 目標が `K_m⁺` より大きい崩壊は `K_m⁺` より大きい -/
theorem succK_lt_psi {m : Nat} {ξ π A : Tm} (hm : 1 ≤ m) (hy : WNF (.Psi ξ π A)) (h : Lt (succK m) π) :
    Lt (succK m) (.Psi ξ π A) := by
  have hK : Lt (.K m) π := lt_transY (WNF.K' hm) (WNF.succK hm) hy.psi.piF (WFY.K_lt_succK hm) h
  by_cases hπ : ∃ e, π = .Om e
  · obtain ⟨e, rfl⟩ := hπ
    have hs0 : ξ = .zero := lt_oneY hy.psi.xiF hy.psi.mlt
    subst hs0
    have hO := hy.psi.piF.om.1
    exact (lt_om_psiY hy).mpr ((lt_om_iffY (succT_WNF (WNF.K' hm)) hO).mp h)
  · exact succK_lt_of_OF hm (IsOF.psi hy fun e e' => hπ ⟨e, e'⟩) hy (K_lt_psi hy hK)

/-- 正則項 `σ`（`K_m` でない）の列 `σ[ξ] = Ψ^0_σ(Y) ⊕ ξ` の不変量 -/
theorem bigInv_tgt {σ Y : Tm} (ht : IsTgt σ) (hb : WNF (.Psi .zero σ Y))
    (hC : ∀ g d, ¬ Lt σ d → inC σ g d = true → inC Y g d = true)
    (hgY : ∀ g d, WNF d → Lt .zero g → (∀ q, argR? σ = some q → Lt q g → Lt (succT q) g) → ¬ Lt σ d →
      inC σ g d = true → Lt Y g) :
    BigInv σ σ (.reg σ (.Psi .zero σ Y)) := by
  have hP := hb.psi
  have hσF := hP.piF
  have hYF := hP.aF
  have hbR : Lt (.Psi .zero σ Y) σ := lt_psi_targetY hb
  have hb0 : Tm.Psi .zero σ Y ≠ .zero := by
    intro e
    cases e
  have hσp := ht.principal
  have hlt : ∀ ξ, WNF ξ → Lt ξ σ → Lt (oadd (.Psi .zero σ Y) ξ) σ := fun ξ hξ h =>
    oadd_lt_prin hb hξ hσp hbR h
  refine ⟨{ good := ⟨fun ξ hξ h => ⟨wnf_oadd hb hξ, hlt ξ hξ h⟩,
              fun ξ η hξ hη h _ => oadd_lt_oadd hb hξ hη h⟩
            pos := fun ξ hξ _ h => absurd h (oadd_ne_zero_left hb hξ hb0)
            hσF := hσF
            hσle := Or.inl rfl
            hσs := self_mem_subs σ
            hσC := fun _ _ _ _ h => h
            ub := ?_
            ub2 := ?_
            lo := fun g d ξ _ hξ _ h => inC_of_oadd_right hb hξ h
            ns := fun _ ξ hξ _ hs => ?_
            lbK := fun m e => absurd e (IsTgt.ne_K ht m)
            lbS := fun m e => absurd e (IsTgt.ne_K ht m) }, ?_⟩
  · intro g d ξ _ hd hξ hξσ h0 hok ht' hξC
    show inC (oadd (.Psi .zero σ Y) ξ) g d = true
    by_cases hσd : Le σ d
    · exact WFY.inC_of_ltY _ (wnf_oadd hb hξ) hd
        (lt_of_lt_of_leY (wnf_oadd hb hξ) hσF hd (hlt ξ hξ hξσ) hσd)
    · have hnl : ¬ Lt σ d := fun h => hσd (Or.inr h)
      have hok' := hok.resolve_left hσd
      exact inC_oadd hb hξ (inC_psi_iff.mpr (Or.inr ⟨ht', inC_zero _ _, hC g d hnl ht',
        hgY g d hd h0 hok' hnl ht'⟩)) hξC
  · intro g d ξ η hg hd hξ hη hlt' hησ h hξC
    show inC (oadd (.Psi .zero σ Y) ξ) g d = true
    have h' : inC (oadd (.Psi .zero σ Y) η) g d = true := h
    by_cases hbd : Lt (.Psi .zero σ Y) d
    · exact inC_oadd hb hξ (WFY.inC_of_ltY _ hb hd hbd) hξC
    refine inC_oadd hb hξ ?_ hξC
    have hdb : Le d (.Psi .zero σ Y) := le_of_not_ltY hb hd hbd
    have hA := wnf_oadd hb hη
    cases hsη : summands η with
    | nil =>
      rw [eq_zero_of_summands_nil hsη] at hlt'
      exact absurd hlt' (not_lt_zero _)
    | cons h'' r =>
      have hN := nfl_summands hη
      have hsum := summands_oadd hsη (nfl_principal (nfl_summands hb)) (nfl_principal hN)
      by_cases hle : leB h'' (.Psi .zero σ Y) = true
      · apply inC_of_mem_summands hA h'
        show _ ∈ summands (oadd (.Psi .zero σ Y) η)
        rw [hsum, summands_principal rfl, List.takeWhile_cons_of_pos hle]
        exact List.mem_append_left _ List.mem_cons_self
      · have hm : h'' ∈ summands (oadd (.Psi .zero σ Y) η) := by
          rw [hsum, hsη]
          exact List.mem_append_right _ List.mem_cons_self
        have hC' := inC_of_mem_summands hA h' hm
        have hhm : h'' ∈ summands η := by
          rw [hsη]
          exact List.mem_cons_self
        have hh := hN.1 h'' hhm
        have hbh : Lt (.Psi .zero σ Y) h'' := by
          apply lt_of_gtY hh.1 hb
          rw [leB_iff] at hle
          simpa using hle
        have hhσ : Lt h'' σ := by
          have hle' : Le h'' η := by
            have := le_ofSummands_of_mem hN hhm
            rwa [ofSummands_summands η hη] at this
          exact lt_of_le_of_ltY hh.1 hη hσF hle' hησ
        obtain ⟨s', a, hmem, hYa, hw, hvis⟩ := above_coll hb _ (Nat.le_refl _) hh.1 hhσ (Or.inr hbh)
        have hwF := hh.1.of_mem_subs hmem
        rcases inC_psi_iff.mp (hvis g d hd hdb hC') with h2 | ⟨h2, -, -, h3⟩
        · exact absurd (lt_of_lt_of_leY hwF hd hb h2 hdb) (not_lt_of_leY hb hwF hw)
        · have hσd : ¬ Lt σ d := fun h4 => hbd (lt_transY hb hσF hd hbR h4)
          exact inC_psi_iff.mpr (Or.inr ⟨h2, inC_zero _ _, hC g d hσd h2,
            lt_of_le_of_ltY hYF hwF.psi.aF hg hYa h3⟩)
  · show ¬ isSucc (oadd (.Psi .zero σ Y) ξ) = true
    by_cases h0 : ξ = .zero
    · rw [h0, oadd_zero, isSucc_principal rfl]
      simp
    · exact not_succ_oadd hb hξ h0 hs
  · intro ξ hξ _ v hv _ hlt'
    exact lt_of_lt_of_leY (hσF.of_mem_subs hv) hb (wnf_oadd hb hξ) (lt_of_mem_tgt hb hv hlt')
      (le_oadd_left hb hξ)

/-- `Ω_{e+1}` の列の不変量 -/
theorem bigInv_om_succ {e : Tm} (ht : WNF (.Om e)) (hs : isSucc e = true) :
    BigInv (.Om e) (.Om e) (.reg (.Om e) (base (.Om e))) :=
  bigInv_tgt (Or.inl ⟨e, rfl, hs⟩) (wnf_base_om ht hs) (fun _ _ _ _ => inC_zero _ _)
    (fun _ _ _ h0 _ _ _ => h0)

/-- `Ξ_m(q)` の列の不変量 -/
theorem bigInv_xi {m : Nat} {q : Tm} (ht : WNF (.Xi m q)) :
    BigInv (.Xi m q) (.Xi m q) (.reg (.Xi m q) (base (.Xi m q))) :=
  bigInv_tgt (Or.inr (Or.inl ⟨m, q, rfl⟩)) (wnf_base_xi ht)
    (fun g d hσd h => by
      rcases inC_xi_iff.mp h with h' | ⟨h1, -⟩
      · exact absurd h' hσd
      · exact inC_succT h1)
    (fun g d _ _ hok hσd h => by
      rcases inC_xi_iff.mp h with h' | ⟨-, h1⟩
      · exact absurd h' hσd
      · exact hok q rfl h1)

/-- `Ψ^ζ_κ(γ)`（`ζ ≠ 0`）の列の不変量 -/
theorem bigInv_psi {ζ κ γ : Tm} (ht : WNF (.Psi ζ κ γ)) (hζ : ζ ≠ .zero) :
    BigInv (.Psi ζ κ γ) (.Psi ζ κ γ) (.reg (.Psi ζ κ γ) (base (.Psi ζ κ γ))) :=
  bigInv_tgt (Or.inr (Or.inr ⟨ζ, κ, γ, rfl, hζ⟩)) (wnf_base_psi ht hζ)
    (fun g d hσd h => by
      rcases inC_psi_iff.mp h with h' | ⟨-, -, h1, -⟩
      · exact absurd h' hσd
      · exact inC_succT h1)
    (fun g d _ _ hok hσd h => by
      rcases inC_psi_iff.mp h with h' | ⟨-, -, -, h1⟩
      · exact absurd h' hσd
      · exact hok γ rfl h1)

/-- `K_m` の列の不変量 -/
theorem bigInv_K {m : Nat} (hm : 1 ≤ m) :
    BigInv (.K m) (.K m) (.reg (.K m) (base (.K m))) := by
  have hb := wnf_base_K m
  have hbR := base_K_lt m
  have hbC : ∀ g d, inC (base (.K m)) g d = true := fun g d => by
    simp only [base]
    split
    · exact inC_zero _ _
    · exact inC_K _ _ _
  have hsub : ∀ v, v ∈ subs (.K m) → v = .K m := fun v hv => by
    simpa [subs] using hv
  refine ⟨{ good := ⟨fun ξ hξ h => ⟨wnf_oadd hb hξ, oadd_lt_prin hb hξ rfl hbR h⟩,
              fun ξ η hξ hη h _ => oadd_lt_oadd hb hξ hη h⟩
            pos := fun _ _ _ _ => hsub
            hσF := WNF.K' hm
            hσle := Or.inl rfl
            hσs := self_mem_subs _
            hσC := fun _ _ _ _ h => h
            ub := fun g d ξ _ _ hξ _ _ _ _ hξC => inC_oadd hb hξ (hbC g d) hξC
            ub2 := fun g d ξ η _ _ hξ _ _ _ _ hξC => inC_oadd hb hξ (hbC g d) hξC
            lo := fun g d ξ _ hξ _ h => inC_of_oadd_right hb hξ h
            ns := fun _ ξ hξ _ hs => ?_
            lbK := fun m' e h => by
              cases e
              exact absurd h (Lt.irrefl _)
            lbS := fun m' e h => by
              cases e
              have h1 := (lt_K_iffY (WNF.succK hm) hm).mp h
              have h2 : lev (succK m) = m + 1 := rfl
              omega }, ?_⟩
  · show ¬ isSucc (oadd (base (.K m)) ξ) = true
    by_cases h0 : ξ = .zero
    · rw [h0, oadd_zero]
      simp only [base]
      split
      · simp [isSucc, summands]
      · simp [isSucc, summands]
    · exact not_succ_oadd hb hξ h0 hs
  · intro ξ _ _ v hv hne
    exact absurd (hsub v hv) hne

end RTKA.Fund
