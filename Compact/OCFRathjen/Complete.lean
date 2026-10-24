import Compact.OCFRathjen.Correct
import Compact.OCFRathjen.Reflection

/-! 弱コンパクト基数の列 `h` だけから `Setting` と `StationaryHyp` を導き、`CmpCorrect` を示す。 -/

namespace OCF.Rathjen

universe u

open Ordinal

noncomputable section

set_option warn.classDefReducibility false in
/-- `h` から得られる `Setting`（`K_{n+1}` は `h` の `n+1` 番目の弱コンパクト基数）。 -/
noncomputable def settingOfWC
    (h : ∀ n : Nat, EnumDef.{u} WeaklyCompactCard.{u} (ordNat.{u} n)) : Setting.{u} where
  Kseq := weaklyCompactAt.{u}
  Kseq_R := weaklyCompactAt_R h
  Kseq_lt := weaklyCompactAt_lt h
  Kseq_inacc := weaklyCompactAt_inacc_of_pairing h pairing_of_omega_le

/-- (B) 各 `K_n` での局所的な反射。 -/
theorem stageReflection_of_wc
    (h : ∀ n : Nat, EnumDef.{u} WeaklyCompactCard.{u} (ordNat.{u} n)) (n : Nat) (hn : 1 ≤ n) :
    @StageReflectionAt.{u} (settingOfWC h) n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact @stageReflectionAt_of_partition.{u} (settingOfWC h) (m + 1) hn
    (weaklyCompactAt_partition h m)

theorem stationaryHyp_of_wc
    (h : ∀ n : Nat, EnumDef.{u} WeaklyCompactCard.{u} (ordNat.{u} n)) :
    @StationaryHyp.{u} (settingOfWC h) :=
  @stationaryHyp_of_stageReflection.{u} (settingOfWC h) (stageReflection_of_wc h)

theorem cmpCorrect_of_weaklyCompact
    (h : ∀ n : Nat, EnumDef.{u} WeaklyCompactCard.{u} (ordNat.{u} n)) :
    @CmpCorrect.{u} (settingOfWC h) :=
  @cmpCorrect_of_stationaryHyp.{u} (settingOfWC h) (stationaryHyp_of_wc h)

end

#print axioms cmpCorrect_of_weaklyCompact

/-! ## `Ξ_n` の引数の上端 `K_n^+ = Ω_{K_n+1}`。

* `Xi_succK_mem`：`K_{n-1} < Ξ_n(K_n^+) < K_n` で `Ξ_n(K_n^+) ∈ M^{K_n^+}`（`StationaryHyp` は `α ≤ K_n^+` を
  含む）。標準形は `Ξ_n(α)` を `α ≤ K_n^+` まで許す。
* `Xi_eq_K_of_succK_lt`：`x > K_n^+` なら `Ξ_n(x) = K_n`。`ψ = Ψ^0_{K_n^+}(K_n^+)` は `C(x, ρ)` に入るが
  `ψ ∉ C(ψ, K_n)` なので `M^ψ` は `K_n` 未満で空で、`M^x` も `(K_{n-1}, K_n)` で空になる。
  `Ξ_n` の引数を `K_n^+` より先に広げても新しい順序数は出ない。 -/

open RTKA (Tm)

theorem C_succK [Setting.{u}] (α β : Ordinal.{u}) (n : Nat) : C α β (Om (K n + succ 0)) :=
  C_Om (K_add_one_lt_Λ n) (C_add (C_K _ _ n) (C_one _ _))

/-- `Ψ^0_{K_n^+}(K_n^+)`（`K_n` と `K_n^+` の間） -/
def psiSuccK (n : Nat) : Tm := .Psi .zero (RTKA.succK n) (RTKA.succK n)

noncomputable section

variable [Setting.{u}]

/-- `Ξ_n(K_n^+) ∈ M^{K_n^+}` かつ `K_{n-1} < Ξ_n(K_n^+) < K_n` -/
theorem Xi_succK_mem (hS : StationaryHyp.{u}) {n : Nat} (hn : 1 ≤ n) :
    M (Om (K n + succ 0)) (Xi n (Om (K n + succ 0))) ∧
      K (n - 1) < Xi n (Om (K n + succ 0)) ∧ Xi n (Om (K n + succ 0)) < K n :=
  Xi_mem hn (hS n hn _ (lt_trans _ _ _ (R_K hn).2.pos (K_lt_Om_succK hn)) (le_refl _)
    (C_succK _ _ n))

theorem good_psiSuccK {n : Nat} (hn : 1 ≤ n) : Good.{u} (psiSuccK n) := by
  have hC : ∀ α β : Ordinal.{u}, C α β (val (RTKA.succK n)) := by
    intro α β
    rw [val_succK]
    exact C_succK α β n
  exact Good.psi .zero (RTKA.succK n) (RTKA.succK n) .one Good.zero (good_succK hn) (good_succK hn)
    rfl (zero_le _) (hC _ _) (C_zero _ _) (hC _ _) rfl (lt_succ_self 0) (C_zero _ _)

/-- `K_n ≤ ψ < K_n^+`（`ψ = Ψ^0_{K_n^+}(K_n^+)`）で `K_n^+` は `Reg` -/
theorem psiSuccK_bounds (hS : StationaryHyp.{u}) {n : Nat} (hn : 1 ≤ n) :
    K n ≤ val.{u} (psiSuccK n) ∧ val.{u} (psiSuccK n) < val (RTKA.succK n) ∧
      IsReg (val.{u} (RTKA.succK n)) := by
  have iv := (good_psiSuccK.{u} hn).inv hS
  exact ⟨(iv.bounds (by intro h; cases h)).2.1, iv.psi _ _ _ rfl⟩

/-- `ψ ∉ C(ψ, K_n)`（Lemma 5.4、`inC_correct`） -/
theorem psiSuccK_not_C (hS : StationaryHyp.{u}) {n : Nat} (hn : 1 ≤ n) :
    ¬ C (val.{u} (psiSuccK n)) (K n) (val (psiSuccK n)) := by
  have g := good_psiSuccK.{u} hn
  have hb := psiSuccK_bounds hS hn
  have e1 : (RTKA.cmp (psiSuccK n) (.K n) == .lt) = false := by
    rw [cmp_correct hS g (Good.kc n hn)]
    cases h : ocmp (val.{u} (psiSuccK n)) (val (.K n)) with
    | lt => exact absurd (ocmp_eq_lt_iff.mp h) (not_lt_of_le hb.1)
    | eq => rfl
    | gt => rfl
  have e2 : (RTKA.cmp (RTKA.succK n) (psiSuccK n) == .lt) = false := by
    rw [cmp_correct hS (good_succK hn) g]
    cases h : ocmp (val.{u} (RTKA.succK n)) (val (psiSuccK n)) with
    | lt => exact absurd (ocmp_eq_lt_iff.mp h) (lt_asymm hb.2.1)
    | eq => rfl
    | gt => rfl
  intro hC
  have hin := (inC_correct hS g g (Good.kc n hn)).mpr hC
  rw [RTKA.inC.eq_def] at hin
  simp only [psiSuccK] at hin e1 e2
  simp [e1, e2] at hin

/-- `x > K_n^+` なら `Ξ_n(x) = K_n` -/
theorem Xi_eq_K_of_succK_lt (hS : StationaryHyp.{u}) {n : Nat} (hn : 1 ≤ n) {x : Ordinal.{u}}
    (hx : Om (K n + succ 0) < x) : Xi n x = K n := by
  apply Xi_eq_K_of_not_lt
  intro hlt
  have hsp := Xi_spec hlt
  have hM := (M_pos_iff (ne_of_gt (lt_of_le_of_lt (zero_le _) hx)) _).mp hsp.1
  have hb := psiSuccK_bounds hS hn
  have hsx : val.{u} (RTKA.succK n) < x := by rw [val_succK]; exact hx
  have hCs : C x (Xi n x) (val.{u} (RTKA.succK n)) := by rw [val_succK]; exact C_succK _ _ n
  have hψC : C x (Xi n x) (val.{u} (psiSuccK n)) :=
    C_Psi hsx (zero_le _) hb.2.2 (C_zero _ _) hCs hCs
  have hst := hM.2.2.2 _ (lt_trans _ _ _ hb.2.1 hsx) hψC
  obtain ⟨σ, hσ, hσgt, hσM⟩ := hst _ (club_gt hM.1.1 hsp.2)
  have hψ0 : val.{u} (psiSuccK n) ≠ 0 := ne_of_gt (lt_of_lt_of_le (R_K hn).2.pos hb.1)
  have hCσ := ((M_pos_iff hψ0 σ).mp hσM).2.2.1
  exact psiSuccK_not_C hS hn (C_mono_base (Or.inl (lt_trans _ _ _ hσ hlt)) hCσ)

end

/-- 弱コンパクト基数の列 `h` のもとで、`K_{n-1} < Ξ_n(K_n^+) < K_n`、`Ξ_n(K_n^+) ∈ M^{K_n^+}`、
    `x > K_n^+` なら `Ξ_n(x) = K_n` -/
theorem Xi_succK_of_wc (h : ∀ n : Nat, EnumDef.{u} WeaklyCompactCard.{u} (ordNat.{u} n))
    {n : Nat} (hn : 1 ≤ n) :
    letI := settingOfWC.{u} h
    (M (Om (K n + succ 0)) (Xi n (Om (K n + succ 0))) ∧
      K (n - 1) < Xi n (Om (K n + succ 0)) ∧ Xi n (Om (K n + succ 0)) < K n) ∧
    ∀ x : Ordinal.{u}, Om (K n + succ 0) < x → Xi n x = K n := by
  letI := settingOfWC.{u} h
  exact ⟨Xi_succK_mem (stationaryHyp_of_wc h) hn,
    fun _ hx => Xi_eq_K_of_succK_lt (stationaryHyp_of_wc h) hn hx⟩

#print axioms Xi_succK_of_wc

/-! ## 等号の定理：標準形の値の集合は `C(Λ, 0)` と一致する（Rathjen の `T(K) = C(K_r, 0)` の加法版）。

* `C_of_good`：標準形の値は `C(Λ, 0)` に入る。
* `isRegTerm_of_good`：値が `Reg` に入る標準形は `isRegTerm` の形（`Ω_{ζ+1}`、`Ξ`、`ξ > 0` の `Ψ^ξ`）。
  `Ω` の引数が極限なら `Ω` は正則でなく（`Om_limit`）、`Ψ^0` も正則でない（Lemma 4.19 (iv)）。
* `mcond_of_Psi_lt`：`Ψ^ξ_π(β) < π` なら (T6) の条件 `ξ ∈ C(m(π), π) ∩ m(π)` が成り立つ
  （Lemma 5.2 (ii) の逆向き。`π` の形で場合分けし、`GenRep_*` と `transfer` で `Ψ` が `π` の定義の条件を
  満たすことを示して矛盾させる）。
* `exists_good_of_Cn`：`C(Λ, 0)` の元は標準形の値（段階についての帰納法。加法的主数は `Cn_gen` で本物の
  生成子に分ける。`Ξ_m(x) < K_m` なら `x ≤ K_m^+`（`Xi_eq_K_of_succK_lt`）で `x ∈ C(x, K_m)`）。
* `nfValue_iff_C`・`nf_unique`：`x ∈ C(Λ, 0)` ⟺ `x` は標準形の値で、その標準形は一意。 -/

noncomputable section

open RTKA (Tm)

/-! ### 和の項 -/

theorem summands_ofSummands : ∀ l : List Tm, (∀ s, s ∈ l → RTKA.isPrincipal s = true) →
    RTKA.summands (RTKA.ofSummands l) = l
  | [], _ => rfl
  | [a], h => RTKA.summands_principal (h a List.mem_cons_self)
  | a :: b :: rest, h => by
    show RTKA.summands (.plus a (RTKA.ofSummands (b :: rest))) = a :: b :: rest
    rw [RTKA.summands_plus,
      summands_ofSummands (b :: rest) (fun s hs => h s (List.mem_cons_of_mem a hs))]

theorem mOf_of_isRegTerm {p : Tm} (h : RTKA.isRegTerm p = true) : ∃ m, RTKA.mOf p = some m := by
  cases p <;> simp_all [RTKA.isRegTerm, RTKA.mOf]

/-- `p` が極限なら `x + p` も極限 -/
theorem isLimit_add {p : Ordinal.{u}} (x : Ordinal.{u}) (hp : IsLimit p) : IsLimit (x + p) := by
  refine ⟨lt_of_lt_of_le hp.1 (right_le_add x p), ?_⟩
  intro γ hγ
  by_cases hγx : γ < x
  · exact lt_of_le_of_lt (succ_le_of_lt hγx) (lt_add_of_pos x hp.1)
  · obtain ⟨d, hd, e⟩ := le_add_cases x p γ (Or.inl hγ) hγx
    have hdp : d < p := by
      cases hd with
      | inl h => exact h
      | inr h => rw [e, h] at hγ; exact absurd hγ (lt_irrefl _)
    rw [e, ← add_succ]
    exact (add_lt_add_iff_right x).mpr (hp.2 d hdp)

variable [Setting.{u}]

theorem exists_terms {Q : Tm → Prop} : ∀ l : List Ordinal.{u},
    (∀ p, p ∈ l → ∃ t, Q t ∧ val.{u} t = p) →
    ∃ ts : List Tm, (∀ t, t ∈ ts → Q t) ∧ ts.map val.{u} = l
  | [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, rfl⟩
  | p :: l, h => by
    obtain ⟨t, ht, e⟩ := h p List.mem_cons_self
    obtain ⟨ts, hts, e'⟩ := exists_terms l (fun q hq => h q (List.mem_cons_of_mem p hq))
    refine ⟨t :: ts, ?_, ?_⟩
    · intro s hs
      cases List.mem_cons.mp hs with
      | inl e => rw [e]; exact ht
      | inr hs => exact hts s hs
    · rw [List.map_cons, e, e']

/-- 加法的主数の標準形の非増加列から和の標準形を作る -/
theorem good_ofSummands : ∀ l : List Tm,
    (∀ s, s ∈ l → Good.{u} s ∧ RTKA.isPrincipal s = true) → Nonincr (l.map val.{u}) →
    Good.{u} (RTKA.ofSummands l) ∧ val.{u} (RTKA.ofSummands l) = listSum (l.map val)
  | [], _, _ => ⟨Good.zero, rfl⟩
  | [a], h, _ => by
    refine ⟨(h a List.mem_cons_self).1, ?_⟩
    show val a = listSum [val a]
    rw [listSum_cons, listSum_nil, add_zero]
  | a :: b :: rest, h, hn => by
    have ha := h a List.mem_cons_self
    have hrest : ∀ s, s ∈ b :: rest → Good.{u} s ∧ RTKA.isPrincipal s = true :=
      fun s hs => h s (List.mem_cons_of_mem a hs)
    have hn2 : (val.{u} a :: (b :: rest).map val).Pairwise (fun x y => y ≤ x) := hn
    have ih := good_ofSummands (b :: rest) hrest (List.pairwise_cons.mp hn2).2
    have hsum := summands_ofSummands (b :: rest) (fun s hs => (hrest s hs).2)
    refine ⟨?_, ?_⟩
    · show Good (.plus a (RTKA.ofSummands (b :: rest)))
      refine Good.plus a _ ha.1 ih.1 ha.2 ?_ ?_
      · intro e
        have h0 := summands_eq_nil.mpr e
        rw [hsum] at h0
        cases h0
      · intro hd hhd
        rw [hsum] at hhd
        simp only [List.head?_cons, Option.some.injEq] at hhd
        subst hhd
        exact (List.pairwise_cons.mp hn2).1 (val b) List.mem_cons_self
    · show val a + val (RTKA.ofSummands (b :: rest)) = listSum (val a :: (b :: rest).map val)
      rw [ih.2, listSum_cons]

/-! ### 標準形の値は `C(Λ, 0)` に入る -/

theorem C_of_good (hS : StationaryHyp.{u}) {t : Tm} (h : Good.{u} t) : C Λ 0 (val.{u} t) := by
  induction h with
  | zero => exact C_zero _ _
  | one => exact C_one _ _
  | kc n _ => exact C_K _ _ n
  | plus _ _ _ _ _ _ _ iha ihb => exact C_add iha ihb
  | om a ha _ _ iha => exact C_Om (ha.inv hS).lt_Λ iha
  | xi n a _ ha ha0 _ _ iha => exact C_Xi n ((ha.inv hS).pos ha0) (ha.inv hS).lt_Λ iha
  | psi _ _ _ _ _ hpi ha hreg hle _ _ _ _ _ _ ihxi ihpi iha =>
    exact C_Psi (ha.inv hS).lt_Λ hle ((hpi.inv hS).reg hreg).1 ihxi ihpi iha

/-! ### 正則な値の標準形 -/

/-- 最後の項が `1` でない 0 以外の標準形の値は極限 -/
theorem isLimit_of_not_isSucc (hS : StationaryHyp.{u}) {c : Tm} (hc : Good.{u} c)
    (hc0 : c ≠ .zero) (hs : RTKA.isSucc c = false) : IsLimit (val.{u} c) := by
  have ic := hc.inv hS
  cases hl : (RTKA.summands c).getLast? with
  | none => exact absurd (summands_eq_nil.mp (List.getLast?_eq_none_iff.mp hl)) hc0
  | some s =>
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hl
    have hsmem : s ∈ RTKA.summands c := by
      rw [hys]
      exact List.mem_append_right _ List.mem_cons_self
    have gs := summands_good c hc s hsmem
    have hs1 : s ≠ .one := by
      intro e
      subst e
      simp [RTKA.isSucc, hl] at hs
    have is := gs.1.inv hS
    have hlim := (is.principal gs.2).isLimit (is.one_lt gs.2 hs1)
    have hcnf := ic.cnf
    rw [hys, List.map_append, List.map_cons, List.map_nil] at hcnf
    rw [hcnf.eq, listSum_append, listSum_cons, listSum_nil, add_zero]
    exact isLimit_add _ hlim

/-- `Ω` の引数が極限なら `Ω` は正則でない -/
theorem not_R_Om_of_isLimit {w : Ordinal.{u}} (hl : IsLimit w) (hΛ : w < Λ) (hlt : w < Om w) :
    ¬ R (Om w) := by
  intro hR
  have hcf : CofinalFrom w (Om w) := by
    refine ⟨fun x => Om (type ((representative w).below x)), ?_, ?_⟩
    · intro x
      exact Om_lt_Om (initial_lt w x) hΛ
    · rw [Om_limit hl hΛ]
      rfl
  have hle : cf (Om w) ≤ w := least_le (fun β => CofinalFrom β (Om w)) hcf
  rw [hR.2.2] at hle
  exact absurd hlt (not_lt_of_le hle)

/-- Lemma 4.19 (iv)：`Ψ^0_π(β) < π` なら `Ψ^0_π(β)` は正則でない -/
theorem not_R_Psi_zero {π β : Ordinal.{u}} (hψ : Psi 0 π β < π) (hΛ : π < Λ) :
    ¬ R (Psi 0 π β) := by
  intro hR
  have sp := Psi_spec hψ
  have hstat : Stationary (Psi 0 π β) (M 0) :=
    (stationary_isLimit hR).mono (fun ρ hρ hl =>
      (M_zero_iff ρ).mpr ⟨hl, lt_trans _ _ _ hρ (lt_trans _ _ _ hψ hΛ)⟩)
  exact lt_irrefl _
    (Psi_le_of_stationary hR (Or.inl hψ) sp.2.2.1 sp.2.2.2.1 sp.2.2.2.2 (zero_le _) hstat)

/-- 値が `Reg` に入る標準形は `isRegTerm` -/
theorem isRegTerm_of_good (hS : StationaryHyp.{u}) {t : Tm} (h : Good.{u} t)
    (hR : IsReg (val.{u} t)) : RTKA.isRegTerm t = true := by
  have it := h.inv hS
  cases h with
  | zero => exact absurd hR.1.1 (not_lt_of_le (zero_le _))
  | one => exact absurd (one_lt_of_R hR.1) (lt_irrefl _)
  | kc n _ => exact absurd rfl (hR.2.2 n)
  | plus a b _ _ _ hb0 _ =>
    exfalso
    have hc := it.cnf
    rw [RTKA.summands_plus, List.map_cons] at hc
    have h2 := (List.cons.inj (cnf_of_principal hR.principal hc)).2
    exact hb0 (summands_eq_nil.mp (List.map_eq_nil_iff.mp h2))
  | om c hc hc0 hlt =>
    show RTKA.isSucc c = true
    cases hs : RTKA.isSucc c with
    | true => rfl
    | false =>
      exact absurd hR.1
        (not_R_Om_of_isLimit (isLimit_of_not_isSucc hS hc hc0 hs) (hc.inv hS).lt_Λ hlt)
  | xi _ _ _ _ _ _ _ => rfl
  | psi xi pi a _ _ hpi _ _ _ _ _ _ _ _ _ =>
    cases xi with
    | zero =>
      exact absurd hR.1 (not_R_Psi_zero (it.psi _ _ _ rfl).1 (hpi.inv hS).lt_Λ)
    | _ => rfl

/-! ### (T6) の条件 -/

/-- `Ψ^ξ_π(β) < π`（`π` は `isRegTerm` の標準形）なら (T6) の条件 `ξ ∈ C(m(π), π) ∩ m(π)` -/
theorem mcond_of_Psi_lt (hS : StationaryHyp.{u}) {p : Tm} (hp : Good.{u} p)
    (hreg : RTKA.isRegTerm p = true) {m : Tm} (hm : RTKA.mOf p = some m) {ξ β : Ordinal.{u}}
    (hψ : Psi ξ (val.{u} p) β < val p) : ξ < val.{u} m ∧ C (val.{u} m) (val p) ξ := by
  have ip := hp.inv hS
  have sp := Psi_spec hψ
  have hπR : IsReg (val.{u} p) := (ip.reg hreg).1
  -- `π ∈ C(β, Ψ)`、`Ψ ≤ π` なので、`π` の生成の引数は `C(β, Ψ)` に入る
  have hgen : GenRep (C β (Psi ξ (val.{u} p) β)) β (val p) :=
    C_gen sp.2.2.2.1 hπR.principal (Or.inl hψ)
  have hcl := sp.2.2.1
  have hξC := Psi_C_xi hψ
  cases hp with
  | zero => simp [RTKA.isRegTerm] at hreg
  | one => simp [RTKA.isRegTerm] at hreg
  | kc _ _ => simp [RTKA.isRegTerm] at hreg
  | plus _ _ _ _ _ _ _ => simp [RTKA.isRegTerm] at hreg
  | om c hc _ hlt =>
    simp only [RTKA.mOf, Option.some.injEq] at hm
    subst hm
    obtain ⟨ζ, hζ, hζC⟩ := (hc.inv hS).isSucc hreg
    have hcΛ := (hc.inv hS).lt_Λ
    -- `ξ = 0`：`ξ > 0` なら `Ψ` は `Ω` の不動点だが、`Ω_ζ < Ψ < Ω_{ζ+1}`
    have hξ0 : ξ = 0 := by
      cases eq_zero_or_pos ξ with
      | inl h => exact h
      | inr hpos =>
        exfalso
        have hfix := M_fixed hpos sp.2.1
        have hcC : C β (Psi ξ (Om (val c)) β) (val c) := GenRep_Om hgen hcΛ hlt
        have hζc : ζ < val.{u} c := by rw [hζ]; exact lt_succ_self ζ
        have hζΛ : ζ < Λ := lt_trans _ _ _ hζc hcΛ
        have hOmζ := hcl _ (C_Om hζΛ (hζC _ _ hcC)) (Om_lt_Om hζc hcΛ)
        have hψΛ := lt_trans _ _ _ hψ ip.lt_Λ
        have h1 : Om (Psi ξ (val (Tm.Om c)) β) < Om (val c) := by rw [hfix]; exact hψ
        have h2 := le_of_lt_succ (hζ ▸ (Om_lt_Om_iff hψΛ hcΛ).mp h1)
        have h3 := Om_le_Om h2 hζΛ
        rw [hfix] at h3
        exact absurd hOmζ (not_lt_of_le h3)
    subst hξ0
    exact ⟨lt_succ_self 0, C_zero _ _⟩
  | xi n a _ _ _ _ _ =>
    simp only [RTKA.mOf, Option.some.injEq] at hm
    subst hm
    obtain ⟨hapos, hgood⟩ := ip.xi n a rfl
    -- `Ψ ∈ M^a` は `Ξ_n(a)` の最小性に反する
    have key : ¬ M (val.{u} a) (Psi ξ (Xi n (val a)) β) := by
      intro hM
      have hK : K (n - 1) < Psi ξ (Xi n (val.{u} a)) β := hcl _ (C_K _ _ (n - 1)) hgood.2.1
      exact absurd (lt_of_le_of_lt (Xi_le_of hM hK (lt_trans _ _ _ hψ hgood.2.2)) hψ)
        (lt_irrefl _)
    have hξa : ξ < val.{u} a := by
      apply lt_of_not_le
      intro hle
      cases hle with
      | inr e => subst e; exact key sp.2.1
      | inl hlt =>
        apply key
        have haC := (GenRep_Xi hgen hapos hgood.2.2).1
        obtain ⟨k, hk⟩ := ((M_pos_iff (ne_of_gt hapos) _).mp hgood.1).2.2.1
        have h' := transfer hψ (le_refl _) hcl k (val a) hk haC
        exact M_of_M sp.2.1 hlt (C_mono_arg (Or.inl hlt) h')
    exact ⟨hξa, C_mono_base (Or.inl hψ) (C_mono_arg (Or.inl hξa) hξC)⟩
  | psi σ κ γ _ _ _ _ _ _ _ _ _ _ _ _ =>
    simp only [RTKA.mOf, Option.some.injEq] at hm
    subst hm
    have hπκ := ip.psi σ κ γ rfl
    have spπ := Psi_spec hπκ.1
    have g := GenRep_Psi hgen hπκ.2 hπκ.1
    -- `Ψ ∈ M^σ` なら `Ψ` は `π = Ψ^σ_κ(γ)` の定義の条件を満たし、`π` の最小性に反する
    have key : ¬ M (val.{u} σ) (Psi ξ (val (Tm.Psi σ κ γ)) β) := by
      intro hM
      obtain ⟨k1, hk1⟩ := spπ.2.2.2.1
      obtain ⟨k2, hk2⟩ := spπ.2.2.2.2
      have hκC := transfer hψ (le_refl _) hcl k1 _ hk1 g.2.1
      have hγC := transfer hψ (le_refl _) hcl k2 _ hk2 g.2.2.1
      have hclγ : ∀ x, C (val.{u} γ) (Psi ξ (val (Tm.Psi σ κ γ)) β) x → x < val κ →
          x < Psi ξ (val (Tm.Psi σ κ γ)) β := by
        intro x hx hxκ
        have hxπ := spπ.2.2.1 x (C_mono_base (Or.inl hψ) hx) hxκ
        exact hcl x (C_mono_arg (Or.inl g.2.2.2) hx) hxπ
      have hle := Psi_le_of spπ.1 hM (lt_trans _ _ _ hψ hπκ.1) hclγ hκC hγC
      exact absurd hψ (not_lt_of_le hle)
    have hξσ : ξ < val.{u} σ := by
      apply lt_of_not_le
      intro hle
      cases hle with
      | inr e => subst e; exact key sp.2.1
      | inl hlt =>
        apply key
        obtain ⟨k, hk⟩ := Psi_C_xi hπκ.1
        have h' := transfer hψ (le_refl _) hcl k _ hk g.1
        exact M_of_M sp.2.1 hlt (C_mono_arg (Or.inl hlt) h')
    exact ⟨hξσ, C_mono_base (Or.inl hψ) (C_mono_arg (Or.inl hξσ) hξC)⟩

/-! ### `C(Λ, 0)` の元は標準形の値 -/

theorem exists_good_of_Cn (hS : StationaryHyp.{u}) :
    ∀ n z, Cn Λ 0 n z → ∃ t, Good.{u} t ∧ val.{u} t = z := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have ihb : ∀ w, Below Λ 0 n w → ∃ t, Good.{u} t ∧ val.{u} t = w := by
      intro w hw
      obtain ⟨k, hk, hkw⟩ := hw
      exact ih k hk w hkw
    -- 加法的主数：`Cn_gen` で本物の生成子に分ける
    have hprin : ∀ p, Cn Λ 0 n p → IsPrincipal p →
        ∃ t, (Good.{u} t ∧ RTKA.isPrincipal t = true) ∧ val.{u} t = p := by
      intro p hp hP
      rcases Cn_gen hp hP (zero_le p) with h | ⟨m, h⟩ | ⟨w, hw, hΛ, hlt, h⟩ |
          ⟨m, x, hx, hpos, _, hX, h⟩ | ⟨ξ, π, β, hξ, hπ, hβ, _, hξβ, hπR, hψ, h⟩
      · exact ⟨.one, ⟨Good.one, rfl⟩, h.symm⟩
      · cases m with
        | zero => exact absurd h hP.1
        | succ m =>
          exact ⟨.K (m + 1), ⟨Good.kc _ (Nat.succ_le_succ (Nat.zero_le m)), rfl⟩, h.symm⟩
      · obtain ⟨tw, gw, ew⟩ := ihb w hw
        subst ew
        have htw0 : tw ≠ .zero := by
          intro e
          subst e
          change (0 : Ordinal.{u}) < Om 0 at hlt
          rw [Om_zero] at hlt
          exact lt_irrefl _ hlt
        exact ⟨.Om tw, ⟨Good.om tw gw htw0 hlt, rfl⟩, h.symm⟩
      · obtain ⟨tx, gx, ex⟩ := ihb x hx
        subst ex
        have hm1 := Xi_level hX
        have htx0 : tx ≠ .zero := by
          intro e
          subst e
          exact lt_irrefl _ hpos
        have hxle : val.{u} tx ≤ Om (K m + succ 0) := by
          apply le_of_not_lt
          intro hgt
          rw [Xi_eq_K_of_succK_lt hS hm1 hgt] at hX
          exact lt_irrefl _ hX
        have hxC : C (val.{u} tx) (K m) (val tx) :=
          C_mono_base (Or.inl hX) ((M_pos_iff (ne_of_gt hpos) _).mp (Xi_spec hX).1).2.2.1
        exact ⟨.Xi m tx, ⟨Good.xi m tx hm1 gx htx0 hxle hxC, rfl⟩, h.symm⟩
      · obtain ⟨tξ, gξ, eξ⟩ := ihb ξ hξ
        obtain ⟨tπ, gπ, eπ⟩ := ihb π hπ
        obtain ⟨tβ, gβ, eβ⟩ := ihb β hβ
        subst eξ eπ eβ
        have hreg := isRegTerm_of_good hS gπ hπR
        obtain ⟨mm, hmm⟩ := mOf_of_isRegTerm hreg
        have mc := mcond_of_Psi_lt hS gπ hreg hmm hψ
        have sp := Psi_spec hψ
        exact ⟨.Psi tξ tπ tβ, ⟨Good.psi tξ tπ tβ mm gξ gπ gβ hreg hξβ
          (C_mono_base (Or.inl hψ) sp.2.2.2.2) (C_mono_base (Or.inl hψ) (Psi_C_xi' hψ))
          (C_mono_base (Or.inl hψ) sp.2.2.2.1) hmm mc.1 mc.2, rfl⟩, h.symm⟩
    -- 一般の元：Cantor 標準形の項ごとに標準形を作って並べる
    intro z hz
    obtain ⟨l, hl⟩ := cnf_exists z
    obtain ⟨ts, hts, e⟩ := exists_terms (Q := fun t => Good.{u} t ∧ RTKA.isPrincipal t = true) l
      (fun p hp => hprin p (Cn_cnf hz hl p hp) (hl.principal hp))
    have hn : Nonincr (ts.map val.{u}) := by rw [e]; exact hl.2.1
    obtain ⟨g, ev⟩ := good_ofSummands ts hts hn
    exact ⟨_, g, by rw [ev, e, ← hl.eq]⟩

/-! ### 等号の定理 -/

/-- 等号の定理：`x` が標準形の値 ⟺ `x ∈ C(Λ, 0)` -/
theorem nfValue_iff_C (hS : StationaryHyp.{u}) (x : Ordinal.{u}) :
    (∃ t, RTKA.isNF t = true ∧ val.{u} t = x) ↔ C Λ 0 x := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact C_of_good hS (good_of_isNF hS t ht)
  · intro hx
    obtain ⟨n, hn⟩ := hx
    obtain ⟨t, g, e⟩ := exists_good_of_Cn hS n x hn
    exact ⟨t, isNF_of_good hS t g, e⟩

/-- 値の標準形は一意 -/
theorem nf_unique (hS : StationaryHyp.{u}) {t t' : Tm} (ht : RTKA.isNF t = true)
    (ht' : RTKA.isNF t' = true) (e : val.{u} t = val t') : t = t' :=
  val_inj hS t t' (good_of_isNF hS t ht) (good_of_isNF hS t' ht') e

end

/-- 弱コンパクト基数の列 `h` のもとで、`C(Λ, 0)` の元はちょうど一つの標準形の値 -/
theorem nfValue_iff_C_of_wc (h : ∀ n : Nat, EnumDef.{u} WeaklyCompactCard.{u} (ordNat.{u} n))
    (x : Ordinal.{u}) :
    letI := settingOfWC.{u} h
    ((∃ t, RTKA.isNF t = true ∧ val.{u} t = x) ↔ C Λ 0 x) ∧
      ∀ t t', RTKA.isNF t = true → RTKA.isNF t' = true → val.{u} t = val t' → t = t' := by
  letI := settingOfWC.{u} h
  exact ⟨nfValue_iff_C (stationaryHyp_of_wc h) x,
    fun _ _ ht ht' e => nf_unique (stationaryHyp_of_wc h) ht ht' e⟩

#print axioms nfValue_iff_C_of_wc

end OCF.Rathjen
