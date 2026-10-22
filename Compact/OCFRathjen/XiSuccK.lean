import Compact.OCFRathjen.WeaklyCompact

/-! `Ξ_n` の引数の上端 `K_n^+ = Ω_{K_n+1}`。

* `Xi_succK_mem`：`K_{n-1} < Ξ_n(K_n^+) < K_n` で `Ξ_n(K_n^+) ∈ M^{K_n^+}`（`StationaryHyp` は `α ≤ K_n^+` を
  含む）。標準形は `Ξ_n(α)` を `α ≤ K_n^+` まで許す。
* `Xi_eq_K_of_succK_lt`：`x > K_n^+` なら `Ξ_n(x) = K_n`。`ψ = Ψ^0_{K_n^+}(K_n^+)` は `C(x, ρ)` に入るが
  `ψ ∉ C(ψ, K_n)` なので `M^ψ` は `K_n` 未満で空で、`M^x` も `(K_{n-1}, K_n)` で空になる。
  `Ξ_n` の引数を `K_n^+` より先に広げても新しい順序数は出ない。 -/

namespace OCF.Rathjen

universe u

open Ordinal

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

end OCF.Rathjen
