import Compact.OCFRathjen.Collapse
import Compact.Additive

/-! 記法系 `T⁺`（`Compact/Additive.lean` の `RTKA`）の項の値と、目標の定理の主張。

* `val`：項の値（`Ψ^ξ_π(α)` は `Psi ξ π α`、`Ξ_n(α)` は `Xi n α`）。
* `StationaryHyp`：Rathjen の Thm. 4.12 にあたる定常性。
  `1 ≤ n`、`0 < α ≤ K_n^+`、`α ∈ C(α, K_n)` なら `M^α` は `K_n` で定常。
* `CmpCorrect`：目標。標準形の項について `cmp` が値の大小と一致する。

`StationaryHyp → CmpCorrect` は `Main.lean` の `cmpCorrect_of_stationaryHyp`。`StationaryHyp` は
`WeaklyCompact.lean` の `stationaryHyp_of_wc` で弱コンパクト基数の列から導く。 -/

namespace OCF.Rathjen

universe u

open Ordinal

noncomputable section

variable [Setting.{u}]

/-- 項の値 -/
def val : RTKA.Tm → Ordinal.{u}
  | .zero => 0
  | .one => succ 0
  | .K n => K n
  | .plus a b => val a + val b
  | .Om a => Om (val a)
  | .Xi n a => Xi n (val a)
  | .Psi xi pi a => Psi (val xi) (val pi) (val a)

theorem val_succK (n : Nat) : val.{u} (RTKA.succK n) = Om (K n + succ 0) := by
  simp only [RTKA.succK, val]

/-- Thm. 4.12 にあたる定常性（`K_n` が弱コンパクトなら成り立つ：`stationaryHyp_of_wc`）：
    `1 ≤ n`、`0 < α ≤ K_n^+`、`α ∈ C(α, K_n)` なら `M^α` は `K_n` で定常 -/
def StationaryHyp : Prop :=
  ∀ n, 1 ≤ n → ∀ α : Ordinal.{u}, 0 < α → α ≤ Om (K n + succ 0) → C α (K n) α →
    Stationary (K n) (M α)

/-- 目標：標準形の項について、`cmp` が値の大小・相等と一致する -/
def CmpCorrect : Prop :=
  ∀ a b : RTKA.Tm, RTKA.isNF a = true → RTKA.isNF b = true →
    (RTKA.lt a b = true ↔ val.{u} a < val b) ∧ (RTKA.cmp a b = .eq ↔ val.{u} a = val b)

/-- `M^α` が `K_m` で定常なら `K_{m-1} < Ξ_m(α) < K_m` で `Ξ_m(α) ∈ M^α` -/
theorem Xi_lt {m : Nat} (hm : 1 ≤ m) {α : Ordinal.{u}} (hstat : Stationary (K m) (M α)) :
    Xi m α < K m := by
  have hlt : K (m - 1) < K m := K_lt (Nat.sub_lt hm Nat.one_pos)
  cases hstat _ (club_gt (R_K hm) hlt) with
  | intro π hπ => exact lt_of_le_of_lt (Xi_le_of hπ.2.2 hπ.2.1 hπ.1) hπ.1

theorem Xi_mem {m : Nat} (hm : 1 ≤ m) {α : Ordinal.{u}} (hstat : Stationary (K m) (M α)) :
    M α (Xi m α) ∧ K (m - 1) < Xi m α ∧ Xi m α < K m :=
  let h := Xi_spec (Xi_lt hm hstat)
  ⟨h.1, h.2, Xi_lt hm hstat⟩

end
end OCF.Rathjen
