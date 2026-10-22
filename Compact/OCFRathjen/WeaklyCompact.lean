import Compact.OCFRathjen.Main
import Compact.OCFRathjen.Pairing
import Compact.OCFRathjen.ReflMain

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

end OCF.Rathjen
