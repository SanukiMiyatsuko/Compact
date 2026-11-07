import Compact.FS.LadHull

/-! 目標が `Ω_c` の崩壊 `t = Ψ^0_{Ω_c}(X)` の下界の振り分け：列は種の倍数（`lbi_mulNat` で済む）か、`Ψ^0_{Ω_c}` の
近似（`app`、一つずらしたものを含む）。近似の場合は仮定 `AppCaseOm` として受け取る。 -/

namespace RTKA.Fund

open Tm W

/-- 種の倍数の列の下界 -/
theorem ladL_mul {p : Tm} (hp : WNF p) (hpp : isPrincipal p = true) (k : Nat) : LadL (.mul p k) := by
  refine ladL_of_nat fun _ n => ?_
  show LBI (mulNat p (n + k)) (mulNat p (n + 1 + k))
  rw [show n + 1 + k = n + k + 1 by omega]
  exact lbi_mulNat hp hpp (n + k)

/-- 目標が `Ω_c` の近似の列の場合の仮定（真の部分項の下界を使ってよい） -/
def AppCaseOm : Prop :=
  ∀ c X τ pre R r P k, WNF (.Psi .zero (.Om c) X) → X ≠ .zero →
    (cs (.Om c) X = .app τ (.psi0 (.Om c)) pre R r P k ∨
      cs (.Om c) X = .shift (.app τ (.psi0 (.Om c)) pre R r P k)) →
    (∀ u, u ∈ subs (.Psi .zero (.Om c) X) → u ≠ .Psi .zero (.Om c) X → LadL (info u).seq) →
    LadL (cs (.Om c) X)

/-- 目標が `Ω_c` の崩壊の下界（近似の場合を仮定して） -/
theorem ladL_psi_om (hA : AppCaseOm) {c X : Tm} (ht : WNF (.Psi .zero (.Om c) X))
    (hIH : ∀ u, u ∈ subs (.Psi .zero (.Om c) X) → u ≠ .Psi .zero (.Om c) X → LadL (info u).seq) :
    LadL (info (.Psi .zero (.Om c) X)).seq := by
  rw [info_seq_psi0]
  have hπ := ht.psi.piF
  have hs : isSucc c = true := (WNF.psiOm ht).2.2.1
  by_cases hX0 : X = .zero
  · subst hX0
    rw [cs_om_zero]
    exact ladL_mul (omBase_wnf hπ hs).1 (omBase_wnf hπ hs).2 2
  rcases cs_om_shape ht hX0 with ⟨p, e, hpF, hpp, -⟩ | ⟨τ, pre, R, r, P, k, e⟩
  · rw [e]
    exact ladL_mul hpF hpp 2
  · exact hA c X τ pre R r P k ht hX0 e hIH

end RTKA.Fund
