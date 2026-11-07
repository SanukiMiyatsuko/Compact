import Compact.FS.LadAdd

/-! 不等式版の梯子の骨組み：項の大きさの帰納法で、全ての項の列の記述が `LadL`（`ω` 型なら隣り合う項の
区間の下界）を満たすことを示す。和は最後の加数から（`ladL_add`）。`Ω_c`（`c` 極限）と `Ψ^0_π(X)` の場合は
仮定として受け取る（`OmLimCase`・`PsiCase`）。 -/

namespace RTKA.Fund

open Tm W

/-- 列の記述の下界の性質：`ω` 型なら隣り合う項の区間の下界 -/
def LadL (s : SeqD) : Prop :=
  match s.dom with
  | .omega => ∀ n, LBI (s.nat n) (s.nat (n + 1))
  | _ => True

theorem ladL_of_nat {s : SeqD} (h : s.dom = .omega → ∀ n, LBI (s.nat n) (s.nat (n + 1))) : LadL s := by
  unfold LadL
  split
  · rename_i hd
    exact h hd
  · trivial

theorem LadL.nat {s : SeqD} (h : LadL s) (hd : s.dom = .omega) : ∀ n, LBI (s.nat n) (s.nat (n + 1)) := by
  unfold LadL at h
  rw [hd] at h
  exact h

/-- 和の項：最後の加数の下界から -/
theorem ladL_add {a b : Tm} (ht : WNF (.plus a b)) (hL : LadL (info b).seq) :
    LadL (info (.plus a b)).seq := by
  obtain ⟨ha, hb, hap, -⟩ := ht.plus
  refine ladL_of_nat fun hd n => ?_
  have hd' : dom b = .omega := hd
  have hG := (seqI_dom_nat hb hd').1.good
  have hy := hG (n + 1)
  show LBI (oadd a ((info b).seq.nat n)) (oadd a ((info b).seq.nat (n + 1)))
  exact lbi_oadd ha hap (hG n).1 hy.1
    (summands_le_of_le ha hap hb hy.1 (summands_le_head_plus ht) (Or.inr hy.2.1)) (hL.nat hd' n)

/-- `Ω_c`（`c` 極限）の場合の仮定 -/
def OmLimCase : Prop :=
  ∀ c, WNF (.Om c) → ¬ isSucc c = true → LadL (info c).seq → LadL (.om (info c).seq)

/-- `Ψ^0_π(X)` の場合の仮定（真の部分項の下界を使ってよい） -/
def PsiCase : Prop :=
  ∀ π X, WNF (.Psi .zero π X) →
    (∀ u, u ∈ subs (.Psi .zero π X) → u ≠ .Psi .zero π X → LadL (info u).seq) →
    LadL (info (.Psi .zero π X)).seq

/-- 正則項の列は `big` 型 -/
theorem ladL_reg (σ b : Tm) : LadL (.reg σ b) := by
  unfold LadL
  simp [SeqD.dom]

/-- 全ての項の列の記述の下界の性質（`Ω_c` の極限と `Ψ^0` の場合を仮定して） -/
theorem ladL_all (hOm : OmLimCase) (hPsi : PsiCase) (t : Tm) (ht : WNF t) : LadL (info t).seq := by
  induction hn : t.size using Nat.strongRecOn generalizing t with
  | ind n ih =>
    have hIC : ∀ u, u ∈ subs t → u ≠ t → LadL (info u).seq := fun u hu hne =>
      ih u.size (hn ▸ size_lt_of_mem_subs_ne hu hne) u (ht.of_mem_subs hu) rfl
    cases t with
    | zero => unfold LadL; simp [info, SeqD.dom]
    | one => unfold LadL; simp [info, SeqD.dom]
    | K m => exact ladL_reg _ _
    | plus a b =>
      have hb : b ∈ subs (.plus a b) := subs_plus_r (self_mem_subs b)
      have hne : b ≠ .plus a b := ne_of_size_lt (by simp only [Tm.size]; omega)
      exact ladL_add ht (hIC b hb hne)
    | Om c =>
      by_cases hs : isSucc c = true
      · have e : (info (.Om c)).seq = .reg (.Om c) (base (.Om c)) := by simp [info, hs]
        rw [e]
        exact ladL_reg _ _
      · have e : (info (.Om c)).seq = .om (info c).seq := by simp [info, hs]
        rw [e]
        have hc : c ∈ subs (.Om c) := subs_om (self_mem_subs c)
        have hne : c ≠ .Om c := ne_of_size_lt (by simp only [Tm.size]; omega)
        exact hOm c ht hs (hIC c hc hne)
    | Xi m q => exact ladL_reg _ _
    | Psi ζ π X =>
      by_cases hζ : ζ = .zero
      · subst hζ
        exact hPsi π X ht hIC
      · have e : (info (.Psi ζ π X)).seq = .reg (.Psi ζ π X) (base (.Psi ζ π X)) := by simp [info, hζ]
        rw [e]
        exact ladL_reg _ _

/-- 二つの場合の仮定から、不等式版の梯子 -/
theorem ladderLB_of (hOm : OmLimCase) (hPsi : PsiCase) : LadderLB := fun t ht hd =>
  (ladL_all hOm hPsi t ht).nat hd

end RTKA.Fund
