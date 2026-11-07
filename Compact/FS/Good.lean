import Compact.FS.Core

/-! 崩壊 `Ψ^0_π(X)` の列の性質（標準形・元の項未満・単調）の枠組みと、単純な出力。

列の記述 `s` が項 `t` について良い（`NatGood`・`BigGood`）とは、列の各項が標準形で `t` 未満、添字について
狭義単調であること。崩壊の列の記述 `cs π X` が全て良ければ、`NF.lean`・`Lt.lean` の仮定
（`PsiNatNF` など）が成り立つ。出力の形ごとに、良いための十分条件を示す：

* `mul p k`（`[n] = p·(n+k)`）：種 `p` が主要項で `t` 未満、`t` が主要項。
* `tower G`（Ω の塔の 1 段目から）：始点 `G` が `t` 未満、`t` が Ω の不動点。

種については、前線の元（`maxL (frB τ X)`）が `Ψ^0_τ(X)` 未満であることを示す。 -/

namespace RTKA.Fund

open Tm W

/-- 共終数 `ω` の列の記述 `s` が `t` について良い：各項が標準形で `t` 未満、狭義単調 -/
def NatGood (t : Tm) (s : SeqD) : Prop :=
  ∀ n, WNF (s.nat n) ∧ Lt (s.nat n) t ∧ Lt (s.nat n) (s.nat (n + 1))

/-- 共終数が正則項 `σ` の列の記述 `s` が `t` について良い：`σ` 未満の添字で各項が標準形・`t` 未満、狭義単調 -/
def BigGood (t σ : Tm) (s : SeqD) : Prop :=
  (∀ ξ, WNF ξ → Lt ξ σ → WNF (s.big ξ) ∧ Lt (s.big ξ) t) ∧
    ∀ ξ η, WNF ξ → WNF η → Lt ξ η → Lt η σ → Lt (s.big ξ) (s.big η)

/-- 崩壊の列の記述が全て良ければ、`ω` 型の列の仮定（標準形・減少・単調）が成り立つ -/
theorem psiNat_of_good
    (h : ∀ π X, WNF (.Psi .zero π X) → dom (.Psi .zero π X) = .omega → NatGood (.Psi .zero π X) (cs π X)) :
    PsiNatNF ∧ PsiNatLt ∧ PsiNatMono :=
  ⟨fun π X n ht hd => (h π X ht hd n).1, fun π X n ht hd => (h π X ht hd n).2.1,
    fun π X n ht hd => (h π X ht hd n).2.2⟩

/-- 崩壊の列の記述が全て良ければ、正則項型の列の仮定（標準形・減少・単調）が成り立つ -/
theorem psiBig_of_good
    (h : ∀ π X σ, WNF (.Psi .zero π X) → dom (.Psi .zero π X) = .big σ →
      BigGood (.Psi .zero π X) σ (cs π X)) :
    PsiBigNF ∧ PsiBigLt ∧ PsiBigMono :=
  ⟨fun π X ξ σ ht hξ hd hlt => ((h π X σ ht hd).1 ξ hξ hlt).1,
    fun π X ξ σ ht hξ hd hlt => ((h π X σ ht hd).1 ξ hξ hlt).2,
    fun π X ξ η σ ht hξ hη hd hlt hη' => (h π X σ ht hd).2 ξ η hξ hη hlt hη'⟩

/-! ### 単純な出力 -/

/-- 種の倍数 `[n] = p·(n+k)` -/
theorem natGood_mul {t p : Tm} (hp : WNF p) (hpp : isPrincipal p = true) (htp : isPrincipal t = true)
    (hlt : Lt p t) (k : Nat) : NatGood t (.mul p k) := fun n =>
  ⟨wnf_mulNat hp hpp _, mulNat_lt_prin hpp htp hlt _, mulNat_lt_mulNat hp hpp (by omega)⟩

/-- `G` から始まる Ω の塔（`t` は Ω の不動点） -/
theorem natGood_tower {t G : Tm} (ht : WNF t) (hOF : IsOF t) (hG : WNF G) (hlt : Lt G t) :
    NatGood t (.tower G) := fun n =>
  ⟨wnf_tower hG _, tower_lt_OF hOF ht hG hlt _, tower_mono hG _⟩

/-! ### 前線の種 -/

theorem frB_eq_fr (R : Tm) : ∀ x : Tm, frB R x = fr R x
  | .plus a b => by simp only [frB, fr, frB_eq_fr R a, frB_eq_fr R b]
  | .Om a => by simp only [frB, fr, frB_eq_fr R a]
  | .Xi m a => by
    simp only [frB, fr, frB_eq_fr R a]
    by_cases h : Lt (Xi m a) R
    · rw [ite_eq_left (ltB_iff.mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun e => h (ltB_iff.mp e)), ite_eq_right h]
  | .Psi s p a => by
    simp only [frB, fr, frB_eq_fr R s, frB_eq_fr R p, frB_eq_fr R a]
    by_cases h : Lt (Psi s p a) R
    · rw [ite_eq_left (ltB_iff.mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun e => h (ltB_iff.mp e)), ite_eq_right h]
  | .zero | .one | .K _ => rfl

theorem maxL_mem : ∀ {l : List Tm} {p : Tm}, maxL l = some p → p ∈ l
  | [], _, h => by simp [maxL] at h
  | x :: xs, p, h => by
    simp only [maxL] at h
    split at h
    · cases h; exact List.mem_cons_self
    · rename_i y hy
      split at h
      · cases h; exact List.mem_cons_of_mem _ (maxL_mem hy)
      · cases h; exact List.mem_cons_self

/-- 引数の前線の最大の元（種）は `Ψ^ξ_τ(X)` 未満 -/
theorem lt_of_maxL_frB {ξ τ X p : Tm} (ht : WNF (.Psi ξ τ X)) (h : maxL (frB τ X) = some p) :
    Lt p (.Psi ξ τ X) := by
  have hm := maxL_mem h
  rw [frB_eq_fr] at hm
  exact FWOrder.k2 ht p hm

/-- 目標自身の前線の最大の元（種）は `Ψ^ξ_τ(X)` 未満 -/
theorem lt_of_maxL_frB_tgt {ξ τ X p : Tm} (ht : WNF (.Psi ξ τ X)) (h : maxL (frB τ τ) = some p) :
    Lt p (.Psi ξ τ X) := by
  have hm := maxL_mem h
  rw [frB_eq_fr] at hm
  exact FWOrder.k2t ht p hm

/-- 前線の元は標準形で主要項 -/
theorem wnf_of_maxL_frB {τ X p : Tm} (hX : WNF X) (h : maxL (frB τ X) = some p) :
    WNF p ∧ isPrincipal p = true := by
  have hm := maxL_mem h
  rw [frB_eq_fr] at hm
  obtain ⟨hs, -⟩ := fr_spec hm
  refine ⟨hX.of_mem_subs hs, ?_⟩
  rcases fr_node hm with ⟨m, a, rfl⟩ | ⟨s, q, a, rfl⟩ <;> rfl

end RTKA.Fund
