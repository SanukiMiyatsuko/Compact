import Compact.OCFRathjen.Eval

/-! 弱コンパクト性（`Π¹₁`-記述不可能性）と、定常性仮定 (S) の導出。

Rathjen 1994 の定理 4.12 は、弱コンパクト基数 `K` に対し
`α < K^Γ` ならば `M^α` が `K` で定常であることを示す。証明では、
`(V_K, ∈, U₁, U₂, U₃, ∈)` に対する `Π¹₁` 文 (4)（`β < α` なる各 `β` について
`M^β` が `K` で定常であることを符号化したもの）を `Π¹₁`-記述不可能性で
反射させ、得られた `τ < K` が (a)(b)(c)(d) と補助主張 (+) を満たすことから
`τ ∈ M^α ∩ E` を導く。

本稿の形式化には集合論の言語（`V_α` 階層と充足関係）がないため、
この証明で実際に用いられる反射原理を `WeaklyCompact` として定式化し、
「各 `K_n`（`1 ≤ n`）は弱コンパクト基数である」を公理 `weaklyCompact` として課す。

反射原理の結論は、定理 4.12 の証明で得られる `τ` の性質を加法版の記号で
書き下したものである：

* `τ < K_n` かつ `τ ∈ E`（反射は任意の club `E` について行える）。
* `τ` は正則（本文の (a)(b)(c)）。
* `α ∈ C(α, τ)`（本文では `E` を `ρ₀ < τ` なるように取り直し、`α ∈ C(α, ρ₀)`
  と単調性から得るが、ここでは反射原理の結論に含める）。
* `C(α, τ) ∩ K(τ) ⊆ τ`（本文の (+) と (a)(b)）。
* `β < α` かつ `β ∈ C(α, τ)` ならば `M^β` は `τ` で定常（本文の (+) と (d)）。

仮定側では、本文の `Π¹₁` 文 (4) の加法版として、(S) の形
（`β < α` なる各 `β` についての定常性）を課す。

`stationaryHyp` で定常性仮定 (S) を `α` についての帰納法で導く。 -/

namespace OCF.Rathjen

universe u

open Ordinal

noncomputable section

variable [Setting.{u}]

/-- `K_n` の弱コンパクト性（`Π¹₁`-記述不可能性）を、Thm. 4.12 の証明で用いられる
反射原理の形に定式化したもの（詳細はファイル冒頭）。 -/
def WeaklyCompact (n : Nat) : Prop :=
  ∀ α, 0 < α → α < Om (K n + succ 0) → C α (K n) α →
    (∀ β, β < α → 0 < β → β < Om (K n + succ 0) → C β (K n) β →
      Stationary (K n) (M β)) →
    ∀ E, Club (K n) E →
      ∃ τ, τ < K n ∧ E τ ∧ IsReg τ ∧ C α τ α ∧
        (∀ x, C α τ x → x < Kabove τ → x < τ) ∧
        (∀ β, β < α → C α τ β → Stationary τ (M β))

/-- 各 `K_n`（`1 ≤ n`）は弱コンパクト基数である（典型的には `K_n` を `n` 番目の
弱コンパクト基数とする）。本稿で許す唯一の集合論的公理。 -/
axiom weaklyCompact (n : Nat) (hn : 1 ≤ n) : WeaklyCompact n

/-- 定常性仮定 (S)（`Eval.lean` の `StationaryHyp`）：弱コンパクト性から従う
（定理 4.12 の加法版）。 -/
theorem stationaryHyp : StationaryHyp.{u} := by
  intro n hn α
  induction α using lt_wellFounded.induction with
  | h β ih =>
    intro hβ0 hβK hCβ E hE
    obtain ⟨τ, hτK, hEτ, hreg, hCβτ, hcl, hstat⟩ :=
      weaklyCompact n hn β hβ0 hβK hCβ ih E hE
    exact ⟨τ, hτK, hEτ, (M_pos_iff (ne_of_gt hβ0) τ).mpr ⟨hreg, hcl, hCβτ, hstat⟩⟩

end
end OCF.Rathjen
