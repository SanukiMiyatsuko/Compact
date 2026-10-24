/-!
# Rathjen の記法系の加法版 `T⁺`

M. Rathjen, *Proof theory of reflection*（APAL 68, 1994）§4–§5 の `T(K)` から Veblen 関数を抜き、
閉包を加法だけにしたもの。Subsp の `OCF/Jaeger` が Jäger の論文に対して行ったのと同じ変更である。
意味論（`C`・`M^α`・`Ξ_n`・`Ψ` の定義と項の値）は `OCFRathjen/Setting.lean`。

`T(K)` との違い：

* `C(α, β)` は `β ∪ {0, 1} ∪ {K_n : n ≥ 1}` を `+`, `Ω`, `Ξ_n`, `Ψ` で閉じたもの（`φ` が無い）。
  `φ` が無いと `1` が項で書けず `Ω_1` も作れないので、`1` を定数に入れた。
* 頂上の `K` を弱コンパクト基数の列 `K_1 < K_2 < ⋯` に替えた。`φ` が無いと `K` より上は `K·n + β`
  しか作れないので、`K_n` より上の順序数は `K_n` より上の正則基数（`Ω_{K_n+1}` など）への `Ψ` で作る。
  Jäger の系に頂上が無いのと同じ形で、項は全て `Λ = sup K_n` 未満。
* `Ξ_n(α) = min(M^α ∩ (K_{n-1}, K_n))`。次数は `α ≤ K_n^+ = Ω_{K_n+1}` に限る。`Ξ_n(K_n^+)` は `K_n` 未満で
  （`M^{K_n^+}` は `K_n` で定常）、`α > K_n^+` なら `Ξ_n(α) = K_n` なので、それより先に広げても新しい順序数は
  出ない（`OCFRathjen/Complete.lean`）。

比較は `T(K)` の Lemma 4.14・4.19、Prop. 4.20・4.21 を、同じ「階」（`K_{n-1} ≤ x < K_n`）の項どうしに
使い、階が違えば階で比べる。`φ` が無いので、和でない項は全て加法的主数で、和は辞書式に比べる。

`cmp`・`inC`・`isNF` は停止性を証明した全域関数（測度は `8 ·（項の大きさの和）+ 段`）。
`cmp` が値の大小と一致すること（したがって標準形の上の整礎な全順序であること）は、`M^α` の定常性
（Rathjen の Thm. 4.12 の拡張、`StationaryHyp`）から `OCFRathjen/Correct.lean` で証明した。`isNF` は意味論版の
条件 `Good` と同値（`isNF_iff_good`）。`StationaryHyp` は `OCFRathjen/Reflection.lean` で弱コンパクト
基数の分割性から導き、全体を `cmpCorrect_of_weaklyCompact`（`OCFRathjen/Complete.lean`）にまとめた。

構成的な整列性の証明（`Classical.choice` も大基数の仮定も使わない）は `WF/` にあり、主定理は
`RTKA.wellFounded_isNF`（`WF/Wmax.lean`）。

標準形の値の集合はちょうど `C(Λ, 0)`（崩壊関数の閉包）で、各元の標準形は一意
（`OCFRathjen/Complete.lean` の `nfValue_iff_C_of_wc`。Rathjen の `T(K) = C(K_r, 0)` にあたる）。
-/

namespace RTKA

inductive Tm where
  | zero
  | one
  /-- `K_n`（`n ≥ 1`、弱コンパクト基数の増加列 `K_1 < K_2 < ⋯` の第 `n` 項。最小の弱コンパクト基数から
      数えた `n` 番目とは限らない） -/
  | K (n : Nat)
  /-- `a + b`（`a` は和でない 0 以外の項、`b ≠ 0`） -/
  | plus (a b : Tm)
  /-- `Ω_a` -/
  | Om (a : Tm)
  /-- `Ξ_n(a)` -/
  | Xi (n : Nat) (a : Tm)
  /-- `Ψ^ξ_π(a)` -/
  | Psi (xi pi a : Tm)
  deriving DecidableEq, Inhabited

open Tm

def summands : Tm → List Tm
  | zero => []
  | plus a b => a :: summands b
  | t => [t]

def ofSummands : List Tm → Tm
  | [] => zero
  | [a] => a
  | a :: rest => plus a (ofSummands rest)

def isPrincipal : Tm → Bool
  | zero | plus _ _ => false
  | _ => true

theorem summands_plus (a b : Tm) : summands (.plus a b) = a :: summands b := rfl

theorem summands_principal {t : Tm} (h : isPrincipal t = true) : summands t = [t] := by
  cases t <;> simp_all [isPrincipal, summands]

def isSucc (c : Tm) : Bool := (summands c).getLast? == some one

/-- 階：`K_{n-1} ≤ x < K_n` となる `n`（`K_0 = 0`）。`0` は `0` -/
def lev : Tm → Nat
  | zero => 0
  | one => 1
  | K n => n + 1
  | plus a _ => lev a
  | Om a => lev a
  | Xi n _ => n
  | Psi _ pi _ => lev pi

/-- `Ψ` の目標になる正則基数の項。`T(K)` の `Reg`（`K` 未満の非可算正則基数）と同じく `K_n` は含めない
    （Prop. 4.21 などの証明が「目標 `π` は `C(β, Ξ(β)) ∩ K` に入れば `Ξ(β)` 未満」を使うため）。 -/
def isRegTerm : Tm → Bool
  | Om c => isSucc c
  | Xi _ _ => true
  | Psi xi _ _ => xi != zero
  | _ => false

/-- 弱到達不能（`M^1` 以上）の項 -/
def isInacc : Tm → Bool
  | K _ | Xi _ _ => true
  | Psi xi _ _ => xi != zero
  | _ => false

/-- `Ω_X = X` となる項（Lemma 4.19 (i)(ii)） -/
def omegaFixed : Tm → Bool
  | K _ | Xi _ _ => true
  | Psi xi pi _ => xi != zero || isInacc pi
  | _ => false

/-- `m(π)` -/
def mOf : Tm → Option Tm
  | Om _ => some one
  | Xi _ a => some a
  | Psi xi _ _ => some xi
  | _ => none

/-- 項の大きさ（停止性の測度に使う） -/
def Tm.size : Tm → Nat
  | zero | one | K _ => 1
  | plus a b => a.size + b.size + 1
  | Om a => a.size + 1
  | Xi _ a => a.size + 1
  | Psi xi pi a => xi.size + pi.size + a.size + 1

def lsize : List Tm → Nat
  | [] => 0
  | t :: ts => t.size + lsize ts

theorem Tm.size_pos (t : Tm) : 0 < t.size := by
  cases t <;> simp only [Tm.size] <;> omega

theorem lsize_summands_le (t : Tm) : lsize (summands t) ≤ t.size := by
  induction t with
  | zero => simp [summands, lsize]
  | plus a b _ ihb => simp only [summands, lsize, Tm.size]; omega
  | _ => simp [summands, lsize]

/-! 比較と `C(γ, δ)` への所属。測度は `8 ·（項の大きさの和）+ 段`（同じ大きさなら段の低い関数を呼ぶ）。 -/

mutual

def cmp (a b : Tm) : Ordering :=
  cmpList (summands a) (summands b)
termination_by 8 * (a.size + b.size) + 3
decreasing_by
  have := lsize_summands_le a
  have := lsize_summands_le b
  omega

def cmpList : List Tm → List Tm → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
    match cmpP x y with
    | .eq => cmpList xs ys
    | o => o
termination_by xs ys => 8 * (lsize xs + lsize ys) + 2
decreasing_by
  all_goals
    simp only [lsize]
    have := Tm.size_pos x
    have := Tm.size_pos y
    omega

/-- 和でない 0 以外の項どうしの比較 -/
def cmpP (x y : Tm) : Ordering :=
  if lev x < lev y then .lt
  else if lev y < lev x then .gt
  else
    match x, y with
    | one, one => .eq
    | one, _ => .lt
    | _, one => .gt
    -- 同じ階の `K` は `K_{n-1}` だけで、その階の他の項より小さい（`Ω_{K_{n-1}} = K_{n-1}` は除く）
    | K _, K _ => .eq
    | K m, Om b => if b == K m then .eq else .lt
    | Om b, K m => if b == K m then .eq else .gt
    | K _, _ => .lt
    | _, K _ => .gt
    | Om a, Om b => cmp a b
    | Om a, y => cmpOmX a y
    | x, Om b => (cmpOmX b x).swap
    | Xi n a, Xi m b =>
      if a == b then .eq else if xiLtXi (Xi n a) (Xi m b) then .lt else .gt
    | Psi xi pi a, Xi m b => if psiLtXi (Psi xi pi a) (Xi m b) then .lt else .gt
    | Xi m b, Psi xi pi a => if psiLtXi (Psi xi pi a) (Xi m b) then .gt else .lt
    | Psi xi pi a, Psi sg ka b => cmpPsi (Psi xi pi a) (Psi sg ka b)
    | _, _ => .eq
termination_by 8 * (x.size + y.size) + 1
decreasing_by all_goals ((try simp only [Tm.size]); omega)

/-- `Ω_a` と同じ階の `X`（`Ξ` または `Ψ`）の比較（Lemma 4.19） -/
def cmpOmX (a X : Tm) : Ordering :=
  if omegaFixed X then cmp a X
  else
    match X with
    -- `Ψ^0_{Ω_c}(β)`、`c = ζ + 1`：`Ω_ζ < X < Ω_c`
    | Psi _ (Om c) _ => if cmp a c == .lt then .lt else .gt
    | _ => .gt
termination_by 8 * (a.size + X.size) + 4
decreasing_by all_goals ((try simp only [Tm.size]); omega)

/-- Lemma 4.14：同じ階の `Ξ_n(α) < Ξ_n(β)` -/
def xiLtXi (x y : Tm) : Bool :=
  match x, y with
  | Xi n a, Xi m b =>
    (cmp a b == .lt && inC a b (Xi m b)) || (cmp b a == .lt && !inC b a (Xi n a))
  | _, _ => false
termination_by 8 * (x.size + y.size)
decreasing_by all_goals ((try simp only [Tm.size]); omega)

/-- Prop. 4.21：同じ階の `Ψ^ξ_π(α) < Ξ_n(β)` -/
def psiLtXi (x y : Tm) : Bool :=
  match x, y with
  | Psi xi pi a, Xi m b =>
    cmp pi (Xi m b) != .gt || (cmp b a == .lt && !inC b a (Psi xi pi a))
  | _, _ => false
termination_by 8 * (x.size + y.size)
decreasing_by all_goals ((try simp only [Tm.size]); omega)

/-- 同じ階の `Ψ` どうしの比較（Prop. 4.17, 4.20） -/
def cmpPsi (x y : Tm) : Ordering :=
  match x, y with
  | Psi xi pi a, Psi sg ka b =>
    let x := Psi xi pi a
    let y := Psi sg ka b
    if x == y then .eq
    else if cmp y pi != .lt then .lt
    else if cmp x ka != .lt then .gt
    else
      let c1 := cmp a b == .lt && inC a b y && inC xi b y && inC pi b y && cmp x ka == .lt
      let c2 := cmp b a != .gt && !(inC b a x && inC sg a x && inC ka a x)
      let c3 := cmp a b == .eq && ka == pi && cmp xi sg == .lt && inC xi b y
      let c4 := cmp sg xi == .lt && !inC sg xi x
      if c1 || c2 || c3 || c4 then .lt else .gt
  | _, _ => .eq
termination_by 8 * (x.size + y.size)
decreasing_by all_goals ((try simp only [Tm.size]); omega)

/-- `α ∈ C(γ, δ)`（Lemma 5.4：`K_δ(α)` の元が全て `γ` 未満、を `α` の構造に沿って判定する） -/
def inC (a g d : Tm) : Bool :=
  match a with
  | zero | one | K _ => true
  | plus x y => inC x g d && inC y g d
  | Om x => inC x g d
  | Xi n b => cmp (Xi n b) d == .lt || (inC b g d && cmp b g == .lt)
  | Psi sg ka b =>
    cmp (Psi sg ka b) d == .lt ||
      (inC ka g d && inC sg g d && inC b g d && cmp b g == .lt)
termination_by 8 * (a.size + max g.size d.size) + 5
decreasing_by all_goals ((try simp only [Tm.size]); omega)

end

def lt (a b : Tm) : Bool := cmp a b == .lt

/-- `K_n^+ = Ω_{K_n + 1}` -/
def succK (n : Nat) : Tm := Om (plus (K n) one)

/-- 標準形（Def. 5.1 の加法版） -/
def isNF (t : Tm) : Bool :=
  match t with
  | zero | one => true
  | K n => n ≥ 1
  | plus a b =>
    isPrincipal a && b != zero && isNF a && isNF b &&
      (match summands b with
       | h :: _ => cmp h a != .gt
       | [] => false)
  | Om a => isNF a && a != zero && lt a t
  | Xi n a => n ≥ 1 && isNF a && a != zero && cmp a (succK n) != .gt && inC a a (K n)
  | Psi xi pi a =>
    isNF xi && isNF pi && isNF a && isRegTerm pi && cmp xi a != .gt &&
      inC a a pi && inC xi a pi && inC pi a pi &&
      (match mOf pi with
       | some m => lt xi m && inC xi m pi
       | none => false)

partial def Tm.fmt : Tm → String
  | zero => "0"
  | one => "1"
  | K n => s!"K{n}"
  | plus a b => s!"{a.fmt}+{b.fmt}"
  | Om a => s!"Ω_{fmtArg a}"
  | Xi n a => s!"Ξ{n}({a.fmt})"
  | Psi xi pi a => s!"Ψ^{fmtArg xi}_{fmtArg pi}({a.fmt})"
where
  fmtArg (t : Tm) : String :=
    match t with
    | plus .. => s!"({t.fmt})"
    | _ => t.fmt

instance : Repr Tm where
  reprPrec t _ := t.fmt

end RTKA
