import Compact.FS.Order
import Compact.FS.Memo

/-! 基本列の定義に使う補助の関数（和・自然な和・正則項の列の始点・前線など）。
基本列そのものは `Compact.FS.Seq` で定義する。比較 `cmp` は使うが、項の総当たりはしない。
`Compact.FS.Memo` を読み込むので、ここから先のコードでは `cmp`・`inC` はメモ化版で計算される。 -/

namespace RTKA.Fund

open Tm

def ltB (a b : Tm) : Bool := cmp a b == .lt
def leB (a b : Tm) : Bool := cmp a b != .gt

/-- 加数の列の併合（大きい順） -/
def merge : List Tm → List Tm → List Tm
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => if leB y x then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys
termination_by xs ys => xs.length + ys.length

/-- 自然な和 -/
def nsum (x y : Tm) : Tm := ofSummands (merge (summands x) (summands y))

/-- 順序数の和 -/
def oadd (x y : Tm) : Tm :=
  match summands y with
  | [] => x
  | h :: _ => ofSummands (((summands x).takeWhile (fun s => leB h s)) ++ summands y)

/-- `Ω_x`（`x = 0` なら `0`、`Ω` の不動点ならそれ自身） -/
def omHat (x : Tm) : Tm := if x = zero then zero else if isPrincipal x && omegaFixed x then x else Om x

def mulNat (x : Tm) (n : Nat) : Tm := ofSummands (List.replicate n x)

/-- 自然数の項 `1 + ⋯ + 1` なら個数、そうでなければ `0` -/
def natOf (ξ : Tm) : Nat := if (summands ξ).all (· == one) then (summands ξ).length else 0

def ofNatT (n : Nat) : Tm := mulNat one n

/-- 最後の加数を除く -/
def pred (a : Tm) : Tm := ofSummands (summands a).dropLast

/-- `a + 1` -/
def sc (a : Tm) : Tm := succT a

/-- 正則項の列の始点 -/
def base (σ : Tm) : Tm :=
  match σ with
  | Om _ => Psi zero σ zero
  | K n => if n ≤ 1 then zero else K (n - 1)
  | Xi _ q => Psi zero σ (sc q)
  | Psi _ _ γ => Psi zero σ (sc γ)
  | _ => zero

/-- 位 `l` の下端 `K_{l-1}` -/
def floorLev (l : Nat) : Tm := if l ≤ 1 then zero else K (l - 1)

/-- 目標の引数（`Ξ_m(q)` なら `q`、`Ψ^ζ_κ(γ)` なら `γ`） -/
def argR? (π : Tm) : Option Tm :=
  match π with
  | Xi _ q => some q
  | Psi _ _ γ => some γ
  | _ => none

/-- `Ψ^0_π(δ)` の引数の下限を満たすか -/
def validR (π δ : Tm) : Bool :=
  match argR? π with
  | some r => ltB r δ
  | none => true

/-- 前線（`Bool` 版） -/
def frB (R : Tm) : Tm → List Tm
  | plus a b => frB R a ++ frB R b
  | Om a => frB R a
  | Xi m a => if ltB (Xi m a) R then [Xi m a] else frB R a
  | Psi s p a => if ltB (Psi s p a) R then [Psi s p a] else frB R s ++ frB R p ++ frB R a
  | _ => []

def maxL : List Tm → Option Tm
  | [] => none
  | x :: xs =>
    match maxL xs with
    | none => some x
    | some y => if ltB x y then some y else some x

/-- `r` が `pre` で始まるなら、`r` の残り -/
def tailRaw (r? : Option Tm) (pre : List Tm) : Option Tm :=
  match r? with
  | none => none
  | some r =>
    if pre.length ≤ (summands r).length ∧ (summands r).take pre.length = pre
    then some (ofSummands ((summands r).drop pre.length)) else none

/-- `G` から始まる `Ω` の塔 -/
def tower (G : Tm) : Nat → Tm
  | 0 => G
  | k + 1 => Om (sc (tower G k))

/-- 仮想的な `K_m` への崩壊 `κ_m(K_m⁺ + 1)` の列の正準な塔：`g_0 = 0`、`g_{k+1} = Ψ⁰_{K_m⁺}(ψ₀ ⊕ g_k)`
    （`ψ₀ = Ψ⁰_{K_m⁺}(0)`） -/
def virtG (m : Nat) : Nat → Tm
  | 0 => zero
  | k + 1 => Psi zero (succK m) (oadd (Psi zero (succK m) zero) (virtG m k))

/-- `κ_m(K_m⁺ + 1)` の列：Ξ の族の閉包が `q = K_m⁺ + 1` で作る列と同じ形 `Ξ_m((ψ₀ ⊕ g_k) # Ξ_m(K_m⁺))` -/
def virtK (m k : Nat) : Tm :=
  Xi m (nsum (oadd (Psi zero (succK m) zero) (virtG m k)) (Xi m (succK m)))

end RTKA.Fund
