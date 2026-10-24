import Compact.Additive

/-! 標準形の総当たり検査（`lake env lean Compact/WF/Test.lean` で実行。ライブラリには入れない）。

構文的な補題の主張を、証明する前に `#eval` で検査するための道具。`nfList k N` は大きさ `N` 以下の標準形
（`K`・`Ξ` の添字は `1` から `k`）。標準形の直下の部分項は標準形なので、候補は標準形の部分項からだけ作り、
`isNF` で絞る。各検査は反例の先頭を返す（空なら成り立つ）。 -/

namespace RTKA

open Tm

/-- 大きさ `N` 以下の標準形（添字 `≤ k`）を大きさごとに並べたもの -/
def nfUpTo (k N : Nat) : Array (List Tm) := Id.run do
  let mut arr : Array (List Tm) := #[[]]
  for n in [1:N+1] do
    let mut ts : List Tm := []
    if n == 1 then
      ts := [zero, one] ++ (List.range k).map (fun i => K (i + 1))
    for a in arr[n-1]! do
      ts := ts ++ [Om a] ++ (List.range k).map (fun i => Xi (i + 1) a)
    for i in [1:n-1] do
      for a in arr[i]! do
        for b in arr[n-1-i]! do
          ts := plus a b :: ts
    for i in [1:n-1] do
      for j in [1:n-1-i] do
        let l := n - 1 - i - j
        if l ≥ 1 then
          for xi in arr[i]! do
            for pi in arr[j]! do
              for a in arr[l]! do
                ts := Psi xi pi a :: ts
    arr := arr.push (ts.filter isNF)
  return arr

/-- 大きさ `N` 以下の標準形（添字 `≤ k`）の一覧 -/
def nfList (k N : Nat) : List Tm := (nfUpTo k N).toList.flatten

/-- 述語を満たさない最初の `n` 個 -/
def firstFails {α : Type} (n : Nat) (xs : List α) (p : α → Bool) : List α :=
  (xs.filter (fun x => !p x)).take n

def pairs (l : List Tm) : List (Tm × Tm) := l.flatMap (fun a => l.map (fun b => (a, b)))

/-- 推移性の反例：`a < b < c` で `a < c` でないもの（`b` を固定して前後を数える） -/
def transFails (l : List Tm) : List (Tm × Tm × Tm) := Id.run do
  let mut out := []
  for b in l do
    let below := l.filter (fun a => lt a b)
    let above := l.filter (fun c => lt b c)
    for a in below do
      for c in above do
        if !(lt a c) && out.length < 5 then out := (a, b, c) :: out
  return out

end RTKA

open RTKA

-- 反射性（全ての項）
#eval firstFails 3 (nfList 2 7) (fun t => cmp t t == .eq)
-- 反対称性・相等（標準形、大きさ ≤ 6）
#eval firstFails 3 (pairs (nfList 2 6)) (fun (a, b) => cmp b a == (cmp a b).swap)
#eval firstFails 3 (pairs (nfList 2 6)) (fun (a, b) => cmp a b != .eq || a == b)
-- 推移性（大きさ ≤ 5）
#eval transFails (nfList 2 5)
