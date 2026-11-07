import Compact.FS.CLem

/-! 基本列の定義。

項 `t` の共終数 `dom t` と基本列 `fundNat t n`（共終数 `ω`）・`fundBig t ξ`（共終数が正則項 `σ`）。

* 和は最後の加数で決まる。正則項 `σ` は `σ[ξ] = base σ ⊕ ξ`。`Ω_c`（`c` 極限）は `Ω_{c[ξ]+1}`。
* 崩壊 `Ψ^0_π(X)` は「種より上の `C(X, ·) ∩ π` の最小の閉包点」で、その列の記述（`SeqD`）を `cseq` が決める。
  - 後者 `X = X' + 1`：Mahlo 添字の上限 `μ` について、定数の種 `Ψ^{μ-1}_π(X')`、変数部分があれば
    Mahlo 添字への挿入、なければ引数への挿入（`mahloSeq`）。引数の下限で塞がる（底）なら目標の族の閉包
    （`famSeq`：`Ξ_m(q)` なら仮想的な `K_m` への崩壊 `mahloVK`、`Ψ^ζ_κ(γ)` なら κ への崩壊で上限 ζ）。
  - 極限 `X`：最後の加数の近似。前線の最大の節点を種とし、近似が種を越えなければ種を挿入する（`limitSeq`）。
* `app τ g pre R r P c`：`g(pre ⊕ (c, P, R[ν]))`（`combine`）。`R` の共終数が `τ` 以上の正則項 `σ` なら対角化
  （添字 `gam`）。種を外に足す型・K の対角化（`canonK`）では添字は正準な塔で、降下列の背骨に乗る。
  ψ・Mahlo 型の生成（`seedOut`）では、目標そのものへの対角化でも 0 番目の近似に種を自然な和で足す
  （`R[0] # P`）。有効性の調整 `c` は必要な最短のもの（`adjC`）。素の近似の 0 番目がちょうど種なら一つずらす
  （`shift`）。
* 列は種を真に越えて始まる：種の倍数は `p·2` から（`famSeq`）、Ω の塔は 1 段目から（`SeqD.nat`）。
  これで `t` の真の部分項で `t` 未満のものは全て `t[n]` 未満になる（隙間）。
* 梯子（`t[n]` が `t[n+1]` の降下列に現れること）を Bachmann 性の必要条件として、各規則を合わせている。
* 比較 `cmp` は使うが、項の総当たりはしない。

計算の仕組み：列の記述は部分項の列の記述を中に持つ（`app` の `r` は `R` の記述）。`info` が項を下から一度だけ
たどって全ての節点の記述を作るので、部分項の列を作り直すことはない。`t[n]` の計算は記述の木を下るだけ。 -/

namespace RTKA.Fund

open Tm

/-- 対角化の生成関数 -/
inductive Gen where
  | psi0 (π : Tm)
  | xi (m : Nat)
  /-- `z ↦ Ψ^z_κ(γ)` -/
  | idx (κ γ : Tm)
  /-- `δ ↦ Ψ^ζ_π(δ)`（Mahlo 添字に種 ζ を持つ崩壊） -/
  | mahlo (ζ π : Tm)

def Gen.ap : Gen → Tm → Tm
  | .psi0 π, δ => Psi zero π δ
  | .xi m, δ => Xi m δ
  | .idx κ γ, z => Psi z κ γ
  | .mahlo ζ π, δ => Psi ζ π δ

/-- 引数に下限のある崩壊の目標 -/
def Gen.tgt? : Gen → Option Tm
  | .psi0 π => some π
  | .mahlo _ π => some π
  | _ => none

/-- 列の記述。部分項 `R` の列は記述 `r` として中に持つ -/
inductive SeqD where
  /-- 列なし（`0`） -/
  | none
  /-- 後者 -/
  | one
  /-- 正則項・`Ψ^ζ_π(X)`（`ζ ≠ 0`）：共終数 `σ`、`[ξ] = b ⊕ ξ` -/
  | reg (σ b : Tm)
  /-- `a + s` -/
  | add (a : Tm) (s : SeqD)
  /-- `Ω_c`（`c` 極限）：`[ξ] = Ω_{c[ξ]+1}` -/
  | om (s : SeqD)
  | mul (B : Tm) (k : Nat)
  | tower (G : Tm)
  /-- `g(pre ⊕ (c, P, R[ν]))`、`r` は `R` の列の記述、`τ` は値の上限（共終数の判定） -/
  | app (τ : Tm) (g : Gen) (pre : List Tm) (R : Tm) (r : SeqD) (P c : Tm)
  /-- 列を一つずらす（`[n] = s[n+1]`。素の近似の 0 番目がちょうど種になるときに使う） -/
  | shift (s : SeqD)
  deriving Inhabited

/-- 加数とその列の記述の並び -/
abbrev DL := List (Tm × SeqD)

/-- 目標の族の記述（`famSeq` が族をたどるのに使う）：`Ξ_m(q)` は `q` の加数、`Ψ^ζ_κ(γ)` は `ζ`・`γ` の加数と `κ` の族 -/
inductive Fam where
  | om
  | xi (m : Nat) (q : Tm) (qs : DL)
  | psi (ζ : Tm) (ζs : DL) (κ : Tm) (κf : Fam) (γ : Tm) (γs : DL)
  | none

/-- Mahlo 添字の上限の加数 -/
def Fam.mdl : Fam → DL
  | .xi _ _ qs => qs
  | .psi _ ζs _ _ _ _ => ζs
  | _ => [(one, .one)]

def lastT (l : DL) : Tm := (l.getLast?.map Prod.fst).getD zero
def lastS (l : DL) : SeqD := (l.getLast?.map Prod.snd).getD .none
def preT (l : DL) : List Tm := l.dropLast.map Prod.fst

/-- Mahlo 添字の上限 -/
def mOfT (π : Tm) : Tm := (mOf π).getD one

/-- 種 `p` を Mahlo 添字に持てるか -/
def idxOK (τ p : Tm) : Bool := ltB p (mOfT τ) && inC p (mOfT τ) τ

def maxO (P : Option Tm) (x : Tm) : Tm :=
  match P with
  | none => x
  | some p => if ltB p x then x else p

def maxOpt (P Q : Option Tm) : Option Tm :=
  match P, Q with
  | none, q => q
  | p, none => p
  | some p, some q => some (if ltB p q then q else p)

/-- `th` より大きい最後の加数で分ける -/
def splitGtD (th : Tm) (ys : DL) : Option (List Tm × Tm × SeqD) :=
  match (ys.takeWhile (fun s => ltB th s.1)).getLast? with
  | none => none
  | some (R, r) => some ((ys.takeWhile (fun s => ltB th s.1)).dropLast.map Prod.fst, R, r)

/-- `τ` 以上の最後の加数で分ける -/
def splitPosD (τ : Tm) (ys : DL) : Option (List Tm × Tm × SeqD) :=
  match (ys.takeWhile (fun s => leB τ s.1)).getLast? with
  | none => none
  | some (R, r) => some ((ys.takeWhile (fun s => leB τ s.1)).dropLast.map Prod.fst, R, r)

/-- K_m の対角化で、近似が K_m^+ を越えうる（仮想的な崩壊 `virtK` と `# P` の旧方式） -/
def kOld (m : Nat) (pre : List Tm) (R : Tm) : Bool := leB (succK m) (oadd (ofSummands pre) R)

/-- 対角化で種を外に足すか（添字は正準な塔）。σ が目標そのもの（生成関数の目標。族の閉包では値の上限 τ と違う）・
    Ξ の崩壊（K）では種を中に入れる -/
def outsideMode (τ σ : Tm) (g : Gen) (pre : List Tm) (R : Tm) : Bool :=
  match σ, g with
  | K m, .psi0 _ => kOld m pre R
  | K m, .mahlo _ _ => kOld m pre R
  | K _, _ => false
  | _, _ => if σ = g.tgt?.getD τ then false else true

/-- Ξ_m で閉じた点（それ未満の ξ の `Ξ_m(ξ)` は全てそれ未満）：`Ξ_m(w)`（`w ≥ K_m`）と、その族を目標に持つ崩壊 -/
def closedPt (m : Nat) : Tm → Bool
  | Xi m' w => m' == m && leB (K m) w
  | Psi _ ρ _ => closedPt m ρ
  | _ => false

/-- `x` が `e` の中に、`x` 以上の節点だけを通って現れる（`d ≤ x` の `C(g, d)` に `e` が入れば `x` も入る） -/
def selfVis (x : Tm) : Tm → Bool
  | plus a b => selfVis x a || selfVis x b
  | Om a => selfVis x a
  | Xi m a => Xi m a == x || (leB x (Xi m a) && selfVis x a)
  | Psi s p a =>
    Psi s p a == x || (leB x (Psi s p a) && (selfVis x s || selfVis x p || selfVis x a))
  | _ => false

/-- `t` の中の、値が `ub` 以下で `cl` を満たす節点のうち、`ub` の中で見えるものの最大のもの -/
def maxCl (cl : Tm → Bool) (ub : Tm) : Tm → Option Tm
  | plus a b => maxOpt (maxCl cl ub a) (maxCl cl ub b)
  | Om a => maxCl cl ub a
  | Xi m' a =>
    maxOpt (if cl (Xi m' a) && leB (Xi m' a) ub && selfVis (Xi m' a) ub then some (Xi m' a) else none)
      (maxCl cl ub a)
  | Psi s p a =>
    maxOpt (if cl (Psi s p a) && leB (Psi s p a) ub && selfVis (Psi s p a) ub then some (Psi s p a) else none)
      (maxOpt (maxCl cl ub s) (maxOpt (maxCl cl ub p) (maxCl cl ub a)))
  | _ => none

/-- `t` の中の Ξ_m で閉じた節点の最大のもの。`Ξ_m(z)` の降下列は z を通るので、塔の始点にできる -/
def maxXiClosed (m : Nat) (ub : Tm) : Tm → Option Tm := maxCl (closedPt m) ub

/-- K の塔の始点：調整 `c`・種 `P` の中の Ξ_m で閉じた点の最大のもの -/
def kStart (m : Nat) (c P : Tm) : Tm := (maxOpt (maxXiClosed m c c) (maxXiClosed m P P)).getD zero

/-- `σ` への崩壊の塔（上端 `T`）で閉じた点：`Ψ^z_σ(w)`（`w ≥ T`）と、その族を目標に持つ崩壊 -/
def closedS (σ T : Tm) : Tm → Bool
  | Psi _ ρ w => (ρ == σ && leB T w) || closedS σ T ρ
  | _ => false

/-- 種を外に足す型の塔の始点：調整 `c`・種 `P` の中の閉じた点の最大のもの -/
def sStart (σ T c P : Tm) : Tm :=
  (maxOpt (maxCl (closedS σ T) c c) (maxCl (closedS σ T) P P)).getD zero

/-- 目標 `τ` の前線の中の、`cl` を満たす点の最大のもの -/
def frCl (cl : Tm → Bool) (τ : Tm) : Tm :=
  (((frB τ τ).map (fun e => maxCl cl e e)).foldr maxOpt none).getD zero

/-- ψ への K の対角化（近似が K_m⁺ 未満）：添字は正準な Ξ の塔 `γ_{k+1} = Ξ_m(pre ⊕ R[γ_k])`
    （種も調整も入れない。降下列の背骨に乗る）。種は外から自然な和で足す -/
def canonK (σ : Tm) (g : Gen) (pre : List Tm) (R : Tm) : Bool :=
  match σ, g with
  | K m, .psi0 _ => !kOld m pre R
  | K m, .mahlo _ _ => !kOld m pre R
  | _, _ => false

/-- ψ・Mahlo 型の生成。目標そのものへの対角化では、0 番目の近似に種を自然な和で足す（`R[0] # P`。
    1 番目以降の添字は値の帰還で既に種を含む） -/
def seedOut : Gen → Bool
  | .psi0 _ => true
  | .mahlo _ _ => true
  | _ => false

/-- 近似 `pre ⊕ (c, P, x)`。ψ への崩壊では有効性の調整 `c` を前に置く（`c + x`、吸収あり）。
    後ろの小さな加数は降下列に現れないため。それ以外（Ξ の底の `+1` など）は自然な和 -/
def combine (g : Gen) (pre : List Tm) (c P x : Tm) : Tm :=
  match g with
  | .psi0 _ => oadd (ofSummands pre) (nsum (oadd c x) P)
  | .mahlo _ _ => oadd (ofSummands pre) (nsum (oadd c x) P)
  | _ => oadd (ofSummands pre) (nsum c (nsum P x))

/-- 対角化での `σ` への崩壊（`k` は段の番号） -/
def col (σ δ : Tm) (k : Nat) : Tm :=
  match σ with
  | K m =>
    if δ = zero then Xi m one
    else if leB δ (succK m) then Xi m δ
    else virtK m k
  | _ => if validR σ δ then Psi zero σ δ else base σ

/-! ### 列の記述の評価（記述の木を下るだけ） -/

/-- 列の記述の共終数 -/
def SeqD.dom : SeqD → Cof Tm
  | .none => .zero
  | .shift s => s.dom
  | .one => .one
  | .reg σ _ => .big σ
  | .add _ s => s.dom
  | .om s => s.dom
  | .app τ _ _ _ r _ _ =>
    match r.dom with
    | .big σ => if ltB σ τ then .big σ else .omega
    | _ => .omega
  | _ => .omega

/-- 列の記述の、添字 `ξ`（正則項未満）の項 -/
def SeqD.big : SeqD → Tm → Tm
  | .shift s, ξ => s.big ξ
  | .reg _ b, ξ => oadd b ξ
  | .add a s, ξ => oadd a (s.big ξ)
  | .om s, ξ => Om (sc (s.big ξ))
  | .app _ g pre _ r P c, ξ => g.ap (combine g pre c P (r.big ξ))
  | _, _ => zero

/-- 対角化の近似の引数 -/
def argOf (τ σ : Tm) (g : Gen) (pre : List Tm) (R : Tm) (r : SeqD) (c P γ : Tm) : Tm :=
  if canonK σ g pre R then combine g pre c P (r.big γ)
  else if outsideMode τ σ g pre R then combine g pre c P (r.big γ)
  else combine g pre c (if seedOut g && γ == zero then P else zero) (r.big γ)

/-- 対角化の添字。正準な塔（`canonK`・種を外に足す型）では種によらない塔、
    そうでなければ種を始点に入れ、値の帰還（`col` と値の大きい方）で進める -/
def gam (τ σ : Tm) (g : Gen) (pre : List Tm) (R : Tm) (r : SeqD) (c P : Tm) : Nat → Tm
  | 0 =>
    if canonK σ g pre R then (match σ with | K m => kStart m c P | _ => zero)
    else if outsideMode τ σ g pre R then
      (match σ with
       | K _ => zero
       | _ => if seedOut g then sStart σ (oadd (ofSummands pre) R) c P else zero)
    else (match σ with | K _ => P | _ => if seedOut g then zero else P)
  | k + 1 =>
    let γ := gam τ σ g pre R r c P k
    if canonK σ g pre R then col σ (oadd (ofSummands pre) (r.big γ)) k
    else if outsideMode τ σ g pre R then
      match σ with
      | K _ => col σ (argOf τ σ g pre R r c P γ) k
      | _ => col σ (oadd (ofSummands pre) (r.big γ)) k
    else
      let A := argOf τ σ g pre R r c P γ
      let cl := col σ A k
      if ltB cl (g.ap A) && ltB (g.ap A) σ then g.ap A else cl

/-- 列の記述の `n` 番目 -/
def SeqD.nat : SeqD → Nat → Tm
  | .shift s, n => s.nat (n + 1)
  | .add a s, n => oadd a (s.nat n)
  | .om s, n => Om (sc (s.nat n))
  | .mul B k, n => mulNat B (n + k)
  | .tower G, n => RTKA.Fund.tower G (n + 1)
  | .app τ g pre R r P c, n =>
    match r.dom with
    | .big σ => if ltB σ τ then zero else g.ap (argOf τ σ g pre R r c P (gam τ σ g pre R r c P n))
    | _ => g.ap (combine g pre c P (r.nat n))
  | _, _ => zero

/-- 列の 0 番目 -/
def SeqD.first (s : SeqD) : Tm :=
  match s.dom with
  | .big _ => s.big zero
  | _ => s.nat 0

/-! ### 崩壊の列の記述 -/

/-- 有効性の調整：`r` の残り `rt` の、最初の近似を有効にする最短の先頭部分（なければ `rt + 1`）。
    降下列の途中の項が自分で計算する調整と一致させるため、必要以上に足さない -/
def adjC (τ : Tm) (approx : Tm → Tm) (rt : Tm) : Tm :=
  match ((List.range ((summands rt).length + 1)).map (fun k => ofSummands ((summands rt).take k))).find?
      (fun c => validR τ (approx c)) with
  | some c => c
  | none => sc rt

/-- K の対角化（`canonK`）で、調整なしの 1 番目の近似 `pre ⊕ (K_m[γ₁] # P)`（`γ₁ = col K_m (pre ⊕ K_m[0])`）が
    有効か。有効なら調整 `c` は塔の元に吸収されないので、調整を入れずに列を一つずらす -/
def canonSecondValid (τ ceil : Tm) (g : Gen) (pre : List Tm) (R : Tm) (r : SeqD) (P k : Tm) : Bool :=
  match r.dom with
  | .big (K m) =>
    !ltB (K m) ceil && canonK (K m) g pre R &&
      validR τ (combine g pre k P (r.big (col (K m) (oadd (ofSummands pre) (r.big (kStart m k P))) 0)))
  | _ => false

/-- 対角化の調整：目標の前線の中の、塔で閉じた点の最大のもの。目標の前線は `t` 未満で、
    `C(X, t)` の閉包はそこから始まる（塔が目標を越えられるように） -/
def kAdj (τ ceil : Tm) (g : Gen) (pre : List Tm) (R : Tm) (r : SeqD) : Tm :=
  match r.dom with
  | .big (K m) =>
    if !ltB (K m) ceil && canonK (K m) g pre R then frCl (closedPt m) τ else zero
  | .big σ =>
    if !ltB σ ceil && outsideMode ceil σ g pre R then
      frCl (closedS σ (oadd (ofSummands pre) R)) τ
    else zero
  | _ => zero

/-- `app` を作る（引数の下限で塞がるなら `none`） -/
def mkApp (ceil : Tm) (g : Gen) (pre : List Tm) (R : Tm) (r : SeqD) (P c : Tm) : Option SeqD :=
  if P ≠ zero ∧ ltB P R = false then none
  else
    match g.tgt? with
    | some τ =>
      let k := kAdj τ ceil g pre R r
      match tailRaw (argR? τ) pre with
      | none => some (.app ceil g pre R r P k)
      | some rt =>
        if leB R rt then none
        else
          let x0 := r.first
          let approx := fun c => combine g pre c P x0
          if validR τ (approx k) then some (.app ceil g pre R r P k)
          else if canonSecondValid τ ceil g pre R r P k then some (.shift (.app ceil g pre R r P k))
          else some (.app ceil g pre R r P (oadd (adjC τ (fun c => approx (oadd c k)) rt) k))
    | _ => some (.app ceil g pre R r P c)

/-- 仮想的な `K_m` への崩壊（`Ξ_m(ξ)`、`ξ < q`）の閉包（`qs` は `q` の加数） -/
def mahloVK (m : Nat) (q : Tm) (qs : DL) (ceil : Tm) (P : Option Tm) : SeqD :=
  if q = one then .tower (maxO P (floorLev m))
  else if isSucc q then
    match splitPosD ceil qs.dropLast with
    | some (pre, R, r) =>
      match mkApp ceil (.xi m) pre R r (maxO P (Xi m (pred q))) zero with
      | some s => s
      | none => .tower (maxO P (Xi m (pred q)))
    | none => .tower (maxO P (Xi m (pred q)))
  else
    let s0 : SeqD := .app ceil (.xi m) (preT qs) (lastT qs) (lastS qs) zero one
    match P with
    | none => s0
    | some p =>
      if ltB p s0.first then s0
      else if s0.first = p then .app ceil (.xi m) (preT qs) (lastT qs) (.shift (lastS qs)) zero one
      else
        match splitGtD p qs with
        | some (pre, R, r) =>
          match mkApp ceil (.xi m) pre R r p zero with
          | some s => s
          | none => .tower p
        | none => .tower p

mutual

/-- 目標の族の、種 `P` より上の閉包（値は `ceil` 未満） -/
def famSeq (πf : Fam) (ceil : Tm) (P : Option Tm) : SeqD :=
  match πf with
  | .om =>
    match P with
    | some p => .mul p 2
    | none => .none
  | .xi m q qs => mahloVK m q qs ceil P
  | .psi ζ ζs κ κf γ γs => mahloSeq κ κf ceil γ γs ζ ζs P
  | .none => .none
termination_by (sizeOf πf, 0)
decreasing_by all_goals (apply Prod.Lex.left; simp only [Fam.psi.sizeOf_spec]; omega)

/-- 「`Ψ^0_τ(Y'+1)`、Mahlo 添字の上限 `μ`」の閉包（種 `P`、値は `ceil` 未満。`ys`・`ms` は `Y'`・`μ` の加数） -/
def mahloSeq (τ : Tm) (τf : Fam) (ceil Y' : Tm) (ys : DL) (μ : Tm) (ms : DL) (P : Option Tm) : SeqD :=
  if μ = one then insertAtM τ τf ceil (maxO P (Psi zero τ Y')) Y' ys
  else if isSucc μ then
    match splitPosD ceil ms.dropLast with
    | some (pre, R, r) =>
      match mkApp ceil (.idx τ Y') pre R r (maxO P (Psi (pred μ) τ Y')) zero with
      | some s => s
      | none => insertAtM τ τf ceil (maxO P (Psi (pred μ) τ Y')) Y' ys
    | none => insertAtM τ τf ceil (maxO P (Psi (pred μ) τ Y')) Y' ys
  else
    let s0 := (mkApp ceil (.idx τ Y') (preT ms) (lastT ms) (lastS ms) zero zero).getD .none
    match P with
    | none => s0
    | some p =>
      if ltB p s0.first then s0
      else if s0.first = p then
        (mkApp ceil (.idx τ Y') (preT ms) (lastT ms) (.shift (lastS ms)) zero zero).getD .none
      else
        match splitGtD p ms with
        | some (pre, R, r) =>
          match mkApp ceil (.idx τ Y') pre R r p zero with
          | some s => s
          | none => insertAtM τ τf ceil p Y' ys
        | none => insertAtM τ τf ceil p Y' ys
termination_by (sizeOf τf, 3)
decreasing_by all_goals (apply Prod.Lex.right; omega)

/-- 後者の崩壊 `Ψ⁰_τ(Y'+1)`（Mahlo の上限つき）への種 `p` の挿入。塞がるときは `deadSeqM` -/
def insertAtM (τ : Tm) (τf : Fam) (ceil p Y' : Tm) (ys : DL) : SeqD :=
  match splitGtD p ys with
  | some (pre, R, r) =>
    if !ltB p (lastT ys) && idxOK τ p then deadSeqM τ τf ceil p Y' ys
    else
      match mkApp ceil (.psi0 τ) pre R r p zero with
      | some s => s
      | none => deadSeqM τ τf ceil p Y' ys
  | none => famSeq τf ceil (some p)
termination_by (sizeOf τf, 2)
decreasing_by all_goals (apply Prod.Lex.right; omega)

/-- 塞がった挿入（引数は `Y'` 以下、`Y'` では添字が p を持てない）：`Y'` が極限なら `Ψ^p_τ(Y'[n])`、
    後者 `Y'' + 1` なら `Ψ^{m(τ)[n] # p}_τ(Y'')`（`τ ≤ m(τ)` なので添字の閉包は必ず作れる）。添字が p を持てなければ族の閉包 -/
def deadSeqM (τ : Tm) (τf : Fam) (ceil p Y' : Tm) (ys : DL) : SeqD :=
  if idxOK τ p then
    match (lastS ys).dom with
    | .one =>
      if leB τ (mOfT τ) && leB τ (pred Y') && validR τ (pred Y') then
        match splitGtD p τf.mdl with
        | some (pre, R, r) => .app ceil (.idx τ (pred Y')) pre R r p zero
        | none => famSeq τf ceil (some p)
      else famSeq τf ceil (some p)
    | _ =>
      match mkApp ceil (.mahlo p τ) (preT ys) (lastT ys) (lastS ys) zero zero with
      | some s => s
      | none => famSeq τf ceil (some p)
  else famSeq τf ceil (some p)
termination_by (sizeOf τf, 1)
decreasing_by all_goals (apply Prod.Lex.right; omega)

end

/-- 挿入が引数の下限で塞がるとき：Mahlo 添字に p を持つ崩壊 `Ψ^p_τ(Y[n])` が p より上の閉包を作る
    （引数が第一の鍵）。添字が p を持てなければ（`p ≥ m(τ)`）族の閉包 -/
def deadSeq (τ : Tm) (τf : Fam) (ceil p : Tm) (ys : DL) : SeqD :=
  if idxOK τ p then
    match mkApp ceil (.mahlo p τ) (preT ys) (lastT ys) (lastS ys) zero zero with
    | some s => s
    | none => famSeq τf ceil (some p)
  else famSeq τf ceil (some p)

/-- 極限の引数（加数 `ys`）への種 `p` の挿入。引数の下限で塞がるときは `deadSeq` -/
def insertAtL (τ : Tm) (τf : Fam) (ceil p : Tm) (ys : DL) : SeqD :=
  match splitGtD p ys with
  | some (pre, R, r) =>
    if !ltB p (lastT ys) && idxOK τ p then deadSeq τ τf ceil p ys
    else
      match mkApp ceil (.psi0 τ) pre R r p zero with
      | some s => s
      | none => deadSeq τ τf ceil p ys
  | none => famSeq τf ceil (some p)

/-- 極限 `X`（加数 `xs`）の崩壊の列 -/
def limitSeq (τ : Tm) (τf : Fam) (ceil X : Tm) (xs : DL) (P : Option Tm) : SeqD :=
  let plain := (mkApp ceil (.psi0 τ) (preT xs) (lastT xs) (lastS xs) zero zero).getD .none
  match maxOpt P (maxL (frB τ X)) with
  | none => plain
  | some p =>
    if ltB p plain.first then plain
    else if plain.first = p then
      (mkApp ceil (.psi0 τ) (preT xs) (lastT xs) (.shift (lastS xs)) zero zero).getD .none
    else insertAtL τ τf ceil p xs

/-- 崩壊 `Ψ^0_π(X)` の列（`πf` は `π` の族、`xs` は `X` の加数） -/
def cseq (π : Tm) (πf : Fam) (X : Tm) (xs : DL) : SeqD :=
  if X = zero then
    match π with
    | Om c => .mul (if c = one then one else omHat (pred c)) 2
    | _ => .none
  else
    match (lastS xs).dom with
    | .one =>
      if validR π (pred X) = false then famSeq πf π (maxL (frB π π))
      else mahloSeq π πf π (pred X) xs.dropLast (mOfT π) πf.mdl none
    | _ => limitSeq π πf π X xs none

/-! ### 項の解析 -/

/-- 項の解析：自身の列の記述・加数ごとの記述・目標の族の記述 -/
structure Info where
  seq : SeqD
  sums : DL
  fam : Fam

/-- 項を下から一度だけたどり、全ての節点の列の記述を作る -/
def info : Tm → Info
  | zero => ⟨.none, [], .none⟩
  | one => ⟨.one, [(one, .one)], .none⟩
  | K m =>
    let s : SeqD := .reg (K m) (base (K m))
    ⟨s, [(K m, s)], .none⟩
  | plus a b =>
    let ia := info a
    let ib := info b
    ⟨.add a ib.seq, (a, ia.seq) :: ib.sums, .none⟩
  | Om c =>
    let s : SeqD := if isSucc c then .reg (Om c) (base (Om c)) else .om (info c).seq
    ⟨s, [(Om c, s)], .om⟩
  | Xi m q =>
    let iq := info q
    let s : SeqD := .reg (Xi m q) (base (Xi m q))
    ⟨s, [(Xi m q, s)], .xi m q iq.sums⟩
  | Psi ζ π X =>
    let iζ := info ζ
    let iπ := info π
    let iX := info X
    let s : SeqD := if ζ = zero then cseq π iπ.fam X iX.sums else .reg (Psi ζ π X) (base (Psi ζ π X))
    ⟨s, [(Psi ζ π X, s)], .psi ζ iζ.sums π iπ.fam X iX.sums⟩

/-- 共終数 -/
def dom (t : Tm) : Cof Tm := (info t).seq.dom

/-- 共終数が正則項の場合の基本列 -/
def fundBig (t ξ : Tm) : Tm := (info t).seq.big ξ

/-- 共終数が `ω` の場合の基本列 -/
def fundNat (t : Tm) (n : Nat) : Tm := (info t).seq.nat n

/-- 基本列 -/
def fund (t ξ : Tm) : Tm :=
  let s := (info t).seq
  match s.dom with
  | .zero => zero
  | .one => pred t
  | .omega => s.nat (natOf ξ)
  | .big σ => s.big (if ltB ξ σ then ξ else zero)

end RTKA.Fund
