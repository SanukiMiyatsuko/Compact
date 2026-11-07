import Compact.Additive
import Std.Data.HashMap

/-! 比較 `cmp` と `C(γ, δ)` への所属 `inC` のメモ化版、およびそれが元の定義と一致することの証明。

`cmp`・`inC` は同じ部分項の組を何度も比べるので、定義どおりに計算すると入れ子の深さについて指数的な時間が
かかる（`Ψ` の比較 `cmpPsi` が `inC` を通して部分項と相手の項を比べ直すため）。メモ化版は計算した組の結果を
表に残し、各組を一度だけ計算する。表の鍵は、`cmp a b` には `Psi a b 0`、`inC a g d` には `Psi a g d` を使う。

`@[csimp]` により、このファイルを読み込んだ後にコンパイルされるコード（基本列など）では、`cmp`・`inC` の
呼び出しがメモ化版に置き換わる。論理上の定義は変わらないので、`cmp`・`inC` についての証明はそのまま使える。 -/

namespace RTKA

open Tm

deriving instance Hashable for Tm

/-- メモの表 -/
structure Memo where
  c : Std.HashMap Tm Ordering
  i : Std.HashMap Tm Bool

def Memo.empty : Memo := ⟨∅, ∅⟩

/-- 短絡評価の `&&`（表を受け渡す） -/
@[inline] def bAnd (x : Bool × Memo) (y : Memo → Bool × Memo) : Bool × Memo :=
  if x.1 then y x.2 else (false, x.2)

/-- 短絡評価の `||`（表を受け渡す） -/
@[inline] def bOr (x : Bool × Memo) (y : Memo → Bool × Memo) : Bool × Memo :=
  if x.1 then (true, x.2) else y x.2

/-- 比較の結果が `.lt` か -/
@[inline] def isLt (r : Ordering × Memo) : Bool × Memo := (r.1 == .lt, r.2)

mutual

def cmpF (a b : Tm) (m : Memo) : Ordering × Memo :=
  match m.c[Psi a b zero]? with
  | some o => (o, m)
  | none =>
    let r := cmpListF (summands a) (summands b) m
    (r.1, { r.2 with c := r.2.c.insert (Psi a b zero) r.1 })
termination_by 8 * (a.size + b.size) + 3
decreasing_by
  have := lsize_summands_le a
  have := lsize_summands_le b
  omega

def cmpListF : List Tm → List Tm → Memo → Ordering × Memo
  | [], [], m => (.eq, m)
  | [], _ :: _, m => (.lt, m)
  | _ :: _, [], m => (.gt, m)
  | x :: xs, y :: ys, m =>
    let r := cmpPF x y m
    match r.1 with
    | .eq => cmpListF xs ys r.2
    | o => (o, r.2)
termination_by xs ys _ => 8 * (lsize xs + lsize ys) + 2
decreasing_by
  all_goals
    simp only [lsize]
    have := Tm.size_pos x
    have := Tm.size_pos y
    omega

def cmpPF (x y : Tm) (m : Memo) : Ordering × Memo :=
  if lev x < lev y then (.lt, m)
  else if lev y < lev x then (.gt, m)
  else
    match x, y with
    | one, one => (.eq, m)
    | one, _ => (.lt, m)
    | _, one => (.gt, m)
    | K _, K _ => (.eq, m)
    | K k, Om b => (if b == K k then .eq else .lt, m)
    | Om b, K k => (if b == K k then .eq else .gt, m)
    | K _, _ => (.lt, m)
    | _, K _ => (.gt, m)
    | Om a, Om b => cmpF a b m
    | Om a, y => cmpOmXF a y m
    | x, Om b => let r := cmpOmXF b x m; (r.1.swap, r.2)
    | Xi n a, Xi k b =>
      if a == b then (.eq, m)
      else let r := xiLtXiF (Xi n a) (Xi k b) m; (if r.1 then .lt else .gt, r.2)
    | Psi xi pi a, Xi k b => let r := psiLtXiF (Psi xi pi a) (Xi k b) m; (if r.1 then .lt else .gt, r.2)
    | Xi k b, Psi xi pi a => let r := psiLtXiF (Psi xi pi a) (Xi k b) m; (if r.1 then .gt else .lt, r.2)
    | Psi xi pi a, Psi sg ka b => cmpPsiF (Psi xi pi a) (Psi sg ka b) m
    | _, _ => (.eq, m)
termination_by 8 * (x.size + y.size) + 1
decreasing_by all_goals ((try simp only [Tm.size]); omega)

def cmpOmXF (a X : Tm) (m : Memo) : Ordering × Memo :=
  if omegaFixed X then cmpF a X m
  else
    match X with
    | Psi _ (Om c) _ => let r := cmpF a c m; (if r.1 == .lt then .lt else .gt, r.2)
    | _ => (.gt, m)
termination_by 8 * (a.size + X.size) + 4
decreasing_by all_goals ((try simp only [Tm.size]); omega)

def xiLtXiF (x y : Tm) (m : Memo) : Bool × Memo :=
  match x, y with
  | Xi n a, Xi k b =>
    bOr (bAnd (isLt (cmpF a b m)) (fun m => inCF a b (Xi k b) m))
      (fun m => bAnd (isLt (cmpF b a m)) (fun m => let r := inCF b a (Xi n a) m; (!r.1, r.2)))
  | _, _ => (false, m)
termination_by 8 * (x.size + y.size)
decreasing_by all_goals ((try simp only [Tm.size]); omega)

def psiLtXiF (x y : Tm) (m : Memo) : Bool × Memo :=
  match x, y with
  | Psi xi pi a, Xi k b =>
    bOr (let r := cmpF pi (Xi k b) m; (r.1 != .gt, r.2))
      (fun m => bAnd (isLt (cmpF b a m)) (fun m => let r := inCF b a (Psi xi pi a) m; (!r.1, r.2)))
  | _, _ => (false, m)
termination_by 8 * (x.size + y.size)
decreasing_by all_goals ((try simp only [Tm.size]); omega)

def cmpPsiF (x y : Tm) (m : Memo) : Ordering × Memo :=
  match x, y with
  | Psi xi pi a, Psi sg ka b =>
    if Psi xi pi a == Psi sg ka b then (.eq, m)
    else
      let r1 := cmpF (Psi sg ka b) pi m
      if r1.1 != .lt then (.lt, r1.2)
      else
        let r2 := cmpF (Psi xi pi a) ka r1.2
        if r2.1 != .lt then (.gt, r2.2)
        else
          let r := bOr
            (bAnd (isLt (cmpF a b r2.2)) (fun m => bAnd (inCF a b (Psi sg ka b) m)
              (fun m => bAnd (inCF xi b (Psi sg ka b) m) (fun m => bAnd (inCF pi b (Psi sg ka b) m)
                (fun m => isLt (cmpF (Psi xi pi a) ka m))))))
            (fun m => bOr
              (bAnd (let r := cmpF b a m; (r.1 != .gt, r.2)) (fun m =>
                let r := bAnd (inCF b a (Psi xi pi a) m) (fun m => bAnd (inCF sg a (Psi xi pi a) m)
                  (fun m => inCF ka a (Psi xi pi a) m))
                (!r.1, r.2)))
              (fun m => bOr
                (bAnd (let r := cmpF a b m; (r.1 == .eq, r.2)) (fun m => bAnd (ka == pi, m)
                  (fun m => bAnd (isLt (cmpF xi sg m)) (fun m => inCF xi b (Psi sg ka b) m))))
                (fun m => bAnd (isLt (cmpF sg xi m)) (fun m =>
                  let r := inCF sg xi (Psi xi pi a) m; (!r.1, r.2)))))
          (if r.1 then .lt else .gt, r.2)
  | _, _ => (.eq, m)
termination_by 8 * (x.size + y.size)
decreasing_by all_goals ((try simp only [Tm.size]); omega)

def inCF (a g d : Tm) (m : Memo) : Bool × Memo :=
  match m.i[Psi a g d]? with
  | some v => (v, m)
  | none =>
    let r := inCB a g d m
    (r.1, { r.2 with i := r.2.i.insert (Psi a g d) r.1 })
termination_by 8 * (a.size + max g.size d.size) + 6
decreasing_by omega

/-- `inC` の本体（部分項への呼び出しはメモ化版） -/
def inCB (a g d : Tm) (m : Memo) : Bool × Memo :=
  match a with
  | zero | one | K _ => (true, m)
  | plus x y => bAnd (inCF x g d m) (fun m => inCF y g d m)
  | Om x => inCF x g d m
  | Xi n b => bOr (isLt (cmpF (Xi n b) d m)) (fun m => bAnd (inCF b g d m) (fun m => isLt (cmpF b g m)))
  | Psi sg ka b =>
    bOr (isLt (cmpF (Psi sg ka b) d m))
      (fun m => bAnd (inCF ka g d m) (fun m => bAnd (inCF sg g d m) (fun m => bAnd (inCF b g d m)
        (fun m => isLt (cmpF b g m)))))
termination_by 8 * (a.size + max g.size d.size) + 5
decreasing_by all_goals ((try simp only [Tm.size]); omega)

end

/-- メモ化した比較 -/
def cmpFast (a b : Tm) : Ordering := (cmpF a b .empty).1

/-- メモ化した `C(γ, δ)` への所属 -/
def inCFast (a g d : Tm) : Bool := (inCF a g d .empty).1

/-! ### メモ化版が元の定義と一致すること -/

/-- 表の内容は全て正しい -/
def Memo.Good (m : Memo) : Prop :=
  (∀ a b o, m.c[Psi a b zero]? = some o → o = cmp a b) ∧
  (∀ a g d v, m.i[Psi a g d]? = some v → v = inC a g d)

theorem Memo.good_empty : Memo.empty.Good :=
  ⟨fun _ _ _ h => by simp [Memo.empty] at h, fun _ _ _ _ h => by simp [Memo.empty] at h⟩

theorem Memo.Good.insC {m : Memo} (hm : m.Good) (a b : Tm) :
    ({ m with c := m.c.insert (Psi a b zero) (cmp a b) } : Memo).Good := by
  refine ⟨fun a' b' o h => ?_, hm.2⟩
  simp only [Std.HashMap.getElem?_insert, beq_iff_eq, Psi.injEq, and_true] at h
  split at h
  · rename_i he
    obtain ⟨rfl, rfl⟩ := he
    cases h
    rfl
  · exact hm.1 a' b' o h

theorem Memo.Good.insI {m : Memo} (hm : m.Good) (a g d : Tm) :
    ({ m with i := m.i.insert (Psi a g d) (inC a g d) } : Memo).Good := by
  refine ⟨hm.1, fun a' g' d' v h => ?_⟩
  simp only [Std.HashMap.getElem?_insert, beq_iff_eq, Psi.injEq] at h
  split at h
  · rename_i he
    obtain ⟨rfl, rfl, rfl⟩ := he
    cases h
    rfl
  · exact hm.2 a' g' d' v h

/-- 値は元の関数の値で、表は正しいまま -/
def Spec {α : Type} (r : α × Memo) (v : α) : Prop := r.1 = v ∧ r.2.Good

theorem Spec.map {α β : Type} {r : α × Memo} {v : α} (h : Spec r v) (f : α → β) : Spec (f r.1, r.2) (f v) :=
  ⟨by rw [h.1], h.2⟩

theorem bAnd_spec {x : Bool × Memo} {y : Memo → Bool × Memo} {X Y : Bool}
    (hx : Spec x X) (hy : ∀ m, m.Good → Spec (y m) Y) : Spec (bAnd x y) (X && Y) := by
  obtain ⟨rfl, h2⟩ := hx
  unfold bAnd
  cases hb : x.1
  · exact ⟨rfl, h2⟩
  · simpa using hy x.2 h2

theorem bOr_spec {x : Bool × Memo} {y : Memo → Bool × Memo} {X Y : Bool}
    (hx : Spec x X) (hy : ∀ m, m.Good → Spec (y m) Y) : Spec (bOr x y) (X || Y) := by
  obtain ⟨rfl, h2⟩ := hx
  unfold bOr
  cases hb : x.1
  · simpa using hy x.2 h2
  · exact ⟨rfl, h2⟩

theorem isLt_spec {r : Ordering × Memo} {v : Ordering} (h : Spec r v) : Spec (isLt r) (v == .lt) :=
  h.map (· == .lt)

mutual

theorem cmpF_spec (a b : Tm) (m : Memo) (hm : m.Good) : Spec (cmpF a b m) (cmp a b) := by
  unfold cmpF
  split
  · rename_i o h
    exact ⟨hm.1 a b o h, hm⟩
  · obtain ⟨e, h2⟩ := cmpListF_spec (summands a) (summands b) m hm
    have e' : (cmpListF (summands a) (summands b) m).1 = cmp a b := by rw [e]; unfold cmp; rfl
    refine ⟨e', ?_⟩
    show ({ (cmpListF (summands a) (summands b) m).2 with
      c := (cmpListF (summands a) (summands b) m).2.c.insert (Psi a b zero)
        (cmpListF (summands a) (summands b) m).1 } : Memo).Good
    rw [e']
    exact h2.insC a b
termination_by 8 * (a.size + b.size) + 3
decreasing_by
  have := lsize_summands_le a
  have := lsize_summands_le b
  omega

theorem cmpListF_spec : ∀ (xs ys : List Tm) (m : Memo), m.Good → Spec (cmpListF xs ys m) (cmpList xs ys)
  | [], [], m, hm => by simp only [cmpListF, cmpList]; exact ⟨rfl, hm⟩
  | [], _ :: _, m, hm => by simp only [cmpListF, cmpList]; exact ⟨rfl, hm⟩
  | _ :: _, [], m, hm => by simp only [cmpListF, cmpList]; exact ⟨rfl, hm⟩
  | x :: xs, y :: ys, m, hm => by
    obtain ⟨e, h2⟩ := cmpPF_spec x y m hm
    simp only [cmpListF, cmpList]
    rw [e]
    cases cmpP x y with
    | lt => exact ⟨rfl, h2⟩
    | eq => exact cmpListF_spec xs ys _ h2
    | gt => exact ⟨rfl, h2⟩
termination_by xs ys _ _ => 8 * (lsize xs + lsize ys) + 2
decreasing_by
  all_goals
    simp only [lsize]
    have := Tm.size_pos x
    have := Tm.size_pos y
    omega

theorem cmpPF_spec (x y : Tm) (m : Memo) (hm : m.Good) : Spec (cmpPF x y m) (cmpP x y) := by
  unfold cmpPF cmpP
  by_cases h1 : lev x < lev y
  · simp only [h1, ↓reduceIte]; exact ⟨rfl, hm⟩
  by_cases h2 : lev y < lev x
  · simp only [h1, h2, ↓reduceIte]; exact ⟨rfl, hm⟩
  simp only [h1, h2, ↓reduceIte]
  cases x <;> cases y
  all_goals first
    | exact ⟨rfl, hm⟩
    | exact cmpF_spec _ _ m hm
    | exact cmpOmXF_spec _ _ m hm
    | exact cmpPsiF_spec _ _ m hm
    | exact (cmpOmXF_spec _ _ m hm).map Ordering.swap
    | exact (psiLtXiF_spec _ _ m hm).map (fun b => if b then Ordering.lt else .gt)
    | exact (psiLtXiF_spec _ _ m hm).map (fun b => if b then Ordering.gt else .lt)
    | skip
  all_goals
    rename_i n a k b
    dsimp only
    by_cases hab : (a == b) = true
    · simp only [hab, ↓reduceIte]; exact ⟨rfl, hm⟩
    · simp only [hab, Bool.false_eq_true, ↓reduceIte]
      exact (xiLtXiF_spec _ _ m hm).map (fun b => if b then Ordering.lt else .gt)
termination_by 8 * (x.size + y.size) + 1
decreasing_by all_goals ((try simp only [Tm.size]); omega)

theorem cmpOmXF_spec (a X : Tm) (m : Memo) (hm : m.Good) : Spec (cmpOmXF a X m) (cmpOmX a X) := by
  unfold cmpOmXF cmpOmX
  by_cases ho : omegaFixed X = true
  · simp only [ho, ↓reduceIte]; exact cmpF_spec a X m hm
  simp only [ho, Bool.false_eq_true, ↓reduceIte]
  cases X with
  | Psi s p b =>
    cases p with
    | Om c => exact (cmpF_spec _ _ m hm).map (fun o => if o == Ordering.lt then Ordering.lt else .gt)
    | _ => exact ⟨rfl, hm⟩
  | _ => exact ⟨rfl, hm⟩
termination_by 8 * (a.size + X.size) + 4
decreasing_by all_goals ((try simp only [Tm.size]); omega)

theorem xiLtXiF_spec (x y : Tm) (m : Memo) (hm : m.Good) : Spec (xiLtXiF x y m) (xiLtXi x y) := by
  unfold xiLtXiF xiLtXi
  cases x with
  | Xi n a =>
    cases y with
    | Xi k b =>
      exact bOr_spec (bAnd_spec (isLt_spec (cmpF_spec _ _ m hm)) (fun m hm => inCF_spec _ _ _ m hm))
        (fun m hm => bAnd_spec (isLt_spec (cmpF_spec _ _ m hm))
          (fun m hm => (inCF_spec _ _ _ m hm).map (!·)))
    | _ => exact ⟨rfl, hm⟩
  | _ => exact ⟨rfl, hm⟩
termination_by 8 * (x.size + y.size)
decreasing_by all_goals ((try simp only [Tm.size]); omega)

theorem psiLtXiF_spec (x y : Tm) (m : Memo) (hm : m.Good) : Spec (psiLtXiF x y m) (psiLtXi x y) := by
  unfold psiLtXiF psiLtXi
  cases x with
  | Psi xi pi a =>
    cases y with
    | Xi k b =>
      exact bOr_spec ((cmpF_spec _ _ m hm).map (· != Ordering.gt))
        (fun m hm => bAnd_spec (isLt_spec (cmpF_spec _ _ m hm))
          (fun m hm => (inCF_spec _ _ _ m hm).map (!·)))
    | _ => exact ⟨rfl, hm⟩
  | _ => exact ⟨rfl, hm⟩
termination_by 8 * (x.size + y.size)
decreasing_by all_goals ((try simp only [Tm.size]); omega)

theorem cmpPsiF_spec (x y : Tm) (m : Memo) (hm : m.Good) : Spec (cmpPsiF x y m) (cmpPsi x y) := by
  unfold cmpPsiF cmpPsi
  cases x with
  | Psi xi pi a =>
    cases y with
    | Psi sg ka b =>
      dsimp only
      by_cases hxy : (Psi xi pi a == Psi sg ka b) = true
      · simp only [hxy, ↓reduceIte]; exact ⟨rfl, hm⟩
      simp only [hxy, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨e1, g1⟩ := cmpF_spec (Psi sg ka b) pi m hm
      rcases r1 : cmpF (Psi sg ka b) pi m with ⟨o1, m1⟩
      rw [r1] at e1 g1
      simp only at e1 g1 ⊢
      subst e1
      by_cases c1 : (cmp (Psi sg ka b) pi != .lt) = true
      · simp only [c1, ↓reduceIte]; exact ⟨rfl, g1⟩
      simp only [c1, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨e2, g2⟩ := cmpF_spec (Psi xi pi a) ka m1 g1
      rcases r2 : cmpF (Psi xi pi a) ka m1 with ⟨o2, m2⟩
      rw [r2] at e2 g2
      simp only at e2 g2 ⊢
      subst e2
      by_cases c2 : (cmp (Psi xi pi a) ka != .lt) = true
      · simp only [c2, ↓reduceIte]; exact ⟨rfl, g2⟩
      simp only [c2, Bool.false_eq_true, ↓reduceIte]
      have h := bOr_spec
        (bAnd_spec (isLt_spec (cmpF_spec a b m2 g2)) (fun m hm => bAnd_spec (inCF_spec a b (Psi sg ka b) m hm)
          (fun m hm => bAnd_spec (inCF_spec xi b (Psi sg ka b) m hm)
            (fun m hm => bAnd_spec (inCF_spec pi b (Psi sg ka b) m hm)
              (fun m hm => isLt_spec (cmpF_spec (Psi xi pi a) ka m hm))))))
        (fun m hm => bOr_spec
          (bAnd_spec ((cmpF_spec b a m hm).map (· != Ordering.gt)) (fun m hm =>
            (bAnd_spec (inCF_spec b a (Psi xi pi a) m hm) (fun m hm => bAnd_spec
              (inCF_spec sg a (Psi xi pi a) m hm) (fun m hm => inCF_spec ka a (Psi xi pi a) m hm))).map (!·)))
          (fun m hm => bOr_spec
            (bAnd_spec ((cmpF_spec a b m hm).map (· == Ordering.eq)) (fun m hm =>
              bAnd_spec (x := (ka == pi, m)) (X := ka == pi) ⟨rfl, hm⟩
                (fun m hm => bAnd_spec (isLt_spec (cmpF_spec xi sg m hm))
                  (fun m hm => inCF_spec xi b (Psi sg ka b) m hm))))
            (fun m hm => bAnd_spec (isLt_spec (cmpF_spec sg xi m hm))
              (fun m hm => (inCF_spec sg xi (Psi xi pi a) m hm).map (!·)))))
      have h' := h.map (fun c => if c then Ordering.lt else .gt)
      simp only [Bool.and_assoc, Bool.or_assoc] at h' ⊢
      exact h'
    | _ => exact ⟨rfl, hm⟩
  | _ => exact ⟨rfl, hm⟩
termination_by 8 * (x.size + y.size)
decreasing_by all_goals ((try simp only [Tm.size]); omega)

theorem inCF_spec (a g d : Tm) (m : Memo) (hm : m.Good) : Spec (inCF a g d m) (inC a g d) := by
  unfold inCF
  split
  · rename_i v h
    exact ⟨hm.2 a g d v h, hm⟩
  · obtain ⟨e, h2⟩ := inCB_spec a g d m hm
    refine ⟨e, ?_⟩
    show ({ (inCB a g d m).2 with
      i := (inCB a g d m).2.i.insert (Psi a g d) (inCB a g d m).1 } : Memo).Good
    rw [e]
    exact h2.insI a g d
termination_by 8 * (a.size + max g.size d.size) + 6
decreasing_by omega

theorem inCB_spec (a g d : Tm) (m : Memo) (hm : m.Good) : Spec (inCB a g d m) (inC a g d) := by
  cases a with
  | zero => unfold inCB inC; exact ⟨rfl, hm⟩
  | one => unfold inCB inC; exact ⟨rfl, hm⟩
  | K _ => unfold inCB inC; exact ⟨rfl, hm⟩
  | plus x y =>
    unfold inCB
    rw [inC]
    exact bAnd_spec (inCF_spec x g d m hm) (fun m hm => inCF_spec y g d m hm)
  | Om x =>
    unfold inCB
    rw [inC]
    exact inCF_spec x g d m hm
  | Xi n b =>
    unfold inCB
    rw [inC]
    exact bOr_spec (isLt_spec (cmpF_spec _ _ m hm))
      (fun m hm => bAnd_spec (inCF_spec b g d m hm) (fun m hm => isLt_spec (cmpF_spec b g m hm)))
  | Psi sg ka b =>
    unfold inCB
    rw [inC]
    have h := bOr_spec (isLt_spec (cmpF_spec (Psi sg ka b) d m hm))
      (fun m hm => bAnd_spec (inCF_spec ka g d m hm) (fun m hm => bAnd_spec (inCF_spec sg g d m hm)
        (fun m hm => bAnd_spec (inCF_spec b g d m hm) (fun m hm => isLt_spec (cmpF_spec b g m hm)))))
    simp only [Bool.and_assoc] at h ⊢
    exact h
termination_by 8 * (a.size + max g.size d.size) + 5
decreasing_by all_goals ((try simp only [Tm.size]); omega)

end

@[csimp] theorem cmp_eq_cmpFast : @cmp = @cmpFast := by
  funext a b
  exact (cmpF_spec a b .empty Memo.good_empty).1.symm

@[csimp] theorem inC_eq_inCFast : @inC = @inCFast := by
  funext a g d
  exact (inCF_spec a g d .empty Memo.good_empty).1.symm

end RTKA
