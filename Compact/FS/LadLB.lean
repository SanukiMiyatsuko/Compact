import Compact.FS.LadderOm

/-! Bachmann 性の不等式による言い換え。

`LBI x y`：区間 `(x, y]` の元 `w` は全て `x ≤ w[0]`。

* `LBI` は推移的で（`LBI.trans`）、`x ≤ y` なら `x` は `y` の降下列に現れる（`descT_of_LBI`）。
* `ω` 型の項 `t` で、隣り合う列の項の間に `LBI t[n] t[n+1]` があれば、共終性から Bachmann 性
  （`t[n] < z < t` なら `t[n] ≤ z[0]`）が従う（`bach_of_LBI`）。降下列を追わずに、区間の元の 0 番目の
  下界だけを示せばよい。 -/

namespace RTKA.Fund

open Tm W

/-- 区間 `(x, y]` の元の 0 番目は `x` 以上 -/
def LBI (x y : Tm) : Prop := ∀ w, WNF w → Lt x w → Le w y → Le x (fund w .zero)

theorem LBI.refl {x : Tm} (hx : WNF x) : LBI x x := fun _ hw h1 h2 =>
  absurd h1 (not_lt_of_leY hw hx h2)

/-- 区間を縮める -/
theorem LBI.mono {x y z : Tm} (hy : WNF y) (hz : WNF z) (h : LBI x z) (hyz : Le y z) : LBI x y :=
  fun w hw h1 h2 => h w hw h1 (le_transY hw hy hz h2 hyz)

/-- `LBI` の推移性 -/
theorem LBI.trans {x y z : Tm} (hx : WNF x) (hy : WNF y) (hxy : Le x y) (h1 : LBI x y) (h2 : LBI y z) :
    LBI x z := by
  intro w hw hxw hwz
  by_cases hwy : Le w y
  · exact h1 w hw hxw hwy
  · have hyw : Lt y w := by
      rcases triY hy hw with h | h | h
      · exact h
      · exact absurd (Or.inl h.symm) hwy
      · exact absurd (Or.inr h) hwy
    exact le_transY hx hy (fund_wnf hw WNF.zero) hxy (h2 w hw hyw hwz)

theorem ne_zero_of_lt {x y : Tm} (h : Lt x y) : y ≠ .zero := by
  rintro rfl
  exact not_lt_zero _ h

/-- 区間の下界から降下列へ：`x ≤ y` で `LBI x y` なら `x ∈ D(y)` -/
theorem descT_of_LBI {x : Tm} (y : NF) : Le x y.1 → LBI x y.1 → DescT x y.1 := by
  refine WellFounded.induction (C := fun y : NF => Le x y.1 → LBI x y.1 → DescT x y.1)
    wellFounded_isNF y ?_
  intro y ih hxy hL
  rcases hxy with e | hlt
  · rw [← e]
    exact .refl
  · have hyF : WNF y.1 := y.2
    have hy0 := ne_zero_of_lt hlt
    have hpF := fund_wnf hyF WNF.zero
    have hplt := fund_zero_lt hyF hy0
    refine .step (ih ⟨fund y.1 .zero, hpF⟩ hplt (hL y.1 hyF hlt (Or.inl rfl)) ?_)
    exact LBI.mono hpF hyF hL (Or.inr hplt)

/-! ### 隣り合う項の下界から Bachmann 性へ -/

/-- `ω` 型の列の単調性（`m ≤ n` なら `t[m] ≤ t[n]`） -/
theorem nat_mono_le {t : Tm} (ht : WNF t) (hd : dom t = .omega) {m n : Nat} (h : m ≤ n) :
    Le ((info t).seq.nat m) ((info t).seq.nat n) := by
  have hG := (seqI_dom_nat ht hd).1.good
  induction n with
  | zero =>
    have : m = 0 := by omega
    rw [this]
    exact Or.inl rfl
  | succ k ih =>
    by_cases e : m = k + 1
    · rw [e]
      exact Or.inl rfl
    · exact le_transY (hG m).1 (hG k).1 (hG (k + 1)).1 (ih (by omega)) (Or.inr (hG k).2.2)

/-- 隣り合う項の下界から：`t[n] < z ≤ t[n+j+1]` なら `t[n] ≤ z[0]` -/
theorem lbi_chain {t : Tm} (ht : WNF t) (hd : dom t = .omega)
    (hL : ∀ n, LBI ((info t).seq.nat n) ((info t).seq.nat (n + 1))) {z : Tm} (hz : WNF z) :
    ∀ j n, Lt ((info t).seq.nat n) z → Le z ((info t).seq.nat (n + j + 1)) →
      Le ((info t).seq.nat n) (fund z .zero) := by
  have hG := (seqI_dom_nat ht hd).1.good
  intro j
  induction j with
  | zero => intro n h1 h2; exact hL n z hz h1 h2
  | succ j ih =>
    intro n h1 h2
    by_cases hle : Le z ((info t).seq.nat (n + 1))
    · exact hL n z hz h1 hle
    · have h3 : Lt ((info t).seq.nat (n + 1)) z := by
        rcases triY (hG (n + 1)).1 hz with h | h | h
        · exact h
        · exact absurd (Or.inl h.symm) hle
        · exact absurd (Or.inr h) hle
      have h4 := ih (n + 1) h3 (by rw [show n + 1 + j + 1 = n + (j + 1) + 1 by omega]; exact h2)
      exact le_transY (hG n).1 (hG (n + 1)).1 (fund_wnf hz WNF.zero) (Or.inr (hG n).2.2) h4

/-- Bachmann 性：隣り合う項の下界と共終性から、`t[n] < z < t` なら `t[n] ≤ z[0]` -/
theorem bach_of_LBI {t : Tm} (ht : WNF t) (hd : dom t = .omega)
    (hL : ∀ n, LBI ((info t).seq.nat n) ((info t).seq.nat (n + 1))) (n : Nat) {z : Tm} (hz : WNF z)
    (h1 : Lt ((info t).seq.nat n) z) (h2 : Lt z t) : Le ((info t).seq.nat n) (fund z .zero) := by
  have hG := (seqI_dom_nat ht hd).1.good
  have hC := seqC_all t ht
  unfold SeqC at hC
  rw [show (info t).seq.dom = dom t from rfl, hd] at hC
  obtain ⟨m, hm⟩ := hC z hz h2
  have hnm : n < m := by
    rcases Nat.lt_or_ge n m with h | h
    · exact h
    · exact absurd (lt_transY (hG n).1 hz (hG n).1 h1 (lt_of_lt_of_leY hz (hG m).1 (hG n).1 hm
        (nat_mono_le ht hd h))) (Lt.irrefl _)
  obtain ⟨j, rfl⟩ : ∃ j, m = n + j + 1 := ⟨m - n - 1, by omega⟩
  exact lbi_chain ht hd hL hz j n h1 (Or.inr hm)

/-- 梯子（不等式版）：`ω` 型の全ての項で、隣り合う列の項の区間の元の 0 番目は下の項以上 -/
def LadderLB : Prop :=
  ∀ t, WNF t → dom t = .omega → ∀ n, LBI ((info t).seq.nat n) ((info t).seq.nat (n + 1))

end RTKA.Fund

namespace RTKA

open Fund Tm W FSDesc

/-- Bachmann 性（不等式版の梯子から） -/
theorem nf_omega_bachmannLB (hL : LadderLB) (a b : NF) (n : Nat)
    (hd : domNF a = .omega) (h1 : fundNF a (ofNatNF n) < b) (h2 : b < a) :
    fundNF a (ofNatNF n) ≤ fundNF b (ofNatNF 0) := by
  have hdT := domNF_omega.mp hd
  rw [nf_le]
  have h1' : Lt ((info a.1).seq.nat n) b.1 := by
    have := (nf_lt).mp h1
    show Lt _ _
    rwa [show (fundNF a (ofNatNF n)).1 = fund a.1 (ofNatT n) from rfl, fund_omega hdT] at this
  have h := bach_of_LBI a.2 hdT (hL a.1 a.2 hdT) n b.2 h1' ((nf_lt).mp h2)
  show Le (fund a.1 (ofNatT n)) (fund b.1 (ofNatT 0))
  rw [fund_omega hdT]
  exact h

/-- 不等式版の梯子があれば `NF` は基本列の公理を満たす（`big` 型の梯子は要らない） -/
def fsNFLB (hL : LadderLB) : FS NF where
  fund := fundNF
  dom := domNF
  Z := zeroNF
  ofNat := ofNatNF
  ofNat_zero := nf_ofNat_zero
  ofNat_dom := nf_ofNat_dom
  ofNat_fund := nf_ofNat_fund
  zero_dom := nf_zero_dom
  zero_unique := nf_zero_unique
  zero_fund := nf_zero_fund
  succ_md := nf_succ_md
  succ_cof := nf_succ_cof
  omega_lt := nf_omega_lt
  omega_mono := nf_omega_mono
  omega_bachmann := fun a b n hd h1 h2 => nf_omega_bachmannLB hL a b n hd h1 h2
  omega_cof := nf_omega_cof
  big_lt := nf_big_lt
  big_mono := nf_big_mono
  big_cof := nf_big_cof

end RTKA
