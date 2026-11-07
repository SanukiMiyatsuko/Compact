import Compact.FS.LadPsiOm

/-! 降下列に沿った閉包の所属の移し替えと、閉包による崩壊の下界。

* `inC_fund0`：`u ∈ C(g, d)` なら `u[0] ∈ C(g, d)`（列の不変量の上界 `NatUB.ub`・`BigUB.ub`。共終数が正則項 `σ` の
  ときは `BigOK σ g d` と `0 < g` が要る）。
* `inC_of_descT`：`x ∈ D(y)` で `y ∈ C(g, d)` なら `x ∈ C(g, d)`。
* `le_psi_of_descT`：`A ∈ D(W₀)`、`W₀ ≤ V`、`W₀ ∈ C(V, q)`（`q = Ψ^0_π(V)`）なら `Ψ^0_π(A) ≤ q`。
  `A` の節点が `q` の閉包に入ることを、`W₀` から降下列に沿って移す（避ける性質は要らない）。 -/

namespace RTKA.Fund

open Tm W

/-- `0` の `natOf` -/
theorem natOf_zero : natOf .zero = 0 := rfl

/-- 0 番目への移し替え：`u ∈ C(g, d)` なら `u[0] ∈ C(g, d)` -/
theorem inC_fund0 {u g d : Tm} (hu : WNF u) (hg : WNF g) (hd : WNF d) (hg0 : Lt .zero g)
    (hB : ∀ σ, dom u = .big σ → BigOK σ g d) (h : inC u g d = true) :
    inC (fund u .zero) g d = true := by
  rw [fund_eq]
  cases hdu : dom u with
  | zero => exact inC_zero _ _
  | one =>
    show inC (pred u) g d = true
    unfold pred
    rw [inC_ofSummands]
    intro s hs
    exact inC_of_mem_summands hu h (List.dropLast_subset _ hs)
  | omega =>
    show inC (fundNat u (natOf .zero)) g d = true
    rw [natOf_zero]
    exact (seqI_dom_nat hu hdu).1.ub g d 0 hg hd h
  | big σ =>
    show inC (fundBig u (if ltB .zero σ = true then .zero else .zero)) g d = true
    have e : (if ltB Tm.zero σ = true then Tm.zero else Tm.zero) = .zero := by split <;> rfl
    rw [e]
    obtain ⟨hU, hreg⟩ := seqI_dom_big hu hdu
    exact hU.ub g d .zero hg hd WNF.zero (zero_lt hreg.ne_zero) hg0 (hB σ hdu) h (inC_zero _ _)

/-- 崩壊の引数はその崩壊の閉包に入る：`a ∈ C(a, Ψ^ξ_π(a))` -/
theorem inC_arg_psi {ξ π a : Tm} (h : WNF (.Psi ξ π a)) : inC a a (.Psi ξ π a) = true :=
  inC_of_fr a h.psi.Ca (fun _ _ h => h) (fun w hw => inC_of_lt_node (fr_node hw) (FWOrder.k2 h w hw))

/-- 0 番目は自分以下 -/
theorem fund_zero_le {b : Tm} (hb : WNF b) : Le (fund b .zero) b := by
  by_cases hb0 : b = .zero
  · subst hb0
    exact Or.inl rfl
  · exact Or.inr (fund_zero_lt hb hb0)

/-- 降下列に沿った移し替え：`x ∈ D(y)` で `y ∈ C(g, d)` なら `x ∈ C(g, d)`
    （降下列の途中の共終数が正則項の項では `BigOK` が要る） -/
theorem inC_of_descT {x g d : Tm} (hg : WNF g) (hd : WNF d) (hg0 : Lt .zero g) :
    ∀ {y : Tm}, DescT x y → WNF y →
      (∀ u σ, WNF u → DescT x u → DescT u y → dom u = .big σ → BigOK σ g d) →
      inC y g d = true → inC x g d = true := by
  intro y h
  induction h with
  | refl => intro _ _ h; exact h
  | @step b hxb ih =>
    intro hb hB h
    have hpF := fund_wnf hb WNF.zero
    refine ih hpF (fun u σ hu hxu hub hdu => hB u σ hu hxu (.step hub) hdu) ?_
    exact inC_fund0 hb hg hd hg0 (fun σ e => hB b σ hb (.step hxb) .refl e) h

/-- `x ∈ D(y)` で `x ≠ y` なら `x ∈ D(y[0])` -/
theorem DescT.of_ne {x y : Tm} (h : DescT x y) (hne : x ≠ y) : DescT x (fund y .zero) := by
  cases h with
  | refl => exact absurd rfl hne
  | step h => exact h

/-- 閉包による崩壊の下界：`A ≤ V`、`A ∈ C(V, q)`（`q = Ψ^0_π(V)` は標準形）なら `Ψ^0_π(A) ≤ q` -/
theorem le_psi_of_inC {π A V : Tm} (hy : WNF (.Psi .zero π A)) (hq : WNF (.Psi .zero π V))
    (hAV : Le A V) (hAC : inC A V (.Psi .zero π V) = true) :
    Le (.Psi .zero π A) (.Psi .zero π V) := by
  rcases hAV with e | hlt
  · rw [e]
    exact Or.inl rfl
  have hyC : inC (.Psi .zero π A) V (.Psi .zero π V) = true := inC_psi_iff.mpr (Or.inr
    ⟨inC_tgt_of_k2t hq fun u hu => FWOrder.k2t hq u hu, inC_zero _ _, hAC, hlt⟩)
  exact Or.inr (coll_psiY hq _ hy hyC (lt_psi_targetY hy))

/-- 閉包による崩壊の下界：`A ∈ D(W₀)`、`W₀ ≤ V`、`W₀ ∈ C(V, q)`（`q = Ψ^0_π(V)` は標準形）なら `Ψ^0_π(A) ≤ q` -/
theorem le_psi_of_descT {π A V W₀ : Tm} (hy : WNF (.Psi .zero π A)) (hq : WNF (.Psi .zero π V))
    (hW₀ : WNF W₀) (hD : DescT A W₀) (hWV : Le W₀ V)
    (hC : inC W₀ V (.Psi .zero π V) = true)
    (hB : ∀ u σ, WNF u → DescT A u → DescT u W₀ → dom u = .big σ → BigOK σ V (.Psi .zero π V)) :
    Le (.Psi .zero π A) (.Psi .zero π V) := by
  have hAF := hy.psi.aF
  have hVF := hq.psi.aF
  have hAW := DescT.le hAF hW₀ hD
  have hAV : Le A V := le_transY hAF hW₀ hVF hAW hWV
  rcases hAV with e | hlt
  · rw [e]
    exact Or.inl rfl
  have hV0 : Lt .zero V := lt_of_le_of_ltY WNF.zero hAF hVF (zero_le A) hlt
  exact le_psi_of_inC hy hq (Or.inr hlt) (inC_of_descT hVF hq hV0 hD hW₀ hB hC)

/-- 極限（後者でない）`g` では `BigOK` は常に成り立つ -/
theorem bigOK_of_ns {σ g d : Tm} (hσ : WNF σ) (hg : WNF g) (hgs : ¬ isSucc g = true) : BigOK σ g d :=
  Or.inr fun q hq hlt => by
    have hqF := wnf_of_argR hσ hq
    rcases succT_le_of_lt hqF hg hlt with e | h
    · exact absurd (e ▸ isSucc_succT q) hgs
    · exact h

/-- 閉包による崩壊の下界（`V` が後者でない場合）：`A ∈ D(W₀)`、`W₀ ≤ V`、`W₀ ∈ C(V, q)` なら `Ψ^0_π(A) ≤ q` -/
theorem le_psi_of_descT_ns {π A V W₀ : Tm} (hy : WNF (.Psi .zero π A)) (hq : WNF (.Psi .zero π V))
    (hW₀ : WNF W₀) (hD : DescT A W₀) (hWV : Le W₀ V)
    (hC : inC W₀ V (.Psi .zero π V) = true) (hVs : ¬ isSucc V = true) :
    Le (.Psi .zero π A) (.Psi .zero π V) :=
  le_psi_of_descT hy hq hW₀ hD hWV hC fun u σ hu _ _ hdu =>
    bigOK_of_ns (seqI_dom_big hu hdu).1.hσF hq.psi.aF hVs

/-- `x ∈ C(V, q)`（`q = Ψ^0_π(V)` は標準形）なら、`x` の前線（`π` について）は全て `q` 未満 -/
theorem fr_lt_of_inC_psi {π V x : Tm} (hq : WNF (.Psi .zero π V)) (hx : WNF x)
    (h : inC x V (.Psi .zero π V) = true) : ∀ f, f ∈ fr π x → Lt f (.Psi .zero π V) := by
  intro f hf
  have hqπ := lt_psi_targetY hq
  have hfC := fr_of_inC x (fun w hw hn hlt => hn (lt_transY (hx.of_mem_subs hw) hq hq.psi.piF hlt hqπ)) h f hf
  exact coll_psiY hq f (hx.of_mem_subs (fr_spec hf).1) hfC (fr_spec hf).2

/-- `R ∈ C(V, q)` なら、`R` の列（ω 型）の全ての項の前線は `q` 未満 -/
theorem seq_fr_lt {π V R : Tm} (hq : WNF (.Psi .zero π V)) (hR : WNF R) (hd : dom R = .omega)
    (hRC : inC R V (.Psi .zero π V) = true) (n : Nat) :
    ∀ f, f ∈ fr π ((info R).seq.nat n) → Lt f (.Psi .zero π V) :=
  fr_lt_of_inC_psi hq ((seqI_dom_nat hR hd).1.good n).1 ((seqI_dom_nat hR hd).1.ub _ _ n hq.psi.aF hq hRC)

end RTKA.Fund
