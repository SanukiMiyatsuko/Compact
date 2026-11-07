import Compact.FS.OmInv

/-! 目標が `Ω_c` の崩壊 `t = Ψ^0_{Ω_c}(X)` の列の不変量：後者の引数（`seqInv_om_succ`）と極限の引数（`seqInv_om_limit`）。
加数の不変量を仮定し、`cs` の分岐ごとに `SeqInv` を示す。

極限の引数の分岐：`p` を前線の最大の元、`y₀` を素の近似の 0 番目とする。

* `p < y₀`（または前線が空）：素の近似。
* `y₀ = p` は起こらない（`p` の引数は `A_0` で、`X` の節点の引数は `A_0` 未満）。
* `y₀ < p`：`p` は `pre` の前線になく、最後の加数の前線にある。`p` より大きい加数がなければ `X = p` で種の倍数。
  あれば種の挿入で、挿入点より後ろの加数は `p` そのもの（`seed_last` で `p` の部分項は `p` 未満）。 -/

namespace RTKA.Fund

open Tm W

theorem inC_pred_of {c g d : Tm} (hc : WNF c) (h : inC c g d = true) : inC (pred c) g d = true := by
  unfold pred
  rw [inC_ofSummands]
  intro s hs
  exact inC_of_mem_summands hc h (List.dropLast_subset _ hs)

theorem inC_of_succT : ∀ {z g d : Tm}, inC (succT z) g d = true → inC z g d = true
  | .zero, _, _, _ => inC_zero _ _
  | .plus a b, g, d, h => by
    have h' : inC (.plus a (succT b)) g d = true := h
    rw [inC_plus, Bool.and_eq_true] at h' ⊢
    exact ⟨h'.1, inC_of_succT h'.2⟩
  | .one, g, d, h | .K _, g, d, h | .Om _, g, d, h | .Xi _ _, g, d, h | .Psi _ _ _, g, d, h => by
    have h' : inC (.plus _ .one) g d = true := h
    rw [inC_plus, Bool.and_eq_true] at h'
    exact h'.1

theorem app_dom_nat {τ P c : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD}
    (hdom : ∀ σ, r.dom ≠ .big σ) : (SeqD.app τ g pre R r P c).dom = .omega := by
  show (match r.dom with
    | Cof.big σ => if ltB σ τ then Cof.big σ else Cof.omega
    | _ => Cof.omega : Cof Tm) = _
  split
  · rename_i σ h
    exact absurd h (hdom σ)
  · rfl

theorem app_dom_big_ge {τ σ P c : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD}
    (hd : r.dom = .big σ) (hlt : ltB σ τ = false) : (SeqD.app τ g pre R r P c).dom = .omega := by
  show (match r.dom with
    | Cof.big σ => if ltB σ τ then Cof.big σ else Cof.omega
    | _ => Cof.omega : Cof Tm) = _
  rw [hd]
  simp [hlt]

theorem app_dom_big_lt {τ σ P c : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD}
    (hd : r.dom = .big σ) (hlt : ltB σ τ = true) : (SeqD.app τ g pre R r P c).dom = .big σ := by
  show (match r.dom with
    | Cof.big σ => if ltB σ τ then Cof.big σ else Cof.omega
    | _ => Cof.omega : Cof Tm) = _
  rw [hd]
  simp [hlt]

theorem dom_ne_of_principal {R : Tm} (hR : WNF R) (hp : isPrincipal R = true) (h1 : R ≠ .one) :
    (info R).seq.dom ≠ .zero ∧ (info R).seq.dom ≠ .one := by
  constructor
  · intro e
    have := (dom_eq_zero_iff hR).mp e
    rw [this] at hp
    cases hp
  · intro e
    have h := (dom_eq_one_iff hR).mp e
    rw [isSucc_principal hp] at h
    exact h1 (by simpa using h)

theorem om_ne_of_lt {c d : Tm} (h : Lt (.Om d) (.Om c)) : (Tm.Om d) ≠ .Om c := fun e => by
  rw [e] at h
  exact Lt.irrefl _ h

theorem genPsi0 (π : Tm) : GenPsi (.psi0 π) .zero π := Or.inl ⟨rfl, rfl⟩

theorem oadd_zero_zero {y : Tm} (hy : WNF y) : oadd .zero y = y := zero_oadd hy

/-- 近似の族から `ω` 型の不変量 -/
theorem natInv_of_pack {ξ π X P : Tm} {pre rest : List Tm} {R : Tm} {s : SeqD}
    (pk : AppPack ξ π X P pre rest R s) (hF : ∀ n f, f ∈ fr π X → Lt f (s.nat n))
    (hrest : ∀ n s', s' ∈ rest → ∀ w, w ∈ subs s' → Lt w (.Psi .zero π X) → Lt w (s.nat n))
    (hPF : WNF P) (hξF : WNF ξ) (hPt : Lt P (.Psi .zero π X)) (hξt : Lt ξ (.Psi .zero π X))
    (hPC : ∀ g d, WNF g → WNF d → inC (.Psi .zero π X) g d = true → inC P g d = true)
    (hU : ∀ g d, WNF g → WNF d → inC (.Psi .zero π X) g d = true → inC ξ g d = true) :
    NatInv (.Psi .zero π X) s := by
  obtain ⟨P', x, -, he, A, hx0, hgap⟩ := pk.ex
  refine ⟨pk.ub hPF hξF hPt hξt hPC hU, fun n v hv hne hlt => ?_⟩
  rw [he n]
  exact gap_point (A n) (hx0 n) (hgap n) (fun f hf => by rw [← he n]; exact hF n f hf)
    (fun s' hs' w hw h => by rw [← he n]; exact hrest n s' hs' w hw h) hv hne hlt

theorem app_big_eq {ξ π P c ceil η : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ π) :
    (SeqD.app ceil g pre R r P c).big η = .Psi ξ π (approx pre P (oadd c (r.big η))) := by
  show g.ap (combine g pre c P (r.big η)) = _
  rw [hg.comb, hg.ap]

/-- 共終数が目標未満の加数の、`t` の不変量 -/
theorem bigInv_app {ξ π σ X P c ceil : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ π) (ht : WNF (.Psi .zero π X)) (hsum : summands X = pre ++ R :: rest)
    (S : SeedHyp π X P R) (adj : AdjHyp π R c)
    (hV : ∀ q, argR? π = some q → Lt q (approx pre P (oadd c (r.big .zero))))
    (hI : IdxHyp ξ π X) (hξ : Le ξ (ofSummands pre))
    (hdc : Lt σ π) (hσ0 : Lt .zero σ) (hR : BigInv R σ r)
    (hF : ∀ η, WNF η → Lt η σ → ∀ f, f ∈ fr π X →
      Lt f (.Psi ξ π (approx pre P (oadd c (r.big η)))))
    (hrest : ∀ η, WNF η → Lt η σ → ∀ s', s' ∈ rest → ∀ w, w ∈ subs s' →
      Lt w (.Psi .zero π X) → Lt w (.Psi ξ π (approx pre P (oadd c (r.big η)))))
    (hPt : Lt P (.Psi .zero π X)) (hξt : Lt ξ (.Psi .zero π X))
    (hPC : ∀ g d, WNF g → WNF d → inC (.Psi .zero π X) g d = true → inC P g d = true)
    (hU : ∀ g d, WNF g → WNF d → inC (.Psi .zero π X) g d = true → inC ξ g d = true) :
    BigInv (.Psi .zero π X) σ (.app ceil g pre R r P c) := by
  have A := fun {η : Tm} (hη : WNF η) (hησ : Lt η σ) =>
    approx1_big ht hsum S adj hV hI hξ hdc hσ0 hR hη hησ
  have hRF : WNF R := (A WNF.zero hσ0).hRF
  have hyF : ∀ η, WNF η → Lt η σ → WNF (r.big η) := fun η hη hησ => (hR.1.good.1 η hη hησ).1
  have hx0 : ∀ η, WNF η → Lt η σ → oadd c (r.big η) = .zero → ∀ v, v ∈ subs R → v = R :=
    fun η hη hησ => adj_zero adj.hF (hyF η hη hησ) (hR.1.pos η hη hησ)
  have hg' : ∀ η, WNF η → Lt η σ → ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v (oadd c (r.big η)) :=
    fun η hη hησ => adj_gap adj.hF (hyF η hη hησ) hRF (hR.2 η hη hησ)
  have hσt : ∀ η, WNF η → Lt η σ → Lt σ (.Psi ξ π (approx pre P (oadd c (r.big η)))) := by
    intro η hη hησ
    have H := A hη hησ
    have hσs : σ ∈ subs R := hR.1.hσs
    have hRt : inC R X (.Psi .zero π X) = true :=
      inC_of_fr_lt hRF H.hπF ht H.hX H.hX (inC_of_mem_summands H.hX ht.psi.Ca H.hRm)
        (Or.inr (lt_psi_targetY ht)) (Or.inl rfl) fun w hw =>
          FWOrder.k2 ht w ((mem_fr_iff H.hX).mpr ⟨R, H.hRm, hw⟩)
    exact H.lt_of_sub_summand (hx0 η hη hησ) (hg' η hη hησ) (hF η hη hησ) (Or.inr rfl) hσs
      (coll_psiY ht σ hR.1.hσF (hR.1.hσC X _ H.hX ht hRt) hdc)
  refine ⟨bigUB_app hg ht hsum S adj hV hI hξ hdc hσ0 hR hσt hPt hξt hPC hU, fun η hη hησ v hv hne hlt => ?_⟩
  rw [app_big_eq hg]
  exact gap_point (A hη hησ) (hx0 η hη hησ) (hg' η hη hησ) (hF η hη hησ) (hrest η hη hησ) hv hne hlt

end RTKA.Fund
