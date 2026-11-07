import Compact.FS.XiG

/-! 目標の族の閉包の枠組み。

`t = Ψ^0_π(X)` の列の項が、`π` より上の目標 `τ` への崩壊になる場合を扱う。

* `Chain π ρ`：`ρ` は `π` の目標をたどって現れる（`π` 自身も含む）。
* `Ad π X g d`：`t ∈ C(g, d)`（`t` は `d` 以上）か `(g, d) = (X, t)`。この `(g, d)` の上で列の項の上界を示せば、
  `t` の上界と、`y ∈ C(X, t)` から `y < t` が出る。
* `MCtx`：`mahloSeq τ τf ceil Y ys μ ms P` の文脈。`T` は `y < π` を示すのに使う `(g, d)` の組（鎖の各段）。
* 種の近似 `Pack`（仮想的な崩壊 `Ψ^0_τ(Y + 1)` についての族）から `t` の不変量へ（`Pack.lift`）。 -/

namespace RTKA.Fund

open Tm W

/-- 目標の鎖 -/
inductive Chain : Tm → Tm → Prop
  | refl (π : Tm) : Chain π π
  | step {ζ κ γ ρ : Tm} : Chain κ ρ → Chain (.Psi ζ κ γ) ρ

theorem Chain.wnf {π ρ : Tm} (hc : Chain π ρ) : WNF π → WNF ρ := by
  induction hc with
  | refl _ => exact id
  | step _ ih => exact fun hπ => ih hπ.psi.piF

/-- 鎖の上では成分が移る -/
theorem Chain.up {π ρ : Tm} (hc : Chain π ρ) : ∀ {g d : Tm}, WNF π → WNF d → ¬ Lt π d →
    inC π g d = true → inC ρ g d = true ∧ ¬ Lt ρ d := by
  induction hc with
  | refl _ => exact fun _ _ h h' => ⟨h', h⟩
  | @step ζ κ γ ρ _ ih =>
    intro g d hπ hd hn h
    have hP := hπ.psi
    rcases inC_psi_iff.mp h with h' | ⟨hk, -, -, -⟩
    · exact absurd h' hn
    · exact ih hP.piF hd (fun h2 => hn (lt_transY hπ hP.piF hd (lt_psi_targetY hπ) h2)) hk

theorem Chain.le {π ρ : Tm} (hc : Chain π ρ) : WNF π → Le π ρ := by
  induction hc with
  | refl _ => exact fun _ => Or.inl rfl
  | @step ζ κ γ ρ h ih =>
    intro hπ
    have hP := hπ.psi
    exact Or.inr (lt_of_lt_of_leY hπ hP.piF (h.wnf hP.piF) (lt_psi_targetY hπ) (ih hP.piF))

theorem Chain.lev_eq {π ρ : Tm} (hc : Chain π ρ) : lev π = lev ρ := by
  induction hc with
  | refl _ => rfl
  | step _ ih => exact ih

/-- 鎖の上の項未満で、鎖の各段の成分に入る項は `π` 未満 -/
theorem Chain.lt_base {π ρ y : Tm} (hc : Chain π ρ) : WNF π → WNF y → Lt y ρ →
    (∀ g d, WNF g → WNF d → Le π d → ¬ Lt ρ d → inC ρ g d = true → inC y g d = true) → Lt y π := by
  induction hc with
  | refl _ => exact fun _ _ h _ => h
  | @step ζ κ γ ρ h ih =>
    intro hπ hy hyρ hC
    have hP := hπ.psi
    have hκ : Lt y κ := ih hP.piF hy hyρ fun g d hg hd hle hn hC' =>
      hC g d hg hd (Or.inr (lt_of_lt_of_leY hπ hP.piF hd (lt_psi_targetY hπ) hle)) hn hC'
    have hu := h.up hP.piF hπ (Lt.asymmY hπ hP.piF (lt_psi_targetY hπ))
      (inC_tgt_of_k2t hπ fun w hw => FWOrder.k2t hπ w hw)
    exact coll_psiY hπ y hy (hC γ _ hP.aF hπ (Or.inl rfl) hu.2 hu.1) hκ

/-- `t ∈ C(g, d)`（`t` は `d` 以上）か `(g, d) = (X, t)` -/
def Ad (π X g d : Tm) : Prop :=
  WNF g ∧ WNF d ∧ ((inC (.Psi .zero π X) g d = true ∧ ¬ Lt (.Psi .zero π X) d) ∨
    (g = X ∧ d = .Psi .zero π X))

theorem Ad.self {π X : Tm} (ht : WNF (.Psi .zero π X)) : Ad π X X (.Psi .zero π X) :=
  ⟨ht.psi.aF, ht, Or.inr ⟨rfl, rfl⟩⟩

theorem Ad.comp {π X g d : Tm} (ht : WNF (.Psi .zero π X)) (h : Ad π X g d) :
    Le d (.Psi .zero π X) ∧ inC π g d = true ∧ inC X g d = true ∧ Le X g := by
  obtain ⟨hg, hd, ⟨h1, h2⟩ | ⟨rfl, rfl⟩⟩ := h
  · obtain ⟨-, hk, hδ, hlt⟩ := comp_of_inC ht hd h2 h1
    exact ⟨le_of_not_ltY ht hd h2, hk, hδ, Or.inr hlt⟩
  · have hX := ht.psi.aF
    have hπF := ht.psi.piF
    exact ⟨Or.inl rfl, inC_tgt_of_k2t ht fun w hw => FWOrder.k2t ht w hw,
      inC_of_fr_lt hX hπF ht hX hX ht.psi.Ca (Or.inr (lt_psi_targetY ht)) (Or.inl rfl)
        fun w hw => FWOrder.k2 ht w hw, Or.inl rfl⟩

/-- 鎖の上の項の成分 -/
theorem Ad.tgt {π X ρ g d : Tm} (ht : WNF (.Psi .zero π X)) (h : Ad π X g d) (hc : Chain π ρ) :
    inC ρ g d = true ∧ ¬ Lt ρ d := by
  obtain ⟨hle, hk, -, -⟩ := h.comp ht
  exact hc.up ht.psi.piF h.2.1
    (fun h2 => not_lt_of_leY h.2.1 ht.psi.piF (le_transY h.2.1 ht ht.psi.piF hle
      (Or.inr (lt_psi_targetY ht))) h2) hk

/-- 種の上界 -/
theorem Ad.seed {π X P g d : Tm} (h : Ad π X g d) (hPF : WNF P) (hPt : Lt P (.Psi .zero π X))
    (hPC : ∀ g d, WNF g → WNF d → inC (.Psi .zero π X) g d = true → inC P g d = true) :
    inC P g d = true := by
  obtain ⟨hg, hd, ⟨h1, -⟩ | ⟨rfl, rfl⟩⟩ := h
  · exact hPC g d hg hd h1
  · exact WFY.inC_of_ltY _ hPF hd hPt

/-- `t` の真の部分項で `t` 未満のものは `y` 未満 -/
def Gp (t y : Tm) : Prop := ∀ v, v ∈ subs t → v ≠ t → Lt v t → Lt v y

/-- `π` 未満で、`Ad` の組の成分に入る項は `t` 未満 -/
theorem lt_t_of {π X y : Tm} (ht : WNF (.Psi .zero π X)) (hy : WNF y) (hπ : Lt y π)
    (hA : ∀ g d, Ad π X g d → inC y g d = true) : Lt y (.Psi .zero π X) :=
  coll_psiY ht y hy (hA X _ (Ad.self ht)) hπ

/-- `ω` 型の列の不変量への持ち上げ -/
theorem natInv_lift {π X t' : Tm} {s : SeqD} (ht : WNF (.Psi .zero π X)) (L : NatL t' s)
    (hlt : ∀ n, Lt (s.nat n) π) (hA : ∀ g d n, Ad π X g d → inC (s.nat n) g d = true)
    (hG : ∀ n, Gp (.Psi .zero π X) (s.nat n)) : NatInv (.Psi .zero π X) s := by
  have hF := fun n => (L.good n).1
  have hL : NatL (.Psi .zero π X) s := L.lower fun n => lt_t_of ht (hF n) (hlt n) fun g d h => hA g d n h
  refine ⟨hL.toUB fun g d n hg hd h => ?_, fun n v hv hne hl => hG n v hv hne hl⟩
  by_cases hdt : Lt (.Psi .zero π X) d
  · exact WFY.inC_of_ltY _ (hF n) hd (lt_transY (hF n) ht hd (hL.good n).2.1 hdt)
  · exact hA g d n ⟨hg, hd, Or.inl ⟨h, hdt⟩⟩

/-- `mahloSeq τ τf ceil Y ys μ ms P` の文脈 -/
structure MCtx (π X τ Y μ : Tm) (T : Tm → Tm → Prop) : Prop where
  ht : WNF (.Psi .zero π X)
  /-- 仮想的な崩壊 -/
  hv : WNF (.Psi .zero τ (sc Y))
  hYC : inC Y Y τ = true
  hτY : ∀ r, argR? τ = some r → Lt r Y
  hle : Le π τ
  hlev : lev π = lev τ
  hYF : WNF Y
  hYm : ∀ u, u ∈ summands Y → u ∈ subs (.Psi .zero π X)
  hμF : WNF μ
  hμY : μ ≠ .one → Le μ Y
  hμm : Le μ (mi τ)
  hμ1 : inC μ Y τ = true
  hμ2 : inC μ (mi τ) τ = true
  hμσ : ∀ σ, WNF σ → Le π σ → inC μ μ σ = true
  comp : ∀ g d, Ad π X g d → Le d τ ∧ inC τ g d = true ∧ inC Y g d = true ∧ Lt Y g ∧ inC μ g d = true
  hT : ∀ g d, T g d → WNF g ∧ WNF d ∧ Le π d ∧ Le d τ ∧ inC τ g d = true ∧ inC Y g d = true ∧
    Le Y g ∧ inC μ g d = true
  ltT : ∀ y, WNF y → Lt y τ → (∀ g d, T g d → inC y g d = true) → Lt y π
  ltI : ∀ z, WNF (.Psi z τ Y) → Lt z μ → (∀ g d, T g d → inC z g d = true) → Lt (.Psi z τ Y) π

namespace MCtx

variable {π X τ Y μ : Tm} {T : Tm → Tm → Prop}

theorem hτF (C : MCtx π X τ Y μ T) : WNF τ := C.hv.psi.piF
theorem hπF (C : MCtx π X τ Y μ T) : WNF π := C.ht.psi.piF
theorem hXF (C : MCtx π X τ Y μ T) : WNF X := C.ht.psi.aF
theorem hτt (C : MCtx π X τ Y μ T) : IsTgt τ := C.hv.psi.tgt

/-- `Ψ^0_τ(Y)` は標準形 -/
theorem hw0 (C : MCtx π X τ Y μ T) : WNF (.Psi .zero τ Y) :=
  wnf_psi0 C.hτF C.hτt C.hYF C.hYC C.hτY

/-- `K_m` が `π` 以上なら `τ` 未満でない -/
theorem τK (C : MCtx π X τ Y μ T) (m : Nat) (hm : 1 ≤ m) (h : ¬ Lt (.K m) π) : Lt τ (.K m) := by
  rcases triY C.hτF (WNF.K' hm) with h' | h' | h'
  · exact h'
  · exact absurd h' (IsTgt.ne_K C.hτt m)
  · exfalso
    apply h
    have hl : lev (Tm.K m) ≤ lev τ := lev_le_of_lt_gen h'
    rw [← C.hlev] at hl
    have hπt := C.ht.psi.tgt
    rcases hπt with ⟨c, e, -⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, -⟩ <;> rw [e] at hl ⊢ <;>
      exact K_lt_of_lev (by rw [← e]; exact C.hπF) rfl rfl hl

end MCtx

theorem sc_ne_zero (Y : Tm) : succT Y ≠ .zero := by
  intro e
  have := lt_succT Y
  rw [e] at this
  exact not_lt_zero _ this

/-- 分割された `Y + 1` の加数 -/
theorem summands_sc {Y R : Tm} {pre rest₀ : List Tm} (hsum : summands Y = pre ++ R :: rest₀) :
    summands (sc Y) = pre ++ R :: (rest₀ ++ [.one]) := by
  show summands (succT Y) = _
  rw [summands_succT, hsum]
  simp

/-- 種の近似 `Pack`（仮想的な崩壊 `Ψ^0_τ(Y + 1)`）から `t` の不変量へ -/
theorem Pack.lift {ξ τ P π X Y μ R : Tm} {T : Tm → Tm → Prop} {pre rest₀ : List Tm} {r s : SeqD}
    (C : MCtx π X τ Y μ T) (hsumY : summands Y = pre ++ R :: rest₀)
    (pk : Pack ξ τ (sc Y) P pre (rest₀ ++ [.one]) R π r s)
    (hPF : WNF P) (hPπ : Lt P π) (hPA : ∀ g d, Ad π X g d → inC P g d = true)
    (hξF : WNF ξ) (hξπ : Lt ξ π) (hξA : ∀ g d, Ad π X g d → inC ξ g d = true)
    (hG : ∀ y, InSeq s y → Gp (.Psi .zero π X) y) :
    SeqI (.Psi .zero π X) s := by
  have ht := C.ht
  have hY := C.hYF
  have hYC := C.hYC
  have hτF := C.hτF
  have hRmY : R ∈ summands Y := by
    rw [hsumY]
    exact List.mem_append_right _ List.mem_cons_self
  have hTY := top_le hY hsumY
  have hN : NFL (pre ++ R :: rest₀) := hsumY ▸ nfl_summands hY
  have hRF : WNF R := (hN.1 R (List.mem_append_right _ List.mem_cons_self)).1
  have hTF : WNF (oadd (ofSummands pre) R) := wnf_oadd (wnf_ofSummands (nfl_append_left hN)) hRF
  rcases pk with ⟨pk, hdt⟩ | ⟨σ, D⟩
  · have key : ∀ g d n, WNF g → WNF d → Le d τ → inC τ g d = true → inC Y g d = true → Le Y g →
        inC P g d = true → inC ξ g d = true → inC (s.nat n) g d = true :=
      fun g d n hg hd hle hk hYg hgY hP hz => pk.ubC g d n hg hd hle hk (inC_of_mem_summands hY hYg hRmY)
        (inC_pre_of_X hY hsumY hYg) (le_transY hTF hY hg hTY hgY) hP hz
    have hF := fun n => (pk.L.good n).1
    have hτlt : ∀ n, Lt (s.nat n) τ := fun n => (pk.L.good n).2.1
    have hA : ∀ g d n, Ad π X g d → inC (s.nat n) g d = true := fun g d n h => by
      obtain ⟨h1, h2, h3, h4, -⟩ := C.comp g d h
      exact key g d n h.1 h.2.1 h1 h2 h3 (Or.inr h4) (hPA g d h) (hξA g d h)
    have hlt : ∀ n, Lt (s.nat n) π := fun n => C.ltT _ (hF n) (hτlt n) fun g d h => by
      obtain ⟨hg, hd, hπd, h1, h2, h3, h4, -⟩ := C.hT g d h
      exact key g d n hg hd h1 h2 h3 h4 (WFY.inC_of_ltY _ hPF hd (lt_of_lt_of_leY hPF C.hπF hd hPπ hπd))
        (WFY.inC_of_ltY _ hξF hd (lt_of_lt_of_leY hξF C.hπF hd hξπ hπd))
    exact seqI_nat hdt (natInv_lift ht pk.L hlt hA fun n => hG _ (Or.inl ⟨hdt, n, rfl⟩))
  · obtain ⟨g₀, c, hg₀, rfl, adj, hV⟩ := D.ex
    have hσ0 : Lt .zero σ := zero_lt D.hreg.ne_zero
    have hσF := D.hB.1.hσF
    have hd' := app_dom_big_lt (P := P) (c := c) (g := g₀) (pre := pre) (R := R) D.hd (ltB_iff.mpr D.hσc)
    have hRX : inC R X (.Psi .zero π X) = true :=
      inC_of_mem_summands hY (C.comp _ _ (Ad.self ht)).2.2.1 hRmY
    have hσt : Lt σ (.Psi .zero π X) := coll_psiY ht σ hσF (D.hB.1.hσC X _ C.hXF ht hRX) D.hσc
    have hσs : σ ∈ subs (.Psi .zero π X) := subs_trans (C.hYm R hRmY) D.hB.1.hσs
    have hS : ∀ η, WNF η → Lt η σ → InSeq (.app π g₀ pre R r P c)
        (.Psi ξ τ (approx pre P (oadd c (r.big η)))) := fun η hη hησ =>
      Or.inr ⟨σ, η, hd', hη, hησ, (app_big_eq hg₀).symm⟩
    have B := bigPack_app (ceil := π) hg₀ D.ht D.hsum D.S adj hV D.hI D.hξ D.hσπ hσ0 D.hB
      fun η hη hησ => hG _ (hS η hη hησ) σ hσs hσt.ne hσt
    have key : ∀ g d η, WNF g → WNF d → WNF η → Lt η σ → Lt .zero g → BigOK σ g d → Le d τ →
        inC τ g d = true → inC Y g d = true → Le Y g → inC P g d = true → inC ξ g d = true →
        inC η g d = true → inC ((SeqD.app π g₀ pre R r P c).big η) g d = true :=
      fun g d η hg hd hη hησ h0 hok hle hk hYg hgY hP hz hηC =>
        B.ubC g d η hg hd hη hησ h0 hok hle hk (inC_of_mem_summands hY hYg hRmY)
          (inC_pre_of_X hY hsumY hYg) (le_transY hTF hY hg hTY hgY) hP hz hηC
    have hF := fun η hη hησ => (B.good.1 η hη hησ).1
    have hY0 : Lt .zero Y := lt_of_lt_of_leY WNF.zero hRF hY (zero_lt (by
      intro e
      have := (hN.1 R (List.mem_append_right _ List.mem_cons_self)).2
      rw [e] at this
      cases this)) (by
        have := le_ofSummands_of_mem (nfl_summands hY) hRmY
        rwa [ofSummands_summands Y hY] at this)
    have hlτ : ∀ η, WNF η → Lt η σ → Lt ((SeqD.app π g₀ pre R r P c).big η) τ := fun η hη hησ =>
      (B.good.1 η hη hησ).2
    have hηπ : ∀ {η : Tm}, WNF η → Lt η σ → Lt η π := fun hη hησ => lt_transY hη hσF C.hπF hησ D.hσc
    have hlt : ∀ η, WNF η → Lt η σ → Lt ((SeqD.app π g₀ pre R r P c).big η) π := fun η hη hησ =>
      C.ltT _ (hF η hη hησ) (hlτ η hη hησ) fun g d h => by
        obtain ⟨hg, hd, hπd, h1, h2, h3, h4, -⟩ := C.hT g d h
        exact key g d η hg hd hη hησ (lt_of_lt_of_leY WNF.zero hY hg hY0 h4)
          (Or.inl (Or.inr (lt_of_lt_of_leY hσF C.hπF hd D.hσc hπd))) h1 h2 h3 h4
          (WFY.inC_of_ltY _ hPF hd (lt_of_lt_of_leY hPF C.hπF hd hPπ hπd))
          (WFY.inC_of_ltY _ hξF hd (lt_of_lt_of_leY hξF C.hπF hd hξπ hπd))
          (WFY.inC_of_ltY _ hη hd (lt_of_lt_of_leY hη C.hπF hd (hηπ hη hησ) hπd))
    have hA : ∀ g d η, Ad π X g d → WNF η → Lt η σ → BigOK σ g d → inC η g d = true →
        inC ((SeqD.app π g₀ pre R r P c).big η) g d = true := fun g d η h hη hησ hok hηC => by
      obtain ⟨h1, h2, h3, h4, -⟩ := C.comp g d h
      exact key g d η h.1 h.2.1 hη hησ (lt_transY WNF.zero hY h.1 hY0 h4) hok h1 h2 h3 (Or.inr h4)
        (hPA g d h) (hξA g d h) hηC
    have hltt : ∀ η, WNF η → Lt η σ → Lt ((SeqD.app π g₀ pre R r P c).big η) (.Psi .zero π X) :=
      fun η hη hησ => coll_psiY ht _ (hF η hη hησ)
        (hA X _ η (Ad.self ht) hη hησ (Or.inl (Or.inr hσt))
          (WFY.inC_of_ltY _ hη ht (lt_transY hη hσF ht hησ hσt))) (hlt η hη hησ)
    refine seqI_big hd' D.hreg ⟨?_, fun η hη hησ v hv hne hl =>
      hG _ (Or.inr ⟨σ, η, hd', hη, hησ, rfl⟩) v hv hne hl⟩
    refine
      { good := ⟨fun η hη hησ => ⟨hF η hη hησ, hltt η hη hησ⟩, B.good.2⟩
        pos := fun η hη hησ e => absurd e (B.pos η hη hησ)
        hσF := hσF
        hσle := Or.inr hσt
        hσs := hσs
        hσC := fun g' e hg' he' h => ?_
        ub := fun g' e η hg' he' hη hησ h0 hok h hηC => ?_
        ub2 := B.ub2
        lo := B.lo
        ns := fun _ η hη hησ hs => B.ns η hη hησ hs
        lbK := fun m e _ η hη hησ => by
          obtain ⟨A, hA⟩ := B.psi η
          have hF' := hF η hη hησ
          rw [hA] at hF' ⊢
          exact Or.inr (K_lt_psi hF' (e ▸ D.hσπ))
        lbS := fun m e h η hη hησ => by
          obtain ⟨A, hA⟩ := B.psi η
          have hF' := hF η hη hησ
          rw [hA] at hF' ⊢
          have hm : 1 ≤ m := (e ▸ hσF : WNF (.K m)).k
          exact Or.inr (succK_lt_psi hm hF' (lt_of_lt_of_leY (WNF.succK hm) C.hπF hτF
            (lt_transY (WNF.succK hm) ht C.hπF h (lt_psi_targetY ht)) C.hle)) }
    · by_cases hdt : Lt (.Psi .zero π X) e
      · exact WFY.inC_of_ltY _ hσF he' (lt_transY hσF ht he' hσt hdt)
      · exact D.hB.1.hσC g' e hg' he' (inC_of_mem_summands hY
          (C.comp g' e ⟨hg', he', Or.inl ⟨h, hdt⟩⟩).2.2.1 hRmY)
    · by_cases hdt : Lt (.Psi .zero π X) e
      · exact WFY.inC_of_ltY _ (hF η hη hησ) he' (lt_transY (hF η hη hησ) ht he' (hltt η hη hησ) hdt)
      · exact hA g' e η ⟨hg', he', Or.inl ⟨h, hdt⟩⟩ hη hησ hok hηC

/-! ### `Ψ^z_τ(Y)` の族 -/

/-- 近似の引数の部品 -/
theorem inC_approx_parts {pre rest : List Tm} {R x P g d : Tm} (hN : NFL (pre ++ R :: rest)) (hx : WNF x)
    (hP : WNF P) (hyR : Lt (nsum x P) R) (h : inC (approx pre P x) g d = true) :
    inC (ofSummands pre) g d = true ∧ inC x g d = true ∧ inC P g d = true := by
  have hy := wnf_nsum hx hP
  have hA : WNF (approx pre P x) := wnf_oadd (wnf_ofSummands (nfl_append_left hN)) hy
  have hmem : ∀ s, s ∈ pre ++ summands (nsum x P) → inC s g d = true := by
    intro s hs
    refine inC_of_mem_summands hA h ?_
    show s ∈ summands (oadd (ofSummands pre) (nsum x P))
    rw [summands_oadd_pre (nfl_append_left hN) hy (head_le_pre hN hy hyR)]
    exact hs
  have hyC : inC (nsum x P) g d = true :=
    (inC_iff_summands hy).mpr fun s hs => hmem s (List.mem_append_right _ hs)
  refine ⟨?_, inC_nsum_left hx hP hyC, inC_nsum_right hx hP hyC⟩
  rw [inC_ofSummands]
  exact fun s hs => hmem s (List.mem_append_left _ hs)

/-- `Ψ^z_τ(Y)`（`z = pre ⊕ (x # P)`、`pre ++ R :: rest` は `μ` の加数）の族の仮定 -/
structure IdxG (τ Y μ P : Tm) (pre rest : List Tm) (R : Tm) : Prop where
  hv : WNF (.Psi .zero τ (sc Y))
  hYF : WNF Y
  hYC : inC Y Y τ = true
  hτY : ∀ r, argR? τ = some r → Lt r Y
  hμF : WNF μ
  hsum : summands μ = pre ++ R :: rest
  hμY : Le μ Y
  hμm : Le μ (mi τ)
  hμ1 : inC μ Y τ = true
  hμ2 : inC μ (mi τ) τ = true
  hPF : WNF P
  hPR : Lt P R
  hPτ : Lt P τ

namespace IdxG

variable {τ Y μ P : Tm} {pre rest : List Tm} {R : Tm}

theorem hτF (G : IdxG τ Y μ P pre rest R) : WNF τ := G.hv.psi.piF
theorem hτt (G : IdxG τ Y μ P pre rest R) : IsTgt τ := G.hv.psi.tgt
theorem hN (G : IdxG τ Y μ P pre rest R) : NFL (pre ++ R :: rest) := G.hsum ▸ nfl_summands G.hμF
theorem hRF (G : IdxG τ Y μ P pre rest R) : WNF R :=
  (G.hN.1 R (List.mem_append_right _ List.mem_cons_self)).1
theorem hRp (G : IdxG τ Y μ P pre rest R) : isPrincipal R = true :=
  (G.hN.1 R (List.mem_append_right _ List.mem_cons_self)).2
theorem hpreF (G : IdxG τ Y μ P pre rest R) : WNF (ofSummands pre) :=
  wnf_ofSummands (nfl_append_left G.hN)
theorem hRm (G : IdxG τ Y μ P pre rest R) : R ∈ summands μ := by
  rw [G.hsum]
  exact List.mem_append_right _ List.mem_cons_self
theorem hTF (G : IdxG τ Y μ P pre rest R) : WNF (oadd (ofSummands pre) R) := wnf_oadd G.hpreF G.hRF
theorem hTμ (G : IdxG τ Y μ P pre rest R) : Le (oadd (ofSummands pre) R) μ := top_le G.hμF G.hsum
theorem hTY (G : IdxG τ Y μ P pre rest R) : Le (oadd (ofSummands pre) R) Y :=
  le_transY G.hTF G.hμF G.hYF G.hTμ G.hμY
theorem hTm (G : IdxG τ Y μ P pre rest R) : Le (oadd (ofSummands pre) R) (mi τ) :=
  le_transY G.hTF G.hμF (WFY.WNF.mi G.hτF) G.hTμ G.hμm
theorem hτC (G : IdxG τ Y μ P pre rest R) : inC τ Y τ = true := inC_tgt G.hτF G.hτt G.hYF G.hτY
theorem hμe (G : IdxG τ Y μ P pre rest R) : μ = ofSummands (pre ++ R :: rest) := by
  rw [← G.hsum, ofSummands_summands μ G.hμF]

theorem parts (G : IdxG τ Y μ P pre rest R) {g d : Tm} (h : inC μ g d = true) :
    inC R g d = true ∧ inC (ofSummands pre) g d = true :=
  ⟨inC_of_mem_summands G.hμF h G.hRm, inC_pre_of_X G.hμF G.hsum h⟩

theorem hyF (G : IdxG τ Y μ P pre rest R) {x : Tm} (hx : WNF x) : WNF (nsum x P) := wnf_nsum hx G.hPF
theorem hyR (G : IdxG τ Y μ P pre rest R) {x : Tm} (hx : WNF x) (hxR : Lt x R) : Lt (nsum x P) R :=
  nsum_lt_prin hx G.hPF G.hRp hxR G.hPR
theorem hAF (G : IdxG τ Y μ P pre rest R) {x : Tm} (hx : WNF x) : WNF (approx pre P x) :=
  wnf_oadd G.hpreF (G.hyF hx)
theorem hAT (G : IdxG τ Y μ P pre rest R) {x : Tm} (hx : WNF x) (hxR : Lt x R) :
    Lt (approx pre P x) (oadd (ofSummands pre) R) :=
  oadd_lt_oadd G.hpreF (G.hyF hx) G.hRF (G.hyR hx hxR)

theorem hAlt (G : IdxG τ Y μ P pre rest R) {x U : Tm} (hx : WNF x) (hxR : Lt x R) (hU : WNF U)
    (hTU : Le (oadd (ofSummands pre) R) U) : Lt (approx pre P x) U :=
  lt_of_lt_of_leY (G.hAF hx) G.hTF hU (G.hAT hx hxR) hTU

theorem inC_A (G : IdxG τ Y μ P pre rest R) {x g d : Tm} (hx : WNF x)
    (hpre : inC (ofSummands pre) g d = true) (hxC : inC x g d = true) (hP : inC P g d = true) :
    inC (approx pre P x) g d = true :=
  inC_oadd G.hpreF (G.hyF hx) hpre (inC_nsum hx G.hPF hxC hP)

/-- 標準形 -/
theorem nf (G : IdxG τ Y μ P pre rest R) {x : Tm} (hx : WNF x) (hxR : Lt x R)
    (h1 : inC x Y τ = true) (h2 : inC x (mi τ) τ = true) : WNF (.Psi (approx pre P x) τ Y) :=
  WNF.mk_psi {
    tgt := G.hτt
    xiF := G.hAF hx
    piF := G.hτF
    aF := G.hYF
    le := ne_gt_of_le (Or.inr (G.hAlt hx hxR G.hYF G.hTY))
    Ca := G.hYC
    Cxi := G.inC_A hx (G.parts G.hμ1).2 h1 (WFY.inC_of_ltY _ G.hPF G.hτF G.hPτ)
    Cpi := G.hτC
    mlt := G.hAlt hx hxR (WFY.WNF.mi G.hτF) G.hTm
    mC := G.inC_A hx (G.parts G.hμ2).2 h2 (WFY.inC_of_ltY _ G.hPF G.hτF G.hPτ) }

/-- 2 点の比較 -/
theorem lt2 (G : IdxG τ Y μ P pre rest R) {x x' : Tm} (hx : WNF x) (hx' : WNF x') (hxR' : Lt x' R)
    (hxx : Lt x x') (hy : WNF (.Psi (approx pre P x) τ Y)) (hy' : WNF (.Psi (approx pre P x') τ Y))
    (hS : inC x' Y (.Psi (approx pre P x') τ Y) = true →
      inC (ofSummands pre) Y (.Psi (approx pre P x') τ Y) = true →
      inC P Y (.Psi (approx pre P x') τ Y) = true → inC x Y (.Psi (approx pre P x') τ Y) = true) :
    Lt (.Psi (approx pre P x) τ Y) (.Psi (approx pre P x') τ Y) := by
  have hAA := approx_mono G.hpreF hx hx' G.hPF hxx
  have hne : Tm.Psi (approx pre P x) τ Y ≠ .Psi (approx pre P x') τ Y := fun e =>
    hAA.ne (Tm.Psi.inj e).1
  have hP' := hy'.psi
  have hC' : inC (approx pre P x') Y (.Psi (approx pre P x') τ Y) = true :=
    inC_of_fr_lt hP'.xiF G.hτF hy' G.hYF G.hYF hP'.Cxi (Or.inr (lt_psi_targetY hy')) (Or.inl rfl)
      fun w hw => FWOrder.k2s hy' w hw
  obtain ⟨h1, h2, h3⟩ := inC_approx_parts G.hN hx' G.hPF (G.hyR hx' hxR') hC'
  exact (lt_psi_psiY rfl hne).mpr (Or.inr ⟨lt_psi_targetY hy', lt_psi_targetY hy, Or.inr (Or.inr
    (Or.inl ⟨cmp_self _, rfl, hAA, G.inC_A hx h1 (hS h2 h1 h3) h3⟩))⟩)

/-- 2 点の上界 -/
theorem ub2 (G : IdxG τ Y μ P pre rest R) {x x' g d : Tm} (hx : WNF x) (hx' : WNF x') (hxR' : Lt x' R)
    (hxx : Lt x x') (hy : WNF (.Psi (approx pre P x) τ Y)) (hy' : WNF (.Psi (approx pre P x') τ Y))
    (hmono : Lt (.Psi (approx pre P x) τ Y) (.Psi (approx pre P x') τ Y)) (hg : WNF g) (hd : WNF d)
    (hS : Le d τ → inC x' g d = true → inC τ g d = true → inC (ofSummands pre) g d = true →
      inC P g d = true → Lt (approx pre P x) g → inC x g d = true)
    (h : inC (.Psi (approx pre P x') τ Y) g d = true) :
    inC (.Psi (approx pre P x) τ Y) g d = true := by
  by_cases hdy : Lt (.Psi (approx pre P x') τ Y) d
  · exact WFY.inC_of_ltY _ hy hd (lt_transY hy hy' hd hmono hdy)
  rcases inC_psi_iff.mp h with h' | ⟨hk, hz, hδ, hlt⟩
  · exact absurd h' hdy
  · have hdτ : Le d τ := le_transY hd hy' G.hτF (le_of_not_ltY hy' hd hdy) (Or.inr (lt_psi_targetY hy'))
    obtain ⟨h1, h2, h3⟩ := inC_approx_parts G.hN hx' G.hPF (G.hyR hx' hxR') hz
    have hA' : Lt (approx pre P x') Y := G.hAlt hx' hxR' G.hYF G.hTY
    have hAg : Lt (approx pre P x) g :=
      lt_transY (G.hAF hx) G.hYF hg (lt_transY (G.hAF hx) (G.hAF hx') G.hYF
        (approx_mono G.hpreF hx hx' G.hPF hxx) hA') hlt
    exact inC_psi_iff.mpr (Or.inr ⟨hk, G.inC_A hx h1 (hS hdτ h2 hk h1 h3 hAg) h3, hδ, hlt⟩)

end IdxG

/-- 共終数が正則項の列の不変量への持ち上げ -/
theorem bigInv_lift {π X σ : Tm} {s : SeqD} (ht : WNF (.Psi .zero π X)) (hX0 : Lt .zero X) (hσF : WNF σ)
    (hσt : Lt σ (.Psi .zero π X)) (hσs : σ ∈ subs (.Psi .zero π X))
    (hσC : ∀ g d, Ad π X g d → inC σ g d = true)
    (hF : ∀ η, WNF η → Lt η σ → WNF (s.big η))
    (hlt : ∀ η, WNF η → Lt η σ → Lt (s.big η) π)
    (hA : ∀ g d η, Ad π X g d → WNF η → Lt η σ → Lt .zero g → BigOK σ g d → inC η g d = true →
      inC (s.big η) g d = true)
    (hmono : ∀ η₁ η₂, WNF η₁ → WNF η₂ → Lt η₁ η₂ → Lt η₂ σ → Lt (s.big η₁) (s.big η₂))
    (hpos : ∀ η, WNF η → Lt η σ → s.big η ≠ .zero)
    (hub2 : ∀ g d η₁ η₂, WNF g → WNF d → WNF η₁ → WNF η₂ → Lt η₁ η₂ → Lt η₂ σ →
      inC (s.big η₂) g d = true → inC η₁ g d = true → inC (s.big η₁) g d = true)
    (hlo : ∀ g d η, WNF d → WNF η → Lt η σ → inC (s.big η) g d = true → inC η g d = true)
    (hns : ∀ η, WNF η → Lt η σ → ¬ isSucc η = true → ¬ isSucc (s.big η) = true)
    (hlb : ∀ m, σ = .K m → Lt (.K m) (.Psi .zero π X) → ∀ ξ, WNF ξ → Lt ξ σ → Le (.K m) (s.big ξ))
    (hlb2 : ∀ m, σ = .K m → Lt (succK m) (.Psi .zero π X) → ∀ ξ, WNF ξ → Lt ξ σ →
      Le (succK m) (s.big ξ))
    (hG : ∀ η, WNF η → Lt η σ → Gp (.Psi .zero π X) (s.big η)) :
    BigInv (.Psi .zero π X) σ s := by
  have hX := ht.psi.aF
  have hltt : ∀ η, WNF η → Lt η σ → Lt (s.big η) (.Psi .zero π X) := fun η hη hησ =>
    coll_psiY ht _ (hF η hη hησ) (hA X _ η (Ad.self ht) hη hησ hX0 (Or.inl (Or.inr hσt))
      (WFY.inC_of_ltY _ hη ht (lt_transY hη hσF ht hησ hσt))) (hlt η hη hησ)
  refine ⟨{ good := ⟨fun η hη hησ => ⟨hF η hη hησ, hltt η hη hησ⟩, hmono⟩
            pos := fun η hη hησ e => absurd e (hpos η hη hησ)
            hσF := hσF
            hσle := Or.inr hσt
            hσs := hσs
            hσC := fun g e hg he h => ?_
            ub := fun g e η hg he hη hησ h0 hok h hηC => ?_
            ub2 := hub2
            lo := hlo
            ns := fun _ η hη hησ hs => hns η hη hησ hs
            lbK := hlb
            lbS := hlb2 }, fun η hη hησ v hv hne hl =>
      hG η hη hησ v hv hne hl⟩
  · by_cases hdt : Lt (.Psi .zero π X) e
    · exact WFY.inC_of_ltY _ hσF he (lt_transY hσF ht he hσt hdt)
    · exact hσC g e ⟨hg, he, Or.inl ⟨h, hdt⟩⟩
  · by_cases hdt : Lt (.Psi .zero π X) e
    · exact WFY.inC_of_ltY _ (hF η hη hησ) he (lt_transY (hF η hη hησ) ht he (hltt η hη hησ) hdt)
    · exact hA g e η ⟨hg, he, Or.inl ⟨h, hdt⟩⟩ hη hησ h0 hok hηC

theorem combine_idx {κ γ P x : Tm} {pre : List Tm} (hx : WNF x) (hP : WNF P) :
    combine (.idx κ γ) pre .zero P x = approx pre P x := by
  show oadd (ofSummands pre) (nsum .zero (nsum P x)) = _
  rw [zero_nsum _ (wnf_nsum hP hx), nsum_comm hP hx]
  rfl

/-- `Ψ^z_τ(Y)` の族の列の出力。不変量は隙間を仮定して示す。列の項は `Ψ^{pre ⊕ (x # P')}_τ(Y)` -/
structure IdxOut (π X τ Y μ P : Tm) (pre : List Tm) (R : Tm) (s : SeqD) : Prop where
  mem : InSeq s s.first
  form : ∀ y, InSeq s y → ∃ P' x, (P' = P ∨ P' = .zero) ∧ y = .Psi (approx pre P' x) τ Y ∧ WNF y ∧ WNF x ∧
    Lt (nsum x P') R ∧ Lt (approx pre P' x) μ ∧ Le s.first y ∧ (P ≠ .zero → Lt P y) ∧
    (x = .zero → ∀ v, v ∈ subs R → v = R) ∧ ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v x
  /-- 0 番目は `π` 未満 -/
  ltπ : Lt s.first π
  /-- 0 番目の上界 -/
  ubF : ∀ g d, WNF g → WNF d → Lt .zero g → (∀ v, v ∈ subs μ → Lt v π → inC v g d = true → Lt v d) →
    inC τ g d = true → inC Y g d = true → Lt Y g → inC μ g d = true → inC P g d = true →
    inC s.first g d = true
  inv : (∀ y, InSeq s y → Gp (.Psi .zero π X) y) → SeqI (.Psi .zero π X) s

/-- 種は近似の崩壊の未満 -/
theorem IdxG.seed_lt {τ Y μ P : Tm} {pre rest : List Tm} {R x : Tm} (G : IdxG τ Y μ P pre rest R)
    (hx : WNF x) (hy : WNF (.Psi (approx pre P x) τ Y)) (hp : P ∈ fr τ P) :
    Lt P (.Psi (approx pre P x) τ Y) :=
  FWOrder.k2s hy P (fr_oadd_of_right G.hpreF (G.hyF hx) (fr_nsum_of_right hx G.hPF hp))

/-- `Ψ^z_τ(Y)` の族の `ω` 型の列 -/
theorem idx_nat_out {π X τ Y μ P : Tm} {T : Tm → Tm → Prop} {pre rest : List Tm} {R : Tm} {x : Nat → Tm}
    {s : SeqD} (C : MCtx π X τ Y μ T) (G : IdxG τ Y μ P pre rest R) (I : Inner P .zero pre R x)
    (he : ∀ n, s.nat n = .Psi (approx pre P (x n)) τ Y) (hdt : s.dom = .omega)
    (hPπ : Lt P π) (hPA : ∀ g d, Ad π X g d → inC P g d = true)
    (hPfr : P ≠ .zero → P ∈ fr τ P) : IdxOut π X τ Y μ P pre R s := by
  have hτF := G.hτF
  have hPC : ∀ {g d : Tm}, Lt P d → WNF d → inC P g d = true := fun h hd => WFY.inC_of_ltY _ G.hPF hd h
  have hx := I.hx
  have hA0 : ∀ n, approx pre P (oadd .zero (x n)) = approx pre P (x n) := fun n => by
    rw [zero_oadd (hx n)]
  have h1 : ∀ n, inC (x n) Y τ = true := fun n =>
    I.ub Y τ n G.hYF hτF (G.parts G.hμ1).1 (G.parts G.hμ1).2 (inC_zero _ _)
      (hPC G.hPτ hτF) (Or.inl G.hTY)
  have h2 : ∀ n, inC (x n) (mi τ) τ = true := fun n =>
    I.ub _ τ n (WFY.WNF.mi hτF) hτF (G.parts G.hμ2).1
      (G.parts G.hμ2).2 (inC_zero _ _) (hPC G.hPτ hτF) (Or.inl G.hTm)
  have hnf : ∀ n, WNF (.Psi (approx pre P (x n)) τ Y) := fun n => G.nf (hx n) (I.hxR n) (h1 n) (h2 n)
  have hm : ∀ n, Lt (.Psi (approx pre P (x n)) τ Y) (.Psi (approx pre P (x (n + 1))) τ Y) := fun n =>
    G.lt2 (hx n) (hx (n + 1)) (I.hxR (n + 1)) (I.mono n) (hnf n) (hnf (n + 1)) fun h hp hP => by
      have hy' := hnf (n + 1)
      exact I.ub2 _ _ n G.hYF hy' h hp (inC_zero _ _) hP
        (by rw [hA0]; exact G.hAlt (hx n) (I.hxR n) G.hYF G.hTY)
  have L : NatL τ s := by
    refine ⟨fun n => ?_, fun n => ?_, fun g d n hg hd h => ?_⟩
    · rw [he n, he (n + 1)]
      exact ⟨hnf n, lt_psi_targetY (hnf n), hm n⟩
    · rw [he n]
      intro e
      cases e
    · rw [he (n + 1)] at h
      rw [he n]
      exact G.ub2 (hx n) (hx (n + 1)) (I.hxR (n + 1)) (I.mono n) (hnf n) (hnf (n + 1)) (hm n) hg hd
        (fun hle h' hk hp hP hlt => I.ub2 g d n hg hd h' hp (inC_zero _ _) hP
          (by rw [hA0]; exact hlt)) h
  have hz : ∀ g d n, WNF g → WNF d → inC μ g d = true → Le Y g →
      inC P g d = true → inC (approx pre P (x n)) g d = true := fun g d n hg hd hμC hYg hP =>
    G.inC_A (hx n) (G.parts hμC).2 (I.ub g d n hg hd (G.parts hμC).1 (G.parts hμC).2
      (inC_zero _ _) hP (Or.inl (le_transY G.hTF G.hYF hg G.hTY hYg))) hP
  have hlt : ∀ n, Lt (s.nat n) π := fun n => by
    rw [he n]
    refine C.ltI _ (hnf n) (G.hAlt (hx n) (I.hxR n) G.hμF G.hTμ) fun g d h => ?_
    obtain ⟨hg, hd, hπd, -, -, -, h4, h5⟩ := C.hT g d h
    exact hz g d n hg hd h5 h4 (hPC (lt_of_lt_of_leY G.hPF C.hπF hd hPπ hπd) hd)
  refine ⟨Or.inl ⟨hdt, 0, first_of_nat hdt⟩, ?_, by rw [first_of_nat hdt]; exact hlt 0,
    fun g d hg hd _ _ hk hYC hYg hμC hP => ?_, fun hG => ?_⟩
  · rintro y (⟨-, n, rfl⟩ | ⟨σ, η, hd, -⟩)
    · refine ⟨P, x n, Or.inl rfl, he n, by rw [he n]; exact hnf n, hx n, G.hyR (hx n) (I.hxR n),
        G.hAlt (hx n) (I.hxR n) G.hμF G.hTμ, ?_, fun h0 => ?_, I.zero n, I.gap n⟩
      · rw [first_of_nat hdt]
        exact le_of_mono (y := s.nat) (fun k => (L.good k).1) (fun k => (L.good k).2.2) n
      · rw [he n]
        exact G.seed_lt (hx n) (hnf n) (hPfr h0)
    · rw [hdt] at hd
      cases hd
  · rw [first_of_nat hdt, he 0]
    exact inC_psi_iff.mpr (Or.inr ⟨hk, hz g d 0 hg hd hμC (Or.inr hYg) hP, hYC, hYg⟩)
  · refine seqI_nat hdt (natInv_lift C.ht L hlt (fun g d n h => ?_)
      fun n => hG _ (Or.inl ⟨hdt, n, rfl⟩))
    · obtain ⟨-, h2', h3, h4, h5⟩ := C.comp g d h
      rw [he n]
      exact inC_psi_iff.mpr (Or.inr ⟨h2', hz g d n h.1 h.2.1 h5 (Or.inr h4) (hPA g d h), h3, h4⟩)

/-- `Ψ^z_τ(Y)` の族の、共終数が `ceil` 未満の列 -/
theorem idx_big_out {π X τ Y μ P σ : Tm} {T : Tm → Tm → Prop} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (C : MCtx π X τ Y μ T) (G : IdxG τ Y μ P pre rest R) (hB : BigInv R σ r) (hreg : RegTerm σ)
    (hd : r.dom = .big σ) (hσπ : Lt σ π) (hRs : R ∈ subs (.Psi .zero π X))
    (hPπ : Lt P π) (hPA : ∀ g d, Ad π X g d → inC P g d = true) (hPfr : P ≠ .zero → P ∈ fr τ P) :
    IdxOut π X τ Y μ P pre R (.app π (.idx τ Y) pre R r P .zero) := by
  have ht := C.ht
  have hτF := G.hτF
  have hπF := C.hπF
  have hσF := hB.1.hσF
  have hU := hB.1
  have hσ0 : Lt .zero σ := zero_lt hreg.ne_zero
  have hστ : Lt σ τ := lt_of_lt_of_leY hσF hπF hτF hσπ C.hle
  have hd' := app_dom_big_lt (P := P) (c := .zero) (g := .idx τ Y) (pre := pre) (R := R) hd (ltB_iff.mpr hσπ)
  have hPC : ∀ {g d : Tm}, Lt P d → WNF d → inC P g d = true := fun h hd => WFY.inC_of_ltY _ G.hPF hd h
  have hxF : ∀ η, WNF η → Lt η σ → WNF (r.big η) := fun η hη hησ => (hU.good.1 η hη hησ).1
  have hxR : ∀ η, WNF η → Lt η σ → Lt (r.big η) R := fun η hη hησ => (hU.good.1 η hη hησ).2
  have he : ∀ η, WNF η → Lt η σ →
      (SeqD.app π (.idx τ Y) pre R r P .zero).big η = .Psi (approx pre P (r.big η)) τ Y := fun η hη hησ => by
    show (Gen.idx τ Y).ap (combine (.idx τ Y) pre .zero P (r.big η)) = _
    rw [combine_idx (hxF η hη hησ) G.hPF]
    rfl
  have hR0 : Lt .zero R := lt_of_le_of_ltY WNF.zero G.hPF G.hRF (zero_le _) G.hPR
  have hTpos : Lt .zero (oadd (ofSummands pre) R) :=
    lt_of_lt_of_leY WNF.zero G.hRF G.hTF hR0 (le_oadd_right G.hpreF G.hRF)
  have hY0 : Lt .zero Y := lt_of_lt_of_leY WNF.zero G.hTF G.hYF hTpos G.hTY
  have hm0 : Lt .zero (mi τ) := lt_of_lt_of_leY WNF.zero G.hTF (WFY.WNF.mi hτF) hTpos G.hTm
  have h1 : ∀ η, WNF η → Lt η σ → inC (r.big η) Y τ = true := fun η hη hησ =>
    hU.ub Y τ η G.hYF hτF hη hησ hY0 (Or.inl (Or.inr hστ)) (G.parts G.hμ1).1
      (WFY.inC_of_ltY _ hη hτF (lt_transY hη hσF hτF hησ hστ))
  have h2 : ∀ η, WNF η → Lt η σ → inC (r.big η) (mi τ) τ = true := fun η hη hησ =>
    hU.ub _ τ η (WFY.WNF.mi hτF) hτF hη hησ hm0 (Or.inl (Or.inr hστ)) (G.parts G.hμ2).1
      (WFY.inC_of_ltY _ hη hτF (lt_transY hη hσF hτF hησ hστ))
  have hnf : ∀ η, WNF η → Lt η σ → WNF (.Psi (approx pre P (r.big η)) τ Y) := fun η hη hησ =>
    G.nf (hxF η hη hησ) (hxR η hη hησ) (h1 η hη hησ) (h2 η hη hησ)
  -- 0 番目との比較
  have hm0' : ∀ η, WNF η → Lt .zero η → Lt η σ →
      Lt (.Psi (approx pre P (r.big .zero)) τ Y) (.Psi (approx pre P (r.big η)) τ Y) := fun η hη h0 hησ =>
    G.lt2 (hxF _ WNF.zero hσ0) (hxF η hη hησ) (hxR η hη hησ) (hU.good.2 _ η WNF.zero hη h0 hησ)
      (hnf _ WNF.zero hσ0) (hnf η hη hησ) fun h _ _ =>
        hU.ub2 _ _ .zero η G.hYF (hnf η hη hησ) WNF.zero hη h0 hησ h (inC_zero _ _)
  have hfirst : (SeqD.app π (.idx τ Y) pre R r P .zero).first = .Psi (approx pre P (r.big .zero)) τ Y := by
    unfold SeqD.first
    rw [hd']
    exact he _ WNF.zero hσ0
  have hz : ∀ g d η, WNF g → WNF d → WNF η → Lt η σ → Lt .zero g → BigOK σ g d → inC μ g d = true → Le Y g →
      inC P g d = true → inC η g d = true → inC (approx pre P (r.big η)) g d = true :=
    fun g d η hg hd hη hησ h0 hok hμC hYg hP hηC =>
      G.inC_A (hxF η hη hησ) (G.parts hμC).2 (hU.ub g d η hg hd hη hησ h0 hok (G.parts hμC).1 hηC) hP
  have hlt : ∀ η, WNF η → Lt η σ → Lt (.Psi (approx pre P (r.big η)) τ Y) π := fun η hη hησ => by
    refine C.ltI _ (hnf η hη hησ) (G.hAlt (hxF η hη hησ) (hxR η hη hησ) G.hμF G.hTμ) fun g d h => ?_
    obtain ⟨hg, hd2, hπd, -, -, -, h4, h5⟩ := C.hT g d h
    have hσd : Lt σ d := lt_of_lt_of_leY hσF hπF hd2 hσπ hπd
    exact hz g d η hg hd2 hη hησ (lt_of_lt_of_leY WNF.zero G.hYF hg hY0 h4) (Or.inl (Or.inr hσd)) h5 h4
      (hPC (lt_of_lt_of_leY G.hPF hπF hd2 hPπ hπd) hd2)
      (WFY.inC_of_ltY _ hη hd2 (lt_transY hη hσF hd2 hησ hσd))
  refine ⟨Or.inr ⟨σ, .zero, hd', WNF.zero, hσ0, first_of_big hd'⟩, ?_,
    by rw [hfirst]; exact hlt _ WNF.zero hσ0,
    fun g d hg hd2 h0 hsub hk hYC hYg hμC hP => ?_, fun hG => ?_⟩
  · rintro y (⟨hdt, -⟩ | ⟨σ', η, hd2, hη, hησ, rfl⟩)
    · rw [hd'] at hdt
      cases hdt
    · rw [hd'] at hd2
      cases hd2
      refine ⟨P, r.big η, Or.inl rfl, he η hη hησ, by rw [he η hη hησ]; exact hnf η hη hησ, hxF η hη hησ,
        G.hyR (hxF η hη hησ) (hxR η hη hησ), G.hAlt (hxF η hη hησ) (hxR η hη hησ) G.hμF G.hTμ, ?_, fun h0 => ?_,
        hU.pos η hη hησ, hB.2 η hη hησ⟩
      · rw [hfirst, he η hη hησ]
        by_cases h0 : η = .zero
        · rw [h0]
          exact Or.inl rfl
        · exact Or.inr (hm0' η hη (zero_lt h0) hησ)
      · rw [he η hη hησ]
        exact G.seed_lt (hxF η hη hησ) (hnf η hη hησ) (hPfr h0)
  · rw [hfirst]
    have hσμ : σ ∈ subs μ := subs_trans (mem_subs_of_mem_summands G.hRm) hU.hσs
    exact inC_psi_iff.mpr (Or.inr ⟨hk, hz g d .zero hg hd2 WNF.zero hσ0 h0
      (Or.inl (Or.inr (hsub σ hσμ hσπ (hU.hσC g d hg hd2 (G.parts hμC).1)))) hμC (Or.inr hYg) hP
      (inC_zero _ _), hYC, hYg⟩)
  · have hRτ : inC R X (.Psi .zero π X) = true :=
      (G.parts (C.comp _ _ (Ad.self ht)).2.2.2.2).1
    have hσt : Lt σ (.Psi .zero π X) := coll_psiY ht σ hσF (hU.hσC X _ C.hXF ht hRτ) hσπ
    have hσs : σ ∈ subs (.Psi .zero π X) := subs_trans hRs hU.hσs
    have hσy : ∀ η, WNF η → Lt η σ → Lt σ (.Psi (approx pre P (r.big η)) τ Y) := fun η hη hησ => by
      have := hG _ (Or.inr ⟨σ, η, hd', hη, hησ, rfl⟩) σ hσs hσt.ne hσt
      rwa [he η hη hησ] at this
    have hmono : ∀ η₁ η₂, WNF η₁ → WNF η₂ → Lt η₁ η₂ → Lt η₂ σ →
        Lt (.Psi (approx pre P (r.big η₁)) τ Y) (.Psi (approx pre P (r.big η₂)) τ Y) := by
      intro η₁ η₂ h₁ h₂ hlt hησ
      have h₁σ := lt_transY h₁ h₂ hσF hlt hησ
      exact G.lt2 (hxF η₁ h₁ h₁σ) (hxF η₂ h₂ hησ) (hxR η₂ h₂ hησ) (hU.good.2 η₁ η₂ h₁ h₂ hlt hησ)
        (hnf η₁ h₁ h₁σ) (hnf η₂ h₂ hησ) fun h _ _ =>
          hU.ub2 _ _ η₁ η₂ G.hYF (hnf η₂ h₂ hησ) h₁ h₂ hlt hησ h
            (WFY.inC_of_ltY _ h₁ (hnf η₂ h₂ hησ) (lt_transY h₁ hσF (hnf η₂ h₂ hησ) h₁σ (hσy η₂ h₂ hησ)))
    have hX0 : Lt .zero X := lt_transY WNF.zero G.hYF C.hXF hY0 (C.comp _ _ (Ad.self ht)).2.2.2.1
    refine seqI_big hd' hreg (bigInv_lift ht hX0 hσF hσt hσs (fun g d h => ?_)
      (fun η hη hησ => by rw [he η hη hησ]; exact hnf η hη hησ)
      (fun η hη hησ => ?_) (fun g d η h hη hησ h0 hok hηC => ?_)
      (fun η₁ η₂ h₁ h₂ hlt hησ => ?_) (fun η hη hησ e => ?_)
      (fun g d η₁ η₂ hg hd' h₁ h₂ hlt hησ h hηC => ?_) (fun g d η hd' hη hησ h => ?_)
      (fun η hη hησ _ => ?_) (fun m e _ η hη hησ => ?_) (fun m e h η hη hησ => ?_)
      (fun η hη hησ => hG _ (Or.inr ⟨σ, η, hd', hη, hησ, rfl⟩)))
    · exact hU.hσC g d h.1 h.2.1 (G.parts (C.comp g d h).2.2.2.2).1
    · rw [he η hη hησ]
      exact hlt η hη hησ
    · obtain ⟨-, h2', h3, h4, h5⟩ := C.comp g d h
      rw [he η hη hησ]
      exact inC_psi_iff.mpr (Or.inr ⟨h2', hz g d η h.1 h.2.1 hη hησ h0 hok h5 (Or.inr h4) (hPA g d h) hηC,
        h3, h4⟩)
    · rw [he η₁ h₁ (lt_transY h₁ h₂ hσF hlt hησ), he η₂ h₂ hησ]
      exact hmono η₁ η₂ h₁ h₂ hlt hησ
    · rw [he η hη hησ] at e
      cases e
    · have h₁σ := lt_transY h₁ h₂ hσF hlt hησ
      rw [he η₂ h₂ hησ] at h
      rw [he η₁ h₁ h₁σ]
      exact G.ub2 (hxF η₁ h₁ h₁σ) (hxF η₂ h₂ hησ) (hxR η₂ h₂ hησ) (hU.good.2 η₁ η₂ h₁ h₂ hlt hησ)
        (hnf η₁ h₁ h₁σ) (hnf η₂ h₂ hησ) (hmono η₁ η₂ h₁ h₂ hlt hησ) hg hd'
        (fun _ h' _ _ _ _ => hU.ub2 g d η₁ η₂ hg hd' h₁ h₂ hlt hησ h' hηC) h
    · rw [he η hη hησ] at h
      have hy := hnf η hη hησ
      rcases inC_psi_iff.mp h with h' | ⟨-, hz', -, -⟩
      · exact WFY.inC_of_ltY _ hη hd' (lt_transY hη hσF hd' hησ (lt_transY hσF hy hd' (hσy η hη hησ) h'))
      · exact hU.lo g d η hd' hη hησ
          (inC_approx_parts G.hN (hxF η hη hησ) G.hPF (G.hyR (hxF η hη hησ) (hxR η hη hησ)) hz').2.1
    · rw [he η hη hησ, isSucc_principal rfl]
      simp
    · rw [he η hη hησ]
      exact Or.inr (K_lt_psi (hnf η hη hησ) (e ▸ hστ))
    · rw [he η hη hησ]
      have hm : 1 ≤ m := (e ▸ hσF : WNF (.K m)).k
      exact Or.inr (succK_lt_psi hm (hnf η hη hησ) (lt_of_lt_of_leY (WNF.succK hm) hπF hτF
        (lt_transY (WNF.succK hm) ht hπF h (lt_psi_targetY ht)) C.hle))

/-- 目標の Mahlo 添字は `K_m⁺` 以下 -/
theorem mi_le_succK : ∀ τ, WNF τ → IsTgt τ → Le (mi τ) (succK (lev τ))
  | .Om c, hτ, _ => by
    have h1 : 1 ≤ lev (Tm.Om c) := lev_posY hτ (by intro e; cases e)
    have h2 : lev (succK (lev (Tm.Om c))) = lev (Tm.Om c) + 1 := rfl
    have h3 : lev Tm.one = 1 := rfl
    exact Or.inr (lt_of_lev_lt' (by rw [h2]; show lev Tm.one < _; omega))
  | .Xi n q, hτ, _ => le_of_ne_gtY hτ.xi.2.1 (WNF.succK hτ.xi.1) hτ.xi.2.2.2.1
  | .Psi ζ κ b, hτ, _ => by
    have hP := hτ.psi
    have ih := mi_le_succK κ hP.piF hP.tgt
    have hl : 1 ≤ lev κ := lev_posY hP.piF (IsTgt.ne_zero hP.tgt)
    exact Or.inr (lt_of_lt_of_leY hP.xiF (WFY.WNF.mi hP.piF) (WNF.succK hl) hP.mlt ih)
  | .zero, _, h => by rcases h with ⟨c, e, -⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, -⟩ <;> cases e
  | .one, _, h => by rcases h with ⟨c, e, -⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, -⟩ <;> cases e
  | .K _, _, h => by rcases h with ⟨c, e, -⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, -⟩ <;> cases e
  | .plus _ _, _, h => by rcases h with ⟨c, e, -⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, -⟩ <;> cases e

/-- 目標の Mahlo 添字未満の `Ξ_m` は目標未満 -/
theorem xi_lt_tgt {A : Tm} {m : Nat} (hX : WNF (.Xi m A)) : ∀ τ, WNF τ → IsTgt τ → lev τ = m →
    Lt A (mi τ) → inC A (mi τ) τ = true → Lt (.Xi m A) τ
  | .Om _, _, _, _, h1, _ => absurd (lt_oneY hX.xi.2.1 h1) hX.xi.2.2.1
  | .Xi n q, _, _, h0, h1, h2 => by
    have e : n = m := h0
    subst e
    exact (lt_xi_xi0 h1.ne).mpr (Or.inl ⟨h1, h2⟩)
  | .Psi ζ κ b, hτ, _, h0, h1, h2 => by
    have hP := hτ.psi
    have hAF := hX.xi.2.1
    have hκ : Lt (.Psi ζ κ b) κ := lt_psi_targetY hτ
    have h3 : Lt A (mi κ) := lt_transY hAF hP.xiF (WFY.WNF.mi hP.piF) h1 hP.mlt
    have h4 : inC A (mi κ) κ = true :=
      inC_mono_proper hP.piF hAF (inC_mono_d hτ hP.piF (Or.inr hκ) hAF h2) fun v hv _ hl =>
        lt_transY (hAF.of_mem_subs hv) hP.xiF (WFY.WNF.mi hP.piF) hl hP.mlt
    have ih := xi_lt_tgt hX κ hP.piF hP.tgt h0 h3 h4
    have hζb : Le ζ b := le_of_ne_gtY hP.xiF hP.aF hP.le
    have h5 : inC A b (.Psi ζ κ b) = true :=
      inC_mono_proper hτ hAF h2 fun v hv _ hl =>
        lt_of_lt_of_leY (hAF.of_mem_subs hv) hP.xiF hP.aF hl hζb
    exact coll_psiY hτ _ hX (inC_xi_iff.mpr (Or.inr ⟨h5, lt_of_lt_of_leY hAF hP.xiF hP.aF h1 hζb⟩)) ih
  | .zero, _, h, _, _, _ => by rcases h with ⟨c, e, -⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, -⟩ <;> cases e
  | .one, _, h, _, _, _ => by rcases h with ⟨c, e, -⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, -⟩ <;> cases e
  | .K _, _, h, _, _, _ => by rcases h with ⟨c, e, -⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, -⟩ <;> cases e
  | .plus _ _, _, h, _, _, _ => by rcases h with ⟨c, e, -⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, -⟩ <;> cases e

/-- 値の帰還の塔（Mahlo 添字） -/
def idxT (τ Y : Tm) (pre : List Tm) (r : SeqD) (P : Tm) : Nat → Tm
  | 0 => P
  | k + 1 => .Psi (approx pre .zero (r.big (idxT τ Y pre r P k))) τ Y

/-- `K_m` の対角化（`Ψ^z_τ(Y)` の族）：添字は値の帰還 -/
theorem idx_K_out {π X τ Y μ P : Tm} {T : Tm → Tm → Prop} {pre rest : List Tm} {R : Tm} {r : SeqD} {m : Nat}
    (C : MCtx π X τ Y μ T) (G : IdxG τ Y μ P pre rest R) (hd : r.dom = .big (.K m))
    (hlt : ltB (.K m) π = false) (hB : BigInv R (.K m) r) (hPπ : Lt P π)
    (hPA : ∀ g d, Ad π X g d → inC P g d = true) :
    IdxOut π X τ Y μ P pre R (.app π (.idx τ Y) pre R r P .zero) := by
  have hU := hB.1
  have hτF := G.hτF
  have hπF := C.hπF
  have hτt := G.hτt
  have hPF := G.hPF
  have hmF := WFY.WNF.mi hτF
  have hm : 1 ≤ m := hU.hσF.k
  have hKF : WNF (.K m) := WNF.K' hm
  have hnl : ¬ Lt (.K m) π := fun h => by
    rw [ltB_iff.mpr h] at hlt
    cases hlt
  have hτK : Lt τ (.K m) := C.τK m hm hnl
  have hπK : Le π (.K m) := Or.inr (lt_of_le_of_ltY hπF hτF hKF C.hle hτK)
  have hRμ : Le R μ := by
    have := le_ofSummands_of_mem (nfl_summands G.hμF) G.hRm
    rwa [ofSummands_summands μ G.hμF] at this
  have hKμ : Le (.K m) μ := le_transY hKF G.hRF G.hμF hU.hσle hRμ
  have hKY : Le (.K m) Y := le_transY hKF G.hμF G.hYF hKμ G.hμY
  have hlτ : 1 ≤ lev τ := lev_posY hτF (IsTgt.ne_zero hτt)
  have hμS : Le μ (succK (lev τ)) :=
    le_transY G.hμF hmF (WNF.succK hlτ) G.hμm (mi_le_succK τ hτF hτt)
  have hl : lev τ = m := by
    have h1 : lev τ ≤ m := (lt_K_iffY hτF hm).mp hτK
    have h2 : lev (Tm.K m) ≤ lev (succK (lev τ)) := by
      rcases le_transY hKF G.hμF (WNF.succK hlτ) hKμ hμS with e | e
      · exact Nat.le_of_eq (congrArg lev e)
      · exact lev_le_of_lt_gen e
    have h3 : lev (Tm.K m) = m + 1 := rfl
    have h4 : lev (succK (lev τ)) = lev τ + 1 := rfl
    omega
  have hKS : Le μ (succK m) := by
    rw [← hl]
    exact hμS
  have hR0 : Lt .zero R := lt_of_le_of_ltY WNF.zero hPF G.hRF (zero_le _) G.hPR
  have hτ0 : Lt .zero τ := lt_of_le_of_ltY WNF.zero hPF hτF (zero_le _) G.hPτ
  have hK0 : Lt .zero (.K m) := lt_transY WNF.zero hτF hKF hτ0 hτK
  have h1K : Lt .one (.K m) := (lt_K_iffY WNF.one hm).mpr hm
  have G0 : IdxG τ Y μ .zero pre rest R :=
    ⟨G.hv, G.hYF, G.hYC, G.hτY, G.hμF, G.hsum, G.hμY, G.hμm, G.hμ1, G.hμ2, WNF.zero, hR0, hτ0⟩
  have hμpos : Lt .zero μ := lt_of_lt_of_leY WNF.zero hKF G.hμF hK0 hKμ
  have hμ0 : μ ≠ .zero := fun e => by
    rw [e] at hμpos
    exact not_lt_zero _ hμpos
  have hμξ : WNF (.Xi m μ) := wnf_xi_mk hm G.hμF hμ0 (ne_gt_of_le hKS) (C.hμσ _ hKF hπK)
  have hR1 : R ≠ .one := fun e => by
    have h := hU.hσle
    rw [e] at h
    exact not_lt_of_leY hKF WNF.one h h1K
  have X0 : XiG m μ .zero .zero pre rest R := ⟨hμξ, G.hsum, WNF.zero, hR0, hK0, Or.inl rfl, hR1⟩
  have hY0 : Lt .zero Y := lt_of_lt_of_leY WNF.zero hKF G.hYF hK0 hKY
  have hm0 : Lt .zero (mi τ) := lt_of_lt_of_leY WNF.zero G.hμF hmF hμpos G.hμm
  have h1Y : Lt .one Y := lt_of_lt_of_leY WNF.one hKF G.hYF h1K hKY
  have h1m : Lt .one (mi τ) :=
    lt_of_lt_of_leY WNF.one hKF hmF h1K (le_transY hKF G.hμF hmF hKμ G.hμm)
  -- 1 段
  have hγτ : ∀ {γ : Tm}, WNF γ → Lt γ π → Lt γ τ := fun hγ h => lt_of_lt_of_leY hγ hπF hτF h C.hle
  have hγK : ∀ {γ : Tm}, WNF γ → Lt γ π → Lt γ (.K m) := fun hγ h =>
    lt_transY hγ hτF hKF (hγτ hγ h) hτK
  have hxF : ∀ {γ : Tm}, WNF γ → Lt γ π → WNF (r.big γ) := fun hγ h =>
    (hU.good.1 _ hγ (hγK hγ h)).1
  have hxR : ∀ {γ : Tm}, WNF γ → Lt γ π → Lt (r.big γ) R := fun hγ h =>
    (hU.good.1 _ hγ (hγK hγ h)).2
  have h1 : ∀ {γ : Tm}, WNF γ → Lt γ π → inC (r.big γ) Y τ = true := fun hγ h =>
    hU.ub Y τ _ G.hYF hτF hγ (hγK hγ h) hY0 (bigOK_none rfl) (G.parts G.hμ1).1
      (WFY.inC_of_ltY _ hγ hτF (hγτ hγ h))
  have h2 : ∀ {γ : Tm}, WNF γ → Lt γ π → inC (r.big γ) (mi τ) τ = true := fun hγ h =>
    hU.ub _ τ _ hmF hτF hγ (hγK hγ h) hm0 (bigOK_none rfl) (G.parts G.hμ2).1
      (WFY.inC_of_ltY _ hγ hτF (hγτ hγ h))
  have hy : ∀ {γ : Tm}, WNF γ → Lt γ π → WNF (.Psi (approx pre .zero (r.big γ)) τ Y) := fun hγ h =>
    G0.nf (hxF hγ h) (hxR hγ h) (h1 hγ h) (h2 hγ h)
  have hAμ : ∀ {γ : Tm}, WNF γ → Lt γ π → Lt (approx pre .zero (r.big γ)) μ := fun hγ h =>
    G0.hAlt (hxF hγ h) (hxR hγ h) G.hμF G.hTμ
  have hAC : ∀ {γ : Tm}, WNF γ → Lt γ π →
      inC (approx pre .zero (r.big γ)) Y (.Psi (approx pre .zero (r.big γ)) τ Y) = true := fun hγ h => by
    have hy' := hy hγ h
    have hP' := hy'.psi
    exact inC_of_fr_lt hP'.xiF hτF hy' G.hYF G.hYF hP'.Cxi (Or.inr (lt_psi_targetY hy')) (Or.inl rfl)
      fun w hw => FWOrder.k2s hy' w hw
  have hup : ∀ {γ : Tm}, WNF γ → Lt γ π → Lt γ (.Psi (approx pre .zero (r.big γ)) τ Y) := fun hγ h =>
    coll_psiY (hy hγ h) _ hγ (hU.lo Y _ _ (hy hγ h) hγ (hγK hγ h)
      (inC_approx_parts G.hN (hxF hγ h) WNF.zero (G0.hyR (hxF hγ h) (hxR hγ h)) (hAC hγ h)).2.1) (hγτ hγ h)
  have hlt1 : ∀ {γ : Tm}, WNF γ → Lt γ π → Lt (.Psi (approx pre .zero (r.big γ)) τ Y) π := fun hγ h =>
    C.ltI _ (hy hγ h) (hAμ hγ h) fun g d hT => by
      obtain ⟨hg, hd2, hπd, -, -, -, h4, h5⟩ := C.hT g d hT
      exact G0.inC_A (hxF hγ h) (G.parts h5).2 (hU.ub g d _ hg hd2 hγ (hγK hγ h)
        (lt_of_lt_of_leY WNF.zero G.hYF hg hY0 h4) (bigOK_none rfl) (G.parts h5).1
        (WFY.inC_of_ltY _ hγ hd2 (lt_of_lt_of_leY hγ hπF hd2 h hπd))) (inC_zero _ _)
  have hcl : ∀ {γ : Tm} (k : Nat), WNF γ → Lt γ π →
      Lt (col (.K m) (approx pre .zero (r.big γ)) k) (.Psi (approx pre .zero (r.big γ)) τ Y) := by
    intro γ k hγ h
    have hy' := hy hγ h
    by_cases hA0 : approx pre .zero (r.big γ) = .zero
    · rw [hA0] at hy' ⊢
      rw [col_K_zero]
      exact coll_psiY hy' _ (wnf_xi_one hm) (inC_xi_iff.mpr (Or.inr ⟨inC_one _ _, h1Y⟩))
        (xi_lt_tgt (wnf_xi_one hm) τ hτF hτt hl h1m (inC_one _ _))
    · have hx := hxF hγ h
      have hxR' := hxR hγ h
      have hA : xA .zero pre .zero (r.big γ) = approx pre .zero (r.big γ) :=
        combine_idx (κ := .zero) (γ := .zero) hx WNF.zero
      have hC : inC (r.big γ) (xA .zero pre .zero (r.big γ)) (.K m) = true := by
        refine X0.hCx hx hxR' (hU.pos _ hγ (hγK hγ h)) (hB.2 _ hγ (hγK hγ h)) fun hR _ => ?_
        by_cases hx0 : r.big γ = .zero
        · rw [hx0]
          exact inC_zero _ _
        · exact hU.ub _ _ _ (wnf_oadd G.hpreF (wnf_nsum hx WNF.zero)) hKF hγ (hγK hγ h)
            (approx_pos G.hpreF hx WNF.zero hx0) (bigOK_none rfl) hR
            (WFY.inC_of_ltY _ hγ hKF (hγK hγ h))
      have hX : WNF (.Xi m (approx pre .zero (r.big γ))) := by
        have := X0.nf (by rw [hA]; exact hA0) hx hxR' hC
        rwa [hA] at this
      have hle : leB (approx pre .zero (r.big γ)) (succK m) = true :=
        leB_iff.mpr (ne_gt_of_le (Or.inr (lt_of_lt_of_leY (G0.hAF hx) G.hμF (WNF.succK hm)
          (hAμ hγ h) hKS)))
      rw [col_K_le hA0 hle]
      exact coll_psiY hy' _ hX (inC_xi_iff.mpr (Or.inr ⟨hAC hγ h, G0.hAlt hx hxR' G.hYF G.hTY⟩))
        (xi_lt_tgt hX τ hτF hτt hl (G0.hAlt hx hxR' hmF G.hTm)
          (G0.inC_A hx (G.parts G.hμ2).2 (h2 hγ h) (inC_zero _ _)))
  -- 塔
  have htow : ∀ k, WNF (idxT τ Y pre r P k) ∧ Lt (idxT τ Y pre r P k) π := by
    intro k
    induction k with
    | zero => exact ⟨hPF, hPπ⟩
    | succ k ih => exact ⟨hy ih.1 ih.2, hlt1 ih.1 ih.2⟩
  have hmono : ∀ k, Lt (idxT τ Y pre r P k) (idxT τ Y pre r P (k + 1)) := fun k =>
    hup (htow k).1 (htow k).2
  have hclo : ∀ g d k, WNF g → WNF d → inC τ g d = true → inC Y g d = true → Lt Y g →
      inC μ g d = true → inC P g d = true → inC (idxT τ Y pre r P k) g d = true := by
    intro g d k hg hd' h1' h2' h3 h4 h5
    induction k with
    | zero => exact h5
    | succ k ih =>
      have hw := htow k
      exact inC_psi_iff.mpr (Or.inr ⟨h1', G0.inC_A (hxF hw.1 hw.2) (G.parts h4).2
        (hU.ub g d _ hg hd' hw.1 (hγK hw.1 hw.2) (lt_transY WNF.zero G.hYF hg hY0 h3) (bigOK_none rfl)
          (G.parts h4).1 ih) (inC_zero _ _), h2', h3⟩)
  -- 定義との対応
  have hA' : ∀ {γ : Tm}, WNF γ → Lt γ π →
      argOf π (.K m) (.idx τ Y) pre R r .zero P γ = approx pre .zero (r.big γ) := fun hγ h => by
    simp only [argOf, canonK, outsideMode, seedOut, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
    exact combine_idx (hxF hγ h) WNF.zero
  have hgam : ∀ n, gam π (.K m) (.idx τ Y) pre R r .zero P n = idxT τ Y pre r P n := by
    intro n
    induction n with
    | zero => simp only [gam, canonK, outsideMode, Bool.false_eq_true, ↓reduceIte, idxT]
    | succ k ih =>
      have hw := htow k
      have h3 : ltB (col (.K m) (approx pre .zero (r.big (idxT τ Y pre r P k))) k)
          ((Gen.idx τ Y).ap (approx pre .zero (r.big (idxT τ Y pre r P k)))) = true :=
        ltB_iff.mpr (hcl k hw.1 hw.2)
      have h4 : ltB ((Gen.idx τ Y).ap (approx pre .zero (r.big (idxT τ Y pre r P k)))) (.K m) = true :=
        ltB_iff.mpr (lt_transY (hy hw.1 hw.2) hτF hKF (lt_psi_targetY (hy hw.1 hw.2)) hτK)
      simp only [gam, canonK, outsideMode, Bool.false_eq_true, ↓reduceIte]
      rw [ih, hA' hw.1 hw.2, h3, h4]
      rfl
  have he : ∀ n, (SeqD.app π (.idx τ Y) pre R r P .zero).nat n = idxT τ Y pre r P (n + 1) := fun n => by
    rw [app_nat_big hd hlt, hgam n, hA' (htow n).1 (htow n).2]
    rfl
  have hdt := app_dom_big_ge (P := P) (c := .zero) (g := .idx τ Y) (pre := pre) (R := R) hd hlt
  have L : NatL τ (.app π (.idx τ Y) pre R r P .zero) := by
    refine ⟨fun n => ?_, fun n => ?_, fun g d n hg hd' h => ?_⟩
    · rw [he n, he (n + 1)]
      exact ⟨(htow (n + 1)).1, hγτ (htow (n + 1)).1 (htow (n + 1)).2, hmono (n + 1)⟩
    · rw [he n]
      intro e
      cases e
    · rw [he (n + 1)] at h
      rw [he n]
      rcases inC_psi_iff.mp h with h' | ⟨-, h', -, -⟩
      · exact WFY.inC_of_ltY _ (htow (n + 1)).1 hd'
          (lt_transY (htow (n + 1)).1 (htow (n + 2)).1 hd' (hmono (n + 1)) h')
      · have hw := htow (n + 1)
        exact hU.lo g d _ hd' hw.1 (hγK hw.1 hw.2)
          (inC_approx_parts G.hN (hxF hw.1 hw.2) WNF.zero (G0.hyR (hxF hw.1 hw.2) (hxR hw.1 hw.2)) h').2.1
  have hlt' : ∀ n, Lt ((SeqD.app π (.idx τ Y) pre R r P .zero).nat n) π := fun n => by
    rw [he n]
    exact (htow (n + 1)).2
  refine ⟨Or.inl ⟨hdt, 0, first_of_nat hdt⟩, ?_, by rw [first_of_nat hdt]; exact hlt' 0,
    fun g d hg hd' _ _ hk hYC hYg hμC hP => ?_, fun hG => ?_⟩
  · rintro y (⟨-, n, rfl⟩ | ⟨σ, η, hd2, -⟩)
    · have hle := le_of_mono (y := (SeqD.app π (.idx τ Y) pre R r P .zero).nat) (fun k => (L.good k).1)
        (fun k => (L.good k).2.2) n
      have hw := htow n
      refine ⟨.zero, r.big (idxT τ Y pre r P n), Or.inr rfl, he n, by rw [he n]; exact (htow (n + 1)).1,
        hxF hw.1 hw.2, G0.hyR (hxF hw.1 hw.2) (hxR hw.1 hw.2), hAμ hw.1 hw.2, ?_, fun _ => ?_,
        hU.pos _ hw.1 (hγK hw.1 hw.2), hB.2 _ hw.1 (hγK hw.1 hw.2)⟩
      · rw [first_of_nat hdt]
        exact hle
      · refine lt_of_lt_of_leY hPF (L.good 0).1 (L.good n).1 ?_ hle
        rw [he 0]
        exact hmono 0
    · rw [hdt] at hd2
      cases hd2
  · rw [first_of_nat hdt, he 0]
    exact hclo g d 1 hg hd' hk hYC hYg hμC hP
  · refine seqI_nat hdt (natInv_lift C.ht L hlt' (fun g d n h => ?_)
      fun n => hG _ (Or.inl ⟨hdt, n, rfl⟩))
    obtain ⟨-, h2', h3, h4, h5⟩ := C.comp g d h
    rw [he n]
    exact hclo g d (n + 1) h.1 h.2.1 h2' h3 h4 h5 (hPA g d h)

/-- 加数の共終数による場合分け -/
theorem idx_app {π X τ Y μ P : Tm} {T : Tm → Tm → Prop} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (C : MCtx π X τ Y μ T) (G : IdxG τ Y μ P pre rest R) (hRI : SeqI R r) (h0 : r.dom ≠ .zero)
    (h1 : r.dom ≠ .one) (hRp : isPrincipal R = true) (hRs : R ∈ subs (.Psi .zero π X))
    (hRsz : R.size < π.size) (hPs : ¬ isSucc P = true)
    (hPπ : Lt P π) (hPA : ∀ g d, Ad π X g d → inC P g d = true) (hPfr : P ≠ .zero → P ∈ fr τ P) :
    IdxOut π X τ Y μ P pre R (.app π (.idx τ Y) pre R r P .zero) := by
  unfold SeqI at hRI
  have hπF := C.hπF
  cases hd : r.dom with
  | zero => exact absurd hd h0
  | one => exact absurd hd h1
  | omega =>
    rw [hd] at hRI
    have hdom : ∀ σ, r.dom ≠ .big σ := fun σ e => by
      rw [hd] at e
      cases e
    exact idx_nat_out C G (inner_nat hRI) (fun n => by
      rw [app_nat_of_not_big hdom n, combine_idx (hRI.1.good n).1 G.hPF]
      rfl) (app_dom_nat hdom) hPπ hPA hPfr
  | big σ =>
    rw [hd] at hRI
    obtain ⟨hBW, hBS, hreg⟩ := hRI
    have hB : BigInv R σ r := ⟨hBW.1, hBS hRp⟩
    have hσF := hB.1.hσF
    by_cases hσπ : Lt σ π
    · exact idx_big_out C G hB hreg hd hσπ hRs hPπ hPA hPfr
    have hlt' : ltB σ π = false := by
      cases e : ltB σ π with
      | false => rfl
      | true => exact absurd (ltB_iff.mp e) hσπ
    rcases hreg with hσt | ⟨m, rfl⟩
    · have hne : σ ≠ π := fun e => by
        have h2 := size_le_of_mem_subs hB.1.hσs
        rw [e] at h2
        omega
      have hπσ : Le π σ := le_of_not_ltY hσF hπF hσπ
      have hμπ := C.hμσ π hπF (Or.inl rfl)
      have hσC := hB.1.hσC μ π G.hμF hπF (G.parts hμπ).1
      have htσ : WNF (.Psi .zero σ μ) :=
        wnf_psi0 hσF hσt G.hμF (C.hμσ σ hσF hπσ) fun q hq => (arg_of_inC hq hσC hσπ).2
      have hR0 : Lt .zero R := lt_of_le_of_ltY WNF.zero G.hPF G.hRF (zero_le _) G.hPR
      have H : DiagHyp .zero σ μ .zero .zero pre rest R r :=
        { ht := htσ, hsum := G.hsum, hRU := hB.1, hRG := hB.2, hGF := WNF.zero
          hGσ := zero_lt hσt.ne_zero, hGs := by simp [isSucc, summands], hQF := WNF.zero, hQR := hR0
          hQσ := zero_lt hσt.ne_zero
          hI := IdxHyp.zero htσ, hξ := zero_le _ }
      refine idx_nat_out C G (H.inner_out (c := .zero) WNF.zero G.hPF hPs (fun _ _ _ _ _ => inC_zero _ _))
        (fun n => ?_) (app_dom_big_ge hd hlt') hPπ hPA hPfr
      rw [app_nat_outG H (by simpa [Gen.tgt?] using hne) rfl hd hlt',
        combine_idx (H.tower n).2.2.hx G.hPF]
      rfl
    · exact idx_K_out C G hd hlt' hB hPπ hPA

end RTKA.Fund
