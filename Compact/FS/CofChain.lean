import Compact.FS.CofMahlo

/-! 鎖の段の分類：`x < t` の節点を鎖の段 `ρ = Ψ^ζ_κ(γ)` と比べる。

目標 `k` が `κ` 以下の節点は、`k ≤ ρ`（下の段）か、`ρ` の前線の元以下（`t` の部分項以下）か、`k = κ` で
`a < γ` または `a = γ`、`s < ζ`（段の節点）。 -/

namespace RTKA.Fund

open Tm W

/-- `π` の目標の前線の元は `t` の部分項で `t` 未満 -/
theorem subLe_frπ {π X x w : Tm} (ht : WNF (.Psi .zero π X)) (hw : w ∈ fr π π) (hxw : Le x w) :
    SubLe (.Psi .zero π X) x := by
  have h1 := (fr_spec hw).1
  have h2 := size_le_of_mem_subs h1
  exact ⟨w, subs_psi_p h1, ne_of_size_lt (by simp only [Tm.size]; omega), FWOrder.k2t ht w hw, hxw⟩

/-- 鎖の段 `ρ` と比べた分類 -/
theorem rho_cls {π X ζ κ γ x : Tm} (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Psi ζ κ γ))
    (hx : WNF x) (hxt : Lt x (.Psi .zero π X)) (htk : Lt (.Psi .zero π X) (tgtN x))
    (hkκ : Le (tgtN x) κ) :
    Le (tgtN x) (.Psi ζ κ γ) ∨ SubLe (.Psi .zero π X) x ∨
      ∃ s a, x = .Psi s κ a ∧ (Lt a γ ∨ (a = γ ∧ Lt s ζ)) := by
  have hπF := ht.psi.piF
  have hρ : WNF (.Psi ζ κ γ) := hc.wnf hπF
  have hP := hρ.psi
  have hπρ := hc.le hπF
  have hxρ : Lt x (.Psi ζ κ γ) :=
    lt_of_lt_of_leY hx hπF hρ (lt_transY hx ht hπF hxt (lt_psi_targetY ht)) hπρ
  have hlt : lev (Tm.Psi .zero π X) = lev κ := by
    have := hc.lev_eq
    simp only [lev] at this ⊢
    exact this
  have hgap : ∀ w, w ∈ fr (.Psi ζ κ γ) (.Psi ζ κ γ) → Le x w → SubLe (.Psi .zero π X) x := fun w hw hxw =>
    subLe_frπ ht (hc.fr_mem hπF hw) hxw
  cases x with
  | Psi s k a =>
    have hQ := hx.psi
    have hl : lev k = lev κ := by
      have h1 := lev_le_of_lt_gen hxρ
      have h2 := lev_le_of_lt_gen htk
      simp only [lev, tgtN] at h1 h2 hlt ⊢
      omega
    have hne : Tm.Psi s k a ≠ .Psi ζ κ γ := fun e => Lt.irrefl _ (e ▸ hxρ)
    rcases (lt_psi_psiY hl hne).mp hxρ with h | ⟨hρk, hxκ, h1 | h2 | h3 | h4⟩
    · exact Or.inl (le_of_not_ltY hρ hQ.piF h)
    · obtain ⟨haγ, -, -, hkC⟩ := h1
      have hkκ' : k = κ := by
        rcases hkκ with e | hk
        · exact e
        · exact absurd (coll_psiY hρ k hQ.piF hkC hk) (Lt.asymmY hρ hQ.piF hρk)
      subst hkκ'
      exact Or.inr (Or.inr ⟨s, a, rfl, Or.inl haγ⟩)
    · obtain ⟨hle, hn⟩ := h2
      obtain ⟨w, hw, hn'⟩ := wit_c2 hρ hx hQ.aF (le_of_ne_gtY hP.aF hQ.aF hle) hxκ hn
      have hwF : WNF w := by
        rcases hw with hw | hw | hw
        · exact hP.aF.of_mem_subs (fr_spec hw).1
        · exact hP.piF.of_mem_subs (fr_spec hw).1
        · exact hP.xiF.of_mem_subs (fr_spec hw).1
      refine Or.inr (Or.inl (hgap w (fr_comp_mem hρ ?_) (le_of_not_ltY hwF hx hn')))
      rcases hw with hw | hw | hw
      · exact Or.inl hw
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr hw)
    · obtain ⟨heq, hκk, hsζ, -⟩ := h3
      have e1 : a = γ := FWOrder.eq hQ.aF hP.aF heq
      subst hκk
      exact Or.inr (Or.inr ⟨s, a, rfl, Or.inr ⟨e1, hsζ⟩⟩)
    · obtain ⟨hζs, hn⟩ := h4
      obtain ⟨w, hw, hn'⟩ := wit_c4 hρ hx hQ.xiF hxρ hζs hn
      have hwF : WNF w := hP.xiF.of_mem_subs (fr_spec hw).1
      exact Or.inr (Or.inl (hgap w (fr_psi_self (Or.inl rfl) hw) (le_of_not_ltY hwF hx hn')))
  | Xi j b =>
    exfalso
    have hj := hx.xi.1
    have hKF := WNF.K' hj
    have hKκ : Lt (.K j) κ := by
      rcases hkκ with e | h
      · exact absurd e.symm (IsTgt.ne_K hP.tgt j)
      · exact h
    have h1 := lev_le_of_lt_gen hKκ
    have h2 : Lt (.K j) (.Psi .zero π X) :=
      K_lt_of_lev ht rfl rfl (by simp only [lev] at h1 hlt ⊢; omega)
    exact Lt.asymmY ht hKF htk h2
  | _ => exact absurd htk (not_lt_zero _)

/-- 鎖の段の下の段 -/
theorem chain_low {π X ζ κ γ p : Tm} (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Psi ζ κ γ))
    (hL : LoT (.Psi .zero π X) (.Psi ζ κ γ) p) : LowC (.Psi .zero π X) κ (some p) := by
  intro x hx hxt htk hkκ
  rcases rho_cls ht hc hx hxt htk (Or.inr hkκ) with hkρ | hsub | ⟨s, a, rfl, -⟩
  · have harg : ∃ a, argR? x = some a := by
      cases x with
      | Psi s k a => exact ⟨a, rfl⟩
      | Xi j b => exact ⟨b, rfl⟩
      | _ => exact absurd htk (not_lt_zero _)
    obtain ⟨a, harg⟩ := harg
    rcases hL x a hx hxt harg htk hkρ with h | h
    · exact Or.inl ⟨p, rfl, h⟩
    · exact Or.inr h
  · exact Or.inr hsub
  · exact absurd hkκ (Lt.irrefl _)

/-- 鎖の段の節点の分類 -/
theorem chain_cls {π X ζ κ γ : Tm} (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Psi ζ κ γ)) :
    ClsC (.Psi .zero π X) κ γ ζ := by
  intro s a hx hxt
  have hπF := ht.psi.piF
  have hρ : WNF (.Psi ζ κ γ) := hc.wnf hπF
  have hP := hρ.psi
  have hρκ : Lt (.Psi ζ κ γ) κ := lt_psi_targetY hρ
  have htκ : Lt (.Psi .zero π X) κ :=
    lt_of_lt_of_leY ht hπF hP.piF (lt_psi_targetY ht) (le_transY hπF hρ hP.piF (hc.le hπF) (Or.inr hρκ))
  rcases rho_cls ht hc hx hxt htκ (Or.inl rfl) with hkρ | hsub | ⟨s', a', e, h⟩
  · exact absurd hρκ (not_lt_of_leY hP.piF hρ hkρ)
  · exact Or.inr (Or.inr hsub)
  · cases e
    rcases h with h | ⟨e, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨e, h⟩)

/-- 鎖の段の添字の残り：`w = Ψ^0_ρ(W) ≤ p` について閉じている -/
theorem chain_hW {π X ζ κ γ p W : Tm} (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Psi ζ κ γ))
    (hw : WNF (.Psi .zero (.Psi ζ κ γ) W)) (hle : Le (.Psi .zero (.Psi ζ κ γ) W) p) (hpF : WNF p)
    (hpρ : Lt p (.Psi ζ κ γ)) :
    ∀ L₁ L₂, summands ζ = L₁ ++ L₂ → (∀ u, u ∈ L₂ → Le u p) →
      ∀ z, WNF (.Psi z κ γ) → Lt (.Psi z κ γ) (.Psi .zero π X) → Lt z ζ → ¬ Lt z (ofSummands L₁) →
      Le (.Psi z κ γ) p ∨ SubLe (.Psi .zero π X) (.Psi z κ γ) := by
  intro L₁ L₂ hsum hL₂ z hx hxt hzζ hzL
  have hπF := ht.psi.piF
  have hρ : WNF (.Psi ζ κ γ) := hc.wnf hπF
  have hP := hρ.psi
  have hκF := hP.piF
  have hζF := hP.xiF
  have hγF := hP.aF
  have hWF := hw.psi.aF
  have hρκ : Lt (.Psi ζ κ γ) κ := lt_psi_targetY hρ
  have hwρ : Lt (.Psi .zero (.Psi ζ κ γ) W) (.Psi ζ κ γ) := lt_psi_targetY hw
  have hwκ : Le (.Psi .zero (.Psi ζ κ γ) W) κ := Or.inr (lt_transY hw hρ hκF hwρ hρκ)
  have hγW : Lt γ W := arg_lt_of_psi hw rfl
  -- `ρ` の前線は `w` 未満
  have hfrw : ∀ f, f ∈ fr (.Psi ζ κ γ) (.Psi ζ κ γ) → Lt f (.Psi .zero (.Psi ζ κ γ) W) := fun f hf =>
    FWOrder.k2t hw f hf
  have hfrκ : ∀ f e, (e = γ ∨ e = κ ∨ e = ζ) → f ∈ fr κ e → Lt f (.Psi .zero (.Psi ζ κ γ) W) :=
    fun f e he hf => by
      rcases he with rfl | rfl | rfl
      · exact hfrw f (fr_comp_mem hρ (Or.inl hf))
      · exact hfrw f (fr_comp_mem hρ (Or.inr (Or.inl hf)))
      · exact hfrw f (fr_comp_mem hρ (Or.inr (Or.inr hf)))
  -- `ζ` の加数で `κ` 未満のものは `w` 未満
  have hsumw : ∀ u, u ∈ summands ζ → Lt u κ → Lt u (.Psi .zero (.Psi ζ κ γ) W) := fun u hu huκ => by
    have huF := hζF.of_mem_subs (mem_subs_of_mem_summands hu)
    have huρ : Lt u (.Psi ζ κ γ) := by
      have h1 : inC u γ κ = true := inC_of_mem_summands hζF hP.Cxi hu
      have h2 : inC u γ (.Psi ζ κ γ) = true :=
        inC_of_fr_lt huF hκF hρ hγF hγF h1 (Or.inr hρκ) (Or.inl rfl) fun f hf =>
          FWOrder.k2s hρ f ((mem_fr_iff hζF).mpr ⟨u, hu, hf⟩)
      exact coll_psiY hρ u huF h2 huκ
    have h1 : inC u γ κ = true := inC_of_mem_summands hζF hP.Cxi hu
    have h2 : inC u W (.Psi .zero (.Psi ζ κ γ) W) = true :=
      inC_of_fr_lt huF hκF hw hγF hWF h1 hwκ (Or.inr hγW) fun f hf =>
        hfrκ f ζ (Or.inr (Or.inr rfl)) ((mem_fr_iff hζF).mpr ⟨u, hu, hf⟩)
    exact coll_psiY hw u huF h2 huρ
  have hN : NFL (L₁ ++ L₂) := hsum ▸ nfl_summands hζF
  have hzF := hx.psi.xiF
  have hfz : ∀ f, f ∈ fr κ z → Lt f (.Psi .zero (.Psi ζ κ γ) W) :=
    tail_fr_lt hκF hw rfl hN hzF (by rw [← hsum, ofSummands_summands _ hζF]; exact hzζ) hzL
      (fun f u hu hf => hfrκ f ζ (Or.inr (Or.inr rfl)) ((mem_fr_iff hζF).mpr
        ⟨u, by rw [hsum]; exact List.mem_append_left _ hu, hf⟩))
      fun u hu => hsumw u (by rw [hsum]; exact List.mem_append_right _ hu)
        (lt_of_le_of_ltY ((hN.1 u (List.mem_append_right _ hu)).1) hpF hκF (hL₂ u hu)
          (lt_transY hpF hρ hκF hpρ hρκ))
  refine Or.inl (Or.inr (lt_of_lt_of_leY hx hw hpF ?_ hle))
  have hxρ : Lt (.Psi z κ γ) (.Psi ζ κ γ) :=
    lt_of_lt_of_leY hx hπF hρ (lt_transY hx ht hπF hxt (lt_psi_targetY ht)) (hc.le hπF)
  have hC : inC (.Psi z κ γ) W (.Psi .zero (.Psi ζ κ γ) W) = true := by
    refine inC_psi_iff.mpr (Or.inr ⟨?_, ?_, ?_, hγW⟩)
    · exact inC_of_fr_lt hκF hκF hw hγF hWF hP.Cpi hwκ (Or.inr hγW) fun f hf =>
        hfrκ f κ (Or.inr (Or.inl rfl)) hf
    · exact inC_of_fr_lt hzF hκF hw hγF hWF hx.psi.Cxi hwκ (Or.inr hγW) hfz
    · exact inC_of_fr_lt hγF hκF hw hγF hWF hP.Ca hwκ (Or.inr hγW) fun f hf =>
        hfrκ f γ (Or.inl rfl) hf
  exact coll_psiY hw _ hx hC hxρ

end RTKA.Fund
