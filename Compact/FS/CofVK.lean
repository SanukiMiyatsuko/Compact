import Compact.FS.CofXi

/-! 鎖の端 `ρ = Ξ_m(q)` の族の閉包 `mahloVK` の共終性（`vk_cof`）。

* 節点の分類：目標が `t` と `ρ` の間なら種以下か部分項以下（`LoT`）、`ρ` と `K_m` の間なら隙間（`wit_psi_xi`）、
  `K_m` なら `Ξ_m(b)` で `b < q` か隙間（`xi_cls`）。
* 種 `p ≥ Ψ^0_ρ(W)` で分けた引数の残り（`xi_hW`）は `Ψ^0_ρ(W)` 未満。 -/

namespace RTKA.Fund

open Tm W

/-- `q` の `K_m` についての前線の元は `ρ = Ξ_m(q)` の前線の元 -/
theorem xi_fr_self {q w : Tm} {m : Nat} (hρ : WNF (.Xi m q)) (hw : w ∈ fr (.K m) q) :
    w ∈ fr (.Xi m q) (.Xi m q) := by
  have hm := hρ.xi.1
  have hρK : Lt (.Xi m q) (.K m) := (lt_K_iffY hρ hm).mpr (Nat.le_refl _)
  have h1 : w ∈ fr (.Xi m q) q := fr_sub (WNF.K' hm) hρ (Or.inr hρK) hρ.xi.2.1 hw (FWOrder.k2x hρ w hw)
  have hne : ¬ Lt (Tm.Xi m q) (.Xi m q) := Lt.irrefl _
  rw [fr]
  simp only [hne, ↓reduceIte]
  exact h1

/-- 鎖の端の `q` の前線の元は `π` の前線の元 -/
theorem xi_fr_mem {π q w : Tm} {m : Nat} (hπF : WNF π) (hc : Chain π (.Xi m q)) (hw : w ∈ fr (.K m) q) :
    w ∈ fr π π :=
  hc.fr_mem hπF (xi_fr_self (hc.wnf hπF) hw)

/-- 鎖の端 `Ξ_m(q)` の下の段：目標が `t` と `K_m` の間の節点は種以下か部分項以下 -/
theorem xi_low {π X q p : Tm} {m : Nat} (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Xi m q))
    (hL : LoT (.Psi .zero π X) (.Xi m q) p) : LowC (.Psi .zero π X) (.K m) (some p) := by
  intro x hx hxt htk hkK
  have hπF := ht.psi.piF
  have hρ : WNF (.Xi m q) := hc.wnf hπF
  have hm := hρ.xi.1
  have hl : lev π = m := hc.lev_eq
  have hkF := tgtN_wnf_lt hx htk
  have harg : ∃ a, argR? x = some a := by
    cases x with
    | Psi s k a => exact ⟨a, rfl⟩
    | Xi j b => exact ⟨b, rfl⟩
    | _ => exact absurd htk (not_lt_zero _)
  obtain ⟨a, harg⟩ := harg
  by_cases hkρ : Lt (.Xi m q) (tgtN x)
  · refine Or.inr ?_
    cases x with
    | Psi s k a' =>
      have hl' : lev k = m := by
        have h1 := lev_le_of_lt_gen hxt
        have h2 := lev_le_of_lt_gen hkρ
        simp only [lev, tgtN] at h1 h2 ⊢
        omega
      have hxρ : Lt (.Psi s k a') (.Xi m q) :=
        lt_transY hx ht hρ hxt (lt_of_lt_of_leY ht hπF hρ (lt_psi_targetY ht) (hc.le hπF))
      obtain ⟨-, w, hw, hn⟩ := wit_psi_xi hx hρ hl' hxρ hkρ
      exact subLe_frπ ht (xi_fr_mem hπF hc hw) (le_of_not_ltY (hρ.xi.2.1.of_mem_subs (fr_spec hw).1) hx hn)
    | Xi j b =>
      exfalso
      have hj := hx.xi.1
      have h3 := (lt_K_iffY (WNF.K' hj) hm).mp hkK
      have h4 : Lt (.K j) (.Xi m q) := K_lt_xi hρ (by simp only [lev] at h3; exact h3)
      exact Lt.asymmY (WNF.K' hj) hρ h4 hkρ
    | _ => cases harg
  · rcases hL x a hx hxt harg htk (le_of_not_ltY hρ hkF hkρ) with h | h
    · exact Or.inl ⟨p, rfl, h⟩
    · exact Or.inr h

/-- 鎖の端 `Ξ_m(q)` の段の節点：`b < q` か部分項以下 -/
theorem xi_cls {π X q b : Tm} {m : Nat} (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Xi m q))
    (hx : WNF (.Xi m b)) (hxt : Lt (.Xi m b) (.Psi .zero π X)) :
    Lt b q ∨ SubLe (.Psi .zero π X) (.Xi m b) := by
  have hπF := ht.psi.piF
  have hρ : WNF (.Xi m q) := hc.wnf hπF
  have hm := hρ.xi.1
  have hqF := hρ.xi.2.1
  have hbF := hx.xi.2.1
  have hxρ : Lt (.Xi m b) (.Xi m q) :=
    lt_transY hx ht hρ hxt (lt_of_lt_of_leY ht hπF hρ (lt_psi_targetY ht) (hc.le hπF))
  have hne : b ≠ q := fun e => by
    subst e
    exact Lt.irrefl _ hxρ
  rcases (lt_xi_xi0 hne).mp hxρ with ⟨h, -⟩ | ⟨hqb, hn⟩
  · exact Or.inl h
  · refine Or.inr ?_
    by_cases hall : ∀ w, w ∈ fr (.K m) q → Lt w (.Xi m b)
    · exfalso
      have hxK : Lt (.Xi m b) (.K m) := (lt_K_iffY hx hm).mpr (Nat.le_refl _)
      have hC : inC q b (.Xi m b) = true :=
        inC_of_fr_lt hqF (WNF.K' hm) hx hqF hbF hρ.xi.2.2.2.2 (Or.inr hxK) (Or.inr hqb) hall
      rw [hC] at hn
      cases hn
    · obtain ⟨w, hw, hn'⟩ := exists_of_not_forall_mem _ hall
      exact subLe_frπ ht (xi_fr_mem hπF hc hw) (le_of_not_ltY (hqF.of_mem_subs (fr_spec hw).1) hx hn')

/-- 鎖の端 `Ξ_m(q)` の引数の残り：`w = Ψ^0_ρ(W) ≤ p` について閉じている -/
theorem xi_hW {π X q p W : Tm} {m : Nat} (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Xi m q))
    (hw : WNF (.Psi .zero (.Xi m q) W)) (hle : Le (.Psi .zero (.Xi m q) W) p) (hpF : WNF p)
    (hpρ : Lt p (.Xi m q)) :
    ∀ L₁ L₂, summands q = L₁ ++ L₂ → (∀ u, u ∈ L₂ → Le u p) →
      ∀ b, WNF (.Xi m b) → Lt (.Xi m b) (.Psi .zero π X) → Lt b q → ¬ Lt b (ofSummands L₁) →
      Le (.Xi m b) p ∨ SubLe (.Psi .zero π X) (.Xi m b) := by
  intro L₁ L₂ hsum hL₂ b hx hxt hbq hbL
  have hπF := ht.psi.piF
  have hρ : WNF (.Xi m q) := hc.wnf hπF
  have hm := hρ.xi.1
  have hKF : WNF (.K m) := WNF.K' hm
  have hqF := hρ.xi.2.1
  have hqC := hρ.xi.2.2.2.2
  have hWF := hw.psi.aF
  have hρK : Lt (.Xi m q) (.K m) := (lt_K_iffY hρ hm).mpr (Nat.le_refl _)
  have hwρ : Lt (.Psi .zero (.Xi m q) W) (.Xi m q) := lt_psi_targetY hw
  have hwK : Le (.Psi .zero (.Xi m q) W) (.K m) := Or.inr (lt_transY hw hρ hKF hwρ hρK)
  have hqW : Lt q W := arg_lt_of_psi hw rfl
  -- `q` の前線は `w` 未満
  have hfrw : ∀ f, f ∈ fr (.K m) q → Lt f (.Psi .zero (.Xi m q) W) := fun f hf =>
    FWOrder.k2t hw f (xi_fr_self hρ hf)
  -- `q` の加数で `K_m` 未満のものは `w` 未満
  have hsumw : ∀ u, u ∈ summands q → Lt u (.K m) → Lt u (.Psi .zero (.Xi m q) W) := fun u hu huK => by
    have huF := hqF.of_mem_subs (mem_subs_of_mem_summands hu)
    have h1 : inC u q (.K m) = true := inC_of_mem_summands hqF hqC hu
    have huρ : Lt u (.Xi m q) := by
      have h2 : inC u q (.Xi m q) = true :=
        inC_of_fr_lt huF hKF hρ hqF hqF h1 (Or.inr hρK) (Or.inl rfl) fun f hf =>
          FWOrder.k2x hρ f ((mem_fr_iff hqF).mpr ⟨u, hu, hf⟩)
      exact coll_xi0 hρ u huF h2 huK
    have h2 : inC u W (.Psi .zero (.Xi m q) W) = true :=
      inC_of_fr_lt huF hKF hw hqF hWF h1 hwK (Or.inr hqW) fun f hf =>
        hfrw f ((mem_fr_iff hqF).mpr ⟨u, hu, hf⟩)
    exact coll_psiY hw u huF h2 huρ
  have hN : NFL (L₁ ++ L₂) := hsum ▸ nfl_summands hqF
  have hbF := hx.xi.2.1
  have hfb : ∀ f, f ∈ fr (.K m) b → Lt f (.Psi .zero (.Xi m q) W) :=
    tail_fr_lt hKF hw rfl hN hbF (by rw [← hsum, ofSummands_summands _ hqF]; exact hbq) hbL
      (fun f u hu hf => hfrw f ((mem_fr_iff hqF).mpr ⟨u, by rw [hsum]; exact List.mem_append_left _ hu, hf⟩))
      fun u hu => hsumw u (by rw [hsum]; exact List.mem_append_right _ hu)
        (lt_of_le_of_ltY ((hN.1 u (List.mem_append_right _ hu)).1) hpF hKF (hL₂ u hu)
          (lt_transY hpF hρ hKF hpρ hρK))
  refine Or.inl (Or.inr (lt_of_lt_of_leY hx hw hpF ?_ hle))
  have hxρ : Lt (.Xi m b) (.Xi m q) :=
    lt_transY hx ht hρ hxt (lt_of_lt_of_leY ht hπF hρ (lt_psi_targetY ht) (hc.le hπF))
  have hbW : Lt b W := lt_transY hbF hqF hWF hbq hqW
  have hC : inC (.Xi m b) W (.Psi .zero (.Xi m q) W) = true :=
    inC_xi_iff.mpr (Or.inr ⟨inC_of_fr_lt hbF hKF hw hbF hWF hx.xi.2.2.2.2 hwK (Or.inr hbW) hfb, hbW⟩)
  exact coll_psiY hw _ hx hC hxρ

/-! ### `Ξ` の族の葉 -/

/-- `Ξ_m` の族の `app` の葉（`vk_out` の出力）の共終性 -/
theorem xi_leaf_cof {π X q : Tm} {m : Nat} (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Xi m q))
    (hS : ∀ u, u ∈ summands q → u ≠ .one → SeqI u (info u).seq)
    (hqs : ∀ u, u ∈ summands q → u ≠ .one → u ∈ subs (.Psi .zero π X) ∧ u.size < π.size)
    (hqσ : ∀ σ, WNF σ → Le π σ → inC q q σ = true)
    (hSC : ∀ u, u ∈ summands q → u ≠ .one → SeqC u (info u).seq)
    (P' c : Tm) (pre rest : List Tm) (R : Tm) (hsum : summands q = pre ++ R :: rest) (hR1 : R ≠ .one)
    (hPR : Lt P' R) (hSP : P' ≠ .zero → SeedP π X P') (hPF : WNF P') (hc' : c = .zero ∨ c = .one)
    (hc0 : c = .zero → P' ≠ .zero)
    (hlow : ∀ x y, InSeq (.app π (.xi m) pre R (info R).seq P' c) y →
      (P' ≠ .zero → Lt P' y) → Le (SeqD.app π (.xi m) pre R (info R).seq P' c).first y →
      WNF x → Lt x (.Psi .zero π X) → Lt (.Psi .zero π X) (tgtN x) → Lt (tgtN x) (.K m) → Lt x y)
    (hcls : ∀ x y, InSeq (.app π (.xi m) pre R (info R).seq P' c) y →
      (P' ≠ .zero → Lt P' y) → Le (SeqD.app π (.xi m) pre R (info R).seq P' c).first y →
      WNF x → Lt x (.Psi .zero π X) → ∀ b, x = .Xi m b → Lt b (oadd (ofSummands pre) R) ∨ Lt x y) :
    SeqI (.Psi .zero π X) (.app π (.xi m) pre R (info R).seq P' c) →
      SeqC (.Psi .zero π X) (.app π (.xi m) pre R (info R).seq P' c) := by
  intro hI
  have hπF := ht.psi.piF
  have hρ : WNF (.Xi m q) := hc.wnf hπF
  have hm : 1 ≤ m := hρ.xi.1
  have hqF := hρ.xi.2.1
  have hKF : WNF (.K m) := WNF.K' hm
  have hρK : Lt (.Xi m q) (.K m) := (lt_K_iffY hρ hm).mpr (Nat.le_refl _)
  have hπK : Le π (.K m) := Or.inr (lt_of_le_of_ltY hπF hρ hKF (hc.le hπF) hρK)
  have o := vk_out ht hc hS hqs hqσ P' c pre rest R hsum hR1 hPR hSP hPF hc' hc0
  have hRm : R ∈ summands q := by
    rw [hsum]
    exact List.mem_append_right _ List.mem_cons_self
  have hRF := hqF.of_mem_subs (mem_subs_of_mem_summands hRm)
  have hRp := nfl_principal (nfl_summands hqF) R hRm
  obtain ⟨h0, h1⟩ := dom_ne_of_principal hRF hRp hR1
  have hP0 : P' = .zero ∨ P' ≠ .zero := by
    by_cases h : P' = .zero
    · exact Or.inl h
    · exact Or.inr h
  have hPK : Lt P' (.K m) := by
    rcases hP0 with rfl | h
    · exact zero_lt (by intro e; cases e)
    · exact lt_of_lt_of_leY (hSP h).hF hπF hKF ((hSP h).hπ ht) hπK
  have hPπ : Lt P' π := by
    rcases hP0 with rfl | h
    · exact zero_lt ht.psi.tgt.ne_zero
    · exact (hSP h).hπ ht
  have hPn : P' = .zero ∨ NodeT P' := by
    rcases hP0 with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (hSP h).hn
  have G : XiG m q P' c pre rest R := ⟨hρ, hsum, hPF, hPR, hPK, hc', hR1⟩
  have hPy : ∀ y, InSeq (.app π (.xi m) pre R (info R).seq P' c) y → P' ≠ .zero → Lt P' y :=
    fun y hy => by
      obtain ⟨P'', x, -, -, -, -, -, -, -, hPy, -, -⟩ := o.form y hy
      exact hPy
  have hfy : ∀ y, InSeq (.app π (.xi m) pre R (info R).seq P' c) y →
      Le (SeqD.app π (.xi m) pre R (info R).seq P' c).first y := fun y hy => by
    obtain ⟨P'', x, -, -, -, -, -, -, hle, -, -, -⟩ := o.form y hy
    exact hle
  obtain ⟨hSx, hBx⟩ := xi_argS ht hc G hc0 (hS R hRm hR1) (hSC R hRm hR1) h0 h1 (hqs R hRm hR1).2 hPπ hqσ hPn
  refine cof_xi ht hc.lev_eq hm hI (fun y hy => ?_) hSx hBx
    (fun x y hy hx hxt _ htk hkK => hlow x y hy (hPy y hy) (hfy y hy) hx hxt htk hkK)
    fun x y hy hx hxt _ b e => hcls x y hy (hPy y hy) (hfy y hy) hx hxt b e
  obtain ⟨P'', x, -, e, -⟩ := o.form y hy
  exact ⟨_, e⟩

/-- `mahloVK` の共終性 -/
theorem vk_cof {π X q : Tm} {m : Nat} {P : Option Tm} (ht : WNF (.Psi .zero π X))
    (hc : Chain π (.Xi m q))
    (hS : ∀ u, u ∈ summands q → u ≠ .one → SeqI u (info u).seq)
    (hqs : ∀ u, u ∈ summands q → u ≠ .one → u ∈ subs (.Psi .zero π X) ∧ u.size < π.size)
    (hqσ : ∀ σ, WNF σ → Le π σ → inC q q σ = true)
    (hSC : ∀ u, u ∈ summands q → u ≠ .one → SeqC u (info u).seq)
    (hP : ∀ p, P = some p → SeedP π X p)
    (hne : ∀ p, P = some p → ¬ isSucc q = true → q ≠ .one →
      XiOut π X m q .zero .one (preT (info q).sums) (lastT (info q).sums) (s0X π m q) →
      (s0X π m q).first ≠ p)
    (hLow : LowC (.Psi .zero π X) (.K m) P)
    (hW : ∀ p, P = some p → ¬ isSucc q = true → q ≠ .one → Lt (s0X π m q).first p →
      ∀ L₁ L₂, summands q = L₁ ++ L₂ → (∀ u, u ∈ L₂ → Le u p) →
      ∀ b, WNF (.Xi m b) → Lt (.Xi m b) (.Psi .zero π X) → Lt b q → ¬ Lt b (ofSummands L₁) →
      Le (.Xi m b) p ∨ SubLe (.Psi .zero π X) (.Xi m b)) :
    SeqI (.Psi .zero π X) (mahloVK m q (info q).sums π P) →
      SeqC (.Psi .zero π X) (mahloVK m q (info q).sums π P) := by
  have hπF := ht.psi.piF
  have hρ : WNF (.Xi m q) := hc.wnf hπF
  have hm : 1 ≤ m := hρ.xi.1
  have hqF := hρ.xi.2.1
  have hq0 : q ≠ .zero := hρ.xi.2.2.1
  have hqC := hρ.xi.2.2.2.2
  have hKF : WNF (.K m) := WNF.K' hm
  have hρK : Lt (.Xi m q) (.K m) := (lt_K_iffY hρ hm).mpr (Nat.le_refl _)
  have hπK : Lt π (.K m) := lt_of_le_of_ltY hπF hρ hKF (hc.le hπF) hρK
  have hl : lev π = m := hc.lev_eq
  have hqρ : inC q q (.Xi m q) = true :=
    inC_of_fr_lt hqF hKF hρ hqF hqF hqC (Or.inr hρK) (Or.inl rfl) fun w hw => FWOrder.k2x hρ w hw
  have hSne : ∀ {p : Tm}, SeedP π X p → p ≠ .zero := fun Sp => by
    rcases Sp.hn with ⟨m', a, e⟩ | ⟨s, q', a, e⟩ <;> rw [e] <;> simp
  have hKt : ∀ j, WNF (.K j) → Lt (.K j) (.Psi .zero π X) → j + 1 ≤ m := fun j _ h => by
    have := lev_le_of_lt_gen h
    simp only [lev] at this
    omega
  have hCls : ∀ b, WNF (.Xi m b) → Lt (.Xi m b) (.Psi .zero π X) →
      Lt b q ∨ SubLe (.Psi .zero π X) (.Xi m b) := fun b hx hxt => xi_cls ht hc hx hxt
  -- 塔の葉
  have htowC : ∀ G, WNF G → (∀ p, P = some p → Le p G) → (∀ j, WNF (.K j) → j + 1 ≤ m → Le (.K j) G) →
      (∀ b, WNF (.Xi m b) → Lt (.Xi m b) (.Psi .zero π X) → Lt b q →
        Le (.Xi m b) G ∨ SubLe (.Psi .zero π X) (.Xi m b)) →
      SeqI (.Psi .zero π X) (.tower G) → SeqC (.Psi .zero π X) (.tower G) :=
    fun G hGF hPG hKG hXG hI' =>
      leaf_tower ht hGF hI' (fun j hj hjt => hKG j hj (hKt j hj hjt)) fun x hx hxt htk => by
        rcases xi_node_split ht hl hm hx hxt htk with hkK | ⟨b, rfl⟩
        · rcases hLow x hx hxt htk hkK with ⟨p, e, h⟩ | h
          · exact Or.inl (le_transY hx (hP p e).hF hGF h (hPG p e))
          · exact Or.inr h
        · rcases hCls b hx hxt with hbq | h
          · exact hXG b hx hxt hbq
          · exact Or.inr h
  unfold mahloVK
  by_cases h1 : q = .one
  · rw [ite_eq_left h1]
    obtain ⟨hfF, -, -⟩ := floorLev_lt ht hl hm
    have hG0 : WNF (maxO P (floorLev m)) ∧ Le (floorLev m) (maxO P (floorLev m)) ∧
        ∀ p, P = some p → Le p (maxO P (floorLev m)) := by
      cases P with
      | none => exact ⟨hfF, Or.inl rfl, fun p e => by cases e⟩
      | some p =>
        have Sp := hP p rfl
        unfold maxO
        by_cases h : ltB p (floorLev m) = true
        · simp only [h, ↓reduceIte]
          exact ⟨hfF, Or.inl rfl, fun p' e => by
            cases e
            exact Or.inr (ltB_iff.mp h)⟩
        · simp only [h, ↓reduceIte]
          exact ⟨Sp.hF, le_of_not_ltY Sp.hF hfF fun h' => h (ltB_iff.mpr h'), fun p' e => by
            cases e
            exact Or.inl rfl⟩
    obtain ⟨g1, g2, g3⟩ := hG0
    refine htowC _ g1 g3 (fun j hj hjm => le_transY hj hfF g1 (K_le_floorLev hj hjm) g2) fun b hb _ hbq => ?_
    exfalso
    rw [h1] at hbq
    exact hb.xi.2.2.1 (lt_oneY hb.xi.2.1 hbq)
  rw [ite_eq_right h1]
  by_cases hs : isSucc q = true
  · rw [ite_eq_left hs]
    have hpq : Lt (pred q) q := pred_lt hqF hs
    have hpF := wnf_pred hqF
    have hpne : pred q ≠ .zero := by
      intro e
      apply h1
      rw [← succT_pred hqF hs, e]
      rfl
    have hy₁ : WNF (.Xi m (pred q)) := wnf_xi_mk hm hpF hpne
      (ne_gt_of_le (le_transY hpF hqF (WNF.succK hm) (Or.inr hpq)
        (le_of_ne_gtY hqF (WNF.succK hm) hρ.xi.2.2.2.1)))
      (inC_pred_self hqF hs hqC)
    have Sx : SeedP π X (.Xi m (pred q)) := seedX ht hc hy₁
      ((lt_xi_xi0 hpq.ne).mpr (Or.inl ⟨hpq, inC_pred_of hqF hqρ⟩)) hpq fun g d h => inC_pred_of hqF h
    obtain ⟨S1, S2, S3⟩ := maxO_seed Sx hP
    have hS0 : maxO P (.Xi m (pred q)) ≠ .zero := hSne S1
    have hy₁K : Lt (.Xi m (pred q)) (.K m) := (lt_K_iffY hy₁ hm).mpr (Nat.le_refl _)
    -- `pred q` の加数の前線と、`π` 未満の加数は `y₁ = Ξ_m(pred q)` 未満
    have hfr₁ : ∀ f u, u ∈ summands (pred q) → f ∈ fr (.K m) u → Lt f (.Xi m (pred q)) := fun f u hu hf =>
      FWOrder.k2x hy₁ f ((mem_fr_iff hpF).mpr ⟨u, hu, hf⟩)
    have hsm₁ : ∀ u, u ∈ summands (pred q) → Lt u π → Lt u (.Xi m (pred q)) := fun u hu huπ => by
      have huF := hpF.of_mem_subs (mem_subs_of_mem_summands hu)
      have h3 : inC u (pred q) (.K m) = true := inC_of_mem_summands hpF (inC_pred_self hqF hs hqC) hu
      have h4 : inC u (pred q) (.Xi m (pred q)) = true :=
        inC_of_fr_lt huF hKF hy₁ hpF hpF h3 (Or.inr hy₁K) (Or.inl rfl) fun f hf => hfr₁ f u hu hf
      exact coll_xi0 hy₁ u huF h4 (lt_transY huF hπF hKF huπ hπK)
    have hble : ∀ b, WNF (.Xi m b) → Lt b q → Le b (pred q) := fun b hb hbq =>
      le_of_lt_succT hb.xi.2.1 hpF (by rw [succT_pred hqF hs]; exact hbq)
    have hps : summands (pred q) = (info q).sums.dropLast.map Prod.fst := by
      rw [sums_pred hqF, info_sums_fst]
    have hKG : ∀ j, WNF (.K j) → j + 1 ≤ m → Le (.K j) (maxO P (.Xi m (pred q))) := fun j hj hjm =>
      Or.inr (lt_of_lt_of_leY hj hy₁ S1.hF (K_lt_xi hy₁ hjm) S2)
    cases hsp : splitPosD π (info q).sums.dropLast with
    | none =>
      -- `pred q` の加数は全て `π` 未満
      have hall : ∀ u, u ∈ summands (pred q) → Lt u π := by
        refine all_lt_of_head hπF (nfl_summands hpF) fun q' tl e h' => ?_
        rw [hps] at e
        cases hd : (info q).sums.dropLast with
        | nil =>
          rw [hd] at e
          cases e
        | cons q'' tl' =>
          rw [hd] at e hsp
          simp only [List.map_cons, List.cons.injEq] at e
          have hq := splitPosD_none_head hsp
          rw [e.1, leB_iff.mpr (ne_gt_of_le h')] at hq
          cases hq
      have hpy : Lt (pred q) (.Xi m (pred q)) := by
        cases hsp' : summands (pred q) with
        | nil =>
          rw [eq_zero_of_summands_nil hsp']
          exact zero_lt (by intro e; cases e)
        | cons u l =>
          have hum : u ∈ summands (pred q) := by rw [hsp']; exact List.mem_cons_self
          exact lt_prin_of_head hsp' rfl ((nfl_summands hpF).1 u hum).2 (hsm₁ u hum (hall u hum))
      show SeqI _ (.tower (maxO P (.Xi m (pred q)))) → SeqC _ (.tower (maxO P (.Xi m (pred q))))
      refine htowC _ S1.hF S3 hKG fun b hb _ hbq => Or.inl ?_
      have hbF := hb.xi.2.1
      refine le_transY hb hy₁ S1.hF (le_xi_of_fr hb hy₁ (hble b hb hbq) fun f hf => ?_) S2
      have hfF := hbF.of_mem_subs (fr_spec hf).1
      exact lt_of_le_of_ltY hfF hpF hy₁ (le_transY hfF hbF hpF (fr_leY hKF hbF hf) (hble b hb hbq)) hpy
    | some q' =>
      obtain ⟨pre, R, r⟩ := q'
      obtain ⟨⟨rest, hsum⟩, rfl, hπR⟩ := split_pos hs hsp
      obtain ⟨L, rest', hys, hL, -, hhd⟩ := splitPosD_rest hsp
      have hRm : R ∈ summands q := by
        rw [hsum]
        exact List.mem_append_right _ List.mem_cons_self
      have hRF := hqF.of_mem_subs (mem_subs_of_mem_summands hRm)
      have hπR' : Le π R := le_of_ne_gtY hπF hRF (leB_iff.mp hπR)
      have hpR : Lt (maxO P (.Xi m (pred q))) R := lt_of_lt_of_leY S1.hF hπF hRF (S1.hπ ht) hπR'
      have hR1 : R ≠ .one := by
        intro e
        rw [e] at hpR
        exact hS0 (lt_oneY S1.hF hpR)
      have hsump : summands (pred q) = (pre ++ [R]) ++ rest'.map Prod.fst := by
        rw [hps, hys, List.map_append, hL, List.map_cons]
        simp
      have hNp : NFL ((pre ++ [R]) ++ rest'.map Prod.fst) := hsump ▸ nfl_summands hpF
      have hrest' : ∀ u, u ∈ rest'.map Prod.fst → Lt u π := by
        refine all_lt_of_head hπF (nfl_append_right hNp) fun q'' tl e h' => ?_
        cases hr : rest' with
        | nil =>
          rw [hr] at e
          cases e
        | cons q3 tl' =>
          rw [hr] at e
          simp only [List.map_cons, List.cons.injEq] at e
          have hq := hhd q3 tl' hr
          rw [e.1, leB_iff.mpr (ne_gt_of_le h')] at hq
          cases hq
      have hT : ofSummands (pre ++ [R]) = oadd (ofSummands pre) R :=
        eq_oadd_of_sum (wnf_ofSummands (nfl_append_left hNp)) (summands_ofSummands _ (nfl_principal
          (nfl_append_left hNp)))
      have hpe : pred q = ofSummands ((pre ++ [R]) ++ rest'.map Prod.fst) := by
        rw [← hsump, ofSummands_summands _ hpF]
      dsimp only
      rw [mkApp_xi (Or.inr (ltB_iff.mpr hpR))]
      simp only
      intro hI
      have hLow' := hLow.mono' S1.hF fun p e => ⟨(hP p e).hF, S3 p e⟩
      refine xi_leaf_cof ht hc hS hqs hqσ hSC _ .zero pre rest R hsum hR1 hpR (fun _ => S1) S1.hF (Or.inl rfl)
        (fun _ => hS0) (fun x y hy hPy _ hx hxt htk hkK => ?_) (fun x y hy hPy _ hx hxt b e => ?_) hI
      · have hyF := seqI_wnf hI hy
        rcases hLow' x hx hxt htk hkK with ⟨p', e, h⟩ | h
        · cases e
          exact lt_of_le_of_ltY hx S1.hF hyF h (hPy hS0)
        · exact h.lt ht hx hyF (seqI_gp hI rfl hy)
      · subst e
        have hyF := seqI_wnf hI hy
        rcases hCls b hx hxt with hbq | hsub
        · by_cases hbT : Lt b (oadd (ofSummands pre) R)
          · exact Or.inl hbT
          · refine Or.inr ?_
            have hbF := hx.xi.2.1
            have hble' := hble b hx hbq
            have hfrb : ∀ f, f ∈ fr (.K m) b → Lt f (.Xi m (pred q)) := by
              rcases hble' with e | hbp
              · intro f hf
                rw [e] at hf
                exact FWOrder.k2x hy₁ f hf
              · refine tail_fr_lt hKF hy₁ rfl hNp hbF (by rw [← hpe]; exact hbp) (by rw [hT]; exact hbT)
                  (fun f u hu hf => hfr₁ f u (by rw [hsump]; exact List.mem_append_left _ hu) hf)
                  fun u hu => hsm₁ u (by rw [hsump]; exact List.mem_append_right _ hu) (hrest' u hu)
            exact lt_of_le_of_ltY hx S1.hF hyF (le_transY hx hy₁ S1.hF (le_xi_of_fr hx hy₁ hble' hfrb) S2)
              (hPy hS0)
        · exact Or.inr (hsub.lt ht hx hyF (seqI_gp hI rfl hy))
  · rw [ite_eq_right hs]
    have hsum := summands_pre_last hq0
    have hlast : lastS (info q).sums = (info (lastT (info q).sums)).seq := lastS_coh (coh_sums q)
    obtain ⟨pre, hpr⟩ : ∃ pre, pre = preT (info q).sums := ⟨_, rfl⟩
    obtain ⟨R, hR⟩ : ∃ R, R = lastT (info q).sums := ⟨_, rfl⟩
    rw [← hpr, ← hR] at hsum
    rw [← hR] at hlast
    have hRm : R ∈ summands q := by
      rw [hsum]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have hR1 : R ≠ .one := by
      intro e
      apply hs
      show (summands q).getLast? == some one
      rw [hsum, e]
      simp
    have hRp := nfl_principal (nfl_summands hqF) R hRm
    have hR0 : R ≠ .zero := by
      intro e
      rw [e] at hRp
      cases hRp
    have hs0 : s0X π m q = .app π (.xi m) pre R (info R).seq .zero .one := by
      unfold s0X
      rw [← hpr, ← hR, hlast]
    have o0 := vk_out ht hc hS hqs hqσ .zero .one pre [] R hsum hR1 (zero_lt hR0) (fun h => absurd rfl h) WNF.zero
      (Or.inr rfl) (fun e => by cases e)
    rw [← hs0] at o0
    obtain ⟨P₀, x₀, -, hx₀, hfF, -, -, -, -, -, -, -⟩ := o0.form _ o0.mem
    have hne' : ∀ p, P = some p → (s0X π m q).first ≠ p := fun p e =>
      hne p e hs h1 (by rw [← hpr, ← hR]; exact o0)
    dsimp only
    rw [← hpr, ← hR, hlast, ← hs0]
    have hTq : oadd (ofSummands pre) R = q := (eq_oadd_of_sum hqF hsum).symm
    have hKs0 : ∀ j, WNF (.K j) → j + 1 ≤ m → Lt (.K j) (s0X π m q).first := fun j _ hjm => by
      rw [hx₀]
      exact K_lt_xi (by rw [← hx₀]; exact hfF) hjm
    -- 素の列 `s0`
    have hs0cof : (∀ x y, InSeq (s0X π m q) y → WNF y → Gp (.Psi .zero π X) y → Le (s0X π m q).first y →
        WNF x → Lt x (.Psi .zero π X) → Lt (.Psi .zero π X) (tgtN x) → Lt (tgtN x) (.K m) → Lt x y) →
        SeqI (.Psi .zero π X) (s0X π m q) → SeqC (.Psi .zero π X) (s0X π m q) := fun hlow hI => by
      rw [hs0] at hI ⊢
      refine xi_leaf_cof ht hc hS hqs hqσ hSC .zero .one pre [] R hsum hR1 (zero_lt hR0) (fun h => absurd rfl h)
        WNF.zero (Or.inr rfl) (fun e => by cases e) (fun x y hy _ hfy hx hxt htk hkK => ?_)
        (fun x y hy _ _ hx hxt b e => ?_) hI
      · exact hlow x y (by rw [hs0]; exact hy) (seqI_wnf hI hy) (seqI_gp hI rfl hy) (by rw [hs0]; exact hfy) hx hxt
          htk hkK
      · subst e
        rcases hCls b hx hxt with hbq | hsub
        · exact Or.inl (by rw [hTq]; exact hbq)
        · exact Or.inr (hsub.lt ht hx (seqI_wnf hI hy) (seqI_gp hI rfl hy))
    cases P with
    | none =>
      exact hs0cof fun x y _ hyF hG _ hx hxt htk hkK => by
        rcases hLow x hx hxt htk hkK with ⟨p, e, -⟩ | h
        · cases e
        · exact h.lt ht hx hyF hG
    | some p =>
      have Sp := hP p rfl
      simp only
      by_cases h2 : ltB p (s0X π m q).first = true
      · rw [ite_eq_left h2]
        exact hs0cof fun x y _ hyF hG hfy hx hxt htk hkK => by
          rcases hLow x hx hxt htk hkK with ⟨p', e, h⟩ | h
          · cases e
            exact lt_of_le_of_ltY hx Sp.hF hyF h (lt_of_lt_of_leY Sp.hF hfF hyF (ltB_iff.mp h2) hfy)
          · exact h.lt ht hx hyF hG
      · rw [ite_eq_right h2, ite_eq_right (hne' p rfl)]
        have hlt : Lt (s0X π m q).first p := by
          rcases triY hfF Sp.hF with h | h | h
          · exact h
          · exact absurd h (hne' p rfl)
          · exact absurd (ltB_iff.mpr h) h2
        cases hsp : splitGtD p (info q).sums with
        | none =>
          have hall : ∀ u, u ∈ summands q → Le u p := fun u hu => by
            cases hxs : (info q).sums with
            | nil =>
              rw [← info_sums_fst, hxs] at hu
              cases hu
            | cons q'' ys =>
              rw [hxs] at hsp
              have h0' := splitGtD_none_head hsp
              have hN := nfl_summands hqF
              rw [← info_sums_fst, hxs] at hu hN
              simp only [List.map_cons] at hu hN
              have hqF' := (hN.1 q''.1 List.mem_cons_self).1
              have hqp : Le q''.1 p := le_of_not_ltY Sp.hF hqF' fun h => by rw [ltB_iff.mpr h] at h0'; cases h0'
              exact le_transY (hN.1 u hu).1 hqF' Sp.hF (le_head_mem hN hu) hqp
          show SeqI _ (.tower p) → SeqC _ (.tower p)
          exact htowC p Sp.hF (fun p' e => by
            cases e
            exact Or.inl rfl) (fun j hj hjm => Or.inr (lt_transY hj hfF Sp.hF (hKs0 j hj hjm) hlt))
            fun b hb hbt hbq => hW p rfl hs h1 hlt [] (summands q) (by simp) hall b hb hbt hbq fun h => not_lt_zero _ h
        | some q' =>
          obtain ⟨pre₂, R₂, r₂⟩ := q'
          obtain ⟨L, rest, hys, hL, hpR₂, -, hhd⟩ := splitGtD_spec hsp
          have hsum₂ : summands q = pre₂ ++ R₂ :: rest.map Prod.fst := by
            rw [← info_sums_fst, hys, List.map_append, hL, List.map_cons]
          have hrc : r₂ = (info R₂).seq := by
            have hm' : (R₂, r₂) ∈ (info q).sums := by
              rw [hys]
              simp
            exact coh_sums q (R₂, r₂) hm'
          subst hrc
          have hpR' : Lt p R₂ := ltB_iff.mp hpR₂
          have hR₂1 : R₂ ≠ .one := by
            intro e
            rw [e] at hpR'
            exact hSne Sp (lt_oneY Sp.hF hpR')
          have hN₂ : NFL ((pre₂ ++ [R₂]) ++ rest.map Prod.fst) := by
            have h' := nfl_summands hqF
            rw [hsum₂] at h'
            simpa using h'
          have hT₂ : ofSummands (pre₂ ++ [R₂]) = oadd (ofSummands pre₂) R₂ :=
            eq_oadd_of_sum (wnf_ofSummands (nfl_append_left hN₂)) (summands_ofSummands _ (nfl_principal
              (nfl_append_left hN₂)))
          have hrestp : ∀ u, u ∈ rest.map Prod.fst → Le u p := by
            intro u hu
            have hNr := nfl_append_right hN₂
            cases hr : rest with
            | nil =>
              rw [hr] at hu
              cases hu
            | cons q'' tl =>
              rw [hr] at hu hNr
              simp only [List.map_cons] at hu hNr
              have hq := hhd q'' tl hr
              have hqF' := (hNr.1 q''.1 List.mem_cons_self).1
              have hqp : Le q''.1 p := le_of_not_ltY Sp.hF hqF' fun h => by rw [ltB_iff.mpr h] at hq; cases hq
              exact le_transY (hNr.1 u hu).1 hqF' Sp.hF (le_head_mem hNr hu) hqp
          dsimp only
          rw [mkApp_xi (Or.inr hpR₂)]
          simp only
          intro hI
          refine xi_leaf_cof ht hc hS hqs hqσ hSC p .zero pre₂ _ R₂ hsum₂ hR₂1 hpR' (fun _ => Sp) Sp.hF
            (Or.inl rfl) (fun _ => hSne Sp) (fun x y hy hPy _ hx hxt htk hkK => ?_)
            (fun x y hy hPy _ hx hxt b e => ?_) hI
          · have hyF := seqI_wnf hI hy
            rcases hLow x hx hxt htk hkK with ⟨p', e, h⟩ | h
            · cases e
              exact lt_of_le_of_ltY hx Sp.hF hyF h (hPy (hSne Sp))
            · exact h.lt ht hx hyF (seqI_gp hI rfl hy)
          · subst e
            have hyF := seqI_wnf hI hy
            have hG := seqI_gp hI rfl hy
            rcases hCls b hx hxt with hbq | hsub
            · by_cases hbT : Lt b (oadd (ofSummands pre₂) R₂)
              · exact Or.inl hbT
              · exact Or.inr (lt_of_le_seed ht Sp.hF hx hyF (hPy (hSne Sp)) hG
                  (hW p rfl hs h1 hlt (pre₂ ++ [R₂]) (rest.map Prod.fst) (by rw [hsum₂]; simp) hrestp b hx hxt hbq
                    (by rw [hT₂]; exact hbT)))
            · exact Or.inr (hsub.lt ht hx hyF hG)

end RTKA.Fund
