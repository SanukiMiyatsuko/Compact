import Compact.FS.Xi

/-! 目標の族の再帰：`t = Ψ^0_π(X)` の鎖の上の `famSeq` の列の不変量（`fam_rec`）。

種 `p` が鎖の段 `ρ` への崩壊 `Ψ^0_ρ(W)` 以上で `t` の部分項を支配する（`Dom`）とき、`ρ` の族の閉包 `famSeq` は `t` の列になる。 -/

namespace RTKA.Fund

open Tm W

theorem Chain.subs {π ρ : Tm} (hc : Chain π ρ) : ρ ∈ subs π := by
  induction hc with
  | refl π => exact self_mem_subs π
  | step _ ih => exact subs_psi_p ih

theorem Chain.snoc {π ρ : Tm} (hc : Chain π ρ) : ∀ {ζ κ γ : Tm}, ρ = .Psi ζ κ γ → Chain π κ := by
  induction hc with
  | refl π =>
    intro ζ κ γ e
    subst e
    exact .step (.refl κ)
  | step _ ih =>
    intro ζ κ γ e
    exact .step (ih e)

/-- 鎖の上の目標の前線は `π` の前線 -/
theorem Chain.fr_mem {π ρ : Tm} (hc : Chain π ρ) : WNF π → ∀ {w : Tm}, w ∈ fr ρ ρ → w ∈ fr π π := by
  induction hc with
  | refl _ => exact fun _ _ h => h
  | step _ ih =>
    intro hπ w hw
    exact fr_tgt_step hπ (ih hπ.psi.piF hw)

/-- 鎖の段の組 -/
def chainT (π ζ κ γ g d : Tm) : Prop :=
  (g = γ ∧ d = .Psi ζ κ γ) ∨
    (WNF g ∧ WNF d ∧ Le π d ∧ ¬ Lt (.Psi ζ κ γ) d ∧ inC (.Psi ζ κ γ) g d = true)

/-- 鎖の上の `ρ = Ψ^ζ_κ(γ)` の文脈 -/
theorem mctx_chain {π X ζ κ γ : Tm} (ht : WNF (.Psi .zero π X)) (hc : Chain π (.Psi ζ κ γ)) :
    MCtx π X κ γ ζ (chainT π ζ κ γ) := by
  have hπF := ht.psi.piF
  have hρ : WNF (.Psi ζ κ γ) := hc.wnf hπF
  have hP := hρ.psi
  have hκF := hP.piF
  have hγF := hP.aF
  have hζF := hP.xiF
  have hρκ : Lt (.Psi ζ κ γ) κ := lt_psi_targetY hρ
  have hπρ : Le π (.Psi ζ κ γ) := hc.le hπF
  have hπκ : Lt π κ := lt_of_le_of_ltY hπF hρ hκF hπρ hρκ
  have hγρ : inC γ γ (.Psi ζ κ γ) = true :=
    inC_of_fr_lt hγF hκF hρ hγF hγF hP.Ca (Or.inr hρκ) (Or.inl rfl) fun w hw => FWOrder.k2 hρ w hw
  have hζρ : inC ζ γ (.Psi ζ κ γ) = true :=
    inC_of_fr_lt hζF hκF hρ hγF hγF hP.Cxi (Or.inr hρκ) (Or.inl rfl) fun w hw => FWOrder.k2s hρ w hw
  have hκρ : inC κ γ (.Psi ζ κ γ) = true := inC_tgt_of_k2t hρ fun w hw => FWOrder.k2t hρ w hw
  have hsF : WNF (succT γ) := succT_WNF hγF
  have hvC : inC (succT γ) (succT γ) κ = true :=
    inC_succT (inC_mono_proper hκF hγF hP.Ca fun v hv _ hl =>
      lt_transY (hγF.of_mem_subs hv) hγF hsF hl (lt_succT γ))
  exact
    { ht := ht
      hv := wnf_psi0 hκF hP.tgt hsF hvC fun r hr =>
        lt_transY (wnf_of_argR hκF hr) hγF hsF (arg_lt_of_psi hρ hr) (lt_succT γ)
      hYC := hP.Ca
      hτY := fun r hr => arg_lt_of_psi hρ hr
      hle := Or.inr hπκ
      hlev := hc.lev_eq
      hYF := hγF
      hYm := fun u hu => subs_trans (subs_psi_p hc.subs) (subs_psi_a (mem_subs_of_mem_summands hu))
      hμF := hζF
      hμY := fun _ => le_of_ne_gtY hζF hγF hP.le
      hμm := Or.inr hP.mlt
      hμ1 := hP.Cxi
      hμ2 := hP.mC
      hμσ := fun σ hσ hπσ => by
        have hms := FWOrder.ms hρ
        by_cases hσρ : Lt σ (.Psi ζ κ γ)
        · refine inC_of_fr_lt hζF hρ hσ hζF hζF hms (Or.inr hσρ) (Or.inl rfl) fun w hw => ?_
          exact lt_of_lt_of_leY (hζF.of_mem_subs (fr_spec hw).1) hπF hσ
            (fr_spec (hc.fr_mem hπF (fr_psi_self (Or.inl rfl) hw))).2 hπσ
        · exact inC_mono_d hρ hσ (le_of_not_ltY hσ hρ hσρ) hζF hms
      comp := fun g d h => by
        obtain ⟨hρC, hnρ⟩ := h.tgt ht hc
        obtain ⟨hdt, -⟩ := h.comp ht
        rcases inC_psi_iff.mp hρC with h' | ⟨h1, h2, h3, h4⟩
        · exact absurd h' hnρ
        · exact ⟨Or.inr (lt_of_le_of_ltY h.2.1 ht hκF hdt (lt_transY ht hπF hκF (lt_psi_targetY ht) hπκ)),
            h1, h3, h4, h2⟩
      hT := fun g d h => by
        rcases h with ⟨rfl, rfl⟩ | ⟨hg, hd, hle, hn, hC⟩
        · exact ⟨hγF, hρ, hπρ, Or.inr hρκ, hκρ, hγρ, Or.inl rfl, hζρ⟩
        · rcases inC_psi_iff.mp hC with h' | ⟨h1, h2, h3, h4⟩
          · exact absurd h' hn
          · exact ⟨hg, hd, hle, Or.inr (lt_of_le_of_ltY hd hρ hκF (le_of_not_ltY hρ hd hn) hρκ), h1, h3,
              Or.inr h4, h2⟩
      ltT := fun y hy hlt hC =>
        hc.lt_base hπF hy (coll_psiY hρ y hy (hC γ _ (Or.inl ⟨rfl, rfl⟩)) hlt)
          fun g d hg hd hle hn hC' => hC g d (Or.inr ⟨hg, hd, hle, hn, hC'⟩)
      ltI := fun z hy hzζ hC => by
        have hne : Tm.Psi z κ γ ≠ .Psi ζ κ γ := fun e => hzζ.ne (Tm.Psi.inj e).1
        have h1 : Lt (.Psi z κ γ) (.Psi ζ κ γ) :=
          (lt_psi_psiY rfl hne).mpr (Or.inr ⟨hρκ, lt_psi_targetY hy, Or.inr (Or.inr (Or.inl
            ⟨cmp_self _, rfl, hzζ, hC γ _ (Or.inl ⟨rfl, rfl⟩)⟩))⟩)
        refine hc.lt_base hπF hy h1 fun g d hg hd hle hn hC' => ?_
        rcases inC_psi_iff.mp hC' with h' | ⟨h2, -, h4, h5⟩
        · exact absurd h' hn
        · exact inC_psi_iff.mpr (Or.inr ⟨h2, hC g d (Or.inr ⟨hg, hd, hle, hn, hC'⟩), h4, h5⟩) }

theorem not_tgt_zero (h : IsTgt .zero) : False := by
  rcases h with ⟨c, e, -⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, -⟩ <;> cases e
theorem not_tgt_one (h : IsTgt .one) : False := by
  rcases h with ⟨c, e, -⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, -⟩ <;> cases e
theorem not_tgt_K {m : Nat} (h : IsTgt (.K m)) : False := by
  rcases h with ⟨c, e, -⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, -⟩ <;> cases e
theorem not_tgt_plus {a b : Tm} (h : IsTgt (.plus a b)) : False := by
  rcases h with ⟨c, e, -⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, -⟩ <;> cases e

/-- 鎖の上の部分項は `t` と異なり、`π` より小さい -/
theorem chain_sub {π X ρ u : Tm} (hc : Chain π ρ) (hu : u ∈ subs ρ) (hne : u ≠ ρ) :
    u ∈ subs (.Psi .zero π X) ∧ u.size < π.size ∧ u ≠ .Psi .zero π X := by
  have h1 := size_lt_of_mem_subs_ne hu hne
  have h2 := size_le_of_mem_subs hc.subs
  have h3 : u.size < π.size := by omega
  refine ⟨subs_trans (subs_psi_p hc.subs) hu, h3, ne_of_size_lt ?_⟩
  simp only [Tm.size]
  omega

/-- 鎖の上の `Ψ^ζ_κ(γ)` の成分の加数の不変量 -/
theorem psi_parts {π X ζ κ γ : Tm}
    (hIH : ∀ u, u ∈ subs (.Psi .zero π X) → u ≠ .Psi .zero π X → SeqI u (info u).seq)
    (hc : Chain π (.Psi ζ κ γ)) :
    (∀ u, u ∈ summands γ → u ≠ .one → SeqI u (info u).seq) ∧
      (∀ u, u ∈ summands ζ → u ≠ .one → SeqI u (info u).seq) ∧
      ∀ u, u ∈ summands ζ → u ≠ .one → u ∈ subs (.Psi .zero π X) ∧ u.size < π.size := by
  have hne0 : ∀ {u : Tm}, u ∈ subs ζ → u ≠ .Psi ζ κ γ := fun hu =>
    ne_of_size_lt (by
      have := size_le_of_mem_subs hu
      simp only [Tm.size]
      omega)
  have hne1 : ∀ {u : Tm}, u ∈ subs γ → u ≠ .Psi ζ κ γ := fun hu =>
    ne_of_size_lt (by
      have := size_le_of_mem_subs hu
      simp only [Tm.size]
      omega)
  refine ⟨fun u hu _ => ?_, fun u hu _ => ?_, fun u hu _ => ?_⟩
  · obtain ⟨h1, -, h3⟩ := chain_sub (X := X) hc (subs_psi_a (mem_subs_of_mem_summands hu))
      (hne1 (mem_subs_of_mem_summands hu))
    exact hIH u h1 h3
  · obtain ⟨h1, -, h3⟩ := chain_sub (X := X) hc (subs_psi_s (mem_subs_of_mem_summands hu))
      (hne0 (mem_subs_of_mem_summands hu))
    exact hIH u h1 h3
  · obtain ⟨h1, h2, -⟩ := chain_sub (X := X) hc (subs_psi_s (mem_subs_of_mem_summands hu))
      (hne0 (mem_subs_of_mem_summands hu))
    exact ⟨h1, h2⟩

/-- 鎖の上の `Ξ_m(q)` の添字の成分 -/
theorem xi_parts {π X q : Tm} {m : Nat} (ht : WNF (.Psi .zero π X))
    (hIH : ∀ u, u ∈ subs (.Psi .zero π X) → u ≠ .Psi .zero π X → SeqI u (info u).seq)
    (hc : Chain π (.Xi m q)) :
    (∀ u, u ∈ summands q → u ≠ .one → SeqI u (info u).seq) ∧
    (∀ u, u ∈ summands q → u ≠ .one → u ∈ subs (.Psi .zero π X) ∧ u.size < π.size) ∧
    ∀ σ, WNF σ → Le π σ → inC q q σ = true := by
  have hπF := ht.psi.piF
  have hρ : WNF (.Xi m q) := hc.wnf hπF
  have hqF := hρ.xi.2.1
  have hKF : WNF (.K m) := WNF.K' hρ.xi.1
  have hρK : Lt (.Xi m q) (.K m) := (lt_K_iffY hρ hρ.xi.1).mpr (Nat.le_refl _)
  have hqρ : inC q q (.Xi m q) = true :=
    inC_of_fr_lt hqF hKF hρ hqF hqF hρ.xi.2.2.2.2 (Or.inr hρK) (Or.inl rfl) fun w hw => FWOrder.k2x hρ w hw
  have hne0 : ∀ {u : Tm}, u ∈ subs q → u ≠ .Xi m q := fun hu =>
    ne_of_size_lt (by
      have := size_le_of_mem_subs hu
      simp only [Tm.size]
      omega)
  have hsub : ∀ {u : Tm}, u ∈ summands q → u ∈ subs q := fun hu => mem_subs_of_mem_summands hu
  refine ⟨fun u hu _ => ?_, fun u hu _ => ?_, fun σ hσ hπσ => ?_⟩
  · obtain ⟨h1, -, h3⟩ := chain_sub (X := X) hc (subs_xi (hsub hu)) (hne0 (hsub hu))
    exact hIH u h1 h3
  · obtain ⟨h1, h2, -⟩ := chain_sub (X := X) hc (subs_xi (hsub hu)) (hne0 (hsub hu))
    exact ⟨h1, h2⟩
  · by_cases hσρ : Lt σ (.Xi m q)
    · refine inC_of_fr_lt hqF hρ hσ hqF hqF hqρ (Or.inr hσρ) (Or.inl rfl) fun w hw' => ?_
      have hne : ¬ Lt (Tm.Xi m q) (.Xi m q) := Lt.irrefl _
      have hw2 : w ∈ fr (.Xi m q) (.Xi m q) := by
        rw [fr]
        simp only [hne, ↓reduceIte]
        exact hw'
      exact lt_of_lt_of_leY (hqF.of_mem_subs (fr_spec hw').1) hπF hσ (fr_spec (hc.fr_mem hπF hw2)).2 hπσ
    · exact inC_mono_d hρ hσ (le_of_not_ltY hσ hρ hσρ) hqF hqρ

theorem fam_mdl {π : Tm} (h : IsTgt π) : (info π).fam.mdl = (info (mi π)).sums := by
  rcases h with ⟨c, rfl, -⟩ | ⟨n, q, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩ <;> rfl

/-- 鎖の上の目標の Mahlo 添字の上限の部品 -/
theorem mpar_chain {π X τ : Tm} (ht : WNF (.Psi .zero π X))
    (hIH : ∀ u, u ∈ subs (.Psi .zero π X) → u ≠ .Psi .zero π X → SeqI u (info u).seq)
    (hc : Chain π τ) (hτt : IsTgt τ) : MPar π X τ (info τ).fam := by
  suffices h : (∀ u, u ∈ summands (mi τ) → u ≠ .one → SeqI u (info u).seq) ∧
      (∀ u, u ∈ summands (mi τ) → u ≠ .one → u ∈ subs (.Psi .zero π X) ∧ u.size < π.size) ∧
      ∀ σ, WNF σ → Le π σ → inC (mi τ) (mi τ) σ = true from ⟨fam_mdl hτt, h.1, h.2.1, h.2.2⟩
  rcases hτt with ⟨c, rfl, -⟩ | ⟨n, q, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩
  · refine ⟨?_, ?_, fun _ _ _ => inC_one _ _⟩ <;>
    · intro u hu h1
      simp only [mi, summands, List.mem_singleton] at hu
      exact absurd hu h1
  · obtain ⟨h1, h2, h3⟩ := xi_parts ht hIH hc
    exact ⟨h1, h2, h3⟩
  · obtain ⟨-, h1, h2⟩ := psi_parts hIH hc
    exact ⟨h1, h2, fun σ hσ hπσ => (mctx_chain (X := X) ht hc).hμσ σ hσ hπσ⟩

/-- 目標の族の再帰 -/
theorem fam_rec {π X : Tm} (ht : WNF (.Psi .zero π X))
    (hIH : ∀ u, u ∈ subs (.Psi .zero π X) → u ≠ .Psi .zero π X → SeqI u (info u).seq) :
    ∀ ρ, Chain π ρ → (∀ c, ρ ≠ .Om c) → ∀ p W, SeedP π X p → Dom (.Psi .zero π X) p →
      WNF (.Psi .zero ρ W) → Le (.Psi .zero ρ W) p →
      SeqI (.Psi .zero π X) (famSeq (info ρ).fam π (some p))
  | .Xi m q, hc, _, p, W, Sp, hD, hw, hle => by
    have hπF := ht.psi.piF
    have hρ : WNF (.Xi m q) := hc.wnf hπF
    have hqF := hρ.xi.2.1
    have hq0 := hρ.xi.2.2.1
    have e : (info (.Xi m q)).fam = .xi m q (info q).sums := rfl
    rw [e, famSeq]
    obtain ⟨hS, hqs, hqσ⟩ := xi_parts ht hIH hc
    refine vk_spec ht hc hS hqs hqσ (fun p' e' => ?_)
      (fun p' e' _ _ o => ?_) (fun y hyF hyp _ hP' _ _ v hv hne' hl => ?_)
      (fun p' e' _ _ _ => ?_)
    · cases e'
      exact Sp
    · cases e'
      intro ef
      have hWF := hw.psi.aF
      have hwρ : Lt (.Psi .zero (.Xi m q) W) (.Xi m q) := lt_psi_targetY hw
      have hC0 : inC (.Xi m q) W (.Psi .zero (.Xi m q) W) = true :=
        inC_tgt_of_k2t hw fun v hv => FWOrder.k2t hw v hv
      rcases inC_xi_iff.mp hC0 with h' | ⟨h2, h3⟩
      · exact absurd h' (Lt.asymmY hw hρ hwρ)
      have h0 : Lt .zero W := lt_transY WNF.zero hqF hWF (zero_lt hq0) h3
      have hπρ := hc.le hπF
      have hC := o.ubF W _ hWF hw h0 (fun v hv hvπ hvC =>
        coll_psiY hw v (hqF.of_mem_subs hv) hvC (lt_of_lt_of_leY (hqF.of_mem_subs hv) hπF hρ hvπ hπρ)) h2 h3
        (inC_zero _ _)
      obtain ⟨P₀, x₀, -, -, hfF, -⟩ := o.form _ o.mem
      have hf := coll_psiY hw _ hfF hC (lt_of_lt_of_leY hfF hπF hρ o.ltπ hπρ)
      rw [ef] at hf
      exact not_lt_of_leY hw Sp.hF hle hf
    · exact hD v hv hne' hl y hyF hyp (hP' p rfl)
    · cases e'
      exact vk_tail_dom ht hc hS hqs hqσ Sp hD
  | .Psi ζ κ γ, hc, _, p, W, Sp, hD, hw, hle => by
    have hπF := ht.psi.piF
    have hρ : WNF (.Psi ζ κ γ) := hc.wnf hπF
    have hP := hρ.psi
    have hζ0 : ζ ≠ .zero := by
      rcases hw.psi.tgt with ⟨c, e, -⟩ | ⟨n, p', e⟩ | ⟨ζ', κ', b, e, h⟩
      · cases e
      · cases e
      · cases e
        exact h
    have C := mctx_chain (X := X) ht hc
    have e : (info (.Psi ζ κ γ)).fam = .psi ζ (info ζ).sums κ (info κ).fam γ (info γ).sums := rfl
    rw [e, famSeq]
    obtain ⟨hSY, hSμ, hμs⟩ := psi_parts hIH hc
    have hfam : ∀ p', SeedP π X p' → Dom (.Psi .zero π X) p' → Le (.Psi .zero κ γ) p' →
        SeqI (.Psi .zero π X) (famSeq (info κ).fam π (some p')) := fun p' S' D' hle' =>
      fam_rec ht hIH κ (hc.snoc rfl) (tgt_not_om hρ hζ0) p' γ S' D' C.hw0 hle'
    have M := mpar_chain ht hIH (hc.snoc rfl) hP.tgt
    refine mahlo_spec C M hζ0 hSY hSμ hμs (fun p' e' => ?_)
      (fun p' e' _ _ o => ?_) (fun y hyF hyp hP' _ _ v hv hne' hl => ?_) hfam (fun p' e' _ _ _ hyp₁ => ?_)
    · cases e'
      exact Sp
    · cases e'
      intro ef
      have hWF := hw.psi.aF
      have hwρ : Lt (.Psi .zero (.Psi ζ κ γ) W) (.Psi ζ κ γ) := lt_psi_targetY hw
      have hC0 : inC (.Psi ζ κ γ) W (.Psi .zero (.Psi ζ κ γ) W) = true :=
        inC_tgt_of_k2t hw fun v hv => FWOrder.k2t hw v hv
      rcases inC_psi_iff.mp hC0 with h' | ⟨h1, h2, h3, h4⟩
      · exact absurd h' (Lt.asymmY hw hρ hwρ)
      have hγ0 : Lt .zero γ := by
        have h5 : Lt .zero ζ := zero_lt hζ0
        exact lt_of_lt_of_leY WNF.zero hP.xiF hP.aF h5 (le_of_ne_gtY hP.xiF hP.aF hP.le)
      have h0 : Lt .zero W := lt_transY WNF.zero hP.aF hWF hγ0 h4
      have hπρ := hc.le hπF
      have hC := o.ubF W _ hWF hw h0 (fun v hv hvπ hvC =>
        coll_psiY hw v (hP.xiF.of_mem_subs hv) hvC (lt_of_lt_of_leY (hP.xiF.of_mem_subs hv) hπF hρ hvπ hπρ))
        h1 h3 h4 h2 (inC_zero _ _)
      obtain ⟨P₀, x₀, -, -, hfF, -⟩ := o.form _ o.mem
      have hf := coll_psiY hw _ hfF hC (lt_of_lt_of_leY hfF hπF hρ o.ltπ hπρ)
      rw [ef] at hf
      exact not_lt_of_leY hw Sp.hF hle hf
    · exact hD v hv hne' hl y hyF hyp (hP' p rfl)
    · cases e'
      exact mahlo_tail_dom C M hSY hSμ hμs Sp hD hyp₁ (hfam p Sp hD hyp₁)
  | .Om c, _, h, _, _, _, _, _, _ => absurd rfl (h c)
  | .zero, _, _, _, _, _, _, hw, _ => (not_tgt_zero hw.psi.tgt).elim
  | .one, _, _, _, _, _, _, hw, _ => (not_tgt_one hw.psi.tgt).elim
  | .K _, _, _, _, _, _, _, hw, _ => (not_tgt_K hw.psi.tgt).elim
  | .plus _ _, _, _, _, _, _, _, hw, _ => (not_tgt_plus hw.psi.tgt).elim

end RTKA.Fund
