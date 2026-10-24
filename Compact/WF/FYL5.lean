import Compact.WF.FYL4

/-! 断片 `FY` の順序の性質の証明：新しい項が `t = Ψ^0_π(γ)` の場合の切断性と反対称性。

切断性の帰納法の測度は、組の大きさの最大値と和の辞書式順序。`p = Ψ^0_ρ(δ) < t` の前線の元が `t` 未満で
あることを示すのに、`p` の真部分項どうしの切断性（最大値が小さい組）を使う。

反対称性で `Ψ` どうしの比較が両方 `<` になる場合は、`t` の切断性から矛盾を導く（上向きの推移性は使わない）。 -/

namespace RTKA

open Tm

/-- 切断性：主要項の組についての切断性から一般の切断性へ（組の大きさの最大値と和の辞書式の帰納法）。
    `ihA` は `p` より小さい項どうし、`ihB` は大きさがどちらも `p`・`q` の大きい方以下で和が小さい組。 -/
theorem GoodY.cut_of_principal_lex {S : List Tm} (G : GoodY S) {t : Tm} (ht : FYNF t)
    (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S)
    (hP : ∀ q p, q ∈ S → p ∈ S → isPrincipal t = true → isPrincipal q = true →
      isPrincipal p = true →
      (∀ a b, a ∈ S → b ∈ S → a.size < p.size → b.size < p.size → Lt b a → Lt a t → Lt b t) →
      (∀ a b, a ∈ S → b ∈ S → a.size + b.size < q.size + p.size →
        (a.size ≤ p.size ∨ a.size ≤ q.size) → (b.size ≤ p.size ∨ b.size ≤ q.size) →
        Lt b a → Lt a t → Lt b t) →
      Lt q p → Lt p t → Lt q t) : CutT S t := by
  have key : ∀ M, ∀ N, ∀ a b, a ∈ S → b ∈ S → a.size ≤ M → b.size ≤ M →
      a.size + b.size ≤ N → Lt b a → Lt a t → Lt b t := by
    intro M
    induction M with
    | zero => intro N a _ _ _ h; exact absurd h (by have := Tm.size_pos a; omega)
    | succ M ihM =>
      intro N
      induction N with
      | zero => intro a _ _ _ _ _ h; exact absurd h (by have := Tm.size_pos a; omega)
      | succ N ihN =>
        intro a b ha hb hMa hMb hN h1 h2
        refine G.cutGen ht hsub (fun htp q p hq hp => ?_) ha hb h1 h2
        have hqS := G.sub hb (mem_subs_of_mem_summands hq)
        have hpS := G.sub ha (mem_subs_of_mem_summands hp)
        have hqs := size_le_of_mem_summands b q hq
        have hps := size_le_of_mem_summands a p hp
        refine hP q p hqS hpS htp (summands_FYNF b (G.nf b hb) q hq).2
          (summands_FYNF a (G.nf a ha) p hp).2 (fun a' b' ha' hb' h1' h2' => ?_)
          (fun a' b' ha' hb' hs' h1' h2' => ?_)
        · exact ihM (a'.size + b'.size) a' b' ha' hb' (by omega) (by omega) (Nat.le_refl _)
        · exact ihN a' b' ha' hb' (by omega) (by omega) (by omega)
  exact fun a b ha hb => key (a.size + b.size) _ a b ha hb (by omega) (by omega) (Nat.le_refl _)

/-- `cmp` が `.eq` でない二つの項について、`x < y ⟺ ¬ y < x` なら反対称 -/
theorem swap_of_iff {x y : Tm} (h1 : cmp x y ≠ .eq) (h2 : cmp y x ≠ .eq)
    (h : Lt x y ↔ ¬ Lt y x) : cmp y x = (cmp x y).swap := by
  unfold Lt at h
  revert h1 h2 h
  cases cmp x y <;> cases cmp y x <;> decide

namespace PsiCtxY

variable {S : List Tm} {π γ : Tm} (P : PsiCtxY S π γ)
include P

/-- `p = Ψ^0_ρ(δ) < t` が `c1` の形（`δ < γ`、`δ, ρ ∈ C(γ, t)`）なら、`p` の前線（`ρ` について）の元は
    `t` 未満（`p` の真部分項どうしの切断性の下で） -/
theorem fr_lt_c1 {ρ δ : Tm} (hpS : Tm.Psi .zero ρ δ ∈ S) (hl : lev ρ = lev π)
    (htρ : Lt (.Psi .zero π γ) ρ) (hinδ : inC δ γ (.Psi .zero π γ) = true)
    (hinρ : inC ρ γ (.Psi .zero π γ) = true) (hpπ : Lt (.Psi .zero ρ δ) π)
    (ihA : ∀ a b, a ∈ S → b ∈ S → a.size < (Tm.Psi .zero ρ δ).size →
      b.size < (Tm.Psi .zero ρ δ).size → Lt b a → Lt a (.Psi .zero π γ) →
      Lt b (.Psi .zero π γ)) :
    ∀ w, (w ∈ fr ρ δ ∨ w ∈ fr ρ ρ) → Lt w (.Psi .zero π γ) := by
  have G := P.G
  have hρS : ρ ∈ S := G.sub hpS (by simp [subs, self_mem_subs])
  have hδS := G.sub hpS (mem_subs_psi_a _ _ δ)
  have hρT := (G.nf _ hpS).psi.2.1
  have hd : ∀ x, x ∈ S → x.size < (Tm.Psi .zero ρ δ).size → ∀ v, v ∈ subs x → ¬ Lt v ρ →
      ¬ Lt v (.Psi .zero π γ) := fun x hx hxs v hv hvρ hvt => by
    have hvS := G.sub hx hv
    have hvs := size_le_of_mem_subs hv
    exact P.tgt_contra hρS hρT hl htρ hvS (G.le_of_not_lt hvS hρS hvρ) (P.tb hvS hvt)
      (fun u huS hus huv => ihA v u hvS huS (by omega)
        (by simp only [Tm.size] at hus ⊢; omega) huv hvt)
  intro w hw
  have hwS : w ∈ S := by
    rcases hw with hw | hw
    · exact G.sub hδS (fr_spec hw).1
    · exact G.sub hρS (fr_spec hw).1
  have hwp : Lt w (.Psi .zero ρ δ) := by
    rcases hw with hw | hw
    · exact G.k2 _ δ hpS w hw
    · exact G.k2t _ δ hpS w hw
  have hin : inC w γ (.Psi .zero π γ) = true := by
    rcases hw with hw | hw
    · exact fr_of_inC δ (hd δ hδS (by simp only [Tm.size]; omega)) hinδ w hw
    · exact fr_of_inC ρ (hd ρ hρS (by simp only [Tm.size]; omega)) hinρ w hw
  exact G.coll_psi P.ht P.πS w hwS hin (G.trans hwS hpS P.πS hwp hpπ)

/-- `t = Ψ^0_π(γ)` は `S` を切断する -/
theorem cut : CutT S (.Psi .zero π γ) := by
  have G := P.G
  refine G.cut_of_principal_lex P.ht P.hsub
    (fun q p hqS hpS _ hqp hpp ihA ihB h1 h2 => ?_)
  have hqF := G.nf q hqS
  have hpF := G.nf p hpS
  refine cut_reduceY P.ht rfl rfl hqF hpF hqp hpp h1 h2 (fun lq lp bq bp => ?_)
  have hpπ := P.tb hpS h2
  have hqπ := G.trans hqS hpS P.πS h1 hpπ
  -- `q` の真部分項 `v < p` は `t` 未満
  have ihq : ∀ v, v ∈ S → v.size < q.size → Lt v p → Lt v (.Psi .zero π γ) :=
    fun v hv hvs hvp => ihB p v hpS hv (by omega) (Or.inl (Nat.le_refl _)) (Or.inr (by omega)) hvp h2
  -- 前線の元以下なら補題 A
  have viaF : ∀ w, (w ∈ fr π γ ∨ w ∈ fr π π) → Le p w → Lt q (.Psi .zero π γ) :=
    fun w hw hpw => P.lemA hqS ⟨w, hw, Or.inr (G.lt_of_lt_of_le hqS hpS (P.F_spec hw).1 h1 hpw)⟩
  -- `p` の真部分項 `w < t` で `q ≤ w`
  have viaLe : ∀ w, w ∈ S → w.size < p.size → Lt w (.Psi .zero π γ) → Le q w →
      Lt q (.Psi .zero π γ) := fun w hwS hws hwt hqw => by
    rcases hqw with e | e
    · rw [e]; exact hwt
    · exact ihB w q hwS hqS (by omega) (Or.inl (by omega)) (Or.inr (Nat.le_refl _)) e hwt
  -- `q = Ξ`
  have viaXi : ∀ m f', q = .Xi m f' → Lt q (.Psi .zero π γ) := fun m f' e => by
    subst e
    have hf'S := G.sub hqS (mem_subs_xi m f')
    refine P.xi_lt_t hqS lq.symm hqπ (fun _ u hu => ?_)
    have huS := G.sub hf'S (fr_spec hu).1
    have := size_le_of_mem_subs (fr_spec hu).1
    exact ihq u huS (by simp only [Tm.size]; omega) (G.trans huS hqS hpS (G.k2x m f' hqS u hu) h1)
  -- `q = Ψ` で目標が `t` 未満
  have viaT : ∀ ρ' α, q = .Psi .zero ρ' α → Lt ρ' (.Psi .zero π γ) → Lt q (.Psi .zero π γ) :=
    fun ρ' α e h => by
      subst e
      have hρ'S : ρ' ∈ S := G.sub hqS (by simp [subs, self_mem_subs])
      exact P.psi_lt_of_tgt hqS lq (P.not_lt_tgt hρ'S hqF.psi.2.1 h)
  rcases shape_FY3 hpF hpp bp with ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨ρ, δ, rfl⟩
  · -- `p = Ω_x`
    have hx := G.sub hpS (mem_subs_om x)
    rcases P.hT with ⟨c, rfl, -⟩ | ⟨n, r0, rfl⟩
    · have hcS := G.sub P.πS (mem_subs_om c)
      have hxc : Lt x c := (lt_om_psiY P.ht).mp h2
      rcases shape_FY4 hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨d, α, rfl⟩ | ⟨m', r, α, rfl⟩
      · have hy := G.sub hqS (mem_subs_om y)
        exact (lt_om_psiY P.ht).mpr (G.trans hy hx hcS ((G.lt_om_iffS hy hx).mp h1) hxc)
      · exact viaXi m' f' rfl
      · have hdS := G.sub hqS (mem_subs_psi_c _ d α)
        have hdc : Lt d c := G.lt_of_le_of_lt hdS hx hcS ((G.lt_psi_omS hqS hx).mp h1) hxc
        have hl : lev d = lev c := lq
        exact P.psi_lt_of_tgt hqS lq (fun h' => (psiOm_lt_om_iff hl).mp h' hdc)
      · exact P.below rfl hqS
          (G.trans hqS hx hcS ((G.lt_OF_omS (psiXiOF _ _ _) hqS hx).mp h1) hxc)
    · have hOF := psiXiOF n r0 γ
      have hxt : Lt x (.Psi .zero (.Xi n r0) γ) := (lt_om_OFG hOF).mp h2
      have hxs : x.size < (Tm.Om x).size := by simp only [Tm.size]; omega
      rcases shape_FY4 hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨d, α, rfl⟩ | ⟨m', r, α, rfl⟩
      · have hy := G.sub hqS (mem_subs_om y)
        exact (lt_om_OFG hOF).mpr (ihB x y hx hy (by simp only [Tm.size]; omega)
          (Or.inl (by omega)) (Or.inr (by simp only [Tm.size]; omega))
          ((G.lt_om_iffS hy hx).mp h1) hxt)
      · exact viaXi m' f' rfl
      · have hdS := G.sub hqS (mem_subs_psi_c _ d α)
        have hdt : Lt d (.Psi .zero (.Xi n r0) γ) := by
          rcases (G.lt_psi_omS hqS hx).mp h1 with e | e
          · rw [e]; exact hxt
          · exact ihB x d hx hdS (by simp only [Tm.size]; omega) (Or.inl (by omega))
              (Or.inr (by simp only [Tm.size]; omega)) e hxt
        exact viaT (.Om d) α rfl ((lt_om_OFG hOF).mpr hdt)
      · exact ihB x _ hx hqS (by omega) (Or.inl (by omega)) (Or.inr (Nat.le_refl _))
          ((G.lt_OF_omS (psiXiOF _ _ _) hqS hx).mp h1) hxt
  · -- `p = Ξ_m(f)`
    have hfS := G.sub hpS (mem_subs_xi m f)
    obtain ⟨-, hinf⟩ := P.xi_lt_t_inv hpS lp.symm h2
    rcases P.hT with ⟨c, rfl, -⟩ | ⟨n, r0, rfl⟩
    · have hcS := G.sub P.πS (mem_subs_om c)
      exact P.below rfl hqS (G.trans hqS hpS hcS h1 ((G.lt_OF_omS (xiOF _ _) hpS hcS).mp hpπ))
    · simp only [lev] at lp
      subst lp
      by_cases hfγ : Lt f γ
      · have hinf' := hinf hfγ
        rcases shape_FY3 hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨ρ', α, rfl⟩
        · have hy := G.sub hqS (mem_subs_om y)
          exact (lt_om_OFG (psiXiOF _ _ _)).mpr (ihq y hy (by simp only [Tm.size]; omega)
            ((lt_om_OFG (xiOF _ _)).mp h1))
        · exact viaXi m' f' rfl
        · have hρ'S : ρ' ∈ S := G.sub hqS (by simp [subs, self_mem_subs])
          rcases (lt_psi_xiY (π := ρ') (a := α) lq).mp h1 with h' | ⟨hfα, hn⟩
          · refine viaT ρ' α rfl ?_
            rcases G.le_of_ne_gt hρ'S hpS h' with e | e
            · rw [e]; exact h2
            · exact ihq ρ' hρ'S (by simp only [Tm.size]; omega) e
          · have hαS := G.sub hqS (mem_subs_psi_a _ _ α)
            obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hpF.xi.2.2.2.2
              (fun v hv h' => G.trans (G.sub hfS hv) hfS hαS h' hfα) hn
            have hwS := G.sub hfS (fr_spec hw).1
            have := size_le_of_mem_subs (fr_spec hw).1
            have hin := fr_of_inC f (fun w' _ hn' => not_lt_of_not_lt_K rfl hn') hinf' w hw
            have hwt := G.coll_psi P.ht P.πS w hwS hin
              (G.trans hwS hpS P.πS (G.k2x _ f hpS w hw) hpπ)
            exact viaLe w hwS (by simp only [Tm.size]; omega) hwt (G.le_of_not_lt hwS hqS hwn)
      · -- `γ ≤ f`：`p < Ξ_n(r0)` から `p` 以上の `π` の前線の元
        have hr0S := G.sub P.πS (mem_subs_xi m r0)
        obtain ⟨-, -, -, -, -, hC⟩ := P.ht.psi
        have hr0γ : Lt r0 γ := by
          rcases inC_xi_iff.mp hC with h' | ⟨-, h'⟩
          · exact absurd h' (Lt.irrefl _)
          · exact h'
        have hγf : Le γ f := G.le_of_not_lt hfS P.γS hfγ
        have hr0f : Lt r0 f := G.lt_of_lt_of_le hr0S P.γS hfS hr0γ hγf
        have hne : f ≠ r0 := fun e => by subst e; exact Lt.irrefl _ hr0f
        rcases (lt_xi_xi0 hne).mp hpπ with ⟨hfr0, -⟩ | ⟨-, hn⟩
        · exact absurd hfr0 (G.asymm hr0S hfS hr0f)
        · obtain ⟨u, hu, hun⟩ := wit_of_not_inC (G.nf _ P.πS).xi.2.2.2.2
            (fun v hv h' => G.trans (G.sub hr0S hv) hr0S hfS h' hr0f) hn
          have huS := G.sub hr0S (fr_spec hu).1
          exact viaF u (Or.inr (G.fr_xi_sub P.πS hu)) (G.le_of_not_lt huS hpS hun)
  · -- `p = Ψ^0_ρ(δ)`
    have hρS : ρ ∈ S := G.sub hpS (by simp [subs, self_mem_subs])
    have hδS := G.sub hpS (mem_subs_psi_a _ _ δ)
    obtain ⟨-, hρT, -, -, h0δ, h0ρ⟩ := hpF.psi
    have lp' : lev ρ = lev π := lp
    rcases (lt_psi_psiY lp' (P.ne_of_mem hpS)).mp h2 with h' | ⟨htρ, -, hc1 | ⟨hγδ, hn⟩⟩
    · -- 目標 `ρ` が `t` 未満
      have hρt := P.tgt_lt hρS hρT h'
      exact ihB ρ q hρS hqS (by simp only [Tm.size]; omega) (Or.inl (by simp only [Tm.size]; omega))
        (Or.inr (Nat.le_refl _)) (G.trans hqS hpS hρS h1 (lt_psi_targetY hpF)) hρt
    · -- `c1`：`δ < γ`、`δ, ρ ∈ C(γ, t)`
      obtain ⟨hδγ, hinδ, hinρ⟩ := hc1
      have frP := P.fr_lt_c1 hpS lp' htρ hinδ hinρ hpπ ihA
      rcases shape_FY3 hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨ρ', α, rfl⟩
      · have hy := G.sub hqS (mem_subs_om y)
        rcases hρT with ⟨d, rfl, -⟩ | ⟨m, r, rfl⟩
        · have hyd : Lt y d := (lt_om_psiY hpF).mp h1
          have hdS := G.sub hρS (mem_subs_om d)
          rcases P.hT with ⟨c, rfl, -⟩ | ⟨n, r0, rfl⟩
          · have hcS := G.sub P.πS (mem_subs_om c)
            exact (lt_om_psiY P.ht).mpr
              (G.lt_of_lt_of_le hy hdS hcS hyd ((G.lt_psi_omS hpS hcS).mp hpπ))
          · rw [inC_om] at hinρ
            have hdt := G.coll_psi P.ht P.πS d hdS hinρ
              (G.trans hdS hpS P.πS (G.cx d δ hpS) hpπ)
            exact (lt_om_OFG (psiXiOF _ _ _)).mpr (ihB d y hdS hy
              (by simp only [Tm.size] at lq ⊢; omega) (Or.inl (by simp only [Tm.size]; omega))
              (Or.inr (by simp only [Tm.size]; omega)) hyd hdt)
        · have hyp : Lt y (.Psi .zero (.Xi m r) δ) := (lt_om_OFG (psiXiOF _ _ _)).mp h1
          rcases P.hT with ⟨c, rfl, -⟩ | ⟨n, r0, rfl⟩
          · have hcS := G.sub P.πS (mem_subs_om c)
            exact (lt_om_psiY P.ht).mpr (G.trans hy hpS hcS hyp
              ((G.lt_OF_omS (psiXiOF _ _ _) hpS hcS).mp hpπ))
          · exact (lt_om_OFG (psiXiOF _ _ _)).mpr (ihq y hy (by simp only [Tm.size]; omega) hyp)
      · exact viaXi m' f' rfl
      · have hρ'S : ρ' ∈ S := G.sub hqS (by simp [subs, self_mem_subs])
        have hαS := G.sub hqS (mem_subs_psi_a _ _ α)
        have lq' : lev ρ' = lev ρ := lq.trans lp.symm
        rcases (lt_psi_psiY lq' h1.ne).mp h1 with h'' | ⟨-, -, hc1' | ⟨hδα, hn'⟩⟩
        · refine viaT ρ' α rfl ?_
          rcases G.le_of_not_lt hpS hρ'S h'' with e | e
          · rw [e]; exact h2
          · exact ihq ρ' hρ'S (by simp only [Tm.size]; omega) e
        · obtain ⟨hαδ, hinα, hinρ'⟩ := hc1'
          by_cases htρ'' : ¬ Lt (.Psi .zero π γ) ρ'
          · exact P.psi_lt_of_tgt hqS lq htρ''
          have htρ' := Decidable.of_not_not htρ''
          have hαγ := G.trans hαS hδS P.γS hαδ hδγ
          refine P.psi_lt_of_c1 hqS lq htρ' hqπ hαγ ?_ ?_
          · refine inC_mono α δ _ γ _ hinα (fun v hv hvp => ?_)
              (fun v hv hvδ => G.trans (G.sub hαS hv) hδS P.γS hvδ hδγ)
            have := size_le_of_mem_subs hv
            exact ihq v (G.sub hαS hv) (by simp only [Tm.size]; omega) hvp
          · refine inC_mono ρ' δ _ γ _ hinρ' (fun v hv hvp => ?_)
              (fun v hv hvδ => G.trans (G.sub hρ'S hv) hδS P.γS hvδ hδγ)
            have := size_le_of_mem_subs hv
            exact ihq v (G.sub hρ'S hv) (by simp only [Tm.size]; omega) hvp
        · have hδα' : Le δ α := G.le_of_ne_gt hδS hαS hδα
          have hg : ∀ x, x ∈ S → ∀ v, v ∈ subs x → Lt v δ → Lt v α := fun x hx v hv h =>
            G.lt_of_lt_of_le (G.sub hx hv) hδS hαS h hδα'
          have hw : ∃ w, (w ∈ fr ρ δ ∨ w ∈ fr ρ ρ) ∧ ¬ Lt w (.Psi .zero ρ' α) := by
            cases e1 : inC δ α (Tm.Psi .zero ρ' α)
            · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC h0δ (hg δ hδS) e1
              exact ⟨w, Or.inl hw, hwn⟩
            · cases e2 : inC ρ α (Tm.Psi .zero ρ' α)
              · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC h0ρ (hg ρ hρS) e2
                exact ⟨w, Or.inr hw, hwn⟩
              · exact absurd ⟨e1, e2⟩ hn'
          obtain ⟨w, hw, hwn⟩ := hw
          have hwS : w ∈ S := by
            rcases hw with hw | hw
            · exact G.sub hδS (fr_spec hw).1
            · exact G.sub hρS (fr_spec hw).1
          have hws : w.size < (Tm.Psi .zero ρ δ).size := by
            rcases hw with hw | hw
            · have := size_le_of_mem_subs (fr_spec hw).1; simp only [Tm.size]; omega
            · have := size_le_of_mem_subs (fr_spec hw).1; simp only [Tm.size]; omega
          exact viaLe w hwS hws (frP w hw) (G.le_of_not_lt hwS hqS hwn)
    · -- `c2`：前線の証人
      obtain ⟨w, hw, hwn⟩ := P.wit (G.le_of_ne_gt P.γS hδS hγδ) hδS hn
      exact viaF w hw (G.le_of_not_lt (P.F_spec hw).1 hpS hwn)

/-- `Ψ` どうしの反対称性 -/
theorem psi_swap {κ β : Tm} (hs : Tm.Psi .zero κ β ∈ S) (hl : lev π = lev κ) :
    cmpPsi (.Psi .zero κ β) (.Psi .zero π γ) = (cmpPsi (.Psi .zero π γ) (.Psi .zero κ β)).swap := by
  have G := P.G
  have hsF := G.nf _ hs
  have hκS : κ ∈ S := G.sub hs (by simp [subs, self_mem_subs])
  have hβS := G.sub hs (mem_subs_psi_a _ _ β)
  have hκT := hsF.psi.2.1
  have hne : Tm.Psi .zero π γ ≠ .Psi .zero κ β := fun e => P.ne_of_mem hs e.symm
  have hne' : Tm.Psi .zero κ β ≠ .Psi .zero π γ := fun e => hne e.symm
  have Ats := lt_psi_psiY hl hne
  have Ast := lt_psi_psiY hl.symm hne'
  have hκπ_of : ¬ Lt (.Psi .zero κ β) π → ¬ Lt (.Psi .zero π γ) κ → False := fun h1 h2 => by
    have hπκ := G.lt_of_le_of_lt P.πS hs hκS (G.le_of_not_lt hs P.πS h1) (lt_psi_targetY hsF)
    exact G.asymm P.πS hκS hπκ (P.tbge hκS hκT.principal h2)
  -- `s < t` と `t < s` は両立しない
  have asym : Lt (.Psi .zero π γ) (.Psi .zero κ β) → Lt (.Psi .zero κ β) (.Psi .zero π γ) → False := by
    intro h h'
    rcases Ats.mp h with a1 | ⟨hsπ, htκ, hc⟩ <;> rcases Ast.mp h' with b1 | ⟨htκ', hsπ', hc'⟩
    · exact hκπ_of a1 b1
    · exact a1 hsπ'
    · exact b1 htκ
    · rcases G.tri P.γS hβS with e | e | e
      · have egt : cmp β γ = .gt := by unfold Lt at e; rw [G.swap P.γS hβS, e]; rfl
        rcases hc with ⟨-, hc⟩ | ⟨hc, -⟩
        · rcases hc' with ⟨e', -⟩ | ⟨-, hc'⟩
          · exact G.asymm P.γS hβS e e'
          · exact hc' hc
        · exact hc egt
      · subst e
        have hargt := P.inC_arg
        rcases hc with ⟨e1, -⟩ | ⟨-, hc⟩
        · exact Lt.irrefl _ e1
        · have hκ : inC κ γ (.Psi .zero π γ) = false := by
            cases e : inC κ γ (Tm.Psi .zero π γ)
            · rfl
            · exact absurd ⟨hargt, e⟩ hc
          obtain ⟨u, hu, hun⟩ := wit_of_not_inC hsF.psi.2.2.2.2.2 (fun _ _ h => h) hκ
          have huS := G.sub hκS (fr_spec hu).1
          exact hun (P.cut _ u hs huS (G.k2t κ γ hs u hu) h')
      · have egt : cmp γ β = .gt := by unfold Lt at e; rw [G.swap hβS P.γS, e]; rfl
        rcases hc' with ⟨-, hc'⟩ | ⟨hc', -⟩
        · rcases hc with ⟨e', -⟩ | ⟨-, hc⟩
          · exact G.asymm hβS P.γS e e'
          · exact hc hc'
        · exact hc' egt
  -- どちらかは成り立つ
  have tot : Lt (.Psi .zero π γ) (.Psi .zero κ β) ∨ Lt (.Psi .zero κ β) (.Psi .zero π γ) := by
    by_cases h1 : Lt (.Psi .zero κ β) π
    · by_cases h2 : Lt (.Psi .zero π γ) κ
      · rcases G.tri P.γS hβS with e | e | e
        · by_cases hin : inC γ β (.Psi .zero κ β) = true ∧ inC π β (.Psi .zero κ β) = true
          · exact Or.inl (Ats.mpr (Or.inr ⟨h1, h2, Or.inl ⟨e, hin.1, hin.2⟩⟩))
          · exact Or.inr (Ast.mpr (Or.inr ⟨h2, h1, Or.inr ⟨by unfold Lt at e; rw [e]; decide, hin⟩⟩))
        · subst e
          by_cases hin : inC κ γ (.Psi .zero π γ) = true
          · by_cases hin' : inC π γ (.Psi .zero κ γ) = true
            · exfalso
              rcases G.tri P.πS hκS with e | e | e
              · exact G.asymm hs P.πS h1 (G.coll_psiS hs π P.πS hin' e)
              · subst e; exact hne rfl
              · exact P.not_lt_tgt hκS hκT (G.coll_psi P.ht P.πS κ hκS hin e) h2
            · exact Or.inr (Ast.mpr (Or.inr ⟨h2, h1, Or.inr ⟨by rw [cmp_self]; decide,
                fun h => hin' h.2⟩⟩))
          · exact Or.inl (Ats.mpr (Or.inr ⟨h1, h2, Or.inr ⟨by rw [cmp_self]; decide,
              fun h => hin h.2⟩⟩))
        · by_cases hin : inC β γ (.Psi .zero π γ) = true ∧ inC κ γ (.Psi .zero π γ) = true
          · exact Or.inr (Ast.mpr (Or.inr ⟨h2, h1, Or.inl ⟨e, hin.1, hin.2⟩⟩))
          · exact Or.inl (Ats.mpr (Or.inr ⟨h1, h2, Or.inr ⟨by unfold Lt at e; rw [e]; decide, hin⟩⟩))
      · exact Or.inr (Ast.mpr (Or.inl h2))
    · by_cases h2 : Lt (.Psi .zero π γ) κ
      · exact Or.inl (Ats.mpr (Or.inl h1))
      · exact absurd (hκπ_of h1 h2) id
  have ne := P.G.ne_new P.ht P.hsub P.htS _ hs
  have key := swap_of_iff ne.2 ne.1 ⟨fun h h' => asym h h', fun h => tot.resolve_right h⟩
  rw [cmp_principal rfl rfl, cmp_principal rfl rfl, cmpP_psi_psi hl, cmpP_psi_psi hl.symm] at key
  exact key

/-- `t = Ψ^0_π(γ)` は `S` の全ての元と反対称 -/
theorem anti : ∀ z, z ∈ S → AntiT (.Psi .zero π γ) z :=
  P.G.anti_new P.ht P.hsub P.htS (fun π' γ' κ β e hs hl => by
    cases e
    exact P.psi_swap hs hl)

end PsiCtxY

end RTKA
