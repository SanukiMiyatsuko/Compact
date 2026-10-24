import Compact.WF.FYL3

/-! 断片 `FY` の順序の性質の証明：新しい項が `t = Ψ^0_π(γ)` の場合の準備（目標は `Ω_c` でも `Ξ_n(p)` でもよい）。

`t` との非対称性を使わずに、比較を直接計算して示す。

1. `tb`：`t` 未満の `S` の元は `π` 未満。`tbge`：`t` が上にない主要項は `π` 未満。
2. `below`（`π = Ω_c`）：`c` 未満の `S` の元は `t` 未満。
3. `tgt_contra`：`t < ρ ≤ v < π` は（`ρ` の真部分項についての切断性の下で）起こらない。
4. `lemA`：`γ` と `π` の前線（`π` について）のどれか以下の `S` の元は `t` 未満（補題 A）。
5. `k2`・`k2t`・`cx`。 -/

namespace RTKA

open Tm

/-! ### 道具 -/

theorem psiOm_lt_om_iff {c γ x : Tm} (hl : lev x = lev c) :
    Lt (.Psi .zero (.Om c) γ) (.Om x) ↔ ¬ Lt x c := by
  rw [lt_principal_iff rfl rfl, cmpP_psi0_om hl]
  unfold Lt
  cases cmp x c <;> simp

theorem OF_lt_om_iff {X x : Tm} (hX : IsOF X) (hl : lev x = lev X) :
    Lt X (.Om x) ↔ cmp x X = .gt := by
  rw [lt_principal_iff hX.principal rfl, cmpP_OF_om hX hl]
  cases cmp x X <;> simp

theorem IsTgt.principal {ρ : Tm} (h : IsTgt ρ) : isPrincipal ρ = true := by
  rcases h with ⟨c, rfl, -⟩ | ⟨n, r, rfl⟩ <;> rfl

theorem IsTgt.not_bot {ρ : Tm} (h : IsTgt ρ) : isBot ρ = false := by
  rcases h with ⟨c, rfl, -⟩ | ⟨n, r, rfl⟩ <;> rfl

theorem IsTgt.np {ρ : Tm} (h : IsTgt ρ) (κ β : Tm) : ρ ≠ .Psi .zero κ β := by
  rcases h with ⟨c, rfl, -⟩ | ⟨n, r, rfl⟩ <;> intro e <;> cases e

theorem psiXiOF (n : Nat) (r γ : Tm) : IsOF (.Psi .zero (.Xi n r) γ) := Or.inr ⟨n, r, γ, rfl⟩

/-- 新しい項 `t = Ψ^0_π(γ)` の文脈 -/
structure PsiCtxY (S : List Tm) (π γ : Tm) : Prop where
  G : GoodY S
  ht : FYNF (.Psi .zero π γ)
  hsub : ∀ s, s ∈ subs (Tm.Psi .zero π γ) → s ≠ .Psi .zero π γ → s ∈ S
  htS : Tm.Psi .zero π γ ∉ S

namespace PsiCtxY

variable {S : List Tm} {π γ : Tm} (P : PsiCtxY S π γ)
include P

theorem πS : π ∈ S :=
  P.hsub π (by simp [subs, self_mem_subs]) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))

theorem γS : γ ∈ S :=
  P.hsub γ (mem_subs_psi_a _ _ γ) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))

theorem hT : IsTgt π := P.ht.psi.2.1

theorem πF : FYNF π := P.ht.psi.2.2.1

theorem ne_of_mem {s : Tm} (hs : s ∈ S) : s ≠ .Psi .zero π γ := fun e => P.htS (e ▸ hs)

theorem lt_of_ne_gt {z : Tm} (hz : z ∈ S) (h : cmp z (.Psi .zero π γ) ≠ .gt) :
    Lt z (.Psi .zero π γ) :=
  P.G.lt_of_ne_gt_new P.ht P.hsub P.htS hz h

/-- `Ψ` でない主要項 `y` について `y < t ⟺ ¬ t < y` -/
theorem lt_iff_np {y : Tm} (hy : y ∈ S) (hyp : isPrincipal y = true)
    (hnp : ∀ κ β, y ≠ .Psi .zero κ β) :
    Lt y (.Psi .zero π γ) ↔ ¬ Lt (.Psi .zero π γ) y := by
  have hs := P.G.swapP_new P.ht P.hsub hy rfl hyp (fun _ _ κ β _ e => absurd e (hnp κ β))
  have hne := (P.G.ne_new P.ht P.hsub P.htS y hy).1
  rw [cmp_principal hyp rfl, hs] at hne
  rw [lt_principal_iff hyp rfl, lt_principal_iff rfl hyp, hs]
  revert hne
  cases cmpP (Tm.Psi .zero π γ) y <;> decide

theorem tgt_lt {ρ : Tm} (hρS : ρ ∈ S) (hρT : IsTgt ρ) (h : ¬ Lt (.Psi .zero π γ) ρ) :
    Lt ρ (.Psi .zero π γ) :=
  (P.lt_iff_np hρS hρT.principal hρT.np).mpr h

theorem not_lt_tgt {ρ : Tm} (hρS : ρ ∈ S) (hρT : IsTgt ρ) (h : Lt ρ (.Psi .zero π γ)) :
    ¬ Lt (.Psi .zero π γ) ρ :=
  (P.lt_iff_np hρS hρT.principal hρT.np).mp h

/-! ### `S` の `Ψ` が `t` 未満になる条件 -/

theorem psi_lt_of_tgt {ρ α : Tm} (hq : Tm.Psi .zero ρ α ∈ S) (hl : lev ρ = lev π)
    (h : ¬ Lt (.Psi .zero π γ) ρ) : Lt (.Psi .zero ρ α) (.Psi .zero π γ) :=
  (lt_psi_psiY hl (P.ne_of_mem hq)).mpr (Or.inl h)

theorem psi_lt_of_c1 {ρ α : Tm} (hq : Tm.Psi .zero ρ α ∈ S) (hl : lev ρ = lev π)
    (htρ : Lt (.Psi .zero π γ) ρ) (hqπ : Lt (.Psi .zero ρ α) π) (hαγ : Lt α γ)
    (h1 : inC α γ (.Psi .zero π γ) = true) (h2 : inC ρ γ (.Psi .zero π γ) = true) :
    Lt (.Psi .zero ρ α) (.Psi .zero π γ) :=
  (lt_psi_psiY hl (P.ne_of_mem hq)).mpr (Or.inr ⟨htρ, hqπ, Or.inl ⟨hαγ, h1, h2⟩⟩)

theorem psi_lt_of_c2 {ρ α : Tm} (hq : Tm.Psi .zero ρ α ∈ S) (hl : lev ρ = lev π)
    (htρ : Lt (.Psi .zero π γ) ρ) (hqπ : Lt (.Psi .zero ρ α) π) (hγα : cmp γ α ≠ .gt)
    (hn : ¬ (inC γ α (.Psi .zero ρ α) = true ∧ inC π α (.Psi .zero ρ α) = true)) :
    Lt (.Psi .zero ρ α) (.Psi .zero π γ) :=
  (lt_psi_psiY hl (P.ne_of_mem hq)).mpr (Or.inr ⟨htρ, hqπ, Or.inr ⟨hγα, hn⟩⟩)

/-- `Ξ_m(f) < t` の条件 -/
theorem xi_lt_t {m : Nat} {f : Tm} (hX : Tm.Xi m f ∈ S) (hl : lev π = m)
    (hXπ : Lt (.Xi m f) π)
    (hfr : Lt f γ → ∀ u, u ∈ fr (.K m) f → Lt u (.Psi .zero π γ)) :
    Lt (.Xi m f) (.Psi .zero π γ) := by
  have G := P.G
  have hfS := G.sub hX (mem_subs_xi m f)
  rw [lt_xi_psiY hl, lt_psi_xiY hl]
  rintro (h | ⟨hfγ, hn⟩)
  · apply h
    unfold Lt at hXπ
    rw [G.swap hX P.πS, hXπ]
    decide
  · rw [inC_of_fr f (G.nf _ hX).xi.2.2.2.2 (fun v hv h' => G.trans (G.sub hfS hv) hfS P.γS h' hfγ)
      (fun u hu => inC_of_lt_node (fr_node hu) (hfr hfγ u hu))] at hn
    cases hn

theorem xi_lt_t_inv {m : Nat} {f : Tm} (hX : Tm.Xi m f ∈ S) (hl : lev π = m)
    (h : Lt (.Xi m f) (.Psi .zero π γ)) :
    Lt (.Xi m f) π ∧ (Lt f γ → inC f γ (.Psi .zero π γ) = true) := by
  rw [lt_xi_psiY hl, lt_psi_xiY hl] at h
  refine ⟨P.G.lt_of_gt P.πS hX ?_, fun hfγ => ?_⟩
  · cases e : cmp π (Tm.Xi m f)
    · exact absurd (Or.inl (by rw [e]; decide)) h
    · exact absurd (Or.inl (by rw [e]; decide)) h
    · rfl
  · cases e : inC f γ (Tm.Psi .zero π γ)
    · exact absurd (Or.inr ⟨hfγ, e⟩) h
    · rfl

/-- 前線の証人：`γ ≤ g` で `γ` か `π` が `C(g, d)` に入らなければ、その前線に `d` 未満でない元がある -/
theorem wit {g d : Tm} (hg : Le γ g) (hgS : g ∈ S)
    (hn : ¬ (inC γ g d = true ∧ inC π g d = true)) :
    ∃ w, (w ∈ fr π γ ∨ w ∈ fr π π) ∧ ¬ Lt w d := by
  have G := P.G
  obtain ⟨-, -, -, -, h0γ, h0π⟩ := P.ht.psi
  cases e1 : inC γ g d
  · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC h0γ
      (fun v hv h => G.lt_of_lt_of_le (G.sub P.γS hv) P.γS hgS h hg) e1
    exact ⟨w, Or.inl hw, hwn⟩
  · cases e2 : inC π g d
    · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC h0π
        (fun v hv h => G.lt_of_lt_of_le (G.sub P.πS hv) P.γS hgS h hg) e2
      exact ⟨w, Or.inr hw, hwn⟩
    · exact absurd ⟨e1, e2⟩ hn

theorem F_spec {w : Tm} (hw : w ∈ fr π γ ∨ w ∈ fr π π) : w ∈ S ∧ Lt w π := by
  rcases hw with hw | hw
  · exact ⟨P.G.sub P.γS (fr_spec hw).1, (fr_spec hw).2⟩
  · exact ⟨P.G.sub P.πS (fr_spec hw).1, (fr_spec hw).2⟩

/-! ### `t` 未満の元は `π` 未満 -/

theorem tb_aux : ∀ N, ∀ z, z ∈ S → z.size ≤ N →
    (Lt z (.Psi .zero π γ) → Lt z π) ∧
      (isPrincipal z = true → ¬ Lt (.Psi .zero π γ) z → Lt z π) := by
  have G := P.G
  have hπp := P.hT.principal
  have hπb := P.hT.not_bot
  intro N
  induction N with
  | zero => intro z _ h; exact absurd h (by have := Tm.size_pos z; omega)
  | succ N ih =>
    have prin : ∀ y, y ∈ S → y.size ≤ N + 1 → isPrincipal y = true →
        (Lt y (.Psi .zero π γ) → Lt y π) ∧ (¬ Lt (.Psi .zero π γ) y → Lt y π) := by
      intro y hy hs hyp
      have hyF := G.nf y hy
      by_cases hl1 : lev y < lev π
      · exact ⟨fun _ => lt_of_lev_lt' hl1, fun _ => lt_of_lev_lt' hl1⟩
      by_cases hl2 : lev π < lev y
      · refine ⟨fun h => absurd (lev_le_of_lt_gen h) (by simp only [lev]; omega),
          fun h => absurd (lt_of_lev_lt' (by simp only [lev]; omega)) h⟩
      have hl : lev y = lev π := by omega
      by_cases hb : isBot y = true
      · have := bot_ltY hb (Nat.le_of_eq hl) hπp hπb P.πF
        exact ⟨fun _ => this, fun _ => this⟩
      rcases shape_FY3 hyF hyp (Bool.eq_false_iff.mpr hb) with ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨ρ, δ, rfl⟩
      · have hx := G.sub hy (mem_subs_om x)
        have ihx := ih x hx (by simp only [Tm.size] at hs; omega)
        rcases P.hT with ⟨c, rfl, -⟩ | ⟨n, r0, rfl⟩
        · have hcS := G.sub P.πS (mem_subs_om c)
          have hl' : lev x = lev c := hl
          refine ⟨fun h => (G.lt_om_iffS hx hcS).mpr ((lt_om_psiY P.ht).mp h), fun h => ?_⟩
          refine (G.lt_om_iffS hx hcS).mpr ?_
          by_cases hxc : Lt x c
          · exact hxc
          · exact absurd ((psiOm_lt_om_iff hl').mpr hxc) h
        · have hOF := psiXiOF n r0 γ
          have hl' : lev x = lev (Tm.Psi .zero (.Xi n r0) γ) := hl
          refine ⟨fun h => (lt_om_OFG (xiOF _ _)).mpr (ihx.1 ((lt_om_OFG hOF).mp h)), fun h => ?_⟩
          refine (lt_om_OFG (xiOF _ _)).mpr (ihx.1 (P.lt_of_ne_gt hx ?_))
          intro e
          exact h ((OF_lt_om_iff hOF hl').mpr e)
      · have hl' : lev π = m := hl.symm
        have key : ¬ Lt (.Psi .zero π γ) (.Xi m f) → Lt (.Xi m f) π := fun h => by
          rw [lt_psi_xiY hl'] at h
          refine G.lt_of_gt P.πS hy ?_
          cases e : cmp π (Tm.Xi m f)
          · exact absurd (Or.inl (by rw [e]; decide)) h
          · exact absurd (Or.inl (by rw [e]; decide)) h
          · rfl
        exact ⟨fun h => key ((lt_xi_psiY hl').mp h), key⟩
      · have hyF' := hyF.psi
        have hρS : ρ ∈ S := G.sub hy (by simp [subs, self_mem_subs])
        have hl' : lev ρ = lev π := hl
        have hne := P.ne_of_mem hy
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rcases (lt_psi_psiY hl' hne).mp h with h' | ⟨-, h', -⟩
          · have := (ih ρ hρS (by simp only [Tm.size] at hs; omega)).2 hyF'.2.1.principal h'
            exact G.trans hy hρS P.πS (lt_psi_targetY hyF) this
          · exact h'
        · by_cases h' : Lt (.Psi .zero ρ δ) π
          · exact h'
          · exact absurd ((lt_psi_psiY hl'.symm (fun e => hne e.symm)).mpr (Or.inl h')) h
    intro z hz hs
    have hzF := G.nf z hz
    refine ⟨fun hzt => ?_, fun hzp => (prin z hz hs hzp).2⟩
    cases hsz : summands z with
    | nil =>
      have : z = .zero := by cases z <;> simp_all [summands]
      subst this
      exact zero_lt (by rcases P.hT with ⟨c, rfl, -⟩ | ⟨n, r, rfl⟩ <;> intro e <;> cases e)
    | cons h rest =>
      have hmem : h ∈ summands z := by rw [hsz]; exact List.mem_cons_self
      have hhS := G.sub hz (mem_subs_of_mem_summands hmem)
      obtain ⟨-, hhp⟩ := summands_FYNF z hzF h hmem
      have hhs := size_le_of_mem_summands z h hmem
      have hht : Lt h (.Psi .zero π γ) :=
        (lt_principal_iff hhp rfl).mpr (cmpP_head_of_lt hsz rfl hzt)
      have := (prin h hhS (by omega) hhp).1 hht
      exact lt_of_head_lt hπp hsz ((lt_principal_iff hhp hπp).mp this)

/-- `t` 未満の `S` の元は `π` 未満 -/
theorem tb {z : Tm} (hz : z ∈ S) (h : Lt z (.Psi .zero π γ)) : Lt z π :=
  (P.tb_aux _ z hz (Nat.le_refl _)).1 h

/-- `t` が上にない主要項は `π` 未満 -/
theorem tbge {z : Tm} (hz : z ∈ S) (hzp : isPrincipal z = true)
    (h : ¬ Lt (.Psi .zero π γ) z) : Lt z π :=
  (P.tb_aux _ z hz (Nat.le_refl _)).2 hzp h

/-! ### `t < ρ ≤ v < π` の矛盾 -/

/-- `t < ρ`（`ρ` は `S` の目標）で `ρ ≤ v < π` なら、`ρ` の真部分項についての「`v` 未満なら `t` 未満」の下で矛盾 -/
theorem tgt_contra {ρ v : Tm} (hρS : ρ ∈ S) (hρT : IsTgt ρ) (hl : lev ρ = lev π)
    (htρ : Lt (.Psi .zero π γ) ρ) (hvS : v ∈ S) (hρv : Le ρ v) (hvπ : Lt v π)
    (H : ∀ u, u ∈ S → u.size < ρ.size → Lt u v → Lt u (.Psi .zero π γ)) : False := by
  have G := P.G
  rcases hρT with ⟨d, rfl, -⟩ | ⟨m, r, rfl⟩
  · have hdS := G.sub hρS (mem_subs_om d)
    rcases P.hT with ⟨c, rfl, -⟩ | ⟨n, r0, rfl⟩
    · have hl' : lev d = lev c := hl
      have hcS := G.sub P.πS (mem_subs_om c)
      exact (psiOm_lt_om_iff hl').mp htρ
        ((G.lt_om_iffS hdS hcS).mp (G.lt_of_le_of_lt hρS hvS P.πS hρv hvπ))
    · have hl' : lev d = lev (Tm.Psi .zero (.Xi n r0) γ) := hl
      have e := (OF_lt_om_iff (psiXiOF n r0 γ) hl').mp htρ
      have hdv : Lt d v := G.lt_of_lt_of_le hdS hρS hvS (G.nf _ hρS).om.2.2 hρv
      have := H d hdS (by simp only [Tm.size]; omega) hdv
      unfold Lt at this
      rw [this] at e
      cases e
  · have hrS := G.sub hρS (mem_subs_xi m r)
    have hl' : lev π = m := hl.symm
    rcases (lt_psi_xiY hl').mp htρ with h | ⟨hrγ, hn⟩
    · apply h
      have := G.lt_of_le_of_lt hρS hvS P.πS hρv hvπ
      unfold Lt at this
      rw [G.swap hρS P.πS, this]
      decide
    · obtain ⟨u, hu, hun⟩ := wit_of_not_inC (G.nf _ hρS).xi.2.2.2.2
        (fun w hw h' => G.trans (G.sub hrS hw) hrS P.γS h' hrγ) hn
      have huS := G.sub hrS (fr_spec hu).1
      have := size_le_of_mem_subs (fr_spec hu).1
      exact hun (H u huS (by simp only [Tm.size]; omega)
        (G.lt_of_lt_of_le huS hρS hvS (G.k2x m r hρS u hu) hρv))

/-! ### `π = Ω_c` のとき：`c` 未満なら `t` 未満 -/

theorem below_aux {c : Tm} (hπ : π = .Om c) : ∀ N, ∀ v, v ∈ S → v.size ≤ N →
    Lt v c → Lt v (.Psi .zero π γ) := by
  subst hπ
  have G := P.G
  have hcS := G.sub P.πS (mem_subs_om c)
  have hcΩ : Lt c (.Om c) := P.πF.om.2.2
  intro N
  induction N with
  | zero => intro v _ h; exact absurd h (by have := Tm.size_pos v; omega)
  | succ N ih =>
    intro v hvS hs hvc
    have hvF := G.nf _ hvS
    cases hsv : summands v with
    | nil =>
      have : v = .zero := by cases v <;> simp_all [summands]
      subst this
      exact zero_lt (by intro e; cases e)
    | cons h rest =>
      have hmem : h ∈ summands v := by rw [hsv]; exact List.mem_cons_self
      have hhS := G.sub hvS (mem_subs_of_mem_summands hmem)
      obtain ⟨hhF, hhp⟩ := summands_FYNF v hvF h hmem
      have hhs := size_le_of_mem_summands v h hmem
      have hhc : Lt h c := G.lt_of_le_of_lt hhS hvS hcS (head_leY hvF hsv) hvc
      have IH : ∀ u, u ∈ S → u.size < h.size → Lt u c → Lt u (.Psi .zero (.Om c) γ) :=
        fun u hu hus huc => ih u hu (by omega) huc
      have hht : Lt h (.Psi .zero (.Om c) γ) := by
        have hl := lev_le_of_lt_gen hhc
        rcases Nat.lt_or_eq_of_le hl with hl | hl
        · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
        by_cases hb : isBot h = true
        · exact bot_ltY hb (by simp only [lev]; omega) rfl rfl P.ht
        rcases shape_FY4 hhF hhp (Bool.eq_false_iff.mpr hb) with
          ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨d, δ, rfl⟩ | ⟨m, r, δ, rfl⟩
        · have hx := G.sub hhS (mem_subs_om x)
          exact (lt_om_psiY P.ht).mpr (G.trans hx hhS hcS hhF.om.2.2 hhc)
        · simp only [lev] at hl
          refine P.xi_lt_t hhS hl.symm (G.trans hhS hcS P.πS hhc hcΩ) (fun _ u hu => ?_)
          have hfS := G.sub hhS (mem_subs_xi m f)
          have huS := G.sub hfS (fr_spec hu).1
          have := size_le_of_mem_subs (fr_spec hu).1
          exact IH u huS (by simp only [Tm.size]; omega)
            (G.trans huS hhS hcS (G.k2x m f hhS u hu) hhc)
        · have hdS := G.sub hhS (mem_subs_psi_c _ d δ)
          have hdc := G.trans hdS hhS hcS (G.cx d δ hhS) hhc
          simp only [lev] at hl
          exact P.psi_lt_of_tgt hhS hl (fun h' => (psiOm_lt_om_iff hl).mp h' hdc)
        · simp only [lev] at hl
          have hρS : Tm.Xi m r ∈ S := G.sub hhS (by simp [subs])
          have hrS := G.sub hρS (mem_subs_xi m r)
          have hδS := G.sub hhS (mem_subs_psi_a _ _ δ)
          have hhπ : Lt (.Psi .zero (.Xi m r) δ) (.Om c) := G.trans hhS hcS P.πS hhc hcΩ
          obtain ⟨-, -, -, -, h0δ, h0ρ⟩ := hhF.psi
          by_cases htρ' : ¬ Lt (.Psi .zero (.Om c) γ) (.Xi m r)
          · exact P.psi_lt_of_tgt hhS hl htρ'
          have htρ : Lt (.Psi .zero (.Om c) γ) (.Xi m r) := Decidable.of_not_not htρ'
          have hcρ : Lt c (.Xi m r) := by
            rcases (lt_psi_xiY (π := .Om c) hl.symm).mp htρ with h' | ⟨hrγ, hn⟩
            · rw [cmp_principal rfl rfl, cmpP_om_xi hl.symm] at h'
              rcases G.le_of_ne_gt hcS hρS h' with e | e
              · exfalso
                have hs' := P.hT
                rcases hs' with ⟨c', e', hsc⟩ | ⟨n', r', e'⟩
                · cases e'
                  rw [e] at hsc
                  simp [isSucc, summands] at hsc
                · cases e'
              · exact e
            · exfalso
              obtain ⟨u, hu, hun⟩ := wit_of_not_inC (G.nf _ hρS).xi.2.2.2.2
                (fun w hw h' => G.trans (G.sub hrS hw) hrS P.γS h' hrγ) hn
              have huS := G.sub hrS (fr_spec hu).1
              have := size_le_of_mem_subs (fr_spec hu).1
              exact hun (IH u huS (by simp only [Tm.size]; omega)
                (G.trans huS hhS hcS (G.k2t _ δ hhS u (G.fr_xi_sub hρS hu)) hhc))
          rcases G.tri hδS P.γS with h' | h' | h'
          · refine P.psi_lt_of_c1 hhS hl htρ hhπ h' ?_ ?_
            · refine inC_of_fr δ h0δ (fun v hv hv' => G.trans (G.sub hδS hv) hδS P.γS hv' h')
                (fun u hu => inC_of_lt_node (fr_node hu) ?_)
              have huS := G.sub hδS (fr_spec hu).1
              have := size_le_of_mem_subs (fr_spec hu).1
              exact IH u huS (by simp only [Tm.size]; omega)
                (G.trans huS hhS hcS (G.k2 _ δ hhS u hu) hhc)
            · refine inC_of_fr _ h0ρ
                (fun v hv hv' => G.trans (G.sub hρS hv) hδS P.γS hv' h')
                (fun u hu => inC_of_lt_node (fr_node hu) ?_)
              have huS := G.sub hρS (fr_spec hu).1
              have := size_le_of_mem_subs (fr_spec hu).1
              exact IH u huS (by simp only [Tm.size] at this ⊢; omega)
                (G.trans huS hhS hcS (G.k2t _ δ hhS u hu) hhc)
          all_goals
            refine P.psi_lt_of_c2 hhS hl htρ hhπ (ne_gt_of_le ?_) (fun ⟨_, hin⟩ => ?_)
            · first | exact Or.inl h'.symm | exact Or.inr h'
            · rw [inC_om] at hin
              exact G.asymm hcS hhS (G.coll_psiS hhS c hcS hin hcρ) hhc
      exact lt_of_head_lt rfl hsv ((lt_principal_iff hhp rfl).mp hht)

/-- `π = Ω_c` なら、`c` 未満の `S` の元は `t` 未満 -/
theorem below {c v : Tm} (hπ : π = .Om c) (hv : v ∈ S) (h : Lt v c) : Lt v (.Psi .zero π γ) :=
  P.below_aux hπ _ v hv (Nat.le_refl _) h

/-! ### 補題 A -/

/-- 補題 A の主要項の場合 -/
theorem lemA_head {h w : Tm} (hhS : h ∈ S) (hhp : isPrincipal h = true)
    (hw : w ∈ fr π γ ∨ w ∈ fr π π) (hhw : Le h w)
    (IH : ∀ u, u ∈ S → u.size < h.size → Le u w → Lt u (.Psi .zero π γ)) :
    Lt h (.Psi .zero π γ) := by
  have G := P.G
  have hhF := G.nf _ hhS
  obtain ⟨hwS, hwπ⟩ := P.F_spec hw
  have hhπ : Lt h π := G.lt_of_le_of_lt hhS hwS P.πS hhw hwπ
  have hl := lev_le_of_lt_gen hhπ
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
  by_cases hb : isBot h = true
  · exact bot_ltY hb (by simp only [lev]; omega) rfl rfl P.ht
  rcases shape_FY3 hhF hhp (Bool.eq_false_iff.mpr hb) with ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨ρ, δ, rfl⟩
  · have hx := G.sub hhS (mem_subs_om x)
    rcases P.hT with ⟨c, rfl, -⟩ | ⟨n, r0, rfl⟩
    · have hcS := G.sub P.πS (mem_subs_om c)
      exact (lt_om_psiY P.ht).mpr ((G.lt_om_iffS hx hcS).mp hhπ)
    · exact (lt_om_OFG (psiXiOF _ _ _)).mpr (IH x hx (by simp only [Tm.size]; omega)
        (Or.inr (G.lt_of_lt_of_le hx hhS hwS hhF.om.2.2 hhw)))
  · simp only [lev] at hl
    refine P.xi_lt_t hhS hl.symm hhπ (fun _ u hu => ?_)
    have hfS := G.sub hhS (mem_subs_xi m f)
    have huS := G.sub hfS (fr_spec hu).1
    have := size_le_of_mem_subs (fr_spec hu).1
    exact IH u huS (by simp only [Tm.size]; omega)
      (Or.inr (G.lt_of_lt_of_le huS hhS hwS (G.k2x m f hhS u hu) hhw))
  · have hρS : ρ ∈ S := G.sub hhS (by simp [subs, self_mem_subs])
    have hδS := G.sub hhS (mem_subs_psi_a _ _ δ)
    obtain ⟨-, hρT, -, -, h0δ, h0ρ⟩ := hhF.psi
    have hl' : lev ρ = lev π := hl
    by_cases htρ' : ¬ Lt (.Psi .zero π γ) ρ
    · exact P.psi_lt_of_tgt hhS hl' htρ'
    have htρ : Lt (.Psi .zero π γ) ρ := Decidable.of_not_not htρ'
    rcases G.tri hδS P.γS with h' | h' | h'
    · refine P.psi_lt_of_c1 hhS hl' htρ hhπ h' ?_ ?_
      · refine inC_of_fr δ h0δ (fun v hv hv' => G.trans (G.sub hδS hv) hδS P.γS hv' h')
          (fun u hu => inC_of_lt_node (fr_node hu) ?_)
        have huS := G.sub hδS (fr_spec hu).1
        have := size_le_of_mem_subs (fr_spec hu).1
        exact IH u huS (by simp only [Tm.size]; omega)
          (Or.inr (G.lt_of_lt_of_le huS hhS hwS (G.k2 _ δ hhS u hu) hhw))
      · refine inC_of_fr ρ h0ρ (fun v hv hv' => G.trans (G.sub hρS hv) hδS P.γS hv' h')
          (fun u hu => inC_of_lt_node (fr_node hu) ?_)
        have huS := G.sub hρS (fr_spec hu).1
        have := size_le_of_mem_subs (fr_spec hu).1
        exact IH u huS (by simp only [Tm.size]; omega)
          (Or.inr (G.lt_of_lt_of_le huS hhS hwS (G.k2t _ δ hhS u hu) hhw))
    all_goals
      -- `w < ρ`
      have hwρ : Lt w ρ := by
        rcases G.tri hwS hρS with e | e | e
        · exact e
        all_goals
          exfalso
          refine P.tgt_contra hρS hρT hl' htρ hwS (by first | exact Or.inl e.symm | exact Or.inr e)
            hwπ (fun u hu hus huw => IH u hu (by simp only [Tm.size]; omega) (Or.inr huw))
      refine P.psi_lt_of_c2 hhS hl' htρ hhπ
        (ne_gt_of_le (by first | exact Or.inl h'.symm | exact Or.inr h')) (fun ⟨hin1, hin2⟩ => ?_)
      have hd : ∀ x, x ∈ S → ∀ w', w' ∈ subs x → ¬ Lt w' π →
          ¬ Lt w' (.Psi .zero ρ δ) := fun x hx w' hw' hn hlt =>
        hn (G.trans (G.sub hx hw') hhS P.πS hlt hhπ)
      have hinw : inC w δ (.Psi .zero ρ δ) = true := by
        rcases hw with hw | hw
        · exact fr_of_inC γ (hd γ P.γS) hin1 w hw
        · exact fr_of_inC π (hd π P.πS) hin2 w hw
      exact G.not_lt_of_le hhS hwS hhw (G.coll_psiS hhS w hwS hinw hwρ)

/-- 補題 A：`γ` と `π` の前線のどれか以下の `S` の元は `t` 未満 -/
theorem lemA_aux : ∀ N, ∀ v, v ∈ S → v.size ≤ N →
    (∃ w, (w ∈ fr π γ ∨ w ∈ fr π π) ∧ Le v w) → Lt v (.Psi .zero π γ) := by
  have G := P.G
  intro N
  induction N with
  | zero => intro v _ h; exact absurd h (by have := Tm.size_pos v; omega)
  | succ N ih =>
    intro v hvS hs ⟨w, hw, hvw⟩
    have hvF := G.nf _ hvS
    obtain ⟨hwS, -⟩ := P.F_spec hw
    cases hsv : summands v with
    | nil =>
      have : v = .zero := by cases v <;> simp_all [summands]
      subst this
      exact zero_lt (by intro e; cases e)
    | cons h rest =>
      have hmem : h ∈ summands v := by rw [hsv]; exact List.mem_cons_self
      have hhS := G.sub hvS (mem_subs_of_mem_summands hmem)
      obtain ⟨-, hhp⟩ := summands_FYNF v hvF h hmem
      have hhs := size_le_of_mem_summands v h hmem
      have hhw : Le h w := G.le_trans hhS hvS hwS (head_leY hvF hsv) hvw
      have hht := P.lemA_head hhS hhp hw hhw (fun u hu hus huw => ih u hu (by omega) ⟨w, hw, huw⟩)
      exact lt_of_head_lt rfl hsv ((lt_principal_iff hhp rfl).mp hht)

theorem lemA {v : Tm} (hv : v ∈ S) (h : ∃ w, (w ∈ fr π γ ∨ w ∈ fr π π) ∧ Le v w) :
    Lt v (.Psi .zero π γ) :=
  P.lemA_aux _ v hv (Nat.le_refl _) h

/-- K2：`γ` の前線は全て `t` 未満 -/
theorem k2 : ∀ w, w ∈ fr π γ → Lt w (.Psi .zero π γ) := fun w hw =>
  P.lemA (P.F_spec (Or.inl hw)).1 ⟨w, Or.inl hw, Le.refl _⟩

/-- K2T：`π` の前線は全て `t` 未満 -/
theorem k2t : ∀ w, w ∈ fr π π → Lt w (.Psi .zero π γ) := fun w hw =>
  P.lemA (P.F_spec (Or.inr hw)).1 ⟨w, Or.inr hw, Le.refl _⟩

theorem inC_arg : inC γ γ (.Psi .zero π γ) = true := inC_arg_of_k2 P.ht P.k2

theorem inC_tgt : inC π γ (.Psi .zero π γ) = true := inC_tgt_of_k2t P.ht P.k2t

/-- CX：`π = Ω_c` なら `c < t` -/
theorem cx {c : Tm} (hπ : π = .Om c) : Lt c (.Psi .zero π γ) := by
  have G := P.G
  have hΩS : Tm.Om c ∈ S := hπ ▸ P.πS
  have hcS := G.sub hΩS (mem_subs_om c)
  have hΩF := G.nf _ hΩS
  have hs : isSucc c = true := by
    rcases P.hT with ⟨c', e, hs⟩ | ⟨n, r, e⟩
    · rw [hπ] at e; cases e; exact hs
    · rw [hπ] at e; cases e
  have hlt : lev c = lev π := by rw [hπ]; rfl
  cases c with
  | one => exact bot_ltY rfl (Nat.le_of_eq hlt) rfl rfl P.ht
  | plus a b =>
    have hcF := G.nf _ hcS
    obtain ⟨-, -, hap, -⟩ := hcF.plus
    have haS := G.sub hcS (show a ∈ subs (.plus a b) by simp [subs, self_mem_subs])
    have haF := G.nf _ haS
    have hac : Lt a (.plus a b) := lt_plus_leftY hcF
    have haΩ : Lt a (.Om (.plus a b)) := G.trans haS hcS hΩS hac hΩF.om.2.2
    have hat : Lt a (.Psi .zero π γ) := by
      have hl : lev a = lev π := hlt
      by_cases hb : isBot a = true
      · exact bot_ltY hb (Nat.le_of_eq hl) rfl rfl P.ht
      rcases shape_FY3 haF hap (Bool.eq_false_iff.mpr hb) with ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨ρ, δ, rfl⟩
      · have hx := G.sub haS (mem_subs_om x)
        have hxc := G.trans hx haS hcS haF.om.2.2 hac
        have ht' := P.ht
        rw [hπ] at ht' ⊢
        exact (lt_om_psiY ht').mpr hxc
      · refine P.k2t _ ?_
        rw [hπ]
        simp [fr, haΩ]
      · refine P.k2t _ ?_
        rw [hπ]
        simp [fr, haΩ]
    exact lt_of_head_lt rfl (summands_plus a b) ((lt_principal_iff hap rfl).mp hat)
  | _ => simp [isSucc, summands] at hs

end PsiCtxY

end RTKA
