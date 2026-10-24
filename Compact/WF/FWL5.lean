import Compact.WF.FWL4

/-! 体系全体の順序の性質の証明：新しい項が `t = Ψ^ξ_π(γ)` の場合の切断性と反対称性
（`FZL5.lean` の一般化）。

目標が `Ψ` になりうるので、`t` と `S` の `Ψ` の反対称性と `t` の切断性を、`S` の元の大きさについて同時に示す。
大きさ `M` 未満の元との反対称性から、大きさ `M` 以下の組の切断性（`cut_le`）が出て、それと大きさ `M` 未満の元との
反対称性から、大きさ `M` の `Ψ` との反対称性（`psi_swap_le`）が出る。

切断性の帰納法の測度は、組の大きさの最大値と和の辞書式順序。`p = Ψ^τ_ρ(δ) < t` を Prop. 4.20 の
(1)〜(4) で分け、(2)・(4) は `t` の前線の証人（補題 A）、(1)・(3) は `p` の前線が `t` 未満であること
（`p` の真部分項どうしの切断性）を使う。 -/

namespace RTKA.W

open Tm
open WFX (fr_mem_psi_p)

/-- 大きさ `M` 以下の組についての `t` の切断性 -/
def CutLe (S : List Tm) (t : Tm) (M : Nat) : Prop :=
  ∀ a b, a ∈ S → b ∈ S → a.size ≤ M → b.size ≤ M → Lt b a → Lt a t → Lt b t

/-- 切断性：主要項の組についての切断性から一般の切断性へ（組の大きさの最大値と和の辞書式の帰納法。
    大きさ `M` 以下の組に限る）。`ihA` は `p` より小さい項どうし、`ihB` は大きさがどちらも `p`・`q` の大きい方
    以下で和が小さい組。 -/
theorem GoodY.cut_le_of_principal_lex {S : List Tm} (G : GoodY S) {t : Tm} (ht : WNF t)
    (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S) (M : Nat)
    (hP : ∀ q p, q ∈ S → p ∈ S → q.size ≤ M → p.size ≤ M → isPrincipal t = true →
      isPrincipal q = true → isPrincipal p = true →
      (∀ a b, a ∈ S → b ∈ S → a.size < p.size → b.size < p.size → Lt b a → Lt a t → Lt b t) →
      (∀ a b, a ∈ S → b ∈ S → a.size + b.size < q.size + p.size →
        (a.size ≤ p.size ∨ a.size ≤ q.size) → (b.size ≤ p.size ∨ b.size ≤ q.size) →
        Lt b a → Lt a t → Lt b t) →
      Lt q p → Lt p t → Lt q t) : CutLe S t M := by
  have key : ∀ M', M' ≤ M → ∀ N, ∀ a b, a ∈ S → b ∈ S → a.size ≤ M' → b.size ≤ M' →
      a.size + b.size ≤ N → Lt b a → Lt a t → Lt b t := by
    intro M'
    induction M' with
    | zero => intro _ N a _ _ _ h; exact absurd h (by have := Tm.size_pos a; omega)
    | succ M' ihM =>
      intro hM' N
      induction N with
      | zero => intro a _ _ _ _ _ h; exact absurd h (by have := Tm.size_pos a; omega)
      | succ N ihN =>
        intro a b ha hb hMa hMb hN h1 h2
        refine G.cutGen ht hsub (fun htp q p hq hp => ?_) ha hb h1 h2
        have hqS := G.sub hb (mem_subs_of_mem_summands hq)
        have hpS := G.sub ha (mem_subs_of_mem_summands hp)
        have hqs := size_le_of_mem_summands b q hq
        have hps := size_le_of_mem_summands a p hp
        refine hP q p hqS hpS (by omega) (by omega) htp (summands_WNF b (G.nf b hb) q hq).2
          (summands_WNF a (G.nf a ha) p hp).2 (fun a' b' ha' hb' h1' h2' => ?_)
          (fun a' b' ha' hb' hs' h1' h2' => ?_)
        · exact ihM (by omega) (a'.size + b'.size) a' b' ha' hb' (by omega) (by omega)
            (Nat.le_refl _)
        · exact ihN a' b' ha' hb' (by omega) (by omega) (by omega)
  exact fun a b ha hb hMa hMb => key M (Nat.le_refl _) (a.size + b.size) a b ha hb hMa hMb
    (Nat.le_refl _)

/-- `cmp` が `.eq` でない二つの項について、`x < y ⟺ ¬ y < x` なら反対称 -/
theorem swap_of_iff {x y : Tm} (h1 : cmp x y ≠ .eq) (h2 : cmp y x ≠ .eq)
    (h : Lt x y ↔ ¬ Lt y x) : cmp y x = (cmp x y).swap := by
  unfold Lt at h
  revert h1 h2 h
  cases cmp x y <;> cases cmp y x <;> decide

/-- `Ψ` どうしの反対称性を大きさ `M` 以下で仮定すれば、新しい項 `t` は大きさ `M` 以下の `S` の元と反対称 -/
theorem GoodY.anti_new_le {S : List Tm} (G : GoodY S) {t : Tm} (ht : WNF t)
    (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S) (htS : t ∉ S) (M : Nat)
    (hPsi : ∀ ξ π γ σ κ β, t = .Psi ξ π γ → Tm.Psi σ κ β ∈ S → (Tm.Psi σ κ β).size ≤ M →
      lev π = lev κ → cmpPsi (.Psi σ κ β) t = (cmpPsi t (.Psi σ κ β)).swap) :
    ∀ z, z ∈ S → z.size ≤ M → AntiT t z := by
  intro z hz hzM
  have hzF := G.nf z hz
  refine ⟨?_, fun h => absurd h (G.ne_new ht hsub htS z hz).2⟩
  rw [cmp_eq z t, cmp_eq t z]
  apply cmpList_swap
  intro x hx y hy
  have hyS := G.sub hz (mem_subs_of_mem_summands hy)
  have hys := size_le_of_mem_summands z y hy
  obtain ⟨-, hyp⟩ := summands_WNF z hzF y hy
  obtain ⟨-, hxp⟩ := summands_WNF t ht x hx
  cases htp : isPrincipal t
  · have hxS : x ∈ S := hsub x (mem_subs_of_mem_summands hx) (by
      intro e; subst e; rw [hxp] at htp; cases htp)
    rw [← cmp_principal hyp hxp, ← cmp_principal hxp hyp]
    exact G.swap hxS hyS
  · rw [summands_principal' htp, List.mem_singleton] at hx
    subst hx
    exact G.swapP_new ht hsub hyS htp hyp (fun ξ π γ σ κ β e1 e2 hl => by
      subst e2; exact hPsi ξ π γ σ κ β e1 hyS (by omega) hl)

/-- `Ξ_j(d) < π`（`π ∈ S` は `Ω` の不動点の目標、階 `j`）、`π ∈ C(a, π)`、`a ≤ d` なら、`π` の前線
    （`π` について）に `Ξ_j(d)` 未満でない元がある -/
theorem GoodY.wit_xi_tgtS {S : List Tm} (G : GoodY S) : ∀ π, π ∈ S → IsOF π → IsTgt π →
    ∀ {j : Nat} {d a : Tm}, Tm.Xi j d ∈ S → a ∈ S → Lt (.Xi j d) π → lev π = j →
      inC π a π = true → Le a d → ∃ w, w ∈ fr π π ∧ ¬ Lt w (.Xi j d) := by
  intro π
  induction π using WFX.size_induction with
  | h π ih =>
  intro hπS hOF hT j d a hxS haS hlt hl hC had
  have hdS := G.sub hxS (mem_subs_xi j d)
  rcases hT with ⟨c, rfl, -⟩ | ⟨m, q, rfl⟩ | ⟨ζ, κ, b, rfl, hζ⟩
  · rcases hOF with ⟨n, a', e⟩ | ⟨ξ', π', a', e, -, -⟩ <;> cases e
  · simp only [lev] at hl
    subst hl
    have hqS := G.sub hπS (mem_subs_xi m q)
    rcases inC_xi_iff.mp hC with h | ⟨-, hqa⟩
    · exact absurd h (Lt.irrefl _)
    have hqd : Lt q d := G.lt_of_lt_of_le hqS haS hdS hqa had
    have hne : d ≠ q := fun e => by subst e; exact Lt.irrefl _ hqd
    rcases (lt_xi_xi0 hne).mp hlt with ⟨hdq, -⟩ | ⟨-, hn⟩
    · exact absurd hdq (G.asymm hqS hdS hqd)
    · obtain ⟨u, hu, hun⟩ := wit_of_not_inC (G.nf _ hπS).xi.2.2.2.2
        (fun v hv h' => G.trans (G.sub hqS hv) hqS hdS h' hqd) hn
      exact ⟨u, G.fr_xi_sub hπS hu, hun⟩
  · have hκS : κ ∈ S := G.sub hπS (by simp [subs, self_mem_subs])
    have wπ := G.nf _ hπS
    have hlκ : lev κ = j := hl
    have hxκ : Lt (.Xi j d) κ := by
      have h1 := (lt_xi_psiY (π := κ) hlκ).mp hlt
      rw [lt_psi_xiY hlκ] at h1
      cases e : cmp κ (.Xi j d) with
      | gt => exact G.lt_of_gt hκS hxS e
      | _ => exact absurd (Or.inl (by rw [e]; decide)) h1
    have hπκ : Lt (.Psi ζ κ b) κ := lt_psi_targetY wπ
    have hκC : inC κ a κ = true := by
      rcases inC_psi_iff.mp hC with h | ⟨h, -, -, -⟩
      · exact absurd h (Lt.irrefl _)
      · exact inC_mono κ a _ a κ h (fun v hv h' => G.trans (G.sub hκS hv) hπS hκS h' hπκ)
          (fun _ _ h => h)
    have hκOF : IsOF κ := by
      rcases wπ.psi.tgt.cases wπ.psi.piF with ⟨c, rfl⟩ | h
      · exact absurd (lt_oneY wπ.psi.xiF wπ.psi.mlt) hζ
      · exact h
    obtain ⟨w, hw, hwn⟩ := ih κ (by simp only [Tm.size]; omega) hκS hκOF wπ.psi.tgt hxS haS hxκ
      hlκ hκC had
    exact ⟨w, fr_mem_psi_p (Lt.irrefl _)
      (G.fr_sub hκS hπS hκS (Or.inr hπκ) hw (G.k2t _ _ _ hπS w hw)), hwn⟩

/-- 大きさ `N` 以下の `S` の元と新しい項 `Ψ^ξ_π(γ)` の反対称性 -/
def ABle (S : List Tm) (ξ π γ : Tm) (N : Nat) : Prop :=
  ∀ z, z ∈ S → z.size ≤ N → AntiT (.Psi ξ π γ) z

theorem ABle.tgt {S : List Tm} {ξ π γ : Tm} {N : Nat} (hA : ABle S ξ π γ N) {ρ : Tm}
    (hρS : ρ ∈ S) (hρ : ρ.size ≤ N) : ∀ σ κ β, ρ = .Psi σ κ β → AntiT (.Psi ξ π γ) ρ :=
  fun _ _ _ _ => hA ρ hρS hρ

namespace PsiCtxY

variable {S : List Tm} {ξ π γ : Tm} (P : PsiCtxY S ξ π γ)
include P

/-- `t < ρ` で `x ∈ S` の `ρ` 以上の部分項は `t` 未満でない（`ρ` 以下の項との切断性と反対称性の下で） -/
theorem hd_of_tgt {ρ x : Tm} (hρS : ρ ∈ S) (hρT : IsTgt ρ) (hl : lev ρ = lev π)
    (htρ : Lt (.Psi ξ π γ) ρ) (hxS : x ∈ S)
    (ihA : ∀ a b, a ∈ S → b ∈ S → a.size ≤ x.size → b.size ≤ ρ.size → Lt b a →
      Lt a (.Psi ξ π γ) → Lt b (.Psi ξ π γ))
    (hA : ABle S ξ π γ ρ.size) :
    ∀ v, v ∈ subs x → ¬ Lt v ρ → ¬ Lt v (.Psi ξ π γ) := fun v hv hvρ hvt => by
  have G := P.G
  have hvS := G.sub hxS hv
  have hvs := size_le_of_mem_subs hv
  refine P.tgt_contra hρS hρT hl htρ hvS (G.le_of_not_lt hvS hρS hvρ) (P.tb hvS hvt)
    (fun u huS hus huv => ihA v u hvS huS hvs (Nat.le_of_lt hus) huv hvt)
    (Or.inr ⟨hvt, fun ρ' hρ'S hρ's hρ'v => ⟨?_, hA ρ' hρ'S hρ's⟩⟩)
  rcases hρ'v with e | e
  · rw [e]; exact hvt
  · exact ihA v ρ' hvS hρ'S hvs hρ's e hvt

/-- `p = Ψ^τ_ρ(δ) < t` が (1) の形（`δ < γ`、`δ, τ, ρ ∈ C(γ, t)`）なら、`p` の前線（`ρ` について）の元は
    `t` 未満（`p` の真部分項どうしの切断性と反対称性の下で） -/
theorem fr_lt_c1 {τ ρ δ : Tm} (hpS : Tm.Psi τ ρ δ ∈ S) (hl : lev ρ = lev π)
    (htρ : Lt (.Psi ξ π γ) ρ) (hinδ : inC δ γ (.Psi ξ π γ) = true)
    (hinτ : inC τ γ (.Psi ξ π γ) = true)
    (hinρ : inC ρ γ (.Psi ξ π γ) = true) (hpπ : Lt (.Psi τ ρ δ) π)
    (ihA : ∀ a b, a ∈ S → b ∈ S → a.size < (Tm.Psi τ ρ δ).size →
      b.size < (Tm.Psi τ ρ δ).size → Lt b a → Lt a (.Psi ξ π γ) →
      Lt b (.Psi ξ π γ))
    (hA : ABle S ξ π γ ρ.size) :
    ∀ w, (w ∈ fr ρ δ ∨ w ∈ fr ρ ρ ∨ w ∈ fr ρ τ) → Lt w (.Psi ξ π γ) := by
  have G := P.G
  have hρS : ρ ∈ S := G.sub hpS (by simp [subs, self_mem_subs])
  have hτS : τ ∈ S := G.sub hpS (by simp [subs, self_mem_subs])
  have hδS := G.sub hpS (mem_subs_psi_a _ _ δ)
  have hρT := (G.nf _ hpS).psi.tgt
  have hd : ∀ x, x ∈ S → x.size < (Tm.Psi τ ρ δ).size → ∀ v, v ∈ subs x → ¬ Lt v ρ →
      ¬ Lt v (.Psi ξ π γ) := fun x hx hxs =>
    P.hd_of_tgt hρS hρT hl htρ hx (fun a b ha hb has hbs h1 h2 =>
      ihA a b ha hb (by omega) (by simp only [Tm.size] at hbs ⊢; omega) h1 h2) hA
  intro w hw
  have hwS : w ∈ S := by
    rcases hw with hw | hw | hw
    · exact G.sub hδS (fr_spec hw).1
    · exact G.sub hρS (fr_spec hw).1
    · exact G.sub hτS (fr_spec hw).1
  have hwp : Lt w (.Psi τ ρ δ) := by
    rcases hw with hw | hw | hw
    · exact G.k2 _ _ δ hpS w hw
    · exact G.k2t _ _ δ hpS w hw
    · exact G.k2s _ _ δ hpS w hw
  have hin : inC w γ (.Psi ξ π γ) = true := by
    rcases hw with hw | hw | hw
    · exact fr_of_inC δ (hd δ hδS (by simp only [Tm.size]; omega)) hinδ w hw
    · exact fr_of_inC ρ (hd ρ hρS (by simp only [Tm.size]; omega)) hinρ w hw
    · exact fr_of_inC τ (hd τ hτS (by simp only [Tm.size]; omega)) hinτ w hw
  exact G.coll_psi P.ht P.πS w hwS hin (G.trans hwS hpS P.πS hwp hpπ)

/-- `τ ∈ C(γ, t)` なら `τ` の前線（`π` について）の元は `t` 未満 -/
theorem fr_lt_of_inC {τ : Tm} (hτS : τ ∈ S) (hin : inC τ γ (.Psi ξ π γ) = true) :
    ∀ w, w ∈ fr π τ → Lt w (.Psi ξ π γ) := fun w hw => by
  have G := P.G
  have hwS := G.sub hτS (fr_spec hw).1
  have hd : ∀ v, v ∈ subs τ → ¬ Lt v π → ¬ Lt v (.Psi ξ π γ) :=
    fun v hv hvπ hvt => hvπ (P.tb (G.sub hτS hv) hvt)
  exact G.coll_psi P.ht P.πS w hwS (fr_of_inC τ hd hin w hw) (fr_spec hw).2

/-- `t` の目標は `Ω_c` か `Ω` の不動点で、`t` 自身は後者のとき `Ω` の不動点 -/
theorem tshape : (∃ c, π = .Om c ∧ ξ = .zero) ∨ (IsOF π ∧ IsOF (.Psi ξ π γ)) := by
  rcases P.ht.shape with ⟨c, rfl, rfl⟩ | hsh
  · exact Or.inl ⟨c, rfl, rfl⟩
  · refine Or.inr ⟨?_, IsOF.psi P.ht (notOm_of_shape hsh)⟩
    rcases P.hT.cases P.πF with ⟨c, e⟩ | h
    · exact absurd e (notOm_of_shape hsh c)
    · exact h

/-- `t = Ψ^ξ_π(γ)` は大きさ `M` 以下の組について `S` を切断する（大きさ `M` 未満の元との反対称性の下で） -/
theorem cut_le (M : Nat) (hA : ABle S ξ π γ (M - 1)) : CutLe S (.Psi ξ π γ) M := by
  have G := P.G
  refine G.cut_le_of_principal_lex P.ht P.hsub M
    (fun q p hqS hpS hqM hpM _ hqp hpp ihA ihB h1 h2 => ?_)
  have hqF := G.nf q hqS
  have hpF := G.nf p hpS
  refine cut_reduceY P.ht rfl rfl hqF hpF hqp hpp h1 h2 (fun lq lp bq bp => ?_)
  have hpπ := P.tb hpS h2
  have hqπ := G.trans hqS hpS P.πS h1 hpπ
  -- 大きさが `p`・`q` 未満の元との反対称性
  have hAp : ∀ N, N < p.size → ABle S ξ π γ N := fun N hN z hz hzN => hA z hz (by omega)
  have hAq : ∀ N, N < q.size → ABle S ξ π γ N := fun N hN z hz hzN => hA z hz (by omega)
  -- `q` の真部分項 `v < p` は `t` 未満
  have ihq : ∀ v, v ∈ S → v.size < q.size → Lt v p → Lt v (.Psi ξ π γ) :=
    fun v hv hvs hvp => ihB p v hpS hv (by omega) (Or.inl (Nat.le_refl _)) (Or.inr (by omega)) hvp h2
  -- 前線の元以下なら補題 A
  have viaF : ∀ w, (w ∈ fr π γ ∨ w ∈ fr π π ∨ w ∈ fr π ξ) → Le p w → Lt q (.Psi ξ π γ) :=
    fun w hw hpw => P.lemA hqS ⟨w, hw, Or.inr (G.lt_of_lt_of_le hqS hpS (P.F_spec hw).1 h1 hpw)⟩
  -- `p` の真部分項 `w < t` で `q ≤ w`
  have viaLe : ∀ w, w ∈ S → w.size < p.size → Lt w (.Psi ξ π γ) → Le q w →
      Lt q (.Psi ξ π γ) := fun w hwS hws hwt hqw => by
    rcases hqw with e | e
    · rw [e]; exact hwt
    · exact ihB w q hwS hqS (by omega) (Or.inl (by omega)) (Or.inr (Nat.le_refl _)) e hwt
  -- `q = Ξ`
  have viaXi : ∀ m f', q = .Xi m f' → Lt q (.Psi ξ π γ) := fun m f' e => by
    subst e
    have hf'S := G.sub hqS (mem_subs_xi m f')
    refine P.xi_lt_t hqS lq.symm hqπ (fun _ u hu => ?_)
    have huS := G.sub hf'S (fr_spec hu).1
    have := size_le_of_mem_subs (fr_spec hu).1
    exact ihq u huS (by simp only [Tm.size]; omega) (G.trans huS hqS hpS (G.k2x m f' hqS u hu) h1)
  -- `q = Ψ` で目標が `t` 未満
  have viaT : ∀ τ' ρ' α, q = .Psi τ' ρ' α → Lt ρ' (.Psi ξ π γ) → Lt q (.Psi ξ π γ) :=
    fun τ' ρ' α e h => by
      subst e
      have hρ'S : ρ' ∈ S := G.sub hqS (by simp [subs, self_mem_subs])
      exact P.psi_lt_of_tgt hqS lq (P.not_lt_tgt hρ'S hqF.psi.tgt
        ((hAq ρ'.size (by simp only [Tm.size]; omega)).tgt hρ'S (Nat.le_refl _)) h)
  -- `q` の成分が `C(g, p)` に入れば `C(γ, t)` に入る（`g ≤ γ`）
  have mono : ∀ x g, x ∈ S → x.size < q.size → g ∈ S → Le g γ → inC x g p = true →
      inC x γ (.Psi ξ π γ) = true := fun x g hxS hxs hgS hgγ hin =>
    inC_mono x g p γ _ hin (fun v hv hvp => by
        have := size_le_of_mem_subs hv
        exact ihq v (G.sub hxS hv) (by omega) hvp)
      (fun v hv hvg => G.lt_of_lt_of_le (G.sub hxS hv) hgS P.γS hvg hgγ)
  rcases shape_FY3 hpF hpp bp with ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨τ, ρ, δ, rfl⟩
  · -- `p = Ω_x`
    have hx := G.sub hpS (mem_subs_om x)
    rcases P.tshape with ⟨c, rfl, rfl⟩ | ⟨hπOF, hOF⟩
    · have hcS := G.sub P.πS (mem_subs_om c)
      have hxc : Lt x c := (lt_om_psiY P.ht).mp h2
      rcases shape_FY4 hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨d, α, rfl⟩ |
        ⟨τ', ρ', α, rfl, hOFq⟩
      · have hy := G.sub hqS (mem_subs_om y)
        exact (lt_om_psiY P.ht).mpr (G.trans hy hx hcS ((G.lt_om_iffS hy hx).mp h1) hxc)
      · exact viaXi m' f' rfl
      · have hdS := G.sub hqS (mem_subs_psi_c _ d α)
        have hdc : Lt d c := G.lt_of_le_of_lt hdS hx hcS ((G.lt_psi_omS hqS hx).mp h1) hxc
        have hl : lev d = lev c := lq
        exact P.psi_lt_of_tgt hqS lq (fun h' => (psiOm_lt_om_iff hl).mp h' hdc)
      · exact P.below rfl hqS
          (G.trans hqS hx hcS ((G.lt_OF_omS hOFq hqS hx).mp h1) hxc)
    · have hxt : Lt x (.Psi ξ π γ) := (lt_om_OFG hOF).mp h2
      have hxs : x.size < (Tm.Om x).size := by simp only [Tm.size]; omega
      rcases shape_FY4 hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨d, α, rfl⟩ |
        ⟨τ', ρ', α, rfl, hOFq⟩
      · have hy := G.sub hqS (mem_subs_om y)
        exact (lt_om_OFG hOF).mpr (ihB x y hx hy (by simp only [Tm.size]; omega)
          (Or.inl (by omega)) (Or.inr (by simp only [Tm.size]; omega))
          ((G.lt_om_iffS hy hx).mp h1) hxt)
      · exact viaXi m' f' rfl
      · have hdS := G.sub hqS (mem_subs_psi_c _ d α)
        have hdt : Lt d (.Psi ξ π γ) := by
          rcases (G.lt_psi_omS hqS hx).mp h1 with e | e
          · rw [e]; exact hxt
          · exact ihB x d hx hdS (by simp only [Tm.size]; omega) (Or.inl (by omega))
              (Or.inr (by simp only [Tm.size]; omega)) e hxt
        exact viaT .zero (.Om d) α rfl ((lt_om_OFG hOF).mpr hdt)
      · exact ihB x _ hx hqS (by omega) (Or.inl (by omega)) (Or.inr (Nat.le_refl _))
          ((G.lt_OF_omS hOFq hqS hx).mp h1) hxt
  · -- `p = Ξ_m(f)`
    have hfS := G.sub hpS (mem_subs_xi m f)
    obtain ⟨-, hinf⟩ := P.xi_lt_t_inv hpS lp.symm h2
    rcases P.tshape with ⟨c, rfl, rfl⟩ | ⟨hπOF, hOF⟩
    · have hcS := G.sub P.πS (mem_subs_om c)
      exact P.below rfl hqS (G.trans hqS hpS hcS h1 ((G.lt_OF_omS (xiOF _ _) hpS hcS).mp hpπ))
    · have lp' : lev π = m := lp.symm
      by_cases hfγ : Lt f γ
      · have hinf' := hinf hfγ
        rcases shape_FY3 hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨τ', ρ', α, rfl⟩
        · have hy := G.sub hqS (mem_subs_om y)
          exact (lt_om_OFG hOF).mpr (ihq y hy (by simp only [Tm.size]; omega)
            ((lt_om_OFG (xiOF _ _)).mp h1))
        · exact viaXi m' f' rfl
        · have hρ'S : ρ' ∈ S := G.sub hqS (by simp [subs, self_mem_subs])
          rcases (lt_psi_xiY (π := ρ') (a := α) (lq.trans lp.symm)).mp h1 with h' | ⟨hfα, hn⟩
          · refine viaT τ' ρ' α rfl ?_
            rcases G.le_of_ne_gt hρ'S hpS h' with e | e
            · rw [e]; exact h2
            · exact ihq ρ' hρ'S (by simp only [Tm.size]; omega) e
          · have hαS := G.sub hqS (mem_subs_psi_a _ _ α)
            obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hpF.xi.2.2.2.2
              (fun v hv h' => G.trans (G.sub hfS hv) hfS hαS h' hfα) hn
            have hwS := G.sub hfS (fr_spec hw).1
            have := size_le_of_mem_subs (fr_spec hw).1
            have hin := fr_of_inC f
              (fun w' _ hn' => not_lt_of_not_lt_K (y := Tm.Psi ξ π γ) lp' hn') hinf' w hw
            have hwt := G.coll_psi P.ht P.πS w hwS hin
              (G.trans hwS hpS P.πS (G.k2x _ f hpS w hw) hpπ)
            exact viaLe w hwS (by simp only [Tm.size]; omega) hwt (G.le_of_not_lt hwS hqS hwn)
      · -- `γ ≤ f`：`p < π` から `p` 以上の `π` の前線の元
        have hγf : Le γ f := G.le_of_not_lt hfS P.γS hfγ
        obtain ⟨u, hu, hun⟩ := G.wit_xi_tgtS π P.πS hπOF P.hT hpS P.γS hpπ lp' P.ht.psi.Cpi hγf
        have huS := G.sub P.πS (fr_spec hu).1
        exact viaF u (Or.inr (Or.inl hu)) (G.le_of_not_lt huS hpS hun)
  · -- `p = Ψ^τ_ρ(δ)`
    have hρS : ρ ∈ S := G.sub hpS (by simp [subs, self_mem_subs])
    have hτS : τ ∈ S := G.sub hpS (by simp [subs, self_mem_subs])
    have hδS := G.sub hpS (mem_subs_psi_a _ _ δ)
    have hpP := hpF.psi
    have lp' : lev ρ = lev π := lp
    have hAρ : ABle S ξ π γ ρ.size := hAp ρ.size (by simp only [Tm.size]; omega)
    rcases (lt_psi_psiY lp' (P.ne_of_mem hpS)).mp h2 with
      h' | ⟨htρ, -, hc1 | ⟨hγδ, hn⟩ | ⟨he, e, hτξ, hinτ⟩ | ⟨hξτ, hn⟩⟩
    · -- 目標 `ρ` が `t` 未満
      have hρt := P.tgt_lt hρS hpP.tgt (hAρ.tgt hρS (Nat.le_refl _)) h'
      exact ihB ρ q hρS hqS (by simp only [Tm.size]; omega) (Or.inl (by simp only [Tm.size]; omega))
        (Or.inr (Nat.le_refl _)) (G.trans hqS hpS hρS h1 (lt_psi_targetY hpF)) hρt
    · -- (1)：`δ < γ`、`δ, τ, ρ ∈ C(γ, t)`
      obtain ⟨hδγ, hinδ, hinτ, hinρ⟩ := hc1
      have frP := P.fr_lt_c1 hpS lp' htρ hinδ hinτ hinρ hpπ ihA hAρ
      rcases shape_FY3 hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨τ', ρ', α, rfl⟩
      · have hy := G.sub hqS (mem_subs_om y)
        rcases hpF.shape with ⟨d, rfl, rfl⟩ | hshp
        · have hyd : Lt y d := (lt_om_psiY hpF).mp h1
          have hdS := G.sub hρS (mem_subs_om d)
          rcases P.tshape with ⟨c, rfl, rfl⟩ | ⟨hπOF, hOF⟩
          · have hcS := G.sub P.πS (mem_subs_om c)
            exact (lt_om_psiY P.ht).mpr
              (G.lt_of_lt_of_le hy hdS hcS hyd ((G.lt_psi_omS hpS hcS).mp hpπ))
          · rw [inC_om] at hinρ
            have hdt := G.coll_psi P.ht P.πS d hdS hinρ
              (G.trans hdS hpS P.πS (G.cx d δ hpS) hpπ)
            exact (lt_om_OFG hOF).mpr (ihB d y hdS hy
              (by simp only [Tm.size] at lq ⊢; omega) (Or.inl (by simp only [Tm.size]; omega))
              (Or.inr (by simp only [Tm.size]; omega)) hyd hdt)
        · have hOFp := IsOF.psi hpF (notOm_of_shape hshp)
          have hyp : Lt y (.Psi τ ρ δ) := (lt_om_OFG hOFp).mp h1
          rcases P.tshape with ⟨c, rfl, rfl⟩ | ⟨hπOF, hOF⟩
          · have hcS := G.sub P.πS (mem_subs_om c)
            exact (lt_om_psiY P.ht).mpr (G.trans hy hpS hcS hyp
              ((G.lt_OF_omS hOFp hpS hcS).mp hpπ))
          · exact (lt_om_OFG hOF).mpr (ihq y hy (by simp only [Tm.size]; omega) hyp)
      · exact viaXi m' f' rfl
      · have hρ'S : ρ' ∈ S := G.sub hqS (by simp [subs, self_mem_subs])
        have hτ'S : τ' ∈ S := G.sub hqS (by simp [subs, self_mem_subs])
        have hαS := G.sub hqS (mem_subs_psi_a _ _ α)
        have lq' : lev ρ' = lev ρ := lq.trans lp.symm
        by_cases htρ'' : ¬ Lt (.Psi ξ π γ) ρ'
        · exact P.psi_lt_of_tgt hqS lq htρ''
        have htρ' := Decidable.of_not_not htρ''
        rcases (lt_psi_psiY lq' h1.ne).mp h1 with
          h'' | ⟨-, -, ⟨hαδ, hinα, hinτ', hinρ'⟩ | ⟨hδα, hn'⟩ | ⟨he', e', hτ'τ, hinτ'⟩ |
            ⟨hττ', hn'⟩⟩
        · refine viaT τ' ρ' α rfl ?_
          rcases G.le_of_not_lt hpS hρ'S h'' with e | e
          · rw [e]; exact h2
          · exact ihq ρ' hρ'S (by simp only [Tm.size]; omega) e
        · -- (1)(1)
          refine P.psi_lt_of_c1 hqS lq htρ' hqπ (G.trans hαS hδS P.γS hαδ hδγ)
            (mono α δ hαS (by simp only [Tm.size]; omega) hδS (Or.inr hδγ) hinα)
            (mono τ' δ hτ'S (by simp only [Tm.size]; omega) hδS (Or.inr hδγ) hinτ')
            (mono ρ' δ hρ'S (by simp only [Tm.size]; omega) hδS (Or.inr hδγ) hinρ')
        · -- (1)(2)：`p` の前線の証人
          have hδα' : Le δ α := G.le_of_ne_gt hδS hαS hδα
          have hg : ∀ x, x ∈ S → ∀ v, v ∈ subs x → Lt v δ → Lt v α := fun x hx v hv h =>
            G.lt_of_lt_of_le (G.sub hx hv) hδS hαS h hδα'
          have hw : ∃ w, (w ∈ fr ρ δ ∨ w ∈ fr ρ ρ ∨ w ∈ fr ρ τ) ∧ ¬ Lt w (.Psi τ' ρ' α) := by
            cases e1 : inC δ α (Tm.Psi τ' ρ' α)
            · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hpP.Ca (hg δ hδS) e1
              exact ⟨w, Or.inl hw, hwn⟩
            · cases e2 : inC τ α (Tm.Psi τ' ρ' α)
              · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hpP.Cxi (hg τ hτS) e2
                exact ⟨w, Or.inr (Or.inr hw), hwn⟩
              · cases e3 : inC ρ α (Tm.Psi τ' ρ' α)
                · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hpP.Cpi (hg ρ hρS) e3
                  exact ⟨w, Or.inr (Or.inl hw), hwn⟩
                · exact absurd ⟨e1, e2, e3⟩ hn'
          obtain ⟨w, hw, hwn⟩ := hw
          have hwS : w ∈ S := by
            rcases hw with hw | hw | hw
            · exact G.sub hδS (fr_spec hw).1
            · exact G.sub hρS (fr_spec hw).1
            · exact G.sub hτS (fr_spec hw).1
          have hws : w.size < (Tm.Psi τ ρ δ).size := by
            rcases hw with hw | hw | hw <;>
              (have := size_le_of_mem_subs (fr_spec hw).1; simp only [Tm.size]; omega)
          exact viaLe w hwS hws (frP w hw) (G.le_of_not_lt hwS hqS hwn)
        · -- (1)(3)：`q = Ψ^{τ'}_ρ(δ)`、`τ' < τ`
          have hαδ := G.eq hαS hδS he'
          subst hαδ e'
          exact P.psi_lt_of_c1 hqS lq htρ' hqπ hδγ hinδ
            (mono τ' α hτ'S (by simp only [Tm.size]; omega) hαS (Or.inr hδγ) hinτ') hinρ
        · -- (1)(4)：`τ < τ'` で `τ ∉ C(τ', q)`
          obtain ⟨w, hw, hwn⟩ := wit_of_not_inC (G.miS hpS)
            (fun v hv h => G.trans (G.sub hτS hv) hτS hτ'S h hττ') hn'
          have hwS := G.sub hτS (fr_spec hw).1
          have := size_le_of_mem_subs (fr_spec hw).1
          exact viaLe w hwS (by simp only [Tm.size]; omega) (frP w (Or.inr (Or.inr hw)))
            (G.le_of_not_lt hwS hqS hwn)
    · -- (2)：前線の証人
      obtain ⟨w, hw, hwn⟩ := P.wit (G.le_of_ne_gt P.γS hδS hγδ) hδS hn
      exact viaF w hw (G.le_of_not_lt (P.F_spec hw).1 hpS hwn)
    · -- (3)：`p = Ψ^τ_π(γ)`、`τ < ξ`、`τ ∈ C(γ, t)`
      have hδγ := G.eq hδS P.γS he
      subst hδγ e
      have frP3 := P.fr_lt_of_inC hτS hinτ
      rcases shape_FY3 hqF hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨τ', ρ', α, rfl⟩
      · have hy := G.sub hqS (mem_subs_om y)
        rcases P.tshape with ⟨c, rfl, rfl⟩ | ⟨-, hOF⟩
        · exact absurd hτξ (not_lt_zero _)
        · have hOFp : IsOF (.Psi τ π δ) := by
            rcases hOF with ⟨n, a, e⟩ | ⟨ξ', π', a', e, hw', hπ'⟩
            · cases e
            · cases e; exact IsOF.psi hpF hπ'
          exact (lt_om_OFG hOF).mpr (ihq y hy (by simp only [Tm.size]; omega)
            ((lt_om_OFG hOFp).mp h1))
      · exact viaXi m' f' rfl
      · have hρ'S : ρ' ∈ S := G.sub hqS (by simp [subs, self_mem_subs])
        have hτ'S : τ' ∈ S := G.sub hqS (by simp [subs, self_mem_subs])
        have hαS := G.sub hqS (mem_subs_psi_a _ _ α)
        have lq' : lev ρ' = lev π := lq
        by_cases htρ'' : ¬ Lt (.Psi ξ π δ) ρ'
        · exact P.psi_lt_of_tgt hqS lq htρ''
        have htρ' := Decidable.of_not_not htρ''
        rcases (lt_psi_psiY lq' h1.ne).mp h1 with
          h'' | ⟨-, -, ⟨hαδ, hinα, hinτ', hinρ'⟩ | ⟨hδα, hn'⟩ | ⟨he', e', hτ'τ, hinτ'⟩ |
            ⟨hττ', hn'⟩⟩
        · refine viaT τ' ρ' α rfl ?_
          rcases G.le_of_not_lt hpS hρ'S h'' with e | e
          · rw [e]; exact h2
          · exact ihq ρ' hρ'S (by simp only [Tm.size]; omega) e
        · -- (3)(1)
          exact P.psi_lt_of_c1 hqS lq htρ' hqπ hαδ
            (mono α δ hαS (by simp only [Tm.size]; omega) P.γS (Or.inl rfl) hinα)
            (mono τ' δ hτ'S (by simp only [Tm.size]; omega) P.γS (Or.inl rfl) hinτ')
            (mono ρ' δ hρ'S (by simp only [Tm.size]; omega) P.γS (Or.inl rfl) hinρ')
        · -- (3)(2)：`p` の前線の証人（`γ`・`π` は `t` と共通、`τ` は `C(γ, t)` に入る）
          have hδα' : Le δ α := G.le_of_ne_gt P.γS hαS hδα
          have hg : ∀ x, x ∈ S → ∀ v, v ∈ subs x → Lt v δ → Lt v α := fun x hx v hv h =>
            G.lt_of_lt_of_le (G.sub hx hv) P.γS hαS h hδα'
          cases e1 : inC δ α (Tm.Psi τ' ρ' α)
          · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hpP.Ca (hg δ P.γS) e1
            have hwS := G.sub P.γS (fr_spec hw).1
            exact P.lemA hqS ⟨w, Or.inl hw, G.le_of_not_lt hwS hqS hwn⟩
          · cases e2 : inC τ α (Tm.Psi τ' ρ' α)
            · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hpP.Cxi (hg τ hτS) e2
              have hwS := G.sub hτS (fr_spec hw).1
              have := size_le_of_mem_subs (fr_spec hw).1
              exact viaLe w hwS (by simp only [Tm.size]; omega) (frP3 w hw)
                (G.le_of_not_lt hwS hqS hwn)
            · cases e3 : inC π α (Tm.Psi τ' ρ' α)
              · obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hpP.Cpi (hg π P.πS) e3
                have hwS := G.sub P.πS (fr_spec hw).1
                exact P.lemA hqS ⟨w, Or.inr (Or.inl hw), G.le_of_not_lt hwS hqS hwn⟩
              · exact absurd ⟨e1, e2, e3⟩ hn'
        · -- (3)(3)：`q = Ψ^{τ'}_π(γ)`、`τ' < τ < ξ`
          have hαδ := G.eq hαS P.γS he'
          subst hαδ e'
          exact P.psi_lt_of_c3 hqS (cmp_self _) (G.trans hτ'S hτS P.ξS hτ'τ hτξ)
            (mono τ' α hτ'S (by simp only [Tm.size]; omega) P.γS (Or.inl rfl) hinτ')
        · -- (3)(4)：`τ < τ'` で `τ ∉ C(τ', q)`
          obtain ⟨w, hw, hwn⟩ := wit_of_not_inC (G.miS hpS)
            (fun v hv h => G.trans (G.sub hτS hv) hτS hτ'S h hττ') hn'
          have hwS := G.sub hτS (fr_spec hw).1
          have := size_le_of_mem_subs (fr_spec hw).1
          exact viaLe w hwS (by simp only [Tm.size]; omega) (frP3 w hw)
            (G.le_of_not_lt hwS hqS hwn)
    · -- (4)：`ξ < τ` で `ξ ∉ C(τ, p)`
      obtain ⟨w, hw, hwn⟩ := P.wit4 hτS hξτ hn
      exact viaF w (Or.inr (Or.inr hw)) (G.le_of_not_lt (P.F_spec (Or.inr (Or.inr hw))).1 hpS hwn)

/-- `Ψ` どうしの反対称性（`s` より小さい元との反対称性と、`s` 以下の組の切断性の下で） -/
theorem psi_swap_le {σ κ β : Tm} (hs : Tm.Psi σ κ β ∈ S) (hl : lev π = lev κ)
    (hA : ABle S ξ π γ ((Tm.Psi σ κ β).size - 1)) (hcut : CutLe S (.Psi ξ π γ) (Tm.Psi σ κ β).size) :
    cmpPsi (.Psi σ κ β) (.Psi ξ π γ) = (cmpPsi (.Psi ξ π γ) (.Psi σ κ β)).swap := by
  have G := P.G
  have hsF := G.nf _ hs
  have hsP := hsF.psi
  have hκS : κ ∈ S := G.sub hs (by simp [subs, self_mem_subs])
  have hσS : σ ∈ S := G.sub hs (by simp [subs, self_mem_subs])
  have hβS := G.sub hs (mem_subs_psi_a _ _ β)
  have hκT := hsP.tgt
  have hAκ : ∀ σ' κ'' β', κ = .Psi σ' κ'' β' → AntiT (.Psi ξ π γ) κ :=
    fun _ _ _ _ => hA κ hκS (by simp only [Tm.size]; omega)
  have hne : Tm.Psi ξ π γ ≠ .Psi σ κ β := fun e => P.ne_of_mem hs e.symm
  have hne' : Tm.Psi σ κ β ≠ .Psi ξ π γ := fun e => hne e.symm
  have Ats := lt_psi_psiY hl hne
  have Ast := lt_psi_psiY hl.symm hne'
  have caseA : ¬ Lt (.Psi σ κ β) π → ¬ Lt (.Psi ξ π γ) κ → False := fun h1 h2 => by
    have hπκ := G.lt_of_le_of_lt P.πS hs hκS (G.le_of_not_lt hs P.πS h1) (lt_psi_targetY hsF)
    exact G.asymm P.πS hκS hπκ (P.tbge hκS hκT.principal h2)
  -- `s` の前線の証人 `u < s`（`u < t` でない）があれば、`s < t` と切断性で矛盾
  have cutW : Lt (.Psi σ κ β) (.Psi ξ π γ) → ∀ u, u ∈ S → Lt u (.Psi σ κ β) →
      u.size < (Tm.Psi σ κ β).size → ¬ Lt u (.Psi ξ π γ) → False :=
    fun hst u hu hus hus' hun => hun (hcut _ u hs hu (Nat.le_refl _) (Nat.le_of_lt hus') hus hst)
  -- `t < s` の (2) の証人
  have W2t : Le β γ → ¬ (inC β γ (.Psi ξ π γ) = true ∧ inC σ γ (.Psi ξ π γ) = true ∧
      inC κ γ (.Psi ξ π γ) = true) →
      ∃ u, u ∈ S ∧ Lt u (.Psi σ κ β) ∧ u.size < (Tm.Psi σ κ β).size ∧
        ¬ Lt u (.Psi ξ π γ) := by
    intro hβγ hn
    have hg : ∀ x, x ∈ S → ∀ v, v ∈ subs x → Lt v β → Lt v γ := fun x hx v hv h =>
      G.lt_of_lt_of_le (G.sub hx hv) hβS P.γS h hβγ
    cases e1 : inC β γ (Tm.Psi ξ π γ)
    · obtain ⟨u, hu, hun⟩ := wit_of_not_inC hsP.Ca (hg β hβS) e1
      have := size_le_of_mem_subs (fr_spec hu).1
      exact ⟨u, G.sub hβS (fr_spec hu).1, G.k2 _ _ _ hs u hu, by simp only [Tm.size]; omega, hun⟩
    · cases e2 : inC σ γ (Tm.Psi ξ π γ)
      · obtain ⟨u, hu, hun⟩ := wit_of_not_inC hsP.Cxi (hg σ hσS) e2
        have := size_le_of_mem_subs (fr_spec hu).1
        exact ⟨u, G.sub hσS (fr_spec hu).1, G.k2s _ _ _ hs u hu, by simp only [Tm.size]; omega,
          hun⟩
      · cases e3 : inC κ γ (Tm.Psi ξ π γ)
        · obtain ⟨u, hu, hun⟩ := wit_of_not_inC hsP.Cpi (hg κ hκS) e3
          have := size_le_of_mem_subs (fr_spec hu).1
          exact ⟨u, G.sub hκS (fr_spec hu).1, G.k2t _ _ _ hs u hu, by simp only [Tm.size]; omega,
            hun⟩
        · exact absurd ⟨e1, e2, e3⟩ hn
  -- `t < s` の (4) の証人
  have W4t : Lt σ ξ → inC σ ξ (.Psi ξ π γ) = false →
      ∃ u, u ∈ S ∧ Lt u (.Psi σ κ β) ∧ u.size < (Tm.Psi σ κ β).size ∧
        ¬ Lt u (.Psi ξ π γ) := by
    intro hσξ hn
    obtain ⟨u, hu, hun⟩ := wit_of_not_inC (G.miS hs)
      (fun v hv h => G.trans (G.sub hσS hv) hσS P.ξS h hσξ) hn
    have := size_le_of_mem_subs (fr_spec hu).1
    exact ⟨u, G.sub hσS (fr_spec hu).1, G.k2s _ _ _ hs u hu, by simp only [Tm.size]; omega, hun⟩
  -- `t < κ` なら `ξ` の前線（`π` について）は `κ` 未満（補題 A と `κ` との反対称性）
  have frξκ : Lt (.Psi ξ π γ) κ → ∀ w, w ∈ fr π ξ → Lt w κ := fun htκ w hw => by
    have hwS := G.sub P.ξS (fr_spec hw).1
    rcases G.tri hwS hκS with h | e | h
    · exact h
    · subst e
      exact absurd htκ (P.not_lt_tgt hwS hκT hAκ (P.k2s w hw))
    · exact absurd htκ (P.not_lt_tgt hκS hκT hAκ
        (P.lemA hκS ⟨w, Or.inr (Or.inr hw), Or.inr h⟩))
  -- `ξ ∈ C(β, s)` と `s < t` の (4) は両立しない
  have c4s_contra : Lt (.Psi σ κ β) π → Lt (.Psi ξ π γ) κ → inC ξ β (.Psi σ κ β) = true →
      Lt ξ σ → inC ξ σ (.Psi σ κ β) = false → False := by
    intro hsπ htκ hinξ hξσ hn
    have hd : ∀ v, v ∈ subs ξ → ¬ Lt v π → ¬ Lt v (.Psi σ κ β) := fun v hv hvπ hvs =>
      hvπ (G.trans (G.sub P.ξS hv) hs P.πS hvs hsπ)
    rw [inC_of_fr ξ P.mi (fun v hv h => G.trans (G.sub P.ξS hv) P.ξS hσS h hξσ)
      (fun w hw => inC_of_lt_node (fr_node hw)
        (G.coll_psiS hs w (G.sub P.ξS (fr_spec hw).1) (fr_of_inC ξ hd hinξ w hw)
          (frξκ htκ w hw)))] at hn
    cases hn
  -- `s < t` と `t < s` は両立しない
  have asym : Lt (.Psi ξ π γ) (.Psi σ κ β) → Lt (.Psi σ κ β) (.Psi ξ π γ) → False := by
    intro h h'
    rcases Ats.mp h with a1 | ⟨hsπ, htκ, hc⟩ <;> rcases Ast.mp h' with b1 | ⟨htκ', hsπ', hc'⟩
    · exact caseA a1 b1
    · exact a1 hsπ'
    · exact b1 htκ
    · rcases hc with ⟨hγβ, hinγ, hinξ, hinπ⟩ | ⟨hβγ, hn⟩ | ⟨he, e, hξσ, hinξ⟩ | ⟨hσξ, hn⟩
      · rcases hc' with ⟨hβγ', -⟩ | ⟨-, hn'⟩ | ⟨he', -⟩ | ⟨hξσ', hn'⟩
        · exact G.asymm P.γS hβS hγβ hβγ'
        · exact hn' ⟨hinγ, hinξ, hinπ⟩
        · have := G.eq hβS P.γS he'
          subst this
          exact Lt.irrefl _ hγβ
        · exact c4s_contra hsπ htκ hinξ hξσ' hn'
      · obtain ⟨u, hu, hus, hus', hun⟩ := W2t (G.le_of_ne_gt hβS P.γS hβγ) hn
        exact cutW h' u hu hus hus' hun
      · have hγβ := G.eq P.γS hβS he
        subst hγβ e
        rcases hc' with ⟨hβγ', -⟩ | ⟨-, hn'⟩ | ⟨-, -, hσξ', -⟩ | ⟨hξσ', hn'⟩
        · exact Lt.irrefl _ hβγ'
        · exact hn' ⟨G.inC_argS hs, hinξ, G.inC_tgtS hs⟩
        · exact G.asymm P.ξS hσS hξσ hσξ'
        · exact c4s_contra hsπ htκ hinξ hξσ' hn'
      · obtain ⟨u, hu, hus, hus', hun⟩ := W4t hσξ hn
        exact cutW h' u hu hus hus' hun
  -- どちらかは成り立つ
  have tot : Lt (.Psi ξ π γ) (.Psi σ κ β) ∨ Lt (.Psi σ κ β) (.Psi ξ π γ) := by
    by_cases h1 : Lt (.Psi σ κ β) π
    · by_cases h2 : Lt (.Psi ξ π γ) κ
      · rcases G.tri P.γS hβS with e | e | e
        · by_cases hin : inC γ β (.Psi σ κ β) = true ∧ inC ξ β (.Psi σ κ β) = true ∧
              inC π β (.Psi σ κ β) = true
          · exact Or.inl (Ats.mpr (Or.inr ⟨h1, h2, Or.inl ⟨e, hin.1, hin.2.1, hin.2.2⟩⟩))
          · exact Or.inr (Ast.mpr (Or.inr ⟨h2, h1, Or.inr (Or.inl
              ⟨by unfold Lt at e; rw [e]; decide, hin⟩)⟩))
        · subst e
          by_cases hA' : inC γ γ (.Psi ξ π γ) = true ∧ inC σ γ (.Psi ξ π γ) = true ∧
              inC κ γ (.Psi ξ π γ) = true
          · by_cases hB : inC γ γ (.Psi σ κ γ) = true ∧ inC ξ γ (.Psi σ κ γ) = true ∧
                inC π γ (.Psi σ κ γ) = true
            · rcases G.tri P.πS hκS with e | e | e
              · exact absurd (G.coll_psiS hs π P.πS hB.2.2 e) (G.asymm hs P.πS h1)
              · subst e
                rcases G.tri P.ξS hσS with e' | e' | e'
                · exact Or.inl (Ats.mpr (Or.inr ⟨h1, h2, Or.inr (Or.inr (Or.inl
                    ⟨cmp_self _, rfl, e', hB.2.1⟩))⟩))
                · subst e'; exact absurd rfl hne
                · exact Or.inr (Ast.mpr (Or.inr ⟨h2, h1, Or.inr (Or.inr (Or.inl
                    ⟨cmp_self _, rfl, e', hA'.2.1⟩))⟩))
              · exact absurd h2 (P.not_lt_tgt hκS hκT hAκ
                  (G.coll_psi P.ht P.πS κ hκS hA'.2.2 e))
            · exact Or.inr (Ast.mpr (Or.inr ⟨h2, h1, Or.inr (Or.inl
                ⟨by rw [cmp_self]; decide, hB⟩)⟩))
          · exact Or.inl (Ats.mpr (Or.inr ⟨h1, h2, Or.inr (Or.inl
              ⟨by rw [cmp_self]; decide, hA'⟩)⟩))
        · by_cases hin : inC β γ (.Psi ξ π γ) = true ∧ inC σ γ (.Psi ξ π γ) = true ∧
              inC κ γ (.Psi ξ π γ) = true
          · exact Or.inr (Ast.mpr (Or.inr ⟨h2, h1, Or.inl ⟨e, hin.1, hin.2.1, hin.2.2⟩⟩))
          · exact Or.inl (Ats.mpr (Or.inr ⟨h1, h2, Or.inr (Or.inl
              ⟨by unfold Lt at e; rw [e]; decide, hin⟩)⟩))
      · exact Or.inr (Ast.mpr (Or.inl h2))
    · by_cases h2 : Lt (.Psi ξ π γ) κ
      · exact Or.inl (Ats.mpr (Or.inl h1))
      · exact absurd (caseA h1 h2) id
  have ne := P.G.ne_new P.ht P.hsub P.htS _ hs
  have key := swap_of_iff ne.2 ne.1 ⟨fun h h' => asym h h', fun h => tot.resolve_right h⟩
  rw [cmp_principal rfl rfl, cmp_principal rfl rfl, cmpP_psi_psi hl, cmpP_psi_psi hl.symm] at key
  exact key

/-- 大きさについての帰納法：`t` は大きさ `N` 以下の全ての元と反対称 -/
theorem anti_le : ∀ N, ABle S ξ π γ N := by
  intro N
  induction N with
  | zero => intro z _ h; exact absurd h (by have := Tm.size_pos z; omega)
  | succ N ih =>
    refine P.G.anti_new_le P.ht P.hsub P.htS (N + 1) (fun _ _ _ σ κ β e hs hsN hl => ?_)
    cases e
    have hA : ABle S ξ π γ ((Tm.Psi σ κ β).size - 1) := fun z hz hzs => ih z hz (by omega)
    exact P.psi_swap_le hs hl hA (P.cut_le _ hA)

/-- `t = Ψ^ξ_π(γ)` は `S` の全ての元と反対称 -/
theorem anti : ∀ z, z ∈ S → AntiT (.Psi ξ π γ) z :=
  fun z hz => P.anti_le z.size z hz (Nat.le_refl _)

/-- `t = Ψ^ξ_π(γ)` は `S` を切断する -/
theorem cut : CutT S (.Psi ξ π γ) := fun a b ha hb =>
  P.cut_le (max a.size b.size) (fun z hz _ => P.anti z hz) a b ha hb
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)

end PsiCtxY

end RTKA.W
