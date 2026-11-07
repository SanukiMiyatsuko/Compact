import Compact.FS.Big

/-! 対角化：加数 `R` の共終数が目標以上の正則項 `σ`（`K_m` でない）のとき。

塔 `γ_0 = 0`、`γ_{k+1} = Ψ^ξ_σ(E_k)`、`E_k = pre ⊕ x_k`。`x_0 = R[0] # Q`、`x_k = R[γ_k]`（`k ≥ 1`）。
`Q` は `σ` が目標そのもののときの種（0 番目の近似にだけ入る）、それ以外は `0`。`ξ` は Mahlo 添字（目標そのものへの
対角化で `Ψ^p_π`、それ以外は `0`）。

* 仮想的な崩壊 `Ψ^0_σ(X)` についての `Approx1` を `k` の帰納法で示す（`DiagHyp.tower`）。`σ` の引数の下限は、`σ` が `R` の部分項なので
  隙間から出る（`DiagHyp.r_lt`）。
* 塔は単調（`lo` により `γ_k` は `C(E_k, γ_{k+1})` に入る）。
* `gamT_inC`：`R`・`σ`・`pre`・`Q` が `C(g, d)` に入り、`E_j < g` なら塔は `C(g, d)` に入る。
* 種を外に足す型：`t[n] = Ψ^{ξ'}_π(pre ⊕ ((c + x_n) # P))`（`DiagHyp.fam_out`）。 -/

namespace RTKA.Fund

open Tm W

/-- 対角化の塔 -/
def gamT (ξ σ : Tm) (pre : List Tm) (r : SeqD) (G Q : Tm) : Nat → Tm
  | 0 => G
  | 1 => .Psi ξ σ (approx pre .zero (nsum (r.big G) Q))
  | k + 2 => .Psi ξ σ (approx pre .zero (r.big (gamT ξ σ pre r G Q (k + 1))))

/-- 塔の各段の近似の `R` の部分 -/
def xT (ξ σ : Tm) (pre : List Tm) (r : SeqD) (G Q : Tm) : Nat → Tm
  | 0 => nsum (r.big G) Q
  | k + 1 => r.big (gamT ξ σ pre r G Q (k + 1))

theorem gamT_succ (ξ σ : Tm) (pre : List Tm) (r : SeqD) (G Q : Tm) (k : Nat) :
    gamT ξ σ pre r G Q (k + 1) = .Psi ξ σ (approx pre .zero (xT ξ σ pre r G Q k)) := by
  cases k <;> rfl

/-- 対角化の仮定 -/
structure DiagHyp (ξ σ X G Q : Tm) (pre rest : List Tm) (R : Tm) (r : SeqD) : Prop where
  ht : WNF (.Psi .zero σ X)
  hsum : summands X = pre ++ R :: rest
  hRU : BigUB R σ r
  hRG : BigGap R σ r
  hGF : WNF G
  hGσ : Lt G σ
  hGs : ¬ isSucc G = true
  hQF : WNF Q
  hQR : Lt Q R
  hQσ : Lt Q σ
  hI : IdxHyp ξ σ X
  hξ : Le ξ (ofSummands pre)

theorem approx_pos {pre : List Tm} {P x : Tm} (hpre : WNF (ofSummands pre)) (hx : WNF x) (hP : WNF P)
    (hx0 : x ≠ .zero) : Lt .zero (approx pre P x) := by
  have hy := wnf_nsum hx hP
  have h1 : Le x (approx pre P x) :=
    le_transY hx hy (wnf_oadd hpre hy) (le_nsum_left hx hP) (le_oadd_right hpre hy)
  exact lt_of_lt_of_leY WNF.zero hx (wnf_oadd hpre hy) (zero_lt hx0) h1

theorem mem_subs_arg {σ q : Tm} (h : argR? σ = some q) : q ∈ subs σ := by
  cases σ with
  | Xi n p =>
    simp only [argR?, Option.some.injEq] at h
    subst h
    exact mem_subs_xi _ _
  | Psi ζ κ b =>
    simp only [argR?, Option.some.injEq] at h
    subst h
    exact subs_psi_a (self_mem_subs _)
  | _ => simp [argR?] at h

theorem size_arg_lt {σ q : Tm} (h : argR? σ = some q) : q.size < σ.size := by
  cases σ with
  | Xi n p =>
    simp only [argR?, Option.some.injEq] at h
    subst h
    simp only [Tm.size]
    omega
  | Psi ζ κ b =>
    simp only [argR?, Option.some.injEq] at h
    subst h
    simp only [Tm.size]
    omega
  | _ => simp [argR?] at h

/-- 加数 `R` の部分項 `σ` の引数の下限 `q` が `X` 未満なら `q + 1 < X`（大きさの議論） -/
theorem succ_lt_of_sub {X R σ q : Tm} (hX : WNF X) (hRm : R ∈ summands X) (hσs : σ ∈ subs R)
    (hq : argR? σ = some q) (hqF : WNF q) (hqX : Lt q X) : Lt (succT q) X := by
  refine (succT_le_of_lt hqF hX hqX).resolve_left fun e => ?_
  have hm := hRm
  rw [← e, summands_succT] at hm
  have h2 := Nat.lt_of_lt_of_le (size_arg_lt hq) (size_le_of_mem_subs hσs)
  rcases List.mem_append.mp hm with h | h
  · have h1 := size_le_of_mem_subs (mem_subs_of_mem_summands h)
    omega
  · have e1 : R = .one := List.mem_singleton.mp h
    rw [e1] at hσs
    simp only [subs, List.mem_singleton] at hσs
    rw [hσs] at hq
    simp [argR?] at hq

namespace DiagHyp

variable {ξ σ X G Q : Tm} {pre rest : List Tm} {R : Tm} {r : SeqD}

theorem hX (H : DiagHyp ξ σ X G Q pre rest R r) : WNF X := H.ht.psi.aF
theorem hσF (H : DiagHyp ξ σ X G Q pre rest R r) : WNF σ := H.ht.psi.piF

theorem hN (H : DiagHyp ξ σ X G Q pre rest R r) : NFL (pre ++ R :: rest) := H.hsum ▸ nfl_summands H.hX

theorem hXeq (H : DiagHyp ξ σ X G Q pre rest R r) : X = ofSummands (pre ++ R :: rest) := by
  rw [← H.hsum, ofSummands_summands X H.hX]

theorem hRm (H : DiagHyp ξ σ X G Q pre rest R r) : R ∈ summands X := by
  rw [H.hsum]
  exact List.mem_append_right _ List.mem_cons_self

theorem hRF (H : DiagHyp ξ σ X G Q pre rest R r) : WNF R :=
  (H.hN.1 R (List.mem_append_right _ List.mem_cons_self)).1

theorem hRp (H : DiagHyp ξ σ X G Q pre rest R r) : isPrincipal R = true :=
  (H.hN.1 R (List.mem_append_right _ List.mem_cons_self)).2

theorem hpreF (H : DiagHyp ξ σ X G Q pre rest R r) : WNF (ofSummands pre) :=
  wnf_ofSummands (nfl_append_left H.hN)

theorem hR0 (H : DiagHyp ξ σ X G Q pre rest R r) : Lt .zero R :=
  zero_lt (by
    intro e
    have := H.hRp
    rw [e] at this
    cases this)

theorem hσ0 (H : DiagHyp ξ σ X G Q pre rest R r) : Lt .zero σ := zero_lt H.ht.psi.tgt.ne_zero

theorem ht0 (H : DiagHyp ξ σ X G Q pre rest R r) : Lt .zero (.Psi .zero σ X) :=
  zero_lt (by intro e; cases e)

theorem hX0 (H : DiagHyp ξ σ X G Q pre rest R r) : Lt .zero X :=
  zero_lt (by
    intro e
    have := H.hRm
    rw [e] at this
    cases this)

theorem hRσ (H : DiagHyp ξ σ X G Q pre rest R r) : inC R X σ = true :=
  inC_of_mem_summands H.hX H.ht.psi.Ca H.hRm

theorem hRt (H : DiagHyp ξ σ X G Q pre rest R r) : inC R X (.Psi .zero σ X) = true :=
  inC_of_fr_lt H.hRF H.hσF H.ht H.hX H.hX H.hRσ (Or.inr (lt_psi_targetY H.ht)) (Or.inl rfl)
    fun w hw => FWOrder.k2 H.ht w ((mem_fr_iff H.hX).mpr ⟨R, H.hRm, hw⟩)

theorem h0F (H : DiagHyp ξ σ X G Q pre rest R r) : WNF (r.big G) :=
  (H.hRU.good.1 G H.hGF H.hGσ).1

theorem h0R (H : DiagHyp ξ σ X G Q pre rest R r) : Lt (r.big G) R :=
  (H.hRU.good.1 G H.hGF H.hGσ).2

theorem hq_size (H : DiagHyp ξ σ X G Q pre rest R r) {q : Tm} (hq : argR? σ = some q) :
    q.size < R.size :=
  Nat.lt_of_lt_of_le (size_arg_lt hq) (size_le_of_mem_subs H.hRU.hσs)

/-- `σ` の引数の下限 `q` について `q + 1 < X`（大きさの議論） -/
theorem hsq (H : DiagHyp ξ σ X G Q pre rest R r) {q : Tm} (hq : argR? σ = some q) :
    Lt (succT q) X :=
  succ_lt_of_sub H.hX H.hRm H.hRU.hσs hq (wnf_of_argR H.hσF hq) (arg_lt_of_psi H.ht hq)

theorem okX (H : DiagHyp ξ σ X G Q pre rest R r) (d : Tm) : BigOK σ X d :=
  Or.inr fun _ hq _ => H.hsq hq

/-- `σ` の引数の下限は隙間から出る -/
theorem r_lt (H : DiagHyp ξ σ X G Q pre rest R r) {x : Tm} (hx : WNF x) (hxR : Lt x R)
    (hx0 : x = .zero → ∀ v, v ∈ subs R → v = R)
    (hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v x) {q : Tm} (hq : argR? σ = some q) :
    Lt q (approx pre .zero x) := by
  have hqs : q ∈ subs R := subs_trans H.hRU.hσs (mem_subs_arg hq)
  have hne : q ≠ R := ne_of_size_lt (H.hq_size hq)
  have hy := wnf_nsum hx WNF.zero
  have hyR := nsum_lt_prin hx WNF.zero H.hRp hxR H.hR0
  have hy0 : nsum x .zero ≠ .zero := by
    rw [nsum_zero _ hx]
    exact fun e => hne (hx0 e q hqs)
  exact lt_approx_of_gap H.hN hy hy0 hyR hx (le_nsum_left hx WNF.zero) hgap hqs hne
    (wnf_of_argR H.hσF hq) (by rw [← H.hXeq]; exact arg_lt_of_psi H.ht hq)

theorem hξA (H : DiagHyp ξ σ X G Q pre rest R r) {y : Tm} (hy : WNF y) :
    Le ξ (oadd (ofSummands pre) y) :=
  le_transY H.hI.hF H.hpreF (wnf_oadd H.hpreF hy) H.hξ (le_oadd_left H.hpreF hy)

/-- 添字 `η` の項の近似の仮定 -/
theorem approx_of (H : DiagHyp ξ σ X G Q pre rest R r) {η : Tm} (hη : WNF η) (hησ : Lt η σ) :
    Approx1 ξ σ X .zero pre rest R (r.big η) := by
  have hxF := (H.hRU.good.1 η hη hησ).1
  have hxR := (H.hRU.good.1 η hη hησ).2
  have hr : ∀ q, argR? σ = some q → Lt q (approx pre .zero (r.big η)) := fun q hq =>
    H.r_lt hxF hxR (fun e => H.hRU.pos η hη hησ e) (H.hRG η hη hησ) hq
  exact
    { ht := H.ht, hsum := H.hsum, hx := hxF, hxR, hPF := WNF.zero, hPR := H.hR0, hPπ := H.hσ0
      hI := H.hI
      hξA := H.hξA (wnf_nsum hxF WNF.zero)
      hr := hr
      hCx := inC_approx_of_ub H.ht H.hsum hxF (fun e => H.hRU.pos η hη hησ e) hxR WNF.zero H.hR0 hr
        (fun hRA _ => by
          by_cases hx0 : r.big η = .zero
          · rw [hx0]
            exact inC_zero _ _
          · exact H.hRU.ub _ _ η (wnf_oadd H.hpreF (wnf_nsum hxF WNF.zero)) H.hσF hη hησ
              (approx_pos H.hpreF hxF WNF.zero hx0) (Or.inl (Or.inl rfl)) hRA
              (WFY.inC_of_ltY _ hη H.hσF hησ))
        (H.hRG η hη hησ) }

/-- 0 番目の近似の仮定 -/
theorem approx_zero (H : DiagHyp ξ σ X G Q pre rest R r) :
    Approx1 ξ σ X .zero pre rest R (nsum (r.big G) Q) := by
  have hxF := wnf_nsum H.h0F H.hQF
  have hle := le_nsum_left H.h0F H.hQF
  have hxR : Lt (nsum (r.big G) Q) R := nsum_lt_prin H.h0F H.hQF H.hRp H.h0R H.hQR
  have hx00 : nsum (r.big G) Q = .zero → r.big G = .zero := fun e => by
    rw [e] at hle
    rcases hle with h | h
    · exact h
    · exact absurd h (not_lt_zero _)
  have hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v (nsum (r.big G) Q) :=
    fun v hv hne hlt => lt_of_lt_of_leY (H.hRF.of_mem_subs hv) H.h0F hxF
      (H.hRG _ H.hGF H.hGσ v hv hne hlt) hle
  have hr : ∀ q, argR? σ = some q → Lt q (approx pre .zero (nsum (r.big G) Q)) := fun q hq =>
    H.r_lt hxF hxR (fun e => H.hRU.pos _ H.hGF H.hGσ (hx00 e)) hgap hq
  exact
    { ht := H.ht, hsum := H.hsum, hx := hxF, hxR, hPF := WNF.zero, hPR := H.hR0, hPπ := H.hσ0
      hI := H.hI
      hξA := H.hξA (wnf_nsum hxF WNF.zero)
      hr := hr
      hCx := inC_approx_of_ub H.ht H.hsum hxF (fun e => H.hRU.pos _ H.hGF H.hGσ (hx00 e)) hxR
        WNF.zero H.hR0 hr
        (fun hRA _ => by
          by_cases hx0 : nsum (r.big G) Q = .zero
          · rw [hx0]
            exact inC_zero _ _
          · refine inC_nsum H.h0F H.hQF (H.hRU.ub _ _ _ (wnf_oadd H.hpreF (wnf_nsum hxF WNF.zero))
              H.hσF H.hGF H.hGσ (approx_pos H.hpreF hxF WNF.zero hx0) (Or.inl (Or.inl rfl)) hRA
              (WFY.inC_of_ltY _ H.hGF H.hσF H.hGσ)) (WFY.inC_of_ltY _ H.hQF H.hσF H.hQσ))
        hgap }

/-- 塔の各段 -/
theorem tower (H : DiagHyp ξ σ X G Q pre rest R r) : ∀ k,
    WNF (gamT ξ σ pre r G Q k) ∧ Lt (gamT ξ σ pre r G Q k) σ ∧
      Approx1 ξ σ X .zero pre rest R (xT ξ σ pre r G Q k)
  | 0 => ⟨H.hGF, H.hGσ, H.approx_zero⟩
  | k + 1 => by
    obtain ⟨-, -, Ha⟩ := tower H k
    rw [gamT_succ]
    have hF := Ha.hnf
    have h1 : Lt (.Psi ξ σ (approx pre .zero (xT ξ σ pre r G Q k))) σ := lt_psi_targetY hF
    refine ⟨hF, h1, ?_⟩
    show Approx1 ξ σ X .zero pre rest R (r.big (gamT ξ σ pre r G Q (k + 1)))
    rw [gamT_succ]
    exact H.approx_of hF h1

/-- 塔は単調 -/
theorem gamT_mono (H : DiagHyp ξ σ X G Q pre rest R r) : ∀ k,
    Lt (gamT ξ σ pre r G Q k) (gamT ξ σ pre r G Q (k + 1))
  | 0 => by
    obtain ⟨hγ, hγσ, Ha⟩ := H.tower 0
    have e : gamT ξ σ pre r G Q (0 + 1) =
        .Psi ξ σ (approx pre .zero (nsum (r.big G) Q)) := gamT_succ ξ σ pre r G Q 0
    have Ha' : Approx1 ξ σ X .zero pre rest R (nsum (r.big G) Q) := Ha
    rw [e]
    have hy := Ha'.hnf
    have h1 := inC_of_fr_lt Ha'.hx H.hσF hy Ha'.hAF Ha'.hAF Ha'.hCx (Or.inr (lt_psi_targetY hy))
      (Or.inl rfl) fun z hz => FWOrder.k2 hy z (Ha'.fr_approx_of_x hz)
    exact coll_psiY hy _ hγ (H.hRU.lo _ _ _ hy hγ hγσ (inC_nsum_left H.h0F H.hQF h1)) hγσ
  | k + 1 => by
    obtain ⟨hγ, hγσ, Ha⟩ := H.tower (k + 1)
    have e : gamT ξ σ pre r G Q (k + 1 + 1) =
        .Psi ξ σ (approx pre .zero (r.big (gamT ξ σ pre r G Q (k + 1)))) := gamT_succ ξ σ pre r G Q (k + 1)
    have Ha' : Approx1 ξ σ X .zero pre rest R (r.big (gamT ξ σ pre r G Q (k + 1))) := Ha
    rw [e]
    have hy := Ha'.hnf
    have h1 := inC_of_fr_lt Ha'.hx H.hσF hy Ha'.hAF Ha'.hAF Ha'.hCx (Or.inr (lt_psi_targetY hy))
      (Or.inl rfl) fun z hz => FWOrder.k2 hy z (Ha'.fr_approx_of_x hz)
    exact coll_psiY hy _ hγ (H.hRU.lo _ _ _ hy hγ hγσ h1) hγσ

/-- 塔の上界 -/
theorem gamT_inC (H : DiagHyp ξ σ X G Q pre rest R r) {g d : Tm} (hg : WNF g) (hd : WNF d)
    (h0 : Lt .zero g) (hok : BigOK σ g d) (hR : inC R g d = true) (hσ : inC σ g d = true)
    (hξ : inC ξ g d = true)
    (hpre : inC (ofSummands pre) g d = true) (hG : inC G g d = true) (hQ : inC Q g d = true) (n : Nat)
    (hlt : ∀ j, j < n → Lt (approx pre .zero (xT ξ σ pre r G Q j)) g) :
    ∀ k, k ≤ n → inC (gamT ξ σ pre r G Q k) g d = true ∧ inC (xT ξ σ pre r G Q k) g d = true
  | 0, _ => ⟨hG, inC_nsum H.h0F H.hQF
      (H.hRU.ub g d _ hg hd H.hGF H.hGσ h0 hok hR hG) hQ⟩
  | k + 1, hk => by
    obtain ⟨-, hx⟩ := gamT_inC H hg hd h0 hok hR hσ hξ hpre hG hQ n hlt k (by omega)
    obtain ⟨hγF, hγσ, Ha⟩ := H.tower k
    have hA : inC (approx pre .zero (xT ξ σ pre r G Q k)) g d = true :=
      inC_oadd H.hpreF Ha.hy hpre (inC_nsum Ha.hx WNF.zero hx (inC_zero _ _))
    have hγ : inC (gamT ξ σ pre r G Q (k + 1)) g d = true := by
      rw [gamT_succ]
      exact inC_psi_iff.mpr (Or.inr ⟨hσ, hξ, hA, hlt k (by omega)⟩)
    obtain ⟨hγF', hγσ', -⟩ := H.tower (k + 1)
    exact ⟨hγ, H.hRU.ub g d _ hg hd hγF' hγσ' h0 hok hR hγ⟩

theorem x_zero (H : DiagHyp ξ σ X G Q pre rest R r) (n : Nat) :
    xT ξ σ pre r G Q n = .zero → ∀ v, v ∈ subs R → v = R := by
  cases n with
  | zero =>
    intro e
    have hle := le_nsum_left H.h0F H.hQF
    have e' : nsum (r.big G) Q = .zero := e
    rw [e'] at hle
    refine H.hRU.pos _ H.hGF H.hGσ ?_
    rcases hle with h | h
    · exact h
    · exact absurd h (not_lt_zero _)
  | succ k =>
    obtain ⟨h1, h2, -⟩ := H.tower (k + 1)
    exact H.hRU.pos _ h1 h2

theorem x_gap (H : DiagHyp ξ σ X G Q pre rest R r) (n : Nat) :
    ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v (xT ξ σ pre r G Q n) := by
  intro v hv hne hlt
  cases n with
  | zero =>
    exact lt_of_lt_of_leY (H.hRF.of_mem_subs hv) H.h0F (wnf_nsum H.h0F H.hQF)
      (H.hRG _ H.hGF H.hGσ v hv hne hlt) (le_nsum_left H.h0F H.hQF)
  | succ k =>
    obtain ⟨h1, h2, -⟩ := H.tower (k + 1)
    exact H.hRG _ h1 h2 v hv hne hlt

/-- 分割の上端 `T = pre ⊕ R` -/
theorem hTF (H : DiagHyp ξ σ X G Q pre rest R r) : WNF (oadd (ofSummands pre) R) :=
  wnf_oadd H.hpreF H.hRF

theorem hRT (H : DiagHyp ξ σ X G Q pre rest R r) : R ∈ summands (oadd (ofSummands pre) R) := by
  have hge : ∀ s h r', s ∈ pre → summands R = h :: r' → leB h s = true := by
    intro s h r' hs e
    rw [summands_principal H.hRp] at e
    simp only [List.cons.injEq] at e
    rw [← e.1, leB_iff]
    exact le_of_nfl_append H.hN s hs
  rw [summands_oadd_pre (nfl_append_left H.hN) H.hRF hge, summands_principal H.hRp]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- 上端についての `q + 1` -/
theorem hsqT (H : DiagHyp ξ σ X G Q pre rest R r) {q : Tm} (hq : argR? σ = some q) :
    Lt (succT q) (oadd (ofSummands pre) R) := by
  have Ha := H.approx_of WNF.zero H.hσ0
  have h1 : Lt q (approx pre .zero (r.big .zero)) :=
    H.r_lt Ha.hx Ha.hxR (fun e => H.hRU.pos _ WNF.zero H.hσ0 e) (H.hRG _ WNF.zero H.hσ0) hq
  exact succ_lt_of_sub H.hTF H.hRT H.hRU.hσs hq (wnf_of_argR H.hσF hq)
    (lt_transY (wnf_of_argR H.hσF hq) Ha.hAF H.hTF h1 Ha.hAtop)

/-- 成分と上端から塔の上界 -/
theorem xT_inC_T (H : DiagHyp ξ σ X G Q pre rest R r) {g d : Tm} (hg : WNF g) (hd : WNF d)
    (hR : inC R g d = true) (hpre : inC (ofSummands pre) g d = true)
    (hgT : Le (oadd (ofSummands pre) R) g) (hG : inC G g d = true) (hQ : inC Q g d = true)
    (hξ : inC ξ g d = true) (n : Nat) :
    inC (gamT ξ σ pre r G Q n) g d = true ∧ inC (xT ξ σ pre r G Q n) g d = true := by
  have hTF := H.hTF
  have h0 : Lt .zero g := by
    have Ha := (H.tower 0).2.2
    have h1 : Lt .zero (oadd (ofSummands pre) R) :=
      lt_of_lt_of_leY WNF.zero H.hRF hTF H.hR0 (le_oadd_right H.hpreF H.hRF)
    exact lt_of_lt_of_leY WNF.zero hTF hg h1 hgT
  have hok : BigOK σ g d := Or.inr fun q hq _ =>
    lt_of_lt_of_leY (succT_WNF (wnf_of_argR H.hσF hq)) hTF hg (H.hsqT hq) hgT
  exact H.gamT_inC hg hd h0 hok hR (H.hRU.hσC g d hg hd hR) hξ hpre hG hQ n
    (fun j _ => lt_of_lt_of_leY (H.tower j).2.2.hAF hTF hg (H.tower j).2.2.hAtop hgT) n
    (Nat.le_refl n)

/-- `X` の成分から塔の上界 -/
theorem xT_inC_X (H : DiagHyp ξ σ X G Q pre rest R r) {g d : Tm} (hg : WNF g) (hd : WNF d)
    (hXC : inC X g d = true) (hgX : Le X g) (hG : inC G g d = true) (hQ : inC Q g d = true)
    (hξ : inC ξ g d = true) (n : Nat) :
    inC (gamT ξ σ pre r G Q n) g d = true ∧ inC (xT ξ σ pre r G Q n) g d = true :=
  H.xT_inC_T hg hd (inC_of_mem_summands H.hX hXC H.hRm) (inC_pre_of_X H.hX H.hsum hXC)
    (le_transY H.hTF H.hX hg (top_le H.hX H.hsum) hgX) hG hQ hξ n

/-! ### 種を外に足す型 -/

theorem xT_eq (H : DiagHyp ξ σ X G .zero pre rest R r) :
    ∀ n, xT ξ σ pre r G .zero n = r.big (gamT ξ σ pre r G .zero n)
  | 0 => nsum_zero _ H.h0F
  | _ + 1 => rfl

theorem xT_mono (H : DiagHyp ξ σ X G .zero pre rest R r) (n : Nat) :
    Lt (xT ξ σ pre r G .zero n) (xT ξ σ pre r G .zero (n + 1)) := by
  rw [H.xT_eq n, H.xT_eq (n + 1)]
  obtain ⟨h1, -, -⟩ := H.tower n
  obtain ⟨h2, h3, -⟩ := H.tower (n + 1)
  exact H.hRU.good.2 _ _ h1 h2 (H.gamT_mono n) h3

theorem xT_lt (H : DiagHyp ξ σ X G .zero pre rest R r) {j : Nat} :
    ∀ {n : Nat}, j < n → Lt (xT ξ σ pre r G .zero j) (xT ξ σ pre r G .zero n)
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    by_cases hj : j = n
    · rw [hj]
      exact H.xT_mono n
    · exact lt_transY (H.tower j).2.2.hx (H.tower n).2.2.hx (H.tower (n + 1)).2.2.hx
        (xT_lt H (by omega)) (H.xT_mono n)

/-- 塔の項は後者でない -/
theorem x_ns (H : DiagHyp ξ σ X G .zero pre rest R r) (n : Nat) :
    ¬ isSucc (xT ξ σ pre r G .zero n) = true := by
  rw [H.xT_eq n]
  obtain ⟨h1, h2, -⟩ := H.tower n
  refine H.hRU.ns H.hRp _ h1 h2 ?_
  cases n with
  | zero => exact H.hGs
  | succ k =>
    rw [gamT_succ, isSucc_principal rfl]
    simp

/-- 近似での始点の引数の条件 -/
theorem ok_approx {π P c : Tm} (H : DiagHyp ξ σ X G .zero pre rest R r) (hc : WNF c) (hP : WNF P)
    (hPs : ¬ isSucc P = true) (n : Nat) :
    BigOK σ (approx pre P (oadd c (xT ξ σ pre r G .zero n))) π := by
  cases hq : argR? σ with
  | none => exact bigOK_none hq
  | some q =>
    have hxF := (H.tower n).2.2.hx
    have hx0 : xT ξ σ pre r G .zero n ≠ .zero := fun e => by
      have hqs : q ∈ subs R := subs_trans H.hRU.hσs (mem_subs_arg hq)
      exact ne_of_size_lt (H.hq_size hq) (H.x_zero n e q hqs)
    have hy := wnf_oadd hc hxF
    have hA := wnf_oadd H.hpreF (wnf_nsum hy hP)
    have hy0 : oadd c (xT ξ σ pre r G .zero n) ≠ .zero := fun e => by
      have h1 := le_oadd_right hc hxF
      rw [e] at h1
      rcases h1 with h1 | h1
      · exact hx0 h1
      · exact not_lt_zero _ h1
    have hn0 : nsum (oadd c (xT ξ σ pre r G .zero n)) P ≠ .zero := fun e => by
      have h1 := le_nsum_left hy hP
      rw [e] at h1
      rcases h1 with h1 | h1
      · exact hy0 h1
      · exact not_lt_zero _ h1
    refine Or.inr fun q' hq' hlt => succT_lt_of_not_succ (wnf_of_argR H.hσF hq') hA ?_ hlt
    exact not_succ_oadd H.hpreF (wnf_nsum hy hP) hn0
      (not_succ_nsum hy hP (not_succ_oadd hc hxF hx0 (H.x_ns n)) hPs)

/-- 塔の次の段が `C(g, d)` に入るなら、前の段の近似も入る -/
theorem out_step (H : DiagHyp ξ σ X G .zero pre rest R r) {g d : Tm} (hg : WNF g) (hd : WNF d) (n : Nat)
    (h : inC (xT ξ σ pre r G .zero (n + 1)) g d = true) : inC (xT ξ σ pre r G .zero n) g d = true := by
  obtain ⟨hγ, -, Ha⟩ := H.tower n
  obtain ⟨hγ', hγσ', -⟩ := H.tower (n + 1)
  have hm := H.gamT_mono n
  have h' : inC (r.big (gamT ξ σ pre r G .zero (n + 1))) g d = true := h
  have hC := H.hRU.lo _ _ _ hd hγ' hγσ' h'
  rw [gamT_succ] at hC
  rcases inC_psi_iff.mp hC with h1 | ⟨-, -, hE, -⟩
  · rw [← gamT_succ] at h1
    rw [H.xT_eq n]
    exact H.hRU.ub2 g d _ _ hg hd hγ hγ' hm hγσ' h'
      (WFY.inC_of_ltY _ hγ hd (lt_transY hγ hγ' hd hm h1))
  · have hy : inC (nsum (xT ξ σ pre r G .zero n) .zero) g d = true :=
      (inC_iff_summands Ha.hy).mpr fun s hs =>
        inC_of_mem_summands Ha.hAF hE (mem_summands_oadd_right Ha.hpreF Ha.hy hs)
    exact inC_nsum_left Ha.hx WNF.zero hy

/-! ### 目標そのものへの対角化 -/

/-- 目標そのものへの対角化の列の局所的な性質：`t[n] = γ_{n+1}` -/
theorem natL_in {P : Tm} {s : SeqD} (H : DiagHyp ξ σ X G P pre rest R r)
    (he : ∀ n, s.nat n = gamT ξ σ pre r G P (n + 1)) : NatL σ s := by
  refine ⟨fun n => ?_, fun n => ?_, fun g d n hg hd h => ?_⟩
  · rw [he n, he (n + 1)]
    obtain ⟨h1, h2, -⟩ := H.tower (n + 1)
    exact ⟨h1, h2, H.gamT_mono (n + 1)⟩
  · rw [he n, gamT_succ]
    intro h
    cases h
  · rw [he (n + 1)] at h
    rw [he n]
    obtain ⟨h1, h2, -⟩ := H.tower (n + 1)
    obtain ⟨h3, -, Ha⟩ := H.tower (n + 1 + 1)
    have hm := H.gamT_mono (n + 1)
    have e := gamT_succ ξ σ pre r G P (n + 1)
    rw [e] at h
    rcases inC_psi_iff.mp h with h' | ⟨-, -, hδ, -⟩
    · rw [← e] at h'
      exact WFY.inC_of_ltY _ h1 hd (lt_transY h1 h3 hd hm h')
    · obtain ⟨-, -, Hb⟩ := H.tower (n + 1)
      have hy : inC (nsum (xT ξ σ pre r G P (n + 1)) .zero) g d = true :=
        (inC_iff_summands Hb.hy).mpr fun s hs =>
          inC_of_mem_summands Hb.hAF hδ (mem_summands_oadd_right Hb.hpreF Hb.hy hs)
      exact H.hRU.lo _ _ _ hd h1 h2 (inC_nsum_left Hb.hx WNF.zero hy)

end DiagHyp

/-! ### 定義の `gam` との対応 -/

/-- ψ・Mahlo 型の生成 -/
def GenPsi (g : Gen) (ξ π : Tm) : Prop := (g = .psi0 π ∧ ξ = .zero) ∨ g = .mahlo ξ π

theorem GenPsi.ap {g : Gen} {ξ π : Tm} (h : GenPsi g ξ π) (A : Tm) : g.ap A = .Psi ξ π A := by
  rcases h with ⟨rfl, rfl⟩ | rfl <;> rfl

theorem GenPsi.comb {g : Gen} {ξ π : Tm} (h : GenPsi g ξ π) (pre : List Tm) (c P x : Tm) :
    combine g pre c P x = approx pre P (oadd c x) := by
  rcases h with ⟨rfl, rfl⟩ | rfl <;> rfl

theorem GenPsi.tgt {g : Gen} {ξ π : Tm} (h : GenPsi g ξ π) : g.tgt? = some π := by
  rcases h with ⟨rfl, rfl⟩ | rfl <;> rfl

theorem GenPsi.seed {g : Gen} {ξ π : Tm} (h : GenPsi g ξ π) : seedOut g = true := by
  rcases h with ⟨rfl, rfl⟩ | rfl <;> rfl

theorem validR_of {σ δ : Tm} (h : ∀ q, argR? σ = some q → Lt q δ) : validR σ δ = true := by
  unfold validR
  cases e : argR? σ with
  | none => rfl
  | some q => exact ltB_iff.mpr (h q e)

section Tgt

variable {τ σ c P : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD}

theorem canonK_tgt (hσ : IsTgt σ) : canonK σ g pre R = false := by
  rcases hσ with ⟨d, rfl, -⟩ | ⟨m, p, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩ <;> cases g <;> rfl

theorem outsideMode_tgt (hσ : IsTgt σ) :
    outsideMode τ σ g pre R = if σ = g.tgt?.getD τ then false else true := by
  rcases hσ with ⟨d, rfl, -⟩ | ⟨m, p, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩ <;> cases g <;> rfl

theorem col_tgt (hσ : IsTgt σ) (δ : Tm) (k : Nat) :
    col σ δ k = if validR σ δ then .Psi .zero σ δ else base σ := by
  rcases hσ with ⟨d, rfl, -⟩ | ⟨m, p, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩ <;> rfl

theorem argOf_tgt (hσ : IsTgt σ) (γ : Tm) :
    argOf τ σ g pre R r c P γ =
      if σ = g.tgt?.getD τ then combine g pre c (if seedOut g && γ == .zero then P else .zero) (r.big γ)
      else combine g pre c P (r.big γ) := by
  unfold argOf
  rw [canonK_tgt hσ, outsideMode_tgt hσ]
  by_cases h : σ = g.tgt?.getD τ <;> simp [h]

theorem gam_zero_tgt (hσ : IsTgt σ) :
    gam τ σ g pre R r c P 0 =
      if σ = g.tgt?.getD τ then (if seedOut g then .zero else P)
      else (if seedOut g then sStart σ (oadd (ofSummands pre) R) c P else .zero) := by
  unfold gam
  rw [canonK_tgt hσ, outsideMode_tgt hσ]
  by_cases h : σ = g.tgt?.getD τ <;>
    rcases hσ with ⟨d, rfl, -⟩ | ⟨m, p, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩ <;> simp [h]

theorem gam_succ_tgt (hσ : IsTgt σ) (k : Nat) :
    gam τ σ g pre R r c P (k + 1) =
      if σ = g.tgt?.getD τ then
        (if ltB (col σ (argOf τ σ g pre R r c P (gam τ σ g pre R r c P k)) k)
              (g.ap (argOf τ σ g pre R r c P (gam τ σ g pre R r c P k))) &&
            ltB (g.ap (argOf τ σ g pre R r c P (gam τ σ g pre R r c P k))) σ
          then g.ap (argOf τ σ g pre R r c P (gam τ σ g pre R r c P k))
          else col σ (argOf τ σ g pre R r c P (gam τ σ g pre R r c P k)) k)
      else col σ (oadd (ofSummands pre) (r.big (gam τ σ g pre R r c P k))) k := by
  have hc := canonK_tgt (σ := σ) (g := g) (pre := pre) (R := R) hσ
  have ho := outsideMode_tgt (τ := τ) (σ := σ) (g := g) (pre := pre) (R := R) hσ
  by_cases h : σ = g.tgt?.getD τ
  · rcases hσ with ⟨d, rfl, -⟩ | ⟨m, p, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩ <;>
      simp only [gam, hc, ho, ite_eq_left h, Bool.false_eq_true, ↓reduceIte]
  · rcases hσ with ⟨d, rfl, -⟩ | ⟨m, p, rfl⟩ | ⟨ζ, κ, b, rfl, -⟩ <;>
      simp only [gam, hc, ho, ite_eq_right h, Bool.false_eq_true, ↓reduceIte]

end Tgt

theorem app_nat_big {τ σ P c : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD}
    (hd : r.dom = .big σ) (hlt : ltB σ τ = false) (n : Nat) :
    (SeqD.app τ g pre R r P c).nat n =
      g.ap (argOf τ σ g pre R r c P (gam τ σ g pre R r c P n)) := by
  show (match r.dom with
    | .big σ => if ltB σ τ then zero else g.ap (argOf τ σ g pre R r c P (gam τ σ g pre R r c P n))
    | _ => g.ap (combine g pre c P (r.nat n))) = _
  rw [hd]
  simp [hlt]

theorem approx_zero_eq {pre : List Tm} {x : Tm} (hx : WNF x) :
    approx pre .zero x = oadd (ofSummands pre) x := by
  unfold approx
  rw [nsum_zero _ hx]

/-- 種を外に足す型の添字は塔 -/
theorem gam_outG {τ σ c P X G : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (H : DiagHyp .zero σ X G .zero pre rest R r) (hne : σ ≠ g.tgt?.getD τ)
    (hG : G = if seedOut g then sStart σ (oadd (ofSummands pre) R) c P else .zero) :
    ∀ n, gam τ σ g pre R r c P n = gamT .zero σ pre r G .zero n
  | 0 => by
    rw [gam_zero_tgt H.ht.psi.tgt, hG]
    simp [hne, gamT]
  | k + 1 => by
    have ih := gam_outG (τ := τ) (c := c) (P := P) H hne hG k
    have Ha := (H.tower k).2.2
    have hx := Ha.hx
    have hr := Ha.hr
    rw [H.xT_eq k] at hx hr
    rw [approx_zero_eq hx] at hr
    rw [gam_succ_tgt H.ht.psi.tgt, ih, gamT_succ, H.xT_eq k, approx_zero_eq hx]
    simp only [hne, ite_false]
    rw [col_tgt H.ht.psi.tgt, validR_of hr]
    rfl

/-- 種を外に足す型の列の項 -/
theorem app_nat_outG {σ P c ceil X G : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (H : DiagHyp .zero σ X G .zero pre rest R r) (hne : σ ≠ g.tgt?.getD ceil)
    (hG : G = if seedOut g then sStart σ (oadd (ofSummands pre) R) c P else .zero)
    (hd : r.dom = .big σ) (hlt : ltB σ ceil = false) (n : Nat) :
    (SeqD.app ceil g pre R r P c).nat n = g.ap (combine g pre c P (xT .zero σ pre r G .zero n)) := by
  rw [app_nat_big hd hlt, gam_outG H hne hG n, argOf_tgt H.ht.psi.tgt, H.xT_eq n]
  simp only [hne, ite_false]

/-- 種を外に足す型の列の項 -/
theorem app_nat_out {ξ' π σ P c ceil X G : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ' π) (H : DiagHyp .zero σ X G .zero pre rest R r) (hne : σ ≠ π)
    (hG : G = sStart σ (oadd (ofSummands pre) R) c P)
    (hd : r.dom = .big σ) (hlt : ltB σ ceil = false) (n : Nat) :
    (SeqD.app ceil g pre R r P c).nat n =
      .Psi ξ' π (approx pre P (oadd c (xT .zero σ pre r G .zero n))) := by
  rw [app_nat_outG H (by rw [hg.tgt]; exact hne) (by rw [hg.seed]; exact hG) hd hlt, hg.comb, hg.ap]

/-- 目標そのものへの対角化の近似 -/
theorem argOf_in {τ ξ π c P γ : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ π) (hπ : IsTgt π) :
    argOf τ π g pre R r c P γ = approx pre (if γ = .zero then P else .zero) (oadd c (r.big γ)) := by
  rw [argOf_tgt hπ, hg.tgt]
  simp [hg.seed, hg.comb]

/-- 目標そのものへの対角化の添字の 1 段 -/
theorem gam_succ_in {τ ξ π c P : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD} (k : Nat)
    (hg : GenPsi g ξ π) (hπ : IsTgt π)
    (h0 : WNF (.Psi .zero π (argOf τ π g pre R r c P (gam τ π g pre R r c P k))))
    (hy : WNF (.Psi ξ π (argOf τ π g pre R r c P (gam τ π g pre R r c P k)))) :
    gam τ π g pre R r c P (k + 1) =
      .Psi ξ π (argOf τ π g pre R r c P (gam τ π g pre R r c P k)) := by
  rw [gam_succ_tgt hπ, hg.tgt]
  simp only [Option.getD_some, ite_true]
  generalize argOf τ π g pre R r c P (gam τ π g pre R r c P k) = A at h0 hy ⊢
  have hv : validR π A = true := validR_of fun q hq => arg_lt_of_psi h0 hq
  rw [col_tgt hπ, hv, hg.ap]
  simp only [ite_true]
  by_cases hξ : ξ = .zero
  · subst hξ
    simp [ltB, cmp_self]
  · have hA : Lt (.Psi .zero π A) (.Psi ξ π A) := by
      have hne : Tm.Psi .zero π A ≠ .Psi ξ π A := fun e => by
        cases e
        exact hξ rfl
      refine (lt_psi_psiY rfl hne).mpr (Or.inr ⟨lt_psi_targetY hy, lt_psi_targetY h0, Or.inr (Or.inr
        (Or.inl ⟨cmp_self _, rfl, zero_lt hξ, inC_zero _ _⟩))⟩)
    have h1 : ltB (.Psi .zero π A) (.Psi ξ π A) = true := ltB_iff.mpr hA
    have h2 : ltB (.Psi ξ π A) π = true := ltB_iff.mpr (lt_psi_targetY hy)
    simp [h1, h2]

/-- 目標そのものへの対角化の添字は塔 -/
theorem gam_in {τ ξ π P X : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ π) (H : DiagHyp ξ π X .zero P pre rest R r) :
    ∀ n, gam τ π g pre R r .zero P n = gamT ξ π pre r .zero P n
  | 0 => by
    rw [gam_zero_tgt H.ht.psi.tgt, hg.tgt]
    simp [hg.seed, gamT]
  | 1 => by
    have Ha := (H.tower 0).2.2
    have hx : WNF (nsum (r.big .zero) P) := Ha.hx
    have e0 : gam τ π g pre R r .zero P 0 = .zero := gam_in hg H 0
    have e1 : argOf τ π g pre R r .zero P (gam τ π g pre R r .zero P 0) =
        approx pre .zero (nsum (r.big .zero) P) := by
      rw [e0, argOf_in hg H.ht.psi.tgt, approx_zero_eq hx]
      simp only [ite_true]
      unfold approx
      rw [zero_oadd H.h0F]
    rw [gam_succ_in 0 hg H.ht.psi.tgt (by rw [e1]; exact wnf_psi0 Ha.hπF Ha.ht.psi.tgt Ha.hAF Ha.hC Ha.hr)
      (by rw [e1]; exact Ha.hnf), e1]
    rfl
  | k + 2 => by
    have Ha := (H.tower (k + 1)).2.2
    have hx : WNF (r.big (gamT ξ π pre r .zero P (k + 1))) := Ha.hx
    have hne : gamT ξ π pre r .zero P (k + 1) ≠ .zero := by
      rw [gamT_succ]
      intro e
      cases e
    have e0 := gam_in (τ := τ) hg H (k + 1)
    have e1 : argOf τ π g pre R r .zero P (gam τ π g pre R r .zero P (k + 1)) =
        approx pre .zero (r.big (gamT ξ π pre r .zero P (k + 1))) := by
      rw [e0, argOf_in hg H.ht.psi.tgt, ite_eq_right hne, zero_oadd hx]
    have Ha' : Approx1 ξ π X .zero pre rest R (r.big (gamT ξ π pre r .zero P (k + 1))) := Ha
    rw [gam_succ_in (k + 1) hg H.ht.psi.tgt
      (by rw [e1]; exact wnf_psi0 Ha'.hπF Ha'.ht.psi.tgt Ha'.hAF Ha'.hC Ha'.hr)
      (by rw [e1]; exact Ha'.hnf), e1]
    rfl

/-- 目標そのものへの対角化の列の項 -/
theorem app_nat_in {ξ π P ceil X : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ π) (H : DiagHyp ξ π X .zero P pre rest R r) (hd : r.dom = .big π)
    (hlt : ltB π ceil = false) (n : Nat) :
    (SeqD.app ceil g pre R r P .zero).nat n = gamT ξ π pre r .zero P (n + 1) := by
  have e0 := gam_in (τ := ceil) hg H n
  have e1 := gam_in (τ := ceil) hg H (n + 1)
  obtain ⟨h1, -, -⟩ := H.tower (n + 1)
  have hA : argOf ceil π g pre R r .zero P (gam ceil π g pre R r .zero P n) =
      approx pre .zero (xT ξ π pre r .zero P n) := by
    rw [e0, argOf_in hg H.ht.psi.tgt]
    cases n with
    | zero =>
      have hx : WNF (nsum (r.big .zero) P) := (H.tower 0).2.2.hx
      show approx pre (if gamT ξ π pre r .zero P 0 = .zero then P else .zero)
        (oadd .zero (r.big (gamT ξ π pre r .zero P 0))) = approx pre .zero (nsum (r.big .zero) P)
      rw [approx_zero_eq hx]
      simp only [gamT, ite_true]
      unfold approx
      rw [zero_oadd H.h0F]
    | succ k =>
      have hx : WNF (r.big (gamT ξ π pre r .zero P (k + 1))) := (H.tower (k + 1)).2.2.hx
      have hne : gamT ξ π pre r .zero P (k + 1) ≠ .zero := by
        rw [gamT_succ]
        intro e
        cases e
      rw [ite_eq_right hne, zero_oadd hx]
      rfl
  rw [app_nat_big hd hlt, hA, hg.ap, gamT_succ]

end RTKA.Fund
