import Compact.FS.CofTow

/-! 近似の列の共終性：`a < pre ⊕ R` で `a ∈ C(a, t)` なら、列の項の引数は `a` を越える（`ArgS`）。

共終数ごとに塔（`Tow`）を作る。目標を越える塔では `t ≤ γ_N` から `a ∈ C(a, γ_N)`、値の帰還の塔では `a` の前線が列の項の下に
あることから `a ∈ C(a, γ_N)` が出るので、`Tow.arg` が使える。 -/

namespace RTKA.Fund

open Tm W

/-- 列の記述 `r` の塔 -/
theorem tow_of {σ : Tm} {pre : List Tm} {R : Tm} {r : SeqD} {γ : Nat → Tm} (hN : NFL (pre ++ [R]))
    (hd : r.dom = .big σ) (hRC : SeqC R r) (hB : BigUB R σ r)
    (hγF : ∀ n, WNF (γ n)) (hlt : ∀ n, Lt (γ n) σ) (mono : ∀ n, Lt (γ n) (γ (n + 1)))
    (hCl : ∀ n, Cl σ (γ n))
    (hC : ∀ n, Clo (γ (n + 1)) (oadd (ofSummands pre) (r.big (γ n))) σ) :
    Tow σ (oadd (ofSummands pre) R) γ (fun n => oadd (ofSummands pre) (r.big (γ n))) := by
  have hpreF := wnf_ofSummands (nfl_append_left hN)
  have hRN := hN.1 R (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  have hxF := fun n => (hB.good.1 (γ n) (hγF n) (hlt n)).1
  have hRC' : ∀ x β, WNF x → Lt x R → WNF β → Lt β σ → Cl σ β → (∀ f, f ∈ fr σ x → Lt f β) →
      Lt x (r.big β) := by
    have := hRC
    unfold SeqC at this
    rwa [hd] at this
  refine ⟨wnf_oadd hpreF hRN.1, hγF, mono, hC, fun n => Or.inr ?_, hlt, fun b hb hbT hf => ?_⟩
  · exact oadd_lt_oadd hpreF (hxF n) (hxF (n + 1)) (hB.good.2 _ _ (hγF n) (hγF (n + 1)) (mono n) (hlt (n + 1)))
  · obtain ⟨b', hb', hb'R, hsub, hle⟩ := lt_oadd_split hN hb hbT
    have hf' : ∀ f, f ∈ fr σ b' → ∃ n, Lt f (γ n) := fun f h => by
      obtain ⟨u, hu, hfu⟩ := (mem_fr_iff hb').mp h
      exact hf f ((mem_fr_iff hb).mpr ⟨u, hsub u hu, hfu⟩)
    obtain ⟨N, hN'⟩ := exists_bound (P := fun _ => True) hγF mono (fr σ b')
      (fun f h => hb'.of_mem_subs (fr_spec h).1) fun f h _ => hf' f h
    have h1 : Lt b' (r.big (γ N)) := hRC' b' (γ N) hb' hb'R (hγF N) (hlt N) (hCl N) fun f h => hN' f h trivial
    exact ⟨N, lt_of_le_of_ltY hb (wnf_oadd hpreF hb') (wnf_oadd hpreF (hxF N)) hle
      (oadd_lt_oadd hpreF hb' (hxF N) h1)⟩

/-- 目標への対角化の塔 -/
theorem DiagHyp.tow {ξ σ X G Q : Tm} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (H : DiagHyp ξ σ X G Q pre rest R r) (hd : r.dom = .big σ) (hRC : SeqC R r) :
    Tow σ (oadd (ofSummands pre) R) (fun n => gamT ξ σ pre r G Q (n + 1))
      (fun n => oadd (ofSummands pre) (r.big (gamT ξ σ pre r G Q (n + 1)))) := by
  have hN : NFL (pre ++ [R]) := by
    have h := H.hN
    rw [show pre ++ R :: rest = (pre ++ [R]) ++ rest by simp] at h
    exact nfl_append_left h
  refine tow_of hN hd hRC H.hRU (fun n => (H.tower (n + 1)).1) (fun n => (H.tower (n + 1)).2.1)
    (fun n => H.gamT_mono (n + 1)) (fun n => ?_) fun n => ?_
  · show Cl σ (gamT ξ σ pre r G Q (n + 1))
    rw [gamT_succ]
    exact Cl.of_psi (H.tower n).2.2.hnf
  · have Ha := (H.tower (n + 1)).2.2
    have Ha' : Approx1 ξ σ X .zero pre rest R (r.big (gamT ξ σ pre r G Q (n + 1))) := Ha
    have e : gamT ξ σ pre r G Q (n + 1 + 1) =
        .Psi ξ σ (approx pre .zero (r.big (gamT ξ σ pre r G Q (n + 1)))) := gamT_succ ξ σ pre r G Q (n + 1)
    have e' := approx_zero_eq (pre := pre) Ha'.hx
    have hy := Ha'.hnf
    rw [e'] at hy
    show Clo (gamT ξ σ pre r G Q (n + 1 + 1)) _ σ
    rw [e, e']
    exact Clo.psi hy

/-- 正準な K の塔の 1 段目以降 -/
theorem KCanon.big_ne {m : Nat} {X : Tm} {pre rest : List Tm} {R : Tm} {r : SeqD} {G : Tm}
    (H : KCanon m X pre rest R r G) (k : Nat) : Cl (.K m) (kTow m pre r G (k + 1)) := by
  obtain ⟨D, e, hy, -⟩ := H.form k
  rw [e]
  exact Cl.of_xi hy

/-- 正準な K の塔 -/
theorem KCanon.tow {m : Nat} {X : Tm} {pre rest : List Tm} {R : Tm} {r : SeqD} {G : Tm}
    (H : KCanon m X pre rest R r G) (hd : r.dom = .big (.K m)) (hRC : SeqC R r) :
    Tow (.K m) (oadd (ofSummands pre) R) (fun n => kTow m pre r G (n + 1))
      (fun n => oadd (ofSummands pre) (r.big (kTow m pre r G (n + 1)))) := by
  have hN : NFL (pre ++ [R]) := by
    have h := H.hN
    rw [show pre ++ R :: rest = (pre ++ [R]) ++ rest by simp] at h
    exact nfl_append_left h
  refine tow_of hN hd hRC H.hB.1 (fun n => (H.tower (n + 1)).1) (fun n => (H.tower (n + 1)).2)
    (fun n => H.mono (n + 1)) (fun n => H.big_ne n) fun n => ?_
  obtain ⟨D, e, hy, hD⟩ := H.form (n + 1)
  show Clo (kTow m pre r G (n + 1 + 1)) _ (.K m)
  rw [e]
  rcases hD with ⟨h0, -⟩ | ⟨-, rfl⟩
  · exfalso
    have h1 := H.x_zero_of (H.x_F (n + 1)) h0
    exact (H.big_ne n).big_ne H.hB.1 (H.tower (n + 1)).1 (H.tower (n + 1)).2 h1
  · exact Clo.xi hy

/-! ### 旧方式：全ての `K_m` 未満の項は `virtK` の下にある -/

theorem virt_tow {m : Nat} (hm : 1 ≤ m) :
    Tow (succK m) (succK m) (fun n => virtG m (n + 1))
      (fun n => oadd (.Psi .zero (succK m) .zero) (virtG m (n + 1))) := by
  have hψ := wnf_psi0K hm
  have hCl : ∀ n, Cl (succK m) (virtG m (n + 1)) := fun n => Cl.of_psi (virtG_spec hm (n + 1)).1
  refine ⟨WNF.succK hm, fun n => (virtG_spec hm (n + 1)).1, fun n => virtG_mono hm (n + 1), fun n => ?_,
    fun n => Or.inr (virtE_mono hm (n + 1)), fun n => (virtG_spec hm (n + 1)).2, fun b hb hbT hf => ?_⟩
  · exact Clo.psi (virtG_spec hm (n + 1 + 1)).1
  · obtain ⟨N, hN⟩ := exists_bound (P := fun _ => True) (y := fun n => virtG m (n + 1))
      (fun n => (virtG_spec hm (n + 1)).1) (fun n => virtG_mono hm (n + 1)) (fr (succK m) b)
      (fun f h => hb.of_mem_subs (fr_spec h).1) fun f h _ => hf f h
    have h1 := (hCl N).2 b hb hbT fun f h => hN f h trivial
    exact ⟨N, lt_of_lt_of_leY hb (virtG_spec hm (N + 1)).1 (virtE_F hm (N + 1)) h1
      (le_oadd_right hψ (virtG_spec hm (N + 1)).1)⟩

theorem K_lt_virtG {m : Nat} (hm : 1 ≤ m) : Lt (.K m) (virtG m 1) := by
  have hy := (virtG_spec hm 1).1
  exact coll_psiY hy _ (WNF.K' hm) (inC_K _ _ _) (WFY.K_lt_succK hm)

/-- 全ての `K_m` 未満の項は `virtK` の下にある -/
theorem virt_all {m : Nat} (hm : 1 ≤ m) : ∀ z, WNF z → Lt z (.K m) → ∃ n, Lt z (virtK m n) := by
  have hKF := WNF.K' hm
  intro z
  induction hn : z.size using Nat.strongRecOn generalizing z with
  | ind n ih =>
    intro hz hzK
    have hparF : ∀ w, w ∈ parF z → WNF w := fun w hw => hz.of_mem_subs (parL_sub (parF_sub_parL hw)).1
    have hpar : ∀ w, w ∈ parF z → ∃ k, Lt w (virtK m k) := fun w hw => by
      have hs := (parL_sub (parF_sub_parL hw)).2
      exact ih w.size (by omega) w rfl (hparF w hw) (lt_transY (hparF w hw) hz hKF (parF_lt hz hw) hzK)
    obtain ⟨N, hN⟩ := exists_bound (P := fun _ => True) (wnf_virtK hm) (virtK_mono hm) (parF z) hparF
      fun w hw _ => hpar w hw
    have hlt : ∀ k, (∀ a, argR? z = some a → Lt a (virtA m k)) → ∃ j, Lt z (virtK m j) := fun k h => by
      refine ⟨max N k, (Clo.xi (wnf_virtK hm _)).lt hz hzK (fun w hw => ?_) fun a e => ?_⟩
      · exact lt_of_lt_of_leY (hparF w hw) (wnf_virtK hm N) (wnf_virtK hm _) (hN w hw trivial)
          (mono_le (wnf_virtK hm) (virtK_mono hm) (Nat.le_max_left _ _))
      · have hAm : ∀ i, Le (virtA m i) (virtA m (i + 1)) := fun i =>
          Or.inr (nsum_lt_left (virtE_F hm i) (virtE_F hm (i + 1)) (wnf_xiS hm) (virtE_mono hm i))
        exact lt_of_lt_of_leY (wnf_of_argR hz e) (virtA_F hm k) (virtA_F hm _) (h a e)
          (mono_le' (virtA_F hm) hAm (Nat.le_max_right _ _))
    cases z with
    | Xi j b =>
      have hj := hz.xi.1
      have hl : j ≤ m := (lt_K_iffY hz hm).mp hzK
      by_cases hj' : j = m
      · subst hj'
        have hbF := hz.xi.2.1
        rcases le_of_ne_gtY hbF (WNF.succK hm) hz.xi.2.2.2.1 with e | hb
        · subst e
          exact ⟨0, xiS_lt_virtK hm 0⟩
        · have hle : Le (.K j) (virtG j 1) := Or.inr (K_lt_virtG hm)
          have hC : inC b b (virtG j (0 + 1)) = true :=
            inC_mono_d hKF (virtG_spec hm 1).1 hle hbF hz.xi.2.2.2.2
          obtain ⟨k, hk⟩ := (virt_tow hm).arg hbF hb hC
          exact hlt (k + 1) fun a e => by
            cases e
            exact lt_of_lt_of_leY hbF (virtE_F hm (k + 1)) (virtA_F hm (k + 1)) hk (virtE_le hm (k + 1))
      · have hK1 : Lt (.K j) (.K m) := (lt_K_iffY (WNF.K' hj) hm).mpr (by simp only [lev]; omega)
        have h1 : Lt (.K j) (virtK m 0) := (Clo.xi (wnf_virtK hm 0)).coll _ (WNF.K' hj) (inC_K _ _ _) hK1
        exact ⟨0, lt_transY hz (WNF.K' hj) (wnf_virtK hm 0) ((lt_K_iffY hz hj).mpr (Nat.le_refl _)) h1⟩
    | Psi s k a =>
      have hP := hz.psi
      have hl : lev (.Psi s k a) ≤ m := (lt_K_iffY hz hm).mp hzK
      have hkK : Lt k (.K m) := (lt_K_iffY hP.piF hm).mpr hl
      have hs : k.size < (Tm.Psi s k a).size := by
        simp only [Tm.size]
        omega
      obtain ⟨j, hj⟩ := ih k.size (by omega) k rfl hP.piF hkK
      exact ⟨j, lt_transY hz hP.piF (wnf_virtK hm j) (lt_psi_targetY hz) hj⟩
    | _ => exact hlt 0 fun a e => by cases e

/-- 旧方式の塔の 2 段目以降は `virtK` -/
theorem KOld.form2 {m : Nat} {X c P : Tm} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (H : KOld m X c P pre rest R r) (k : Nat) : oT m pre r c P (k + 1 + 1) = virtK m (k + 1) := by
  obtain ⟨hγ, hγK⟩ := H.tower k
  obtain ⟨hγ', hγK'⟩ := H.tower (k + 1)
  have hx := H.hB.1.good.2 _ _ hγ hγ' (H.mono k) hγK'
  have hAA := H.A_mono (H.x_F k) (H.x_F (k + 1)) hx
  have hS : Lt (succK m) (approx pre P (oadd c (r.big (oT m pre r c P (k + 1))))) :=
    lt_of_le_of_ltY H.hSF (H.hAF (H.x_F k)) (H.hAF (H.x_F (k + 1))) (H.lbA hγ hγK) hAA
  rcases H.form hγ' hγK' with ⟨-, e⟩ | ⟨e, -⟩
  · rw [e] at hS
    exact absurd hS (Lt.irrefl _)
  · exact e

/-- 全ての `K_m` 未満の項は旧方式の塔の下にある -/
theorem KOld.all {m : Nat} {X c P : Tm} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (H : KOld m X c P pre rest R r) {z : Tm} (hz : WNF z) (hzK : Lt z (.K m)) :
    ∃ n, Lt z (oT m pre r c P (n + 1 + 1)) := by
  obtain ⟨n, hn⟩ := virt_all H.hm z hz hzK
  refine ⟨n, ?_⟩
  rw [H.form2 n]
  exact lt_transY hz (wnf_virtK H.hm n) (wnf_virtK H.hm _) hn (virtK_mono H.hm n)

/-! ### 引数の共終性 -/

/-- 列の項の引数の共終性 -/
def ArgS (t T ξ τ : Tm) (s : SeqD) : Prop :=
  ∀ a N, WNF a → Lt a T → inC a a t = true → (∀ u, u ∈ fr t a → Lt u (s.nat N)) →
    ∃ n A, N ≤ n ∧ s.nat n = .Psi ξ τ A ∧ Lt a A

theorem le_approx {pre : List Tm} {c P x : Tm} (hpreF : WNF (ofSummands pre)) (hc : WNF c) (hP : WNF P)
    (hx : WNF x) : Le (oadd (ofSummands pre) x) (approx pre P (oadd c x)) := by
  have hy := wnf_oadd hc hx
  have hz := wnf_nsum hy hP
  have h1 : Le x (nsum (oadd c x) P) :=
    le_transY hx hy hz (le_oadd_right hc hx) (le_nsum_left hy hP)
  rcases h1 with e | h
  · exact Or.inl (by unfold approx; rw [← e])
  · exact Or.inr (oadd_lt_oadd hpreF hx hz h)

/-- 共終数 `ω` の加数 -/
theorem argS_nat {t ξ τ P c ceil : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ τ) (hN : NFL (pre ++ R :: rest)) (hc : WNF c) (hP : WNF P) (hd : r.dom = .omega)
    (hF : ∀ n, WNF (r.nat n)) (hmo : ∀ n, Lt (r.nat n) (r.nat (n + 1))) (hRC : SeqC R r) :
    ArgS t (oadd (ofSummands pre) R) ξ τ (.app ceil g pre R r P c) := by
  have hN' : NFL (pre ++ [R]) := by
    rw [show pre ++ R :: rest = (pre ++ [R]) ++ rest by simp] at hN
    exact nfl_append_left hN
  have hpreF := wnf_ofSummands (nfl_append_left hN')
  have hRC' : ∀ x, WNF x → Lt x R → ∃ n, Lt x (r.nat n) := by
    have := hRC
    unfold SeqC at this
    rwa [hd] at this
  intro a N ha haT _ _
  obtain ⟨a', ha', ha'R, -, hle⟩ := lt_oadd_split hN' ha haT
  obtain ⟨n₀, hn₀⟩ := hRC' a' ha' ha'R
  have hdom : ∀ σ, r.dom ≠ .big σ := fun σ e => by
    rw [hd] at e
    cases e
  have hn : Lt a' (r.nat (max n₀ N)) :=
    lt_of_lt_of_leY ha' (hF n₀) (hF _) hn₀ (mono_le hF hmo (Nat.le_max_left _ _))
  refine ⟨max n₀ N, _, Nat.le_max_right _ _, by rw [app_nat_of_not_big hdom (max n₀ N), hg.comb, hg.ap], ?_⟩
  exact lt_of_lt_of_leY ha (wnf_oadd hpreF (hF _)) (wnf_oadd hpreF (wnf_nsum (wnf_oadd hc (hF _)) hP))
    (lt_of_le_of_ltY ha (wnf_oadd hpreF ha') (wnf_oadd hpreF (hF _)) hle (oadd_lt_oadd hpreF ha' (hF _) hn))
    (le_approx hpreF hc hP (hF _))

theorem closedS_node {σ T : Tm} : ∀ {x : Tm}, closedS σ T x = true →
    (∃ m a, x = .Xi m a) ∨ ∃ s p a, x = .Psi s p a
  | .zero, h | .one, h | .K _, h | .plus _ _, h | .Om _, h | .Xi _ _, h => by simp [closedS] at h
  | .Psi s p a, _ => Or.inr ⟨s, p, a, rfl⟩

theorem closedPt_node {m : Nat} : ∀ {x : Tm}, closedPt m x = true →
    (∃ m a, x = .Xi m a) ∨ ∃ s p a, x = .Psi s p a
  | .zero, h | .one, h | .K _, h | .plus _ _, h | .Om _, h => by simp [closedPt] at h
  | .Xi n a, _ => Or.inl ⟨n, a, rfl⟩
  | .Psi s p a, _ => Or.inr ⟨s, p, a, rfl⟩

/-- 目標 `τ` を越える `σ` の塔 -/
theorem pass_out {τ σ X G c P : Tm} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (H : DiagHyp .zero σ X G .zero pre rest R r) (hd : r.dom = .big σ) (hRC : SeqC R r) (hσt : IsTgt σ)
    (hτF : WNF τ) (hτt : IsTgt τ) (hτσ : Lt τ σ) (hrT : ∀ q, argR? τ = some q → Lt q (oadd (ofSummands pre) R))
    (hTs : ¬ isSucc (oadd (ofSummands pre) R) = true) (hT0 : oadd (ofSummands pre) R ≠ .zero)
    (hG : G = sStart σ (oadd (ofSummands pre) R) c P) (hcF : WNF c) (hPF : WNF P)
    (hck : c = frCl (closedS σ (oadd (ofSummands pre) R)) τ ∨
      ∃ d, WNF d ∧ c = oadd d (frCl (closedS σ (oadd (ofSummands pre) R)) τ)) :
    ∃ N, Lt τ (gamT .zero σ pre r G .zero (N + 1)) := by
  have Tw := H.tow hd hRC
  have hσF := H.hσF
  refine Tw.tgt_pass hτF hτt hτσ hrT hTs hT0 fun e he => ?_
  have heF := hτF.of_mem_subs (fr_spec he).1
  refine tow_pass_tgt Tw hσt H.hGF (H.gamT_mono 0) (fun u hu => ?_) (fun q hq => ?_) e heF
    (lt_transY heF hτF hσF (fr_spec he).2 hτσ) ?_
  · show Lt u (gamT .zero σ pre r G .zero (0 + 1))
    rw [gamT_succ]
    exact FWOrder.k2t (H.tower 0).2.2.hnf u hu
  · have Ha := (H.tower 1).2.2
    have Ha' : Approx1 .zero σ X .zero pre rest R (r.big (gamT .zero σ pre r G .zero (0 + 1))) := Ha
    have h := Ha'.hr q hq
    rwa [approx_zero_eq Ha'.hx] at h
  · rw [hG]
    exact cf_front (fun _ h => closedS_node h) hτF he hcF hPF hck

/-- 目標 `τ` を越える K の塔 -/
theorem pass_canon {τ X c P : Tm} {m : Nat} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (H : KCanon m X pre rest R r (kStart m c P)) (hd : r.dom = .big (.K m)) (hRC : SeqC R r)
    (hτF : WNF τ) (hτt : IsTgt τ) (hτK : Lt τ (.K m))
    (hrT : ∀ q, argR? τ = some q → Lt q (oadd (ofSummands pre) R))
    (hTs : ¬ isSucc (oadd (ofSummands pre) R) = true) (hT0 : oadd (ofSummands pre) R ≠ .zero)
    (hcF : WNF c) (hPF : WNF P)
    (hck : c = frCl (closedPt m) τ ∨ ∃ d, WNF d ∧ c = oadd d (frCl (closedPt m) τ)) :
    ∃ N, Lt τ (kTow m pre r (kStart m c P) (N + 1)) := by
  have Tw := H.tow hd hRC
  have hKF := H.hKF
  have hKT : Le (.K m) (oadd (ofSummands pre) R) :=
    le_transY hKF H.hRF H.hTF H.hB.1.hσle (le_oadd_right H.hpreF H.hRF)
  refine Tw.tgt_pass hτF hτt hτK hrT hTs hT0 fun e he => ?_
  have heF := hτF.of_mem_subs (fr_spec he).1
  exact tow_pass_K Tw hKT H.hGF (H.mono 0) e heF (lt_transY heF hτF hKF (fr_spec he).2 hτK)
    (cf_front (fun _ h => closedPt_node h) hτF he hcF hPF hck)

/-- 種を外に足す型 -/
theorem argS_out {t ξ τ σ X G P c ceil : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ τ) (H : DiagHyp .zero σ X G .zero pre rest R r) (hne : σ ≠ τ)
    (hG : G = sStart σ (oadd (ofSummands pre) R) c P) (hd : r.dom = .big σ) (hlt : ltB σ ceil = false)
    (hRC : SeqC R r) (hc : WNF c) (hP : WNF P) (htF : WNF t)
    (hpass : ∃ N, Le t (gamT .zero σ pre r G .zero (N + 1))) :
    ArgS t (oadd (ofSummands pre) R) ξ τ (.app ceil g pre R r P c) := by
  intro a N ha haT hC _
  obtain ⟨M, hM⟩ := hpass
  have Tw := H.tow hd hRC
  obtain ⟨n, hn⟩ := Tw.arg (N := M) ha haT (inC_mono_d htF (Tw.hγF M) hM ha hC)
  have hAF : ∀ i, WNF (oadd (ofSummands pre) (r.big (gamT .zero σ pre r G .zero (i + 1)))) := fun i =>
    (Tw.hC i).hA
  have hn' := lt_of_lt_of_leY ha (hAF n) (hAF _) hn (mono_le' hAF Tw.hAm (Nat.le_max_left n N))
  refine ⟨max n N + 1, _, by omega, app_nat_out hg H hne hG hd hlt (max n N + 1), ?_⟩
  have hxF : WNF (r.big (gamT .zero σ pre r G .zero (max n N + 1))) := (H.tower (max n N + 1)).2.2.hx
  exact lt_of_lt_of_leY ha (wnf_oadd H.hpreF hxF) (wnf_oadd H.hpreF (wnf_nsum (wnf_oadd hc hxF) hP)) hn'
    (le_approx H.hpreF hc hP hxF)

/-- 目標そのものへの対角化 -/
theorem argS_in {t ξ τ X P ceil : Tm} {g : Gen} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ τ) (H : DiagHyp ξ τ X .zero P pre rest R r) (hd : r.dom = .big τ)
    (hlt : ltB τ ceil = false) (hRC : SeqC R r) (htF : WNF t)
    (hyt : ∀ n, Lt ((SeqD.app ceil g pre R r P .zero).nat n) t) :
    ArgS t (oadd (ofSummands pre) R) ξ τ (.app ceil g pre R r P .zero) := by
  intro a N ha haT hC hfr
  have he := app_nat_in hg H hd hlt
  have Tw := H.tow hd hRC
  have h1 : inC a a (gamT ξ τ pre r .zero P (N + 1)) = true :=
    inC_of_fr_lt ha htF (Tw.hγF N) ha ha hC (Or.inr (by rw [← he N]; exact hyt N)) (Or.inl rfl)
      fun u hu => by
        rw [← he N]
        exact hfr u hu
  obtain ⟨n, hn⟩ := Tw.arg (N := N) ha haT h1
  have hAF : ∀ i, WNF (oadd (ofSummands pre) (r.big (gamT ξ τ pre r .zero P (i + 1)))) := fun i =>
    (Tw.hC i).hA
  have hn' := lt_of_lt_of_leY ha (hAF n) (hAF _) hn (mono_le' hAF Tw.hAm (Nat.le_max_left n N))
  have hxF : WNF (r.big (gamT ξ τ pre r .zero P (max n N + 1))) := (H.tower (max n N + 1)).2.2.hx
  have e : gamT ξ τ pre r .zero P (max n N + 1 + 1) =
      .Psi ξ τ (approx pre .zero (r.big (gamT ξ τ pre r .zero P (max n N + 1)))) :=
    gamT_succ ξ τ pre r .zero P (max n N + 1)
  refine ⟨max n N + 1, _, by omega, by rw [he, e], ?_⟩
  rw [approx_zero_eq hxF]
  exact hn'

/-- 正準な K の塔 -/
theorem argS_canon {t ξ τ X P c ceil : Tm} {g : Gen} {m d : Nat} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ τ) (H : KCanon m X pre rest R r (kStart m c P)) (hd : r.dom = .big (.K m))
    (hlt : ltB (.K m) ceil = false) (hcan : canonK (.K m) g pre R = true) (hRC : SeqC R r) (hc : WNF c) (hP : WNF P)
    (htF : WNF t) (hpass : ∃ N, Le t (kTow m pre r (kStart m c P) (N + 1))) {s : SeqD}
    (hs : ∀ n, s.nat n = (SeqD.app ceil g pre R r P c).nat (n + d)) :
    ArgS t (oadd (ofSummands pre) R) ξ τ s := by
  intro a N ha haT hC _
  obtain ⟨M, hM⟩ := hpass
  have Tw := H.tow hd hRC
  obtain ⟨n, hn⟩ := Tw.arg (N := M) ha haT (inC_mono_d htF (Tw.hγF M) hM ha hC)
  have hxF : ∀ k, WNF (r.big (kTow m pre r (kStart m c P) k)) := H.x_F
  have hxm : Lt (oadd (ofSummands pre) (r.big (kTow m pre r (kStart m c P) (n + 1))))
      (oadd (ofSummands pre) (r.big (kTow m pre r (kStart m c P) (max (n + 2) N + d)))) := by
    refine oadd_lt_oadd H.hpreF (hxF _) (hxF _) (H.x_lt ?_)
    omega
  refine ⟨max (n + 2) N, approx pre P (oadd c (r.big (kTow m pre r (kStart m c P) (max (n + 2) N + d)))),
    Nat.le_max_right _ _, ?_, ?_⟩
  · rw [hs, app_nat_big hd hlt, gam_canon hcan, argOf_canon hcan, hg.comb, hg.ap]
  · exact lt_of_lt_of_leY ha (wnf_oadd H.hpreF (hxF _)) (wnf_oadd H.hpreF (wnf_nsum (wnf_oadd hc (hxF _)) hP))
      (lt_transY ha (wnf_oadd H.hpreF (hxF _)) (wnf_oadd H.hpreF (hxF _)) hn hxm)
      (le_approx H.hpreF hc hP (hxF _))

/-- 旧方式の K の塔 -/
theorem argS_old {t ξ τ X P c ceil : Tm} {g : Gen} {m : Nat} {pre rest : List Tm} {R : Tm} {r : SeqD}
    (hg : GenPsi g ξ τ) (H : KOld m X c P pre rest R r) (hd : r.dom = .big (.K m))
    (hlt : ltB (.K m) ceil = false) (hold : kOld m pre R = true) (hRC : SeqC R r) :
    ArgS t (oadd (ofSummands pre) R) ξ τ (.app ceil g pre R r P c) := by
  have hN : NFL (pre ++ [R]) := by
    have h := H.hN
    rw [show pre ++ R :: rest = (pre ++ [R]) ++ rest by simp] at h
    exact nfl_append_left h
  have hRC' : ∀ x β, WNF x → Lt x R → WNF β → Lt β (.K m) → Cl (.K m) β → (∀ f, f ∈ fr (.K m) x → Lt f β) →
      Lt x (r.big β) := by
    have := hRC
    unfold SeqC at this
    rwa [hd] at this
  have hyF : ∀ n, WNF (oT m pre r c P n) := fun n => (H.tower n).1
  intro a N ha haT _ _
  obtain ⟨a', ha', ha'R, -, hle⟩ := lt_oadd_split hN ha haT
  obtain ⟨M₀, hM₀⟩ := exists_bound (P := fun _ => True) hyF H.mono (fr (.K m) a')
    (fun f h => ha'.of_mem_subs (fr_spec h).1) fun f h _ => by
      obtain ⟨n, hn⟩ := H.all (ha'.of_mem_subs (fr_spec h).1) (fr_spec h).2
      exact ⟨_, hn⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = max M₀ N := ⟨_, rfl⟩
  have hM : ∀ f, f ∈ fr (.K m) a' → True → Lt f (oT m pre r c P M) := fun f h _ =>
    lt_of_lt_of_leY (ha'.of_mem_subs (fr_spec h).1) (hyF M₀) (hyF M) (hM₀ f h trivial)
      (mono_le hyF H.mono (by omega))
  have hβ := H.tower (M + 1)
  have hCl : Cl (.K m) (oT m pre r c P (M + 1)) := by
    obtain ⟨hγ, hγK⟩ := H.tower M
    rcases H.form hγ hγK with ⟨e, -⟩ | ⟨e, -⟩
    · rw [e]
      exact Cl.of_xi (wnf_xiS H.hm)
    · rw [e]
      exact Cl.of_xi (wnf_virtK H.hm M)
  have h1 := hRC' a' _ ha' ha'R hβ.1 hβ.2 hCl fun f h =>
    lt_transY (ha'.of_mem_subs (fr_spec h).1) (hyF M) hβ.1 (hM f h trivial) (H.mono M)
  have hxF := H.x_F (M + 1)
  refine ⟨M + 1, _, by omega, by rw [app_nat_big hd hlt, gam_old hg hold, argOf_old hg hold, hg.comb, hg.ap], ?_⟩
  exact lt_of_lt_of_leY ha (wnf_oadd H.hpreF hxF) (wnf_oadd H.hpreF (wnf_nsum (wnf_oadd H.hc hxF) H.hP))
    (lt_of_le_of_ltY ha (wnf_oadd H.hpreF ha') (wnf_oadd H.hpreF hxF) hle (oadd_lt_oadd H.hpreF ha' hxF h1))
    (le_approx H.hpreF H.hc H.hP hxF)

end RTKA.Fund
