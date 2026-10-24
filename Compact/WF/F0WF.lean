import Compact.WF.Dist

/-! 断片 `F0` の標準形の整列性（`Classical.choice` も大基数も使わない）。

最大の区別集合 `W`（`Dist.lean`）が `0`・`1`・`+`・`Ω`・`K_n`・`Ψ` について閉じていることを示し、
全ての `F0` の標準形が `W` に入ることを大きさの帰納法で導く。`W` の元は `W` の中で到達可能なので、
`F0` の標準形の上の `<` は整礎になる（`wellFounded_F0`）。

* `W_om`：`Ω_a`。`a ∈ W` についての帰納法で、`one_step` を基数 `Ω_a` に使う。
* `W_K`：`K_n`。`n` についての帰納法で、`one_step` を基数 `K_n` に使う。
* `W_psi`：`Ψ_c(a)`。`a ∈ W` についての帰納法（Arai の Lemma 8.2 にあたる）。区間の下端 `κ` で
  `W` が `C^κ(W)` の到達可能部分と一致することを使い、`Ψ_c(a)` より小さい `C^κ(W)` の元が
  `W` に入ることを、引数の比較（`lt_psi_same_F0`）で場合分けして示す。 -/

namespace RTKA

open Tm

/-! ### 基本の閉包性 -/

theorem D_empty : D (fun _ => False) :=
  ⟨fun _ h => h.elim, fun _ _ ⟨_, h, _⟩ => h.elim⟩

theorem isCard_zero : isCard .zero := ⟨F0NF.zero, rfl⟩

theorem isCard_om {c : Tm} (h : F0NF (.Om c)) : isCard (.Om c) := by
  refine ⟨h, ?_⟩
  unfold bot
  rw [show ix (Tm.Om c) = c from rfl, cardOf_om h]

theorem W_zero : W .zero :=
  W.of_one_step D_empty isCard_zero trivial (fun t _ h _ => absurd h (not_lt_zero t))
    (fun μ _ h => absurd h (not_lt_zero μ))

theorem W_one : W .one := by
  apply (D_W.2 .zero isCard_zero ⟨.zero, W_zero, Le.refl _⟩ .one F0NF.one (Le.refl _)).mpr
  refine ⟨F0NF.one, trivial, Acc.intro _ (fun u ⟨hu, _, hlt⟩ => ?_)⟩
  have := lt_one hu hlt
  subst this
  exact Acc.intro _ (fun v ⟨_, _, hv⟩ => absurd hv (not_lt_zero v))

theorem W_plus {p s : Tm} (hp : W p) (hs : W s) (h : F0NF (.plus p s)) : W (.plus p s) := by
  obtain ⟨hpF, hsF, -, -⟩ := h.plus
  obtain ⟨hκ, hix⟩ := bot_card hpF
  have g : Ge W (bot p) := ⟨p, hp, bot_le hpF⟩
  have hWp := (D_W.2 (bot p) hκ g p hpF (by unfold Bl; rw [hix]; exact Le.refl _)).mp hp
  have hbls : Bl (bot p) s := by
    unfold Bl
    rw [hix]
    have := ix_le_ix hsF h (lt_plus_right h)
    exact this
  have hWs := (D_W.2 (bot p) hκ g s hsF hbls).mp hs
  apply (D_W.2 (bot p) hκ g _ h (by unfold Bl; rw [hix]; exact Le.refl _)).mpr
  refine ⟨h, Or.inr ⟨hWp.2.1, hWs.2.1⟩, ?_⟩
  have key : ∀ s', Acc (RC W (bot p)) s' → F0NF (.plus p s') →
      Acc (RC W (bot p)) (.plus p s') := by
    intro s' hacc
    induction hacc with
    | intro s' _ ih =>
      intro hps'
      refine Acc.intro _ (fun u ⟨hu, hcu, hlt⟩ => ?_)
      rcases lt_plus_cases hps' hu hlt with h1 | rfl | ⟨u', rfl, hu'F, hu's⟩
      · exact hWp.2.2.inv ⟨hu, hcu, h1⟩
      · exact hWp.2.2
      · have hle : Le (bot p) (.plus p u') :=
          Le.trans hκ.1 hpF hu (bot_le hpF) (Or.inr (lt_plus_left hu))
        exact ih u' ⟨hu'F, (CS_plus_of_le hκ.1 hu hle hcu).2, hu's⟩ hu
  exact key s hWs.2.2 h

theorem W.plus_args {a b : Tm} (h : W (.plus a b)) : W a ∧ W b := by
  have hF := h.nf
  obtain ⟨hκ, -⟩ := bot_card hF
  obtain ⟨hca, hcb⟩ := CS_plus_of_le hκ.1 hF (bot_le hF) (D.mem_CS D_W h hκ)
  exact ⟨D.mem_of_CS_lt D_W h hF.plus.1 hca (lt_plus_left hF),
    D.mem_of_CS_lt D_W h hF.plus.2.1 hcb (lt_plus_right hF)⟩

theorem W.om_arg {x : Tm} (h : W (.Om x)) : W x := by
  have hF := h.nf
  obtain ⟨hκ, -⟩ := bot_card hF
  exact D.mem_of_CS_lt D_W h hF.om.1 (CS_om_of_le hκ.1 hF (bot_le hF) (D.mem_CS D_W h hκ))
    hF.om.2.2

theorem isSucc_plus {a b : Tm} (hb0 : b ≠ .zero) (h : isSucc (.plus a b) = true) :
    isSucc b = true := by
  simp only [isSucc, summands_plus] at h ⊢
  cases hsb : summands b with
  | nil => exact absurd hsb (summands_ne_nil hb0)
  | cons x xs => rw [hsb, List.getLast?_cons_cons] at h; rw [← hsb] at h ⊢; exact h

/-- 後者が `W` に入れば前者も入る -/
theorem W_pred : ∀ {c : Tm}, W c → isSucc c = true → W (pred c)
  | .zero, _, h => by simp [isSucc, summands] at h
  | .one, _, _ => W_zero
  | .plus a b, hW, hs => by
    have hF := hW.nf
    obtain ⟨-, -, -, hb0⟩ := hF.plus
    obtain ⟨hWa, hWb⟩ := W.plus_args hW
    have hsb := isSucc_plus hb0 hs
    obtain ⟨e, hpF⟩ := succT_pred hF hs
    cases b with
    | one => exact hWa
    | plus p q =>
      have ih := W_pred hWb hsb
      obtain ⟨hκ, -⟩ := bot_card hF
      have hc : CS W (bot (.plus a (.plus p q))) (pred (.plus a (.plus p q))) := by
        show CS W _ (.plus a (pred (.plus p q)))
        exact Or.inr ⟨D.mem_CS D_W hWa hκ, D.mem_CS D_W ih hκ⟩
      have hlt : Lt (pred (.plus a (.plus p q))) (.plus a (.plus p q)) := by
        have := lt_succT (pred (.plus a (.plus p q)))
        rwa [e] at this
      exact D.mem_of_CS_lt D_W hW hpF hc hlt
    | zero => exact absurd rfl hb0
    | K _ | Om _ | Xi _ _ | Psi _ _ _ => simp [isSucc, summands] at hsb
  | .K _, _, h | .Om _, _, h | .Xi _ _, _, h | .Psi _ _ _, _, h => by
    simp [isSucc, summands] at h

/-! ### 下の閉包と区間の判定 -/

/-- `Ψ_c(e)` は `Ω_c` 未満の基数以上 -/
theorem card_le_psi {μ c e : Tm} (hμ : isCard μ) (ht : F0NF (.Psi .zero (.Om c) e))
    (h : Lt μ (.Om c)) : Le μ (.Psi .zero (.Om c) e) := by
  obtain ⟨-, c', hc', hcF, hs, -⟩ := ht.psi
  cases hc'
  have h1 : Lt (ix μ) c := (card_lt_iff hμ (isCard_om hcF)).mp h
  rcases le_pred (ix_F0NF hμ.1) hcF.om.1 hs h1 with e2 | e2
  · have := bot_eq_of_ix hμ ht (by rw [ix_psi]; exact e2.symm)
    rw [← this]
    exact bot_le ht
  · exact Or.inr (ix_lt_ix hμ.1 ht (by rw [ix_psi]; exact e2))

theorem K_lt_of_lt_om {m : Nat} {a : Tm} (hm : F0NF (.K m)) (hO : F0NF (.Om a))
    (h : Lt (.K m) (.Om a)) : Lt (.K m) a := by
  have haF := hO.om.1
  have hl := lev_le_of_lt hm hO h
  simp only [lev] at hl
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · exact lt_of_lev_lt hm haF (by simp only [lev]; exact hl)
  · rcases tri haF hm with h' | h' | h'
    · exact absurd (lev_lt_of_lt_K haF hm h') (by omega)
    · exact absurd h' hO.om_ne_k
    · exact h'

/-- `Ω_z` が標準形なら `z + 1 < Ω_z` -/
theorem succT_lt_om {z : Tm} (h : F0NF (.Om z)) : Lt (succT z) (.Om z) := by
  have hz := h.om
  cases hs : summands z with
  | nil => exact absurd hs (summands_ne_nil hz.2.1)
  | cons x xs =>
    have hlt : Lt z (.Om z) := hz.2.2
    unfold Lt at hlt ⊢
    rw [cmp_eq, hs, summands_principal' (t := .Om z) rfl] at hlt
    rw [cmp_eq, summands_succT, hs, summands_principal' (t := .Om z) rfl]
    rcases cmpList_lt_cases hlt with e | ⟨-, e'⟩
    · rw [List.cons_append, cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]
    · cases xs with
      | nil => rw [cmpList_nil_nil] at e'; cases e'
      | cons _ _ => rw [cmpList_cons_nil] at e'; cases e'

/-- 下の閉包：`μ ≤ B` で、`B` 未満の `K_m` と `Ω_y`（`y ∈ W`）が `W` に入るなら、
    `C^μ(W) ∩ μ ⊆ W` -/
theorem W_of_CS_lt {B : Tm} (hB : F0NF B)
    (hK : ∀ m, F0NF (.K m) → Lt (.K m) B → W (.K m))
    (hOm : ∀ y, W y → F0NF (.Om y) → Lt (.Om y) B → W (.Om y)) {μ : Tm} (hμ : isCard μ)
    (hμB : Le μ B) : ∀ t, F0NF t → CS W μ t → Lt t μ → W t
  | .zero, _, _, _ => W_zero
  | .one, _, _, _ => W_one
  | .K m, ht, _, hlt => hK m ht (lt_of_lt_of_le ht hμ.1 hB hlt hμB)
  | .plus a b, ht, hc, hlt => by
    rcases hc with ⟨-, h⟩ | ⟨ha, hb⟩
    · exact h
    · obtain ⟨haF, hbF, -, -⟩ := ht.plus
      exact W_plus
        (W_of_CS_lt hB hK hOm hμ hμB a haF ha (lt_trans_F0 haF ht hμ.1 (lt_plus_left ht) hlt))
        (W_of_CS_lt hB hK hOm hμ hμB b hbF hb (lt_trans_F0 hbF ht hμ.1 (lt_plus_right ht) hlt)) ht
  | .Om a, ht, hc, hlt => by
    rcases hc with ⟨-, h⟩ | ha
    · exact h
    · have haF := ht.om.1
      have hW := W_of_CS_lt hB hK hOm hμ hμB a haF ha (lt_trans_F0 haF ht hμ.1 ht.om.2.2 hlt)
      exact hOm a hW ht (lt_of_lt_of_le ht hμ.1 hB hlt hμB)
  | .Xi _ _, ht, _, _ => (ht.not_xi).elim
  | .Psi s p e, ht, hc, hlt => by
    rcases hc with ⟨-, h⟩ | ⟨hp, -⟩
    · exact h
    · obtain ⟨rfl, c, rfl, -⟩ := ht.psi
      exact absurd hlt (not_lt_of_le hμ.1 ht (card_le_psi hμ ht hp))

/-- 区間の判定：`C^μ(W)` の元が `μ` の区間に入れば `μ ≤ W` -/
theorem ge_of_CS {B : Tm} (hB : F0NF B)
    (hK : ∀ m, F0NF (.K m) → Lt (.K m) B → W (.K m))
    (hOm : ∀ y, W y → F0NF (.Om y) → Lt (.Om y) B → W (.Om y)) {μ : Tm} (hμ : isCard μ)
    (hμB : Lt μ B) : ∀ t, F0NF t → CS W μ t → ix t = ix μ → Ge W μ := by
  have hWge : ∀ t, F0NF t → W t → ix t = ix μ → Ge W μ := by
    intro t ht hW e
    refine ⟨t, hW, ?_⟩
    rw [← bot_eq_of_ix hμ ht e]
    exact bot_le ht
  intro t
  induction t with
  | zero => intro ht _ e; exact hWge _ ht W_zero e
  | one => intro ht _ e; exact hWge _ ht W_one e
  | K m =>
    intro ht _ e
    have hμe : μ = .K m := (bot_eq_of_ix hμ ht e).symm
    subst hμe
    exact hWge _ ht (hK m ht hμB) e
  | plus a b iha _ =>
    intro ht hc e
    rcases hc with ⟨-, h⟩ | ⟨ha, -⟩
    · exact hWge _ ht h e
    · exact iha ht.plus.1 ha e
  | Om a _ =>
    intro ht hc e
    rcases hc with ⟨-, h⟩ | ha
    · exact hWge _ ht h e
    · have hμe : μ = .Om a := by
        rw [← bot_eq_of_ix hμ ht e]
        exact cardOf_om ht
      subst hμe
      have hWa := W_of_CS_lt hB hK hOm hμ (Or.inr hμB) a ht.om.1 ha ht.om.2.2
      exact hWge _ ht (hOm a hWa ht hμB) e
  | Xi _ _ _ => intro ht; exact (ht.not_xi).elim
  | Psi s p β _ _ _ =>
    intro ht hc e
    rcases hc with ⟨-, h⟩ | ⟨hp, -, hpc, -⟩
    · exact hWge _ ht h e
    · obtain ⟨rfl, c, rfl, hcF, hs, -⟩ := ht.psi
      have hμe : μ = cardOf (pred c) := (bot_eq_of_ix hμ ht e).symm
      have hcc : CS W μ c := (CS_om_iff hμ.1 hcF hp).mp hpc
      refine ⟨μ, ?_, Le.refl _⟩
      obtain ⟨e', hpF⟩ := succT_pred hcF.om.1 hs
      rcases isIdx_pred hcF.om.1 hs with h0 | ⟨m, hm, hm1⟩ | hO
      · rw [hμe, h0]; exact W_zero
      · rw [hμe, hm]
        rw [hμe, hm] at hμB
        exact hK m (F0NF.K' hm1) hμB
      · have hμO : μ = .Om (pred c) := by rw [hμe, cardOf_om hO]
        have hcμ : Lt c μ := by
          rw [hμO]
          have := succT_lt_om hO
          rwa [e'] at this
        have hWc := W_of_CS_lt hB hK hOm hμ (Or.inr hμB) c hcF.om.1 hcc hcμ
        have hWp := W_pred hWc hs
        rw [hμO]
        rw [hμO] at hμB
        exact hOm _ hWp hO hμB

/-- 下の区間の条件（`one_step` の `GC`） -/
theorem gc_W {B : Tm} (hB : F0NF B)
    (hK : ∀ m, F0NF (.K m) → Lt (.K m) B → W (.K m))
    (hOm : ∀ y, W y → F0NF (.Om y) → Lt (.Om y) B → W (.Om y)) :
    ∀ μ, isCard μ → Lt μ B → ∀ t, F0NF t → Bl μ t → (W t ↔ WC W μ t) := by
  intro μ hμ hμB t ht hb
  have hle : Le μ B := Or.inr hμB
  rcases (show Le (ix t) (ix μ) from hb) with e | e
  · constructor
    · intro hW
      have g : Ge W μ := ⟨t, hW, by rw [← bot_eq_of_ix hμ ht e]; exact bot_le ht⟩
      exact (D_W.2 μ hμ g t ht hb).mp hW
    · intro hWC
      have g : Ge W μ := ge_of_CS hB hK hOm hμ hμB t ht hWC.2.1 e
      exact (D_W.2 μ hμ g t ht hb).mpr hWC
  · have htμ : Lt t μ := ix_lt_ix ht hμ.1 e
    constructor
    · intro hW
      refine ⟨ht, CS.base htμ hW, ?_⟩
      refine acc_transfer (fun v => F0NF v ∧ Le v t) ?_ ?_ t (acc_W hW) ⟨ht, Le.refl _⟩
      · rintro u v ⟨hu, -, huv⟩ ⟨hv, hvt⟩
        exact ⟨hu, Or.inr (lt_of_lt_of_le hu hv ht huv hvt)⟩
      · rintro u v ⟨hu, hcu, huv⟩ ⟨hv, hvt⟩
        have hut := lt_of_lt_of_le hu hv ht huv hvt
        exact ⟨W_of_CS_lt hB hK hOm hμ hle u hu hcu (lt_trans_F0 hu ht hμ.1 hut htμ), huv⟩
    · intro hWC
      exact W_of_CS_lt hB hK hOm hμ hle t ht hWC.2.1 htμ

/-! ### `Ω` と `K_n` -/

theorem W_om_aux : ∀ a, Acc (RX W) a → W a → F0NF (.Om a) → W (.Om a) := by
  intro a hacc
  induction hacc with
  | intro a _ ih =>
    intro ha hO
    have hK : ∀ m, F0NF (.K m) → Lt (.K m) (.Om a) → W (.K m) := fun m hm hlt =>
      D.mem_of_CS_lt D_W ha hm trivial (K_lt_of_lt_om hm hO hlt)
    have hOm : ∀ y, W y → F0NF (.Om y) → Lt (.Om y) (.Om a) → W (.Om y) := fun y hy hyO hlt =>
      ih y ⟨hy, (lt_om_iff hyO.om.1 hO.om.1).mp hlt⟩ hy hyO
    exact W.of_one_step D_W (isCard_om hO) (Or.inr (CS.base hO.om.2.2 ha))
      (fun t ht hlt hc => W_of_CS_lt hO hK hOm (isCard_om hO) (Le.refl _) t ht hc hlt)
      (gc_W hO hK hOm)

theorem W_om {a : Tm} (ha : W a) (hO : F0NF (.Om a)) : W (.Om a) :=
  W_om_aux a (acc_W ha) ha hO

theorem lt_of_K_lt_K {m n : Nat} (h : Lt (.K m) (.K n)) : m < n := by
  rcases Nat.lt_trichotomy m n with h' | h' | h'
  · exact h'
  · subst h'; exact absurd h (Lt.irrefl _)
  · rw [lt_principal_iff rfl rfl, cmpP_of_lev_gt (by simp only [lev]; omega)] at h
    cases h

theorem W_K_aux : ∀ n m, 1 ≤ m → m < n → W (.K m) := by
  intro n
  induction n with
  | zero => intro m _ h; exact absurd h (Nat.not_lt_zero m)
  | succ n ih =>
    intro m hm h
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h | rfl
    · exact ih m hm h
    · have hKF : F0NF (.K m) := F0NF.K' hm
      have hK : ∀ m', F0NF (.K m') → Lt (.K m') (.K m) → W (.K m') := fun m' hm' hlt =>
        ih m' hm'.k (lt_of_K_lt_K hlt)
      have hOm : ∀ y, W y → F0NF (.Om y) → Lt (.Om y) (.K m) → W (.Om y) := fun y hy hyO _ =>
        W_om hy hyO
      exact W.of_one_step D_W ⟨hKF, rfl⟩ trivial
        (fun t ht hlt hc => W_of_CS_lt hKF hK hOm ⟨hKF, rfl⟩ (Le.refl _) t ht hc hlt)
        (gc_W hKF hK hOm)

theorem W_K {m : Nat} (hm : 1 ≤ m) : W (.K m) := W_K_aux (m + 1) m hm (Nat.lt_succ_self m)

/-! ### `Ψ` -/

theorem W_cardOf_pred {c : Tm} (hc : W c) (hs : isSucc c = true) : W (cardOf (pred c)) := by
  have hp := W_pred hc hs
  rcases isIdx_pred hc.nf hs with h0 | ⟨m, hm, hm1⟩ | hO
  · rw [h0]; exact W_zero
  · rw [hm]; exact W_K hm1
  · rw [cardOf_om hO]; exact W_om hp hO

theorem CS_W_plus {κ a b : Tm} (hκ : isCard κ) (h : CS W κ (.plus a b)) : CS W κ a ∧ CS W κ b := by
  rcases h with ⟨-, hW⟩ | h
  · obtain ⟨ha, hb⟩ := W.plus_args hW
    exact ⟨D.mem_CS D_W ha hκ, D.mem_CS D_W hb hκ⟩
  · exact h

theorem CS_W_om {κ x : Tm} (hκ : isCard κ) (h : CS W κ (.Om x)) : CS W κ x := by
  rcases h with ⟨-, hW⟩ | h
  · exact D.mem_CS D_W hW.om_arg hκ
  · exact h

/-- `Ψ_c(a) ≤ Ψ_e(β) < Ω_c` なら `e = c` -/
theorem eq_of_psi_between {c e a β : Tm} (hα : F0NF (.Psi .zero (.Om c) a))
    (ht : F0NF (.Psi .zero (.Om e) β)) (h1 : ¬ Lt (.Psi .zero (.Om e) β) (.Psi .zero (.Om c) a))
    (h2 : Lt (.Psi .zero (.Om e) β) (.Om c)) : e = c := by
  obtain ⟨-, c', hc', hcF, hcs, -⟩ := hα.psi
  cases hc'
  obtain ⟨-, e', he', heF, hes, -⟩ := ht.psi
  cases he'
  have hle1 : Le (pred c) (pred e) := by
    have := ix_le_ix' hα ht (le_of_not_lt hα ht h1)
    rwa [ix_psi, ix_psi] at this
  have hlt : Lt (pred e) c := by
    rcases ix_le_ix ht hcF h2 with e2 | e2
    · exfalso
      have hb := bot_eq_of_ix (isCard_om hcF) ht e2
      exact not_lt_of_le hcF ht (by rw [← hb]; exact bot_le ht) h2
    · rw [ix_psi] at e2
      exact e2
  have hpe := (succT_pred heF.om.1 hes).2
  have hpc := (succT_pred hcF.om.1 hcs).2
  have hle2 := le_pred hpe hcF.om.1 hcs hlt
  have e3 := Le.antisymm hpc hpe hle1 hle2
  rw [← (succT_pred heF.om.1 hes).1, ← (succT_pred hcF.om.1 hcs).1, e3]

/-- `bot (Ψ_c(a)) < Ω_e` で `Ψ_e(b) < Ψ_c(a)` なら `e = c` -/
theorem eq_of_psi_gen {c e a b : Tm} (hα : F0NF (.Psi .zero (.Om c) a))
    (hu : F0NF (.Psi .zero (.Om e) b)) (h1 : Lt (bot (.Psi .zero (.Om c) a)) (.Om e))
    (h2 : Lt (.Psi .zero (.Om e) b) (.Psi .zero (.Om c) a)) : e = c := by
  obtain ⟨-, c', hc', hcF, hcs, -⟩ := hα.psi
  cases hc'
  obtain ⟨-, e', he', heF, hes, -⟩ := hu.psi
  cases he'
  obtain ⟨hκ, hix⟩ := bot_card hα
  have h3 : Lt (pred c) e := by
    have := (card_lt_iff hκ (isCard_om heF)).mp h1
    rw [hix, ix_psi] at this
    exact this
  have hpe := (succT_pred heF.om.1 hes).2
  have hpc := (succT_pred hcF.om.1 hcs).2
  have hle1 := le_pred hpc heF.om.1 hes h3
  have hle2 : Le (pred e) (pred c) := by
    have := ix_le_ix hu hα h2
    rwa [ix_psi, ix_psi] at this
  have e3 := Le.antisymm hpc hpe hle1 hle2
  rw [← (succT_pred heF.om.1 hes).1, ← (succT_pred hcF.om.1 hcs).1, e3]

/-- 場合 B の探索：`a < b` で `a` が `C(b, Ψ_c(b))` に入らないなら、`Ψ_c(b) ≤ w < Ψ_c(a)` となる
    `w ∈ W` がある（`a` の成分を `Ω_c` 以上の `Ψ` を通って辿る） -/
theorem find_w {c a b : Tm} (hα : F0NF (.Psi .zero (.Om c) a))
    (hu : F0NF (.Psi .zero (.Om c) b)) (hab : Lt a b) :
    ∀ t, F0NF t → inC t a (.Om c) = true → inC t a (.Psi .zero (.Om c) a) = true →
      inC t b (.Psi .zero (.Om c) b) = false → CS W (.Om c) t →
      ∃ w, W w ∧ Le (.Psi .zero (.Om c) b) w ∧ Lt w (.Psi .zero (.Om c) a) := by
  obtain ⟨-, c', hc', hcF, -, haF, -⟩ := hα.psi
  cases hc'
  obtain ⟨-, -, -, -, -, hbF, -⟩ := hu.psi
  have hcc := isCard_om hcF
  have LC : ∀ t, F0NF t → CS W (.Om c) t → Lt t (.Om c) → W t :=
    W_of_CS_lt hcF (fun m hm _ => W_K hm.k) (fun y hy hyO _ => W_om hy hyO) hcc (Le.refl _)
  have hαc : Lt (.Psi .zero (.Om c) a) (.Om c) := lt_psi_om_self c a
  intro t
  induction t with
  | zero => intro _ _ _ h; rw [inC_zero] at h; cases h
  | one => intro _ _ _ h; rw [inC_one] at h; cases h
  | K m => intro _ _ _ h; rw [inC_K] at h; cases h
  | plus t1 t2 ih1 ih2 =>
    intro ht h1 h2 h3 hcs
    obtain ⟨hc1, hc2⟩ := CS_W_plus hcc hcs
    rw [inC_plus, Bool.and_eq_true] at h1 h2
    rw [inC_plus] at h3
    cases e1 : inC t1 b (.Psi .zero (.Om c) b)
    · exact ih1 ht.plus.1 h1.1 h2.1 e1 hc1
    · rw [e1, Bool.true_and] at h3
      exact ih2 ht.plus.2.1 h1.2 h2.2 h3 hc2
  | Om x ihx =>
    intro ht h1 h2 h3 hcs
    rw [inC_om] at h1 h2 h3
    exact ihx ht.om.1 h1 h2 h3 (CS_W_om hcc hcs)
  | Xi _ _ _ => intro ht; exact (ht.not_xi).elim
  | Psi s p β _ ihp ihβ =>
    intro ht h1 h2 h3 hcs
    obtain ⟨rfl, e, rfl, heF, -, hβF, -⟩ := ht.psi
    have hnu : ¬ Lt (.Psi .zero (.Om e) β) (.Psi .zero (.Om c) b) := by
      intro h
      rw [inC_psi_iff.mpr (Or.inl h)] at h3
      cases h3
    by_cases hlt : Lt (.Psi .zero (.Om e) β) (.Om c)
    · refine ⟨_, LC _ ht hcs hlt, le_of_not_lt hu ht hnu, ?_⟩
      by_cases htα : Lt (.Psi .zero (.Om e) β) (.Psi .zero (.Om c) a)
      · exact htα
      · exfalso
        have hec := eq_of_psi_between hα ht htα hlt
        subst hec
        rcases inC_psi_iff.mp h2 with h | ⟨-, -, hβin, hβa⟩
        · exact htα h
        · have hne : β ≠ a := fun e => by subst e; exact Lt.irrefl _ hβa
          exact htα ((lt_psi_same_F0 ht hα hne).mpr (Or.inl ⟨hβa, hβin⟩))
    · have htα : ¬ Lt (.Psi .zero (.Om e) β) (.Psi .zero (.Om c) a) :=
        fun h => hlt (lt_trans_F0 ht hα hcF h hαc)
      obtain ⟨hpa, -, hβa, hβlt⟩ := inC_params h1 hlt
      obtain ⟨hpα, -, hβα, -⟩ := inC_params h2 htα
      have hle : Le (.Om c) (.Psi .zero (.Om e) β) := le_of_not_lt hcF ht hlt
      obtain ⟨-, -, hpc, hβc⟩ := CS_psi_of_le hcF ht hle hcs
      have hβb : Lt β b := lt_trans_F0 hβF haF hbF hβlt hab
      cases e1 : inC (.Om e) b (.Psi .zero (.Om c) b)
      · exact ihp heF hpa hpα e1 hpc
      · cases e2 : inC β b (.Psi .zero (.Om c) b)
        · exact ihβ hβF hβa hβα e2 hβc
        · exfalso
          rw [inC_psi_iff.mpr (Or.inr ⟨e1, inC_zero _ _, e2, hβb⟩)] at h3
          cases h3

/-- `Ψ_c(a)` より小さい `C^κ(W)` の元は `W` に入る（`κ` は `Ψ_c(a)` の区間の下端。Arai の
    Claim 8.3 にあたる） -/
theorem below_psi {a c : Tm} (hα : F0NF (.Psi .zero (.Om c) a)) (ha : W a) (hc : W c)
    (MIH : ∀ b, W b → Lt b a → ∀ e, W e → F0NF (.Psi .zero (.Om e) b) →
      W (.Psi .zero (.Om e) b)) :
    ∀ n u, u.size ≤ n → F0NF u → CS W (bot (.Psi .zero (.Om c) a)) u →
      Lt u (.Psi .zero (.Om c) a) → W u := by
  obtain ⟨-, c', hc', hcF, -, haF, hCa, -⟩ := hα.psi
  cases hc'
  obtain ⟨hκ, hix⟩ := bot_card hα
  have hκα : Le (bot (.Psi .zero (.Om c) a)) (.Psi .zero (.Om c) a) := bot_le hα
  intro n
  induction n with
  | zero => intro u hs; exact absurd hs (by have := Tm.size_pos u; omega)
  | succ n ih =>
    -- 場合 A の引数（`C(a, Ψ_c(a))` に入る項）は `W` に入る
    have arg : ∀ s, F0NF s → CS W (bot (.Psi .zero (.Om c) a)) s →
        inC s a (.Psi .zero (.Om c) a) = true → s.size ≤ n → W s := by
      intro s
      induction s with
      | zero => intros; exact W_zero
      | one => intros; exact W_one
      | K m => intro hs _ _ _; exact W_K hs.k
      | plus s1 s2 ih1 ih2 =>
        intro hs hcs hin hsz
        by_cases hlt : Lt (.plus s1 s2) (.Psi .zero (.Om c) a)
        · exact ih _ hsz hs hcs hlt
        · have hle := Le.trans hκ.1 hα hs hκα (le_of_not_lt hα hs hlt)
          obtain ⟨hc1, hc2⟩ := CS_plus_of_le hκ.1 hs hle hcs
          rw [inC_plus, Bool.and_eq_true] at hin
          simp only [Tm.size] at hsz
          exact W_plus (ih1 hs.plus.1 hc1 hin.1 (by omega)) (ih2 hs.plus.2.1 hc2 hin.2 (by omega)) hs
      | Om x ihx =>
        intro hs hcs hin hsz
        by_cases hlt : Lt (.Om x) (.Psi .zero (.Om c) a)
        · exact ih _ hsz hs hcs hlt
        · have hle := Le.trans hκ.1 hα hs hκα (le_of_not_lt hα hs hlt)
          rw [inC_om] at hin
          simp only [Tm.size] at hsz
          exact W_om (ihx hs.om.1 (CS_om_of_le hκ.1 hs hle hcs) hin (by omega)) hs
      | Xi _ _ _ => intro hs; exact (hs.not_xi).elim
      | Psi s' p b' _ ihp ihb =>
        intro hs hcs hin hsz
        by_cases hlt : Lt (.Psi s' p b') (.Psi .zero (.Om c) a)
        · exact ih _ hsz hs hcs hlt
        · obtain ⟨rfl, e, rfl, heF, -, hbF, -⟩ := hs.psi
          have hle := Le.trans hκ.1 hα hs hκα (le_of_not_lt hα hs hlt)
          obtain ⟨-, -, hpc, hbc⟩ := CS_psi_of_le hκ.1 hs hle hcs
          obtain ⟨hinp, -, hinb, hba⟩ := inC_params hin hlt
          simp only [Tm.size] at hsz
          have hWe : W e := (ihp heF hpc hinp (by simp only [Tm.size]; omega)).om_arg
          exact MIH b' (ihb hbF hbc hinb (by omega)) hba e hWe hs
    intro u hsz hu hcu hlt
    have hcu0 := hcu
    cases u with
    | zero => exact W_zero
    | one => exact W_one
    | K m => exact W_K hu.k
    | plus u1 u2 =>
      rcases hcu with ⟨-, h⟩ | ⟨h1, h2⟩
      · exact h
      · simp only [Tm.size] at hsz
        exact W_plus
          (ih u1 (by omega) hu.plus.1 h1 (lt_trans_F0 hu.plus.1 hu hα (lt_plus_left hu) hlt))
          (ih u2 (by omega) hu.plus.2.1 h2 (lt_trans_F0 hu.plus.2.1 hu hα (lt_plus_right hu) hlt))
          hu
    | Om x =>
      rcases hcu with ⟨-, h⟩ | h1
      · exact h
      · simp only [Tm.size] at hsz
        exact W_om (ih x (by omega) hu.om.1 h1 (lt_trans_F0 hu.om.1 hu hα hu.om.2.2 hlt)) hu
    | Xi _ _ => exact (hu.not_xi).elim
    | Psi s p b =>
      rcases hcu with ⟨-, h⟩ | ⟨hp, -, -, hbc⟩
      · exact h
      · obtain ⟨rfl, e, rfl, -, -, hbF, -⟩ := hu.psi
        have hec : e = c := eq_of_psi_gen hα hu hp hlt
        subst hec
        have hne : b ≠ a := fun h => by subst h; exact Lt.irrefl _ hlt
        rcases (lt_psi_same_F0 hu hα hne).mp hlt with ⟨hba, hin⟩ | ⟨hab, hfail⟩
        · simp only [Tm.size] at hsz
          exact MIH b (arg b hbF hbc hin (by omega)) hba _ hc hu
        · obtain ⟨w, hw, huw, hwα⟩ := find_w hα hu hab a haF hCa (k2_ic_F0 hα).1 hfail
            (D.mem_CS D_W ha (isCard_om hcF))
          rcases huw with rfl | huw
          · exact hw
          · have hwF := hw.nf
            have hixw : ix w = ix (.Psi .zero (.Om e) a) := by
              have h1 := ix_le_ix hu hwF huw
              have h2 := ix_le_ix hwF hα hwα
              rw [ix_psi] at h1
              rw [ix_psi] at h2 ⊢
              exact Le.antisymm (ix_F0NF hwF) (ix_F0NF hu) h2 h1
            have hbw : bot w = bot (.Psi .zero (.Om e) a) := by
              unfold bot
              rw [hixw]
            exact D.mem_of_CS_lt D_W hw hu (by rw [hbw]; exact hcu0) huw

theorem W_psi_aux : ∀ a, Acc (RX W) a → W a → ∀ c, W c → F0NF (.Psi .zero (.Om c) a) →
    W (.Psi .zero (.Om c) a) := by
  intro a hacc
  induction hacc with
  | intro a _ MIH =>
    intro ha c hc hα
    obtain ⟨-, c', hc', hcF, hcs, -⟩ := hα.psi
    cases hc'
    have MIH' : ∀ b, W b → Lt b a → ∀ e, W e → F0NF (.Psi .zero (.Om e) b) →
        W (.Psi .zero (.Om e) b) :=
      fun b hb hba e he hbe => MIH b ⟨hb, hba⟩ hb e he hbe
    obtain ⟨hκ, hix⟩ := bot_card hα
    have hWκ : W (bot (.Psi .zero (.Om c) a)) := W_cardOf_pred hc hcs
    have g : Ge W (bot (.Psi .zero (.Om c) a)) := ⟨_, hWκ, Le.refl _⟩
    have hblα : Bl (bot (.Psi .zero (.Om c) a)) (.Psi .zero (.Om c) a) := by
      unfold Bl
      rw [hix]
      exact Le.refl _
    have hκc : Lt (bot (.Psi .zero (.Om c) a)) (.Om c) :=
      lt_of_le_of_lt hκ.1 hα hcF (bot_le hα) (lt_psi_om_self c a)
    apply (D_W.2 _ hκ g _ hα hblα).mpr
    refine ⟨hα, Or.inr ⟨hκc, trivial, (CS_om_iff hκ.1 hcF hκc).mpr (D.mem_CS D_W hc hκ),
      D.mem_CS D_W ha hκ⟩, Acc.intro _ (fun u ⟨hu, hcu, hlt⟩ => ?_)⟩
    have hWu := below_psi hα ha hc MIH' _ u (Nat.le_refl _) hu hcu hlt
    have hblu : Bl (bot (.Psi .zero (.Om c) a)) u := by
      unfold Bl
      rw [hix]
      exact ix_le_ix hu hα hlt
    exact ((D_W.2 _ hκ g u hu hblu).mp hWu).2.2

theorem W_psi {a c : Tm} (ha : W a) (hc : W c) (hα : F0NF (.Psi .zero (.Om c) a)) :
    W (.Psi .zero (.Om c) a) :=
  W_psi_aux a (acc_W ha) ha c hc hα

/-! ### 整列性 -/

/-- `F0` の標準形は全て `W` に入る -/
theorem W_all : ∀ n t, t.size ≤ n → F0NF t → W t := by
  intro n
  induction n with
  | zero => intro t h; exact absurd h (by have := Tm.size_pos t; omega)
  | succ n ih =>
    intro t hsz ht
    cases t with
    | zero => exact W_zero
    | one => exact W_one
    | K m => exact W_K ht.k
    | plus a b =>
      simp only [Tm.size] at hsz
      exact W_plus (ih a (by omega) ht.plus.1) (ih b (by omega) ht.plus.2.1) ht
    | Om a =>
      simp only [Tm.size] at hsz
      exact W_om (ih a (by omega) ht.om.1) ht
    | Xi _ _ => exact (ht.not_xi).elim
    | Psi s p a =>
      obtain ⟨rfl, c, rfl, hcF, -, haF, -⟩ := ht.psi
      simp only [Tm.size] at hsz
      exact W_psi (ih a (by omega) haF) (ih c (by omega) hcF.om.1) ht

theorem F0NF.W {t : Tm} (h : F0NF t) : W t := W_all _ t (Nat.le_refl _) h

/-- `F0` の標準形は `<` について到達可能 -/
theorem acc_F0 {t : Tm} (ht : F0NF t) : Acc (fun u v => F0NF u ∧ Lt u v) t :=
  acc_transfer (fun _ => True) (fun _ _ _ _ => trivial)
    (fun _ _ ⟨hu, huv⟩ _ => ⟨hu.W, huv⟩) t (acc_W ht.W) trivial

/-- `F0` の標準形の上の `<` は整礎 -/
theorem wellFounded_F0 : WellFounded (fun a b : {t : Tm // F0NF t} => Lt a.1 b.1) := by
  constructor
  rintro ⟨t, ht⟩
  have key : ∀ t, Acc (fun u v => F0NF u ∧ Lt u v) t → ∀ ht : F0NF t,
      Acc (fun a b : {t : Tm // F0NF t} => Lt a.1 b.1) ⟨t, ht⟩ := by
    intro t h
    induction h with
    | intro t _ ih =>
      intro ht
      exact Acc.intro _ (fun ⟨u, hu⟩ hlt => ih u ⟨hu, hlt⟩ hu)
  exact key t (acc_F0 ht) ht

end RTKA
