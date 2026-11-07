import Compact.FS.Good

/-! 前線による比較の道具と、後者の引数の崩壊の列の最初の分岐。

* `psi_lt_psi_of_arg`：同じ目標・同じ Mahlo 添字の崩壊の比較（Prop. 4.20 の (1)）を、小さい方の引数の前線
  （目標について）で言い換える。前線の元が全て大きい方の崩壊未満なら、引数の大小がそのまま崩壊の大小になる。
* `psi_lt_psi_succ`：後者の種 `Ψ^ξ_τ(Y) < Ψ^ξ_τ(Y+1)`。
* 目標が `Ω_c` で引数が後者 `Y+1` のとき、`Y` に種 `Ψ^0_{Ω_c}(Y)` より大きい加数がなければ、列は種の倍数
  `[n] = Ψ^0_{Ω_c}(Y)·(n+1)` で、良い。 -/

namespace RTKA.Fund

open Tm W

/-- `x ∈ C(g0, R)` で、`x` の前線（`R` について）の元が全て `d` 未満なら、`d ≤ R`・`g0 ≤ g` のとき `x ∈ C(g, d)` -/
theorem inC_of_fr_lt {x g0 g d R : Tm} (hx : WNF x) (hR : WNF R) (hd : WNF d) (hg0 : WNF g0) (hg : WNF g)
    (h0 : inC x g0 R = true) (hdR : Le d R) (hgg : Le g0 g) (hfr : ∀ w, w ∈ fr R x → Lt w d) :
    inC x g d = true :=
  (inC_frY hx hR hd hg0 hg h0 hdR hgg).mpr fun w hw =>
    WFY.inC_of_ltY g (hx.of_mem_subs (fr_spec hw).1) hd (hfr w hw)

/-- 同じ目標・同じ Mahlo 添字の崩壊の比較：`a < b` で、`a` の前線（目標について）の元が全て `Ψ^ξ_τ(b)` 未満なら
    `Ψ^ξ_τ(a) < Ψ^ξ_τ(b)` -/
theorem psi_lt_psi_of_arg {ξ τ a b : Tm} (ha : WNF (.Psi ξ τ a)) (hb : WNF (.Psi ξ τ b)) (hab : Lt a b)
    (hfr : ∀ w, w ∈ fr τ a → Lt w (.Psi ξ τ b)) : Lt (.Psi ξ τ a) (.Psi ξ τ b) := by
  have hPa := ha.psi
  have hPb := hb.psi
  have hne : Tm.Psi ξ τ a ≠ .Psi ξ τ b := fun e => by cases e; exact Lt.irrefl _ hab
  rw [lt_psi_psiY rfl hne]
  have hbτ : Lt (.Psi ξ τ b) τ := lt_psi_targetY hb
  have hleτ : Le (.Psi ξ τ b) τ := Or.inr hbτ
  refine Or.inr ⟨hbτ, lt_psi_targetY ha, Or.inl ⟨hab, ?_, ?_, ?_⟩⟩
  · exact inC_of_fr_lt hPa.aF hPa.piF hb hPa.aF hPb.aF hPa.Ca hleτ (Or.inr hab) hfr
  · exact inC_of_fr_lt hPb.xiF hPb.piF hb hPb.aF hPb.aF hPb.Cxi hleτ (Or.inl rfl)
      (fun w hw => FWOrder.k2s hb w hw)
  · exact inC_of_fr_lt hPb.piF hPb.piF hb hPb.aF hPb.aF hPb.Cpi hleτ (Or.inl rfl)
      (fun w hw => FWOrder.k2t hb w hw)

theorem fr_succT (R : Tm) : ∀ z : Tm, fr R (succT z) = fr R z
  | .zero => rfl
  | .plus a b => by
    show fr R (.plus a (succT b)) = fr R (.plus a b)
    simp only [fr, fr_succT R b]
  | .one | .K _ | .Om _ | .Xi _ _ | .Psi _ _ _ => by
    show fr R (.plus _ .one) = _
    simp [fr]

/-- 後者の種：`Ψ^ξ_τ(Y) < Ψ^ξ_τ(Y+1)` -/
theorem psi_lt_psi_succ {ξ τ Y : Tm} (h0 : WNF (.Psi ξ τ Y)) (h1 : WNF (.Psi ξ τ (succT Y))) :
    Lt (.Psi ξ τ Y) (.Psi ξ τ (succT Y)) :=
  psi_lt_psi_of_arg h0 h1 (lt_succT Y) (fun w hw => FWOrder.k2 h1 w (by rw [fr_succT]; exact hw))

/-! ### 解析の加数の最後の記述 -/

theorem sums_ne_nil {X : Tm} (hX0 : X ≠ zero) : (info X).sums ≠ [] := by
  intro e
  have := info_sums_fst X
  rw [e] at this
  exact summands_ne_nil hX0 this.symm

theorem lastS_cons {p : Tm × SeqD} {l : DL} (hl : l ≠ []) : lastS (p :: l) = lastS l := by
  obtain ⟨q, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  simp only [lastS, List.getLast?_cons_cons]

/-- 0 でない項の共終数は、最後の加数の記述の共終数 -/
theorem lastS_dom : ∀ {X : Tm}, WNF X → X ≠ zero → (lastS (info X).sums).dom = dom X
  | .zero, _, h => absurd rfl h
  | .plus a b, hX, _ => by
    obtain ⟨-, hb, -, hb0⟩ := hX.plus
    show (lastS ((a, (info a).seq) :: (info b).sums)).dom = dom b
    rw [lastS_cons (sums_ne_nil hb0)]
    exact lastS_dom hb hb0
  | .one, _, _ | .K _, _, _ | .Om _, _, _ | .Xi _ _, _, _ | .Psi _ _ _, _, _ => rfl

/-! ### 後者の引数の崩壊の、前の引数の崩壊（種） -/

/-- `X` の加数の前の部分（`pred X`）は、`X ∈ C(X, d)` なら `C(pred X, d)` に入る（大きさの議論） -/
theorem inC_pred_self {X d : Tm} (hX : WNF X) (hs : isSucc X = true) (h : inC X X d = true) :
    inC (pred X) (pred X) d = true := by
  have hpX := wnf_pred hX
  have h1 : inC (pred X) X d = true := by
    unfold pred
    rw [inC_ofSummands]
    intro s hsm
    exact inC_of_mem_summands hX h (List.dropLast_subset _ hsm)
  have h2 : inC (pred X) (succT (pred X)) d = true := by rw [succT_pred hX hs]; exact h1
  exact inC_pred_of_size hpX (pred X) hpX (Nat.le_refl _) h2

/-- 目標が `Ω_c`、引数が後者の標準形の崩壊について、前の引数の崩壊 `Ψ^0_{Ω_c}(pred X)` は標準形 -/
theorem wnf_psi_om_pred {c X : Tm} (ht : WNF (.Psi .zero (.Om c) X)) (hs : isSucc X = true) :
    WNF (.Psi .zero (.Om c) (pred X)) := by
  have hP := ht.psi
  exact wnf_psi0 hP.piF hP.tgt (wnf_pred hP.aF) (inC_pred_self hP.aF hs hP.Ca)
    (fun r hr => by simp [argR?] at hr)

/-- 後者の引数の崩壊の種は元の項未満 -/
theorem psi_pred_lt {ξ τ X : Tm} (h0 : WNF (.Psi ξ τ (pred X))) (ht : WNF (.Psi ξ τ X))
    (hs : isSucc X = true) : Lt (.Psi ξ τ (pred X)) (.Psi ξ τ X) := by
  have hX := ht.psi.aF
  have e := succT_pred hX hs
  have h1 : WNF (.Psi ξ τ (succT (pred X))) := by rw [e]; exact ht
  have := psi_lt_psi_succ h0 h1
  rwa [e] at this

/-! ### 目標が `Ω_c`、引数が後者で、種より大きい加数がない場合：種の倍数 -/

/-- 目標が `Ω_c`、引数が後者のとき、`cs` は種 `Ψ^0_{Ω_c}(pred X)` の挿入（`insertAtM`） -/
theorem cs_om_succ {c X : Tm} (ht : WNF (.Psi .zero (.Om c) X)) (hs : isSucc X = true) :
    cs (.Om c) X = insertAtM (.Om c) .om (.Om c) (.Psi .zero (.Om c) (pred X)) (pred X)
      (info X).sums.dropLast := by
  have hX := ht.psi.aF
  have hX0 : X ≠ zero := by rintro rfl; simp [isSucc, summands] at hs
  have hd : (lastS (info X).sums).dom = .one := by
    rw [lastS_dom hX hX0]; exact (dom_eq_one_iff hX).mpr hs
  unfold cs cseq
  simp only [hX0, ↓reduceIte, hd, validR, argR?, Bool.true_eq_false]
  unfold mahloSeq
  simp only [mOfT, mOf, Option.getD_some, ↓reduceIte, maxO]
  rfl

/-- 種より大きい加数がなければ、列は種の倍数 -/
theorem cs_om_succ_mul {c X : Tm} (ht : WNF (.Psi .zero (.Om c) X)) (hs : isSucc X = true)
    (hnone : splitGtD (.Psi .zero (.Om c) (pred X)) (info X).sums.dropLast = none) :
    cs (.Om c) X = .mul (.Psi .zero (.Om c) (pred X)) 2 := by
  rw [cs_om_succ ht hs]
  unfold insertAtM
  rw [hnone]
  unfold famSeq
  rfl

theorem natGood_om_succ_mul {c X : Tm} (ht : WNF (.Psi .zero (.Om c) X)) (hs : isSucc X = true)
    (hnone : splitGtD (.Psi .zero (.Om c) (pred X)) (info X).sums.dropLast = none) :
    NatGood (.Psi .zero (.Om c) X) (cs (.Om c) X) := by
  rw [cs_om_succ_mul ht hs hnone]
  have hp := wnf_psi_om_pred ht hs
  exact natGood_mul hp rfl rfl (psi_pred_lt hp ht hs) 2

end RTKA.Fund
