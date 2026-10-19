import Compact.OCFRathjen.Good

/-! `cmp`・`inC` の正しさ（Rathjen Lemma 5.4、Prop. 4.20・4.21 などを `T⁺` の比較の各節に当てはめる）。

`Good` な項について、`RTKA.cmp a b = ocmp (val a) (val b)` と
`RTKA.inC a g d = true ↔ val a ∈ C(val g, val d)` を、`cmp`・`inC` の停止性の測度
（`8 ·（大きさの和）+ 段`）についての帰納法で同時に示す（`CmpOK`）。 -/

namespace OCF.Rathjen

universe u

open Ordinal

noncomputable section

open RTKA (Tm)

/-! ### 順序数の比較 -/

open Classical in
/-- 順序数の比較 -/
def ocmp (x y : Ordinal.{u}) : Ordering :=
  if x < y then .lt else if x = y then .eq else .gt

theorem ocmp_of_lt {x y : Ordinal.{u}} (h : x < y) : ocmp x y = .lt := by
  unfold ocmp; simp [h]

theorem ocmp_of_eq {x y : Ordinal.{u}} (h : x = y) : ocmp x y = .eq := by
  unfold ocmp; subst h; simp [lt_irrefl]

theorem ocmp_of_gt {x y : Ordinal.{u}} (h : y < x) : ocmp x y = .gt := by
  unfold ocmp; simp [lt_asymm h, ne_of_gt h]

theorem ocmp_eq_lt_iff {x y : Ordinal.{u}} : ocmp x y = .lt ↔ x < y := by
  rcases lt_total x y with h | h | h
  · simp [ocmp_of_lt h, h]
  · subst h; simp [ocmp_of_eq rfl, lt_irrefl]
  · simp [ocmp_of_gt h, lt_asymm h]

theorem ocmp_eq_eq_iff {x y : Ordinal.{u}} : ocmp x y = .eq ↔ x = y := by
  rcases lt_total x y with h | h | h
  · simp [ocmp_of_lt h, ne_of_lt h]
  · subst h; simp [ocmp_of_eq rfl]
  · simp [ocmp_of_gt h, ne_of_gt h]

theorem ocmp_eq_gt_iff {x y : Ordinal.{u}} : ocmp x y = .gt ↔ y < x := by
  rcases lt_total x y with h | h | h
  · simp [ocmp_of_lt h, lt_asymm h]
  · subst h; simp [ocmp_of_eq rfl, lt_irrefl]
  · simp [ocmp_of_gt h, h]

theorem ocmp_swap (x y : Ordinal.{u}) : (ocmp x y).swap = ocmp y x := by
  rcases lt_total x y with h | h | h
  · rw [ocmp_of_lt h, ocmp_of_gt h]; rfl
  · subst h; rw [ocmp_of_eq rfl]; rfl
  · rw [ocmp_of_gt h, ocmp_of_lt h]; rfl

/-- 大小が同じなら比較も同じ -/
theorem ocmp_congr {x y x' y' : Ordinal.{u}} (h1 : x < y ↔ x' < y') (h2 : y < x ↔ y' < x') :
    ocmp x y = ocmp x' y' := by
  rcases lt_total x y with h | h | h
  · rw [ocmp_of_lt h, ocmp_of_lt (h1.mp h)]
  · subst h
    rw [ocmp_of_eq rfl]
    rcases lt_total x' y' with h' | h' | h'
    · exact absurd (h1.mpr h') (lt_irrefl _)
    · rw [ocmp_of_eq h']
    · exact absurd (h2.mpr h') (lt_irrefl _)
  · rw [ocmp_of_gt h, ocmp_of_gt (h2.mp h)]

theorem ocmp_add_left (a x y : Ordinal.{u}) : ocmp (a + x) (a + y) = ocmp x y :=
  ocmp_congr (add_lt_add_iff_right a) (add_lt_add_iff_right a)

variable [Setting.{u}]

theorem ocmp_Om {x y : Ordinal.{u}} (hx : x < Λ) (hy : y < Λ) : ocmp (Om x) (Om y) = ocmp x y :=
  ocmp_congr (Om_lt_Om_iff hx hy) (Om_lt_Om_iff hy hx)

theorem Om_le_Om {x y : Ordinal.{u}} (h : x ≤ y) (hy : y < Λ) : Om x ≤ Om y := by
  cases h with
  | inl h => exact Or.inl (Om_lt_Om h hy)
  | inr e => rw [e]; exact le_refl _

omit [Setting] in
theorem bnot_iff {b : Bool} {P : Prop} (h : b = true ↔ P) : (!b) = true ↔ ¬ P := by
  cases b <;> simp_all

/-! ### 和の項 -/

theorem summands_good : ∀ (t : Tm), Good.{u} t →
    ∀ s, s ∈ RTKA.summands t → Good.{u} s ∧ RTKA.isPrincipal s = true := by
  intro t
  induction t with
  | zero => intro _ s hs; simp [RTKA.summands] at hs
  | plus a b _ ihb =>
    intro h s hs
    cases h with
    | plus _ _ ha hb hap _ _ =>
      rw [summands_plus] at hs
      cases List.mem_cons.mp hs with
      | inl e => rw [e]; exact ⟨ha, hap⟩
      | inr hs => exact ihb hb s hs
  | _ =>
    intro h s hs
    simp only [RTKA.summands, List.mem_singleton] at hs
    rw [hs]
    exact ⟨h, rfl⟩

/-! ### 帰納法の仮定 -/

/-- 測度 `N` 未満の `cmp`・`inC` の呼び出しが正しい -/
def CmpOK (N : Nat) : Prop :=
  (∀ a b : Tm, 8 * (a.size + b.size) + 3 < N → Good.{u} a → Good.{u} b →
    RTKA.cmp a b = ocmp (val.{u} a) (val b)) ∧
  (∀ a g d : Tm, 8 * (a.size + g.size) + 5 < N → 8 * (a.size + d.size) + 5 < N →
    Good.{u} a → Good.{u} g → Good.{u} d →
    (RTKA.inC a g d = true ↔ C (val.{u} g) (val d) (val a)))

/-! ### `inC`（Lemma 5.4） -/

theorem inC_ok (hS : StationaryHyp.{u}) {N : Nat} (hN : CmpOK.{u} N) {a g d : Tm}
    (hm1 : 8 * (a.size + g.size) + 5 ≤ N) (hm2 : 8 * (a.size + d.size) + 5 ≤ N)
    (ha : Good.{u} a) (hg : Good.{u} g) (hd : Good.{u} d) :
    RTKA.inC a g d = true ↔ C (val.{u} g) (val d) (val a) := by
  have ia := ha.inv hS
  have ha' := ha
  cases ha with
  | zero => rw [RTKA.inC]; exact ⟨fun _ => C_zero _ _, fun _ => rfl⟩
  | one => rw [RTKA.inC]; exact ⟨fun _ => C_one _ _, fun _ => rfl⟩
  | kc n _ => rw [RTKA.inC]; exact ⟨fun _ => C_K _ _ n, fun _ => rfl⟩
  | plus x y hx hy _ _ _ =>
    simp only [RTKA.Tm.size] at hm1 hm2
    rw [RTKA.inC, Bool.and_eq_true, hN.2 x g d (by omega) (by omega) hx hg hd,
      hN.2 y g d (by omega) (by omega) hy hg hd]
    have hc := ia.cnf
    rw [summands_plus, List.map_cons] at hc
    show _ ↔ C _ _ (val x + val y)
    apply Iff.intro
    · intro h; exact C_add h.1 h.2
    · intro h
      have hall := (C_iff_cnf hc).mp h
      refine And.intro (hall _ List.mem_cons_self) ?_
      exact (C_iff_cnf (hy.inv hS).cnf).mpr (fun p hp => hall p (List.mem_cons_of_mem _ hp))
  | om x hx _ hlt =>
    simp only [RTKA.Tm.size] at hm1 hm2
    rw [RTKA.inC, hN.2 x g d (by omega) (by omega) hx hg hd]
    have hΛ := (hx.inv hS).lt_Λ
    apply Iff.intro
    · intro h; exact C_Om hΛ h
    · intro h
      cases lt_or_le (Om (val.{u} x)) (val d) with
      | inl h' => exact C_lt (lt_of_le_of_lt (le_Om hΛ) h')
      | inr h' => exact GenRep_Om (C_gen h (ia.principal rfl) h') hΛ hlt
  | xi n b _ hb _ _ _ =>
    simp only [RTKA.Tm.size] at hm1 hm2
    have e1 := hN.1 _ d (by simp only [RTKA.Tm.size]; omega) ha' hd
    have e2 := hN.2 b g d (by omega) (by omega) hb hg hd
    have e3 := hN.1 b g (by omega) hb hg
    rw [RTKA.inC, e1, e3]
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, ocmp_eq_lt_iff, e2]
    have hx := ia.xi n b rfl
    apply Iff.intro
    · intro h
      cases h with
      | inl h => exact C_lt h
      | inr h => exact C_Xi n hx.1 h.2 h.1
    · intro h
      cases lt_or_le (val.{u} (.Xi n b)) (val d) with
      | inl h' => exact Or.inl h'
      | inr h' =>
        have g' := GenRep_Xi (C_gen h (ia.principal rfl) h') hx.1 hx.2.2.2
        exact Or.inr ⟨g'.1, g'.2⟩
  | psi sg ka b _ hsg hka hb _ hle _ _ _ _ _ _ =>
    simp only [RTKA.Tm.size] at hm1 hm2
    have e1 := hN.1 _ d (by simp only [RTKA.Tm.size]; omega) ha' hd
    have eka := hN.2 ka g d (by omega) (by omega) hka hg hd
    have esg := hN.2 sg g d (by omega) (by omega) hsg hg hd
    have eb := hN.2 b g d (by omega) (by omega) hb hg hd
    have e3 := hN.1 b g (by omega) hb hg
    rw [RTKA.inC, e1, e3]
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, ocmp_eq_lt_iff, eka, esg, eb]
    have hp := ia.psi sg ka b rfl
    apply Iff.intro
    · intro h
      cases h with
      | inl h => exact C_lt h
      | inr h => exact C_Psi h.2 hle hp.2 h.1.1.2 h.1.1.1 h.1.2
    · intro h
      cases lt_or_le (val.{u} (.Psi sg ka b)) (val d) with
      | inl h' => exact Or.inl h'
      | inr h' =>
        have g' := GenRep_Psi (C_gen h (ia.principal rfl) h') hp.2 hp.1
        exact Or.inr ⟨⟨⟨g'.2.1, g'.1⟩, g'.2.2.1⟩, g'.2.2.2⟩

/-! ### `cmpOmX`（Lemma 4.19） -/

theorem cmpOmX_ok (hS : StationaryHyp.{u}) {N : Nat} (hN : CmpOK.{u} N) {a X : Tm}
    (hm : 8 * (a.size + X.size) + 4 ≤ N) (ha : Good.{u} a) (hX : Good.{u} X)
    (hXk : (∃ n b, X = .Xi n b) ∨ (∃ xi pi b, X = .Psi xi pi b)) :
    RTKA.cmpOmX a X = ocmp (Om (val.{u} a)) (val X) := by
  have ia := ha.inv hS
  have iX := hX.inv hS
  rw [RTKA.cmpOmX.eq_def]
  by_cases hf : RTKA.omegaFixed X = true
  · simp only [hf, ↓reduceIte]
    rw [hN.1 a X (by omega) ha hX]
    have e := ocmp_Om ia.lt_Λ iX.lt_Λ
    rw [iX.fixed hf] at e
    exact e.symm
  · simp only [hf, Bool.false_eq_true, ↓reduceIte]
    rcases hXk with ⟨n, b, rfl⟩ | ⟨xi, pi, b, rfl⟩
    · simp [RTKA.omegaFixed] at hf
    · have hf' : xi = .zero ∧ RTKA.isInacc pi = false := by simpa [RTKA.omegaFixed] using hf
      obtain ⟨rfl, hpi⟩ := hf'
      have hX' := hX
      cases hX with
      | psi _ _ _ _ _ hpi' _ hreg _ _ _ _ _ _ _ =>
        cases pi with
        | Om c =>
          cases hpi' with
          | om _ hc _ _ =>
            dsimp only
            simp only [RTKA.Tm.size] at hm
            rw [hN.1 a c (by omega) ha hc]
            have hp := iX.psi .zero (.Om c) b rfl
            split
            · rename_i h
              exact (ocmp_of_lt (iX.psi0 c b rfl _ (ocmp_eq_lt_iff.mp (beq_iff_eq.mp h)))).symm
            · rename_i h
              have hca : val.{u} c ≤ val a :=
                le_of_not_lt (fun h' => h (beq_iff_eq.mpr (ocmp_of_lt h')))
              exact (ocmp_of_gt (lt_of_lt_of_le hp.1 (Om_le_Om hca ia.lt_Λ))).symm
        | Xi _ _ => simp [RTKA.isInacc] at hpi
        | Psi _ _ _ => simp [RTKA.isInacc, RTKA.isRegTerm] at hpi hreg; exact absurd hpi hreg
        | _ => simp [RTKA.isRegTerm] at hreg

/-! ### `xiLtXi`（Lemma 4.14） -/

theorem xiLtXi_ok (hS : StationaryHyp.{u}) {N : Nat} (hN : CmpOK.{u} N) {n : Nat} {a b : Tm}
    (hm : 8 * (a.size + b.size + 2) ≤ N) (ha : Good.{u} (.Xi n a)) (hb : Good.{u} (.Xi n b)) :
    RTKA.xiLtXi (.Xi n a) (.Xi n b) = true ↔ val.{u} (.Xi n a) < val (.Xi n b) := by
  have hxa := (ha.inv hS).xi n a rfl
  have hxb := (hb.inv hS).xi n b rfl
  have ha' := ha
  have hb' := hb
  cases ha with
  | xi _ _ _ ha _ _ _ =>
    cases hb with
    | xi _ _ _ hb _ _ _ =>
      have e2 := hN.2 a b (.Xi n b) (by omega) (by simp only [RTKA.Tm.size]; omega) ha hb hb'
      have e4 := hN.2 b a (.Xi n a) (by omega) (by simp only [RTKA.Tm.size]; omega) hb ha ha'
      rw [RTKA.xiLtXi, hN.1 a b (by omega) ha hb, hN.1 b a (by omega) hb ha]
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, ocmp_eq_lt_iff, e2, bnot_iff e4]
      exact (Xi_lt_Xi_iff hxa.1 hxb.1 hxa.2 hxb.2).symm

/-! ### `psiLtXi`（Prop. 4.21） -/

theorem psiLtXi_ok (hS : StationaryHyp.{u}) {N : Nat} (hN : CmpOK.{u} N) {xi pi a b : Tm}
    {m : Nat} (hm : 8 * (xi.size + pi.size + a.size + b.size + 2) ≤ N)
    (hx : Good.{u} (.Psi xi pi a)) (hy : Good.{u} (.Xi m b)) (hlev : RTKA.lev pi = m) :
    RTKA.psiLtXi (.Psi xi pi a) (.Xi m b) = true ↔ val.{u} (.Psi xi pi a) < val (.Xi m b) := by
  have hp := (hx.inv hS).psi xi pi a rfl
  have hxb := (hy.inv hS).xi m b rfl
  have hx' := hx
  have hy' := hy
  cases hx with
  | psi _ _ _ _ _ hpi ha hreg _ _ _ _ _ _ _ =>
    cases hy with
    | xi _ _ _ hb _ _ _ =>
      have hπK : val.{u} pi < K m := by
        rw [← hlev]; exact ((hpi.inv hS).bounds (ne_zero_of_isRegTerm hreg)).2.2
      have e3 := hN.2 b a (.Psi xi pi a) (by omega) (by simp only [RTKA.Tm.size]; omega) hb ha hx'
      rw [RTKA.psiLtXi, hN.1 pi _ (by simp only [RTKA.Tm.size]; omega) hpi hy',
        hN.1 b a (by omega) hb ha]
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, ocmp_eq_lt_iff,
        ocmp_eq_gt_iff, bnot_iff e3]
      rw [not_lt_iff_le]
      exact (Psi_lt_Xi_iff hxb.1 hxb.2 hp.1 hπK).symm

/-! ### `cmpPsi`（Prop. 4.17・4.20） -/

theorem cmpPsi_ok (hS : StationaryHyp.{u}) {N : Nat} (hN : CmpOK.{u} N) {xi pi a sg ka b : Tm}
    (hm : 8 * (xi.size + pi.size + a.size + sg.size + ka.size + b.size + 2) ≤ N)
    (hx : Good.{u} (.Psi xi pi a)) (hy : Good.{u} (.Psi sg ka b)) :
    RTKA.cmpPsi (.Psi xi pi a) (.Psi sg ka b) = ocmp (val.{u} (.Psi xi pi a)) (val (.Psi sg ka b)) := by
  have px := (hx.inv hS).psi xi pi a rfl
  have py := (hy.inv hS).psi sg ka b rfl
  have hx' := hx
  have hy' := hy
  cases hx with
  | psi _ _ _ _ hxi hpi ha _ _ _ _ _ _ _ _ =>
    cases hy with
    | psi _ _ _ _ hsg hka hb _ _ _ _ _ _ _ _ =>
      rw [RTKA.cmpPsi]
      split
      · rename_i h
        rw [beq_iff_eq.mp h]
        exact (ocmp_of_eq rfl).symm
      rename_i hne
      have hne' : val.{u} (.Psi xi pi a) ≠ val (.Psi sg ka b) := fun e =>
        hne (beq_iff_eq.mpr (val_inj hS _ _ hx' hy' e))
      rw [hN.1 _ pi (by simp only [RTKA.Tm.size]; omega) hy' hpi]
      split
      · rename_i h
        have h' : val.{u} pi ≤ val (.Psi sg ka b) :=
          le_of_not_lt (fun h' => (bne_iff_ne.mp h) (ocmp_of_lt h'))
        exact (ocmp_of_lt (lt_of_lt_of_le px.1 h')).symm
      rename_i hyπ
      have hyπ' : val.{u} (.Psi sg ka b) < val pi := by
        simp only [bne_iff_ne, ne_eq, ocmp_eq_lt_iff] at hyπ
        exact Classical.not_not.mp hyπ
      rw [hN.1 _ ka (by simp only [RTKA.Tm.size]; omega) hx' hka]
      split
      · rename_i h
        have h' : val.{u} ka ≤ val (.Psi xi pi a) :=
          le_of_not_lt (fun h' => (bne_iff_ne.mp h) (ocmp_of_lt h'))
        exact (ocmp_of_gt (lt_of_lt_of_le py.1 h')).symm
      rename_i hxκ
      have hxκ' : val.{u} (.Psi xi pi a) < val ka := by
        simp only [bne_iff_ne, ne_eq, ocmp_eq_lt_iff] at hxκ
        exact Classical.not_not.mp hxκ
      have key := Psi_lt_Psi_iff px.2 py.2 px.1 py.1 hyπ' hxκ'
      have e_ab := hN.1 a b (by omega) ha hb
      have e_ba := hN.1 b a (by omega) hb ha
      have e_xs := hN.1 xi sg (by omega) hxi hsg
      have e_sx := hN.1 sg xi (by omega) hsg hxi
      have i1 := hN.2 a b _ (by omega) (by simp only [RTKA.Tm.size]; omega) ha hb hy'
      have i2 := hN.2 xi b _ (by omega) (by simp only [RTKA.Tm.size]; omega) hxi hb hy'
      have i3 := hN.2 pi b _ (by omega) (by simp only [RTKA.Tm.size]; omega) hpi hb hy'
      have i4 := hN.2 b a _ (by omega) (by simp only [RTKA.Tm.size]; omega) hb ha hx'
      have i5 := hN.2 sg a _ (by omega) (by simp only [RTKA.Tm.size]; omega) hsg ha hx'
      have i6 := hN.2 ka a _ (by omega) (by simp only [RTKA.Tm.size]; omega) hka ha hx'
      have i7 := hN.2 sg xi _ (by omega) (by simp only [RTKA.Tm.size]; omega) hsg hxi hx'
      have i456 : (RTKA.inC b a (.Psi xi pi a) && RTKA.inC sg a (.Psi xi pi a) &&
          RTKA.inC ka a (.Psi xi pi a)) = true ↔
          (C (val.{u} a) (val (.Psi xi pi a)) (val b) ∧ C (val a) (val (.Psi xi pi a)) (val sg) ∧
            C (val a) (val (.Psi xi pi a)) (val ka)) := by
        rw [Bool.and_eq_true, Bool.and_eq_true, i4, i5, i6, and_assoc]
      have hkp : ka = pi ↔ val.{u} ka = val pi :=
        ⟨fun e => by rw [e], fun e => val_inj hS _ _ hka hpi e⟩
      rw [e_ab, e_ba, e_xs, e_sx]
      dsimp only
      split
      · rename_i hc
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
          ocmp_eq_lt_iff, ocmp_eq_gt_iff, ocmp_eq_eq_iff, i1, i2, i3, bnot_iff i456, bnot_iff i7,
          hkp] at hc
        apply Eq.symm
        apply ocmp_of_lt
        apply key.mpr
        rcases hc with ((h | h) | h) | h
        · exact Or.inl ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2⟩
        · exact Or.inr (Or.inl ⟨le_of_not_lt h.1, h.2⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩))
        · exact Or.inr (Or.inr (Or.inr h))
      · rename_i hc
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
          ocmp_eq_lt_iff, ocmp_eq_gt_iff, ocmp_eq_eq_iff, i1, i2, i3, bnot_iff i456, bnot_iff i7,
          hkp, not_or] at hc
        apply Eq.symm
        apply ocmp_of_gt
        have hnlt : ¬ val.{u} (.Psi xi pi a) < val (.Psi sg ka b) := by
          intro hlt
          rcases key.mp hlt with h | h | h | h
          · exact hc.1.1.1 ⟨⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩, hxκ'⟩
          · exact hc.1.1.2 ⟨not_lt_of_le h.1, h.2⟩
          · exact hc.1.2 ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩
          · exact hc.2 h
        rcases lt_total (val.{u} (.Psi xi pi a)) (val (.Psi sg ka b)) with h | h | h
        · exact absurd h hnlt
        · exact absurd h hne'
        · exact h

/-! ### `cmpP`：和でない項どうしの比較 -/

theorem cmpP_ok (hS : StationaryHyp.{u}) {N : Nat} (hN : CmpOK.{u} N) {x y : Tm}
    (hm : 8 * (x.size + y.size) + 1 ≤ N) (hx : Good.{u} x) (hy : Good.{u} y)
    (hxp : RTKA.isPrincipal x = true) (hyp : RTKA.isPrincipal y = true) :
    RTKA.cmpP x y = ocmp (val.{u} x) (val y) := by
  have ix := hx.inv hS
  have iy := hy.inv hS
  have bx := ix.bounds (ne_zero_of_isPrincipal hxp)
  have bY := iy.bounds (ne_zero_of_isPrincipal hyp)
  rw [RTKA.cmpP.eq_def]
  by_cases hl : RTKA.lev x < RTKA.lev y
  · simp only [hl, ↓reduceIte]
    exact (ocmp_of_lt (lt_of_lt_of_le bx.2.2 (le_trans (K_le (by omega)) bY.2.1))).symm
  by_cases hl' : RTKA.lev y < RTKA.lev x
  · simp only [hl, hl', ↓reduceIte]
    exact (ocmp_of_gt (lt_of_lt_of_le bY.2.2 (le_trans (K_le (by omega)) bx.2.1))).symm
  simp only [hl, hl', ↓reduceIte]
  have hlev : RTKA.lev x = RTKA.lev y := by omega
  -- `K_{lev - 1}` との比較
  have kx : ∀ n, RTKA.lev x = n + 1 → (∀ m, x ≠ .K m) → K n < val.{u} x := by
    intro n hn hK
    have h := ix.strict hxp hK
    rw [hn, Nat.add_sub_cancel] at h
    exact h
  have ky : ∀ n, RTKA.lev y = n + 1 → (∀ m, y ≠ .K m) → K n < val.{u} y := by
    intro n hn hK
    have h := iy.strict hyp hK
    rw [hn, Nat.add_sub_cancel] at h
    exact h
  have hx' := hx
  have hy' := hy
  cases hx with
  | zero => simp [RTKA.isPrincipal] at hxp
  | plus => simp [RTKA.isPrincipal] at hxp
  | one =>
    cases hy with
    | zero => simp [RTKA.isPrincipal] at hyp
    | plus => simp [RTKA.isPrincipal] at hyp
    | one => exact (ocmp_of_eq rfl).symm
    | _ => dsimp only; exact (ocmp_of_lt (iy.one_lt rfl (by intro h; cases h))).symm
  | kc n hn =>
    cases hy with
    | zero => simp [RTKA.isPrincipal] at hyp
    | plus => simp [RTKA.isPrincipal] at hyp
    | one => dsimp only; exact (ocmp_of_gt (ix.one_lt rfl (by intro h; cases h))).symm
    | kc m _ =>
      dsimp only
      simp only [RTKA.lev] at hlev
      have e : n = m := by omega
      subst e
      exact (ocmp_of_eq rfl).symm
    | om b _ _ _ =>
      dsimp only
      have hK := ky n (by simp only [RTKA.lev] at hlev ⊢; omega) (fun _ h => by cases h)
      have hne : ¬ (b == Tm.K n) = true := by
        rw [beq_iff_eq]
        intro e
        subst e
        have h := hK
        rw [show val.{u} (Tm.Om (Tm.K n)) = Om (K n) from rfl, Om_K hn] at h
        exact lt_irrefl _ h
      simp only [hne]
      exact (ocmp_of_lt hK).symm
    | xi m c _ _ _ _ _ =>
      dsimp only
      exact (ocmp_of_lt (ky n (by simp only [RTKA.lev] at hlev ⊢; omega)
        (fun _ h => by cases h))).symm
    | psi _ pi _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      dsimp only
      exact (ocmp_of_lt (ky n (by simp only [RTKA.lev] at hlev ⊢; omega)
        (fun _ h => by cases h))).symm
  | om a ha _ _ =>
    cases hy with
    | zero => simp [RTKA.isPrincipal] at hyp
    | plus => simp [RTKA.isPrincipal] at hyp
    | one => dsimp only; exact (ocmp_of_gt (ix.one_lt rfl (by intro h; cases h))).symm
    | kc m hm' =>
      dsimp only
      have hK := kx m (by simp only [RTKA.lev] at hlev ⊢; omega) (fun _ h => by cases h)
      have hne : ¬ (a == Tm.K m) = true := by
        rw [beq_iff_eq]
        intro e
        subst e
        have h := hK
        rw [show val.{u} (Tm.Om (Tm.K m)) = Om (K m) from rfl, Om_K hm'] at h
        exact lt_irrefl _ h
      simp only [hne]
      exact (ocmp_of_gt hK).symm
    | om b hb _ _ =>
      dsimp only
      simp only [RTKA.Tm.size] at hm
      rw [hN.1 a b (by omega) ha hb]
      exact (ocmp_Om (ha.inv hS).lt_Λ (hb.inv hS).lt_Λ).symm
    | xi m c _ _ _ _ _ =>
      dsimp only
      simp only [RTKA.Tm.size] at hm
      exact cmpOmX_ok hS hN (by simp only [RTKA.Tm.size]; omega) ha hy' (Or.inl ⟨m, c, rfl⟩)
    | psi sg ka c _ _ _ _ _ _ _ _ _ _ _ _ =>
      dsimp only
      simp only [RTKA.Tm.size] at hm
      exact cmpOmX_ok hS hN (by simp only [RTKA.Tm.size]; omega) ha hy'
        (Or.inr ⟨sg, ka, c, rfl⟩)
  | xi n a _ ha _ _ _ =>
    have hxa := ix.xi n a rfl
    cases hy with
    | zero => simp [RTKA.isPrincipal] at hyp
    | plus => simp [RTKA.isPrincipal] at hyp
    | one => dsimp only; exact (ocmp_of_gt (ix.one_lt rfl (by intro h; cases h))).symm
    | kc m _ =>
      dsimp only
      exact (ocmp_of_gt (kx m (by simp only [RTKA.lev] at hlev ⊢; omega)
        (fun _ h => by cases h))).symm
    | om b hb _ _ =>
      dsimp only
      simp only [RTKA.Tm.size] at hm
      rw [cmpOmX_ok hS hN (by simp only [RTKA.Tm.size]; omega) hb hx' (Or.inl ⟨n, a, rfl⟩),
        ocmp_swap]
      rfl
    | xi m b _ hb _ _ _ =>
      dsimp only
      simp only [RTKA.lev] at hlev
      subst hlev
      have hxb := iy.xi n b rfl
      by_cases hab : a = b
      · subst hab
        simp only [beq_self_eq_true, ↓reduceIte]
        exact (ocmp_of_eq rfl).symm
      · have hab' : ¬ (a == b) = true := by rw [beq_iff_eq]; exact hab
        simp only [hab', Bool.false_eq_true, ↓reduceIte]
        have hiff := xiLtXi_ok hS hN (by simp only [RTKA.Tm.size] at hm; omega) hx' hy'
        split
        · rename_i h
          exact (ocmp_of_lt (hiff.mp h)).symm
        · rename_i h
          apply Eq.symm
          apply ocmp_of_gt
          have hne : val.{u} (.Xi n a) ≠ val (.Xi n b) := fun e =>
            hab (val_inj hS _ _ ha hb (Xi_inj hxa.1 hxb.1 hxa.2 hxb.2 e))
          rcases lt_total (val.{u} (.Xi n a)) (val (.Xi n b)) with h' | h' | h'
          · exact absurd (hiff.mpr h') h
          · exact absurd h' hne
          · exact h'
    | psi xi pi c _ _ _ _ _ _ _ _ _ _ _ _ =>
      dsimp only
      simp only [RTKA.lev] at hlev
      have hp := iy.psi xi pi c rfl
      have hiff := psiLtXi_ok hS hN (by simp only [RTKA.Tm.size] at hm; omega) hy' hx' hlev.symm
      split
      · rename_i h
        exact (ocmp_of_gt (hiff.mp h)).symm
      · rename_i h
        apply Eq.symm
        apply ocmp_of_lt
        have hne : val.{u} (.Psi xi pi c) ≠ val (.Xi n a) := Xi_ne_Psi hxa.1 hxa.2.2.2 hp.1 hp.2
        rcases lt_total (val.{u} (.Psi xi pi c)) (val (.Xi n a)) with h' | h' | h'
        · exact absurd (hiff.mpr h') h
        · exact absurd h' hne
        · exact h'
  | psi xi pi a _ _ _ _ _ _ _ _ _ _ _ _ =>
    have hp := ix.psi xi pi a rfl
    cases hy with
    | zero => simp [RTKA.isPrincipal] at hyp
    | plus => simp [RTKA.isPrincipal] at hyp
    | one => dsimp only; exact (ocmp_of_gt (ix.one_lt rfl (by intro h; cases h))).symm
    | kc m _ =>
      dsimp only
      exact (ocmp_of_gt (kx m (by simp only [RTKA.lev] at hlev ⊢; omega)
        (fun _ h => by cases h))).symm
    | om b hb _ _ =>
      dsimp only
      simp only [RTKA.Tm.size] at hm
      rw [cmpOmX_ok hS hN (by simp only [RTKA.Tm.size]; omega) hb hx' (Or.inr ⟨xi, pi, a, rfl⟩),
        ocmp_swap]
      rfl
    | xi m b _ _ _ _ _ =>
      dsimp only
      simp only [RTKA.lev] at hlev
      have hxb := iy.xi m b rfl
      have hiff := psiLtXi_ok hS hN (by simp only [RTKA.Tm.size] at hm; omega) hx' hy' hlev
      split
      · rename_i h
        exact (ocmp_of_lt (hiff.mp h)).symm
      · rename_i h
        apply Eq.symm
        apply ocmp_of_gt
        have hne : val.{u} (.Psi xi pi a) ≠ val (.Xi m b) := Xi_ne_Psi hxb.1 hxb.2.2.2 hp.1 hp.2
        rcases lt_total (val.{u} (.Psi xi pi a)) (val (.Xi m b)) with h' | h' | h'
        · exact absurd (hiff.mpr h') h
        · exact absurd h' hne
        · exact h'
    | psi sg ka b _ _ _ _ _ _ _ _ _ _ _ _ =>
      dsimp only
      exact cmpPsi_ok hS hN (by simp only [RTKA.Tm.size] at hm; omega) hx' hy'

/-! ### 和の比較（辞書式） -/

theorem cmpList_ok (hS : StationaryHyp.{u}) {N : Nat} (hN : CmpOK.{u} N) :
    ∀ (xs ys : List Tm), 8 * (RTKA.lsize xs + RTKA.lsize ys) + 2 ≤ N →
    (∀ t, t ∈ xs → Good.{u} t ∧ RTKA.isPrincipal t = true) →
    (∀ t, t ∈ ys → Good.{u} t ∧ RTKA.isPrincipal t = true) →
    CNF (listSum (xs.map val.{u})) (xs.map val) → CNF (listSum (ys.map val.{u})) (ys.map val) →
    RTKA.cmpList xs ys = ocmp (listSum (xs.map val.{u})) (listSum (ys.map val)) := by
  intro xs
  induction xs with
  | nil =>
    intro ys _ _ _ _ hy
    cases ys with
    | nil => rw [RTKA.cmpList]; exact (ocmp_of_eq rfl).symm
    | cons y ys =>
      rw [RTKA.cmpList]
      rw [List.map_cons] at hy
      exact (ocmp_of_lt hy.pos).symm
  | cons x xs ih =>
    intro ys hm hxs hys hx hy
    cases ys with
    | nil =>
      rw [RTKA.cmpList]
      rw [List.map_cons] at hx
      exact (ocmp_of_gt hx.pos).symm
    | cons y ys =>
      simp only [RTKA.lsize] at hm
      have hx0 := hxs x List.mem_cons_self
      have hy0 := hys y List.mem_cons_self
      rw [RTKA.cmpList, cmpP_ok hS hN (by omega) hx0.1 hy0.1 hx0.2 hy0.2]
      simp only [List.map_cons] at hx hy ⊢
      rcases lt_total (val.{u} x) (val y) with h | h | h
      · rw [ocmp_of_lt h]
        exact (ocmp_of_lt (lt_of_lt_of_le (hx.lt_of_head_lt ((hy0.1.inv hS).principal hy0.2) h)
          hy.head_le)).symm
      · rw [ocmp_of_eq h]
        dsimp only
        rw [ih ys (by omega) (fun t ht => hxs t (List.mem_cons_of_mem _ ht))
          (fun t ht => hys t (List.mem_cons_of_mem _ ht)) hx.tail hy.tail,
          listSum_cons, listSum_cons, h, ocmp_add_left]
      · rw [ocmp_of_gt h]
        exact (ocmp_of_gt (lt_of_lt_of_le (hy.lt_of_head_lt ((hx0.1.inv hS).principal hx0.2) h)
          hx.head_le)).symm

theorem cmp_ok (hS : StationaryHyp.{u}) {N : Nat} (hN : CmpOK.{u} N) {a b : Tm}
    (hm : 8 * (a.size + b.size) + 3 ≤ N) (ha : Good.{u} a) (hb : Good.{u} b) :
    RTKA.cmp a b = ocmp (val.{u} a) (val b) := by
  have ia := ha.inv hS
  have ib := hb.inv hS
  have la := RTKA.lsize_summands_le a
  have lb := RTKA.lsize_summands_le b
  rw [RTKA.cmp, cmpList_ok hS hN _ _ (by omega) (summands_good a ha) (summands_good b hb)
    ⟨ia.cnf.1, ia.cnf.2.1, rfl⟩ ⟨ib.cnf.1, ib.cnf.2.1, rfl⟩, ← ia.cnf.eq, ← ib.cnf.eq]

/-! ### 帰納法 -/

theorem cmpOK_succ (hS : StationaryHyp.{u}) {N : Nat} (hN : CmpOK.{u} N) : CmpOK.{u} (N + 1) :=
  ⟨fun _ _ _ ha hb => cmp_ok hS hN (by omega) ha hb,
   fun _ _ _ _ _ ha hg hd => inC_ok hS hN (by omega) (by omega) ha hg hd⟩

theorem cmpOK_all (hS : StationaryHyp.{u}) : ∀ N, CmpOK.{u} N
  | 0 => ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | N + 1 => cmpOK_succ hS (cmpOK_all hS N)

/-- `Good` な項について `cmp` は値の比較と一致する -/
theorem cmp_correct (hS : StationaryHyp.{u}) {a b : Tm} (ha : Good.{u} a) (hb : Good.{u} b) :
    RTKA.cmp a b = ocmp (val.{u} a) (val b) :=
  (cmpOK_all hS _).1 a b (Nat.lt_succ_self _) ha hb

/-- `Good` な項について `inC a g d` は `val a ∈ C(val g, val d)` と一致する（Lemma 5.4） -/
theorem inC_correct (hS : StationaryHyp.{u}) {a g d : Tm} (ha : Good.{u} a) (hg : Good.{u} g)
    (hd : Good.{u} d) : RTKA.inC a g d = true ↔ C (val.{u} g) (val d) (val a) :=
  (cmpOK_all hS (8 * (a.size + g.size + d.size) + 6)).2 a g d (by omega) (by omega) ha hg hd

end
end OCF.Rathjen
