import Compact.FS.Main

/-! 共終性：`x < t` は列のどこかの項の下に入る。

`x` の大きさの帰納法で示す。

* `Clo y A T`：`y` は `T` 未満で、`C(A, y)` の `T` 未満の元は `y` 未満（崩壊の性質）。
* `x` が標準形なら、`x` の成分は `C(arg x, 目標)` に入り、その前線の元（`parF x`）は `x` 未満。帰納法の仮定で前線の元が
  `y` 未満なら `x` の成分は `C(arg x, y)` に入るので、`arg x < A` さえ言えれば `x < y`（`Clo.lt`）。
* `x < t` の比較（`below_psi`・`below_xi`）：目標が `t` 未満か、隙間（`x ≤ w`、`w` は `t` の真の部分項）か、`arg x < X`。
* 共終数が大きい項では、添字 `β` が閉じた点（`Cl σ β`）で `x` の前線が `β` 未満なら `x < t[β]`（`SeqC`）。 -/

namespace RTKA.Fund

open Tm W

/-- `β` は `σ` の中で閉じた点：前線が `β` 未満の `σ` 未満の元は `β` 未満 -/
def Cl (σ β : Tm) : Prop :=
  (∀ d, ¬ Lt β d → inC β .zero d = false) ∧
    ∀ x, WNF x → Lt x σ → (∀ f, f ∈ fr σ x → Lt f β) → Lt x β

/-- 列の共終性 -/
def SeqC (t : Tm) (s : SeqD) : Prop :=
  match s.dom with
  | .omega => ∀ x, WNF x → Lt x t → ∃ n, Lt x (s.nat n)
  | .big σ => ∀ x β, WNF x → Lt x t → WNF β → Lt β σ → Cl σ β → (∀ f, f ∈ fr σ x → Lt f β) →
      Lt x (s.big β)
  | _ => True

/-- 崩壊の性質 -/
structure Clo (y A T : Tm) : Prop where
  hy : WNF y
  hA : WNF A
  hT : WNF T
  hyT : Lt y T
  prin : isPrincipal y = true
  coll : ∀ z, WNF z → inC z A y = true → Lt z T → Lt z y

theorem Clo.psi {ξ τ A : Tm} (hy : WNF (.Psi ξ τ A)) : Clo (.Psi ξ τ A) A τ :=
  ⟨hy, hy.psi.aF, hy.psi.piF, lt_psi_targetY hy, rfl, coll_psiY hy⟩

theorem Clo.xi {m : Nat} {A : Tm} (hy : WNF (.Xi m A)) : Clo (.Xi m A) A (.K m) :=
  ⟨hy, hy.xi.2.1, WNF.K' hy.xi.1, (lt_K_iffY hy hy.xi.1).mpr (Nat.le_refl _), rfl, coll_xi0 hy⟩

/-- `x` の成分の前線 -/
def parF : Tm → List Tm
  | .plus a b => [a, b]
  | .Om e => [e]
  | .Xi j b => fr (.K j) b
  | .Psi s k a => fr k a ++ fr k s ++ fr k k
  | _ => []

/-- 帰納法で使う部分項 -/
def parL : Tm → List Tm
  | .Psi s k a => k :: (fr k a ++ fr k s ++ fr k k)
  | x => parF x

theorem parF_sub_parL {x w : Tm} (h : w ∈ parF x) : w ∈ parL x := by
  cases x with
  | Psi s k a => exact List.mem_cons_of_mem _ h
  | _ => exact h

theorem parF_lt : ∀ {x w : Tm}, WNF x → w ∈ parF x → Lt w x
  | .zero, _, _, h | .one, _, _, h | .K _, _, _, h => by simp [parF] at h
  | .plus a b, w, hx, h => by
    simp only [parF, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact lt_plus_leftY hx
    · exact lt_plus_rightY hx
  | .Om e, w, hx, h => by
    simp only [parF, List.mem_singleton] at h
    rw [h]
    exact hx.om.2.2
  | .Xi j b, w, hx, h => FWOrder.k2x hx w h
  | .Psi s k a, w, hx, h => by
    simp only [parF, List.mem_append] at h
    rcases h with (h | h) | h
    · exact FWOrder.k2 hx w h
    · exact FWOrder.k2s hx w h
    · exact FWOrder.k2t hx w h

theorem parL_sub : ∀ {x w : Tm}, w ∈ parL x → w ∈ subs x ∧ w.size < x.size
  | .zero, _, h | .one, _, h | .K _, _, h => by simp [parL, parF] at h
  | .plus a b, w, h => by
    simp only [parL, parF, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · refine ⟨subs_plus_l (self_mem_subs _), ?_⟩
      simp only [Tm.size]
      omega
    · refine ⟨subs_plus_r (self_mem_subs _), ?_⟩
      simp only [Tm.size]
      omega
  | .Om e, w, h => by
    simp only [parL, parF, List.mem_singleton] at h
    rw [h]
    refine ⟨subs_om (self_mem_subs _), ?_⟩
    simp only [Tm.size]
    omega
  | .Xi j b, w, h => by
    have h1 := (fr_spec (show w ∈ fr (.K j) b from h)).1
    have h2 := size_le_of_mem_subs h1
    refine ⟨subs_xi h1, ?_⟩
    simp only [Tm.size]
    omega
  | .Psi s k a, w, h => by
    simp only [parL, List.mem_cons, List.mem_append] at h
    rcases h with rfl | (h | h) | h
    · refine ⟨subs_psi_p (self_mem_subs _), ?_⟩
      simp only [Tm.size]
      omega
    · have h1 := (fr_spec h).1
      have h2 := size_le_of_mem_subs h1
      refine ⟨subs_psi_a h1, ?_⟩
      simp only [Tm.size]
      omega
    · have h1 := (fr_spec h).1
      have h2 := size_le_of_mem_subs h1
      refine ⟨subs_psi_s h1, ?_⟩
      simp only [Tm.size]
      omega
    · have h1 := (fr_spec h).1
      have h2 := size_le_of_mem_subs h1
      refine ⟨subs_psi_p h1, ?_⟩
      simp only [Tm.size]
      omega

/-- 崩壊の性質からの比較：成分の前線が `y` 未満で `arg x < A` なら `x < y` -/
theorem Clo.lt {y A T x : Tm} (C : Clo y A T) (hx : WNF x) (hxT : Lt x T)
    (hF : ∀ w, w ∈ parF x → Lt w y) (harg : ∀ a, argR? x = some a → Lt a A) : Lt x y := by
  have hy := C.hy
  have hA := C.hA
  cases x with
  | zero =>
    exact zero_lt fun e => by
      have := C.prin
      rw [e] at this
      cases this
  | one => exact C.coll _ hx (inC_one _ _) hxT
  | K m => exact C.coll _ hx (inC_K _ _ _) hxT
  | plus a b => exact (lt_plus_prin_iffY hx C.prin).mpr (hF a (by simp [parF]))
  | Om e =>
    refine C.coll _ hx ?_ hxT
    rw [inC_om]
    exact WFY.inC_of_ltY _ hx.om.1 hy (hF e (by simp [parF]))
  | Xi j b =>
    obtain ⟨hj, hbF, -, -, hbC⟩ := hx.xi
    have hKF := WNF.K' hj
    by_cases h : Lt y (.K j)
    · have hba := harg b rfl
      refine C.coll _ hx (inC_xi_iff.mpr (Or.inr ⟨?_, hba⟩)) hxT
      exact inC_of_fr_lt hbF hKF hy hbF hA hbC (Or.inr h) (Or.inr hba) hF
    · exact lt_of_lt_of_leY hx hKF hy ((lt_K_iffY hx hj).mpr (Nat.le_refl _)) (le_of_not_ltY hy hKF h)
  | Psi s k a =>
    have hP := hx.psi
    by_cases h : Lt y k
    · have hba := harg a rfl
      have hle : Le y k := Or.inr h
      refine C.coll _ hx (inC_psi_iff.mpr (Or.inr ⟨?_, ?_, ?_, hba⟩)) hxT
      · exact inC_of_fr_lt hP.piF hP.piF hy hP.aF hA hP.Cpi hle (Or.inr hba) fun w hw =>
          hF w (by simp [parF, hw])
      · exact inC_of_fr_lt hP.xiF hP.piF hy hP.aF hA hP.Cxi hle (Or.inr hba) fun w hw =>
          hF w (by simp [parF, hw])
      · exact inC_of_fr_lt hP.aF hP.piF hy hP.aF hA hP.Ca hle (Or.inr hba) fun w hw =>
          hF w (by simp [parF, hw])
    · exact lt_of_lt_of_leY hx hP.piF hy (lt_psi_targetY hx) (le_of_not_ltY hy hP.piF h)

/-- `Ψ^0` の崩壊は目標にならない -/
theorem not_tgt_psi0 {π X : Tm} (h : IsTgt (.Psi .zero π X)) : False := by
  rcases h with ⟨c, e, -⟩ | ⟨n, p, e⟩ | ⟨ζ, κ, b, e, h⟩
  · cases e
  · cases e
  · cases e
    exact h rfl

/-- `Ψ^s_k(a) < t` の分解 -/
theorem below_psi {π X s k a : Tm} (ht : WNF (.Psi .zero π X)) (hx : WNF (.Psi s k a))
    (hlt : Lt (.Psi s k a) (.Psi .zero π X)) :
    Lt k (.Psi .zero π X) ∨ (∃ w, (w ∈ fr π X ∨ w ∈ fr π π) ∧ Le (.Psi s k a) w) ∨
      (Lt (.Psi .zero π X) k ∧ Lt a X ∧ inC a X (.Psi .zero π X) = true ∧
        inC s X (.Psi .zero π X) = true ∧ inC k X (.Psi .zero π X) = true) := by
  have hP := hx.psi
  have hQ := ht.psi
  by_cases hl : lev k = lev π
  · rcases (lt_psi_psiY hl hlt.ne).mp hlt with h | ⟨htk, hxπ, h | ⟨h1, h2⟩ | ⟨-, -, h, -⟩ | ⟨-, h⟩⟩
    · rcases le_of_not_ltY ht hP.piF h with e | h'
      · rw [e] at hP
        exact (not_tgt_psi0 hP.tgt).elim
      · exact Or.inl h'
    · exact Or.inr (Or.inr ⟨htk, h.1, h.2.1, h.2.2.1, h.2.2.2⟩)
    · obtain ⟨w, hw, hn⟩ := wit_c2 ht hx hP.aF (le_of_ne_gtY hQ.aF hP.aF h1) hxπ h2
      have hwF : WNF w := by
        rcases hw with hw | hw | hw
        · exact hQ.aF.of_mem_subs (fr_spec hw).1
        · exact hQ.piF.of_mem_subs (fr_spec hw).1
        · simp [fr] at hw
      refine Or.inr (Or.inl ⟨w, ?_, le_of_not_ltY hwF hx hn⟩)
      rcases hw with hw | hw | hw
      · exact Or.inl hw
      · exact Or.inr hw
      · simp [fr] at hw
    · exact absurd h (not_lt_zero _)
    · rw [inC_zero] at h
      cases h
  · have h1 : lev (.Psi s k a) ≤ lev (.Psi .zero π X) := lev_le_of_lt_gen hlt
    simp only [lev] at h1
    exact Or.inl (lt_of_lev_lt' (by simp only [lev]; omega))

/-- `Ξ_j(b) < t` の分解 -/
theorem below_xi {π X : Tm} {j : Nat} {b : Tm} (ht : WNF (.Psi .zero π X)) (hx : WNF (.Xi j b))
    (hlt : Lt (.Xi j b) (.Psi .zero π X)) :
    Lt (.K j) (.Psi .zero π X) ∨ (∃ w, w ∈ fr π π ∧ Le (.Xi j b) w) ∨
      (Lt (.Psi .zero π X) (.K j) ∧ Lt b X ∧ inC b X (.Psi .zero π X) = true) := by
  have hQ := ht.psi
  obtain ⟨hj, hbF, -, -, -⟩ := hx.xi
  by_cases hl : lev π = j
  · have h1 := (lt_xi_psiY hl).mp hlt
    rw [lt_psi_xiY hl] at h1
    have h2 : cmp π (.Xi j b) = .gt := by
      refine Classical.byContradiction fun h => h1 (Or.inl h)
    have hxπ : Lt (.Xi j b) π := lt_of_gtY hQ.piF hx h2
    by_cases hb : Lt b X
    · refine Or.inr (Or.inr ⟨(lt_K_iffY ht hj).mpr (by simp only [lev]; omega), hb, ?_⟩)
      cases e : inC b X (.Psi .zero π X) with
      | true => rfl
      | false => exact absurd (Or.inr ⟨hb, e⟩) h1
    · refine Or.inr (Or.inl ?_)
      have hXb : Le X b := le_of_not_ltY hbF hQ.aF hb
      have hπK : Lt π (.K j) := (lt_K_iffY hQ.piF hj).mpr (by omega)
      have hnC : ¬ inC π b (.Xi j b) = true := fun h =>
        Lt.asymmY hx hQ.piF hxπ (coll_xi0 hx π hQ.piF h hπK)
      by_cases hall : ∀ w, w ∈ fr π π → Lt w (.Xi j b)
      · exact absurd ((inC_frY hQ.piF hQ.piF hx hQ.aF hbF hQ.Cpi (Or.inr hxπ) hXb).mpr
          fun w hw => inC_of_lt_node (fr_node hw) (hall w hw)) hnC
      · obtain ⟨w, hw, hn⟩ := exists_of_not_forall_mem _ hall
        exact ⟨w, hw, le_of_not_ltY (hQ.piF.of_mem_subs (fr_spec hw).1) hx hn⟩
  · have h1 : lev (.Xi j b) ≤ lev (.Psi .zero π X) := lev_le_of_lt_gen hlt
    simp only [lev] at h1
    exact Or.inl (bot_ltY rfl (by simp only [lev]; omega) rfl rfl ht)

/-- 前線の元は隙間で列の項の下に入る -/
theorem gp_fr {π X y w : Tm} (ht : WNF (.Psi .zero π X)) (hG : Gp (.Psi .zero π X) y)
    (hw : w ∈ fr π X ∨ w ∈ fr π π) : Lt w y := by
  rcases hw with hw | hw
  · have h1 := (fr_spec hw).1
    have h2 := size_le_of_mem_subs h1
    exact hG w (subs_psi_a h1) (ne_of_size_lt (by simp only [Tm.size]; omega)) (FWOrder.k2 ht w hw)
  · have h1 := (fr_spec hw).1
    have h2 := size_le_of_mem_subs h1
    exact hG w (subs_psi_p h1) (ne_of_size_lt (by simp only [Tm.size]; omega)) (FWOrder.k2t ht w hw)

/-- 列の項 `y` の下に入る一歩：隙間か目標か崩壊の性質で `x < y`、そうでなければ `arg x < X` -/
theorem node_arg {π X y A T x : Tm} (ht : WNF (.Psi .zero π X)) (C : Clo y A T)
    (htT : Lt (.Psi .zero π X) T) (hG : Gp (.Psi .zero π X) y) (hx : WNF x)
    (hxt : Lt x (.Psi .zero π X)) (hF : ∀ w, w ∈ parF x → Lt w y)
    (hk : ∀ s k a, x = .Psi s k a → Lt k (.Psi .zero π X) → Lt k y) :
    Lt x y ∨ ∃ a, argR? x = some a ∧ Lt a X ∧ inC a a (.Psi .zero π X) = true ∧
      ∀ u, u ∈ fr (.Psi .zero π X) a → u ∈ parF x := by
  have hxT := lt_transY hx ht C.hT hxt htT
  have hy := C.hy
  have hlow : ∀ w, w ∈ parF x → Lt w (.Psi .zero π X) := fun w hw =>
    lt_transY (hx.of_mem_subs (parL_sub (parF_sub_parL hw)).1) hx ht (parF_lt hx hw) hxt
  cases x with
  | Psi s k a =>
    have hP := hx.psi
    rcases below_psi ht hx hxt with h | ⟨w, hw, hle⟩ | ⟨htk, h, -⟩
    · exact Or.inl (lt_transY hx hP.piF hy (lt_psi_targetY hx) (hk s k a rfl h))
    · have hwy := gp_fr ht hG hw
      have hwF : WNF w := by
        rcases hw with hw | hw
        · exact ht.psi.aF.of_mem_subs (fr_spec hw).1
        · exact ht.psi.piF.of_mem_subs (fr_spec hw).1
      exact Or.inl (lt_of_le_of_ltY hx hwF hy hle hwy)
    · have hfr : ∀ w, w ∈ fr k a → w ∈ parF (.Psi s k a) := fun w hw => by simp [parF, hw]
      refine Or.inr ⟨a, rfl, h, ?_, fun u hu => hfr u (fr_up ht hP.piF htk hP.aF (fun w hw => hlow w (hfr w hw)) hu)⟩
      exact inC_of_fr_lt hP.aF hP.piF ht hP.aF hP.aF hP.Ca (Or.inr htk) (Or.inl rfl)
        fun w hw => hlow w (hfr w hw)
  | Xi j b =>
    obtain ⟨hj, hbF, -, -, hbC⟩ := hx.xi
    have hKF := WNF.K' hj
    rcases below_xi ht hx hxt with h | ⟨w, hw, hle⟩ | ⟨htK, h, -⟩
    · have h1 : Lt (.K j) y := C.coll _ hKF (inC_K _ _ _) (lt_transY hKF ht C.hT h htT)
      exact Or.inl (lt_transY hx hKF hy ((lt_K_iffY hx hj).mpr (Nat.le_refl _)) h1)
    · have hwy := gp_fr ht hG (Or.inr hw)
      exact Or.inl (lt_of_le_of_ltY hx (ht.psi.piF.of_mem_subs (fr_spec hw).1) hy hle hwy)
    · refine Or.inr ⟨b, rfl, h, ?_, fun u hu => fr_up ht hKF htK hbF (fun w hw => hlow w hw) hu⟩
      exact inC_of_fr_lt hbF hKF ht hbF hbF hbC (Or.inr htK) (Or.inl rfl) fun w hw => hlow w hw
  | _ => exact Or.inl (C.lt hx hxT hF fun _ e => by cases e)

theorem mono_le {y : Nat → Tm} (hyF : ∀ n, WNF (y n)) (hm : ∀ n, Lt (y n) (y (n + 1))) {m n : Nat}
    (h : m ≤ n) : Le (y m) (y n) := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    rw [this]
    exact Or.inl rfl
  | succ k ih =>
    by_cases e : m = k + 1
    · rw [e]
      exact Or.inl rfl
    · exact le_transY (hyF m) (hyF k) (hyF (k + 1)) (ih (by omega)) (Or.inr (hm k))

/-- `ω` 型の共終性の帰納法 -/
theorem cof_nat {t : Tm} {y : Nat → Tm} (hyF : ∀ n, WNF (y n)) (hm : ∀ n, Lt (y n) (y (n + 1)))
    (hstep : ∀ x, WNF x → Lt x t → ∀ N, (∀ w, w ∈ parL x → Lt w t → Lt w (y N)) → ∃ m, Lt x (y m)) :
    ∀ x, WNF x → Lt x t → ∃ n, Lt x (y n) := by
  intro x
  induction hn : x.size using Nat.strongRecOn generalizing x with
  | ind n ih =>
    intro hx hxt
    have key : ∀ l : List Tm, (∀ w, w ∈ l → WNF w ∧ w.size < n) → ∃ N, ∀ w, w ∈ l → Lt w t → Lt w (y N) := by
      intro l
      induction l with
      | nil => exact fun _ => ⟨0, fun w hw => by cases hw⟩
      | cons a l ihl =>
        intro h
        obtain ⟨N, hN⟩ := ihl fun w hw => h w (List.mem_cons_of_mem _ hw)
        obtain ⟨haF, has⟩ := h a List.mem_cons_self
        by_cases hat : Lt a t
        · obtain ⟨N', hN'⟩ := ih a.size (by omega) a rfl haF hat
          refine ⟨max N N', fun w hw hwt => ?_⟩
          rcases List.mem_cons.mp hw with rfl | hw'
          · exact lt_of_lt_of_leY haF (hyF N') (hyF _) hN' (mono_le hyF hm (Nat.le_max_right _ _))
          · exact lt_of_lt_of_leY (h w hw).1 (hyF N) (hyF _) (hN w hw' hwt)
              (mono_le hyF hm (Nat.le_max_left _ _))
        · exact ⟨N, fun w hw hwt => by
            rcases List.mem_cons.mp hw with rfl | hw'
            · exact absurd hwt hat
            · exact hN w hw' hwt⟩
    obtain ⟨N, hN⟩ := key (parL x) fun w hw => by
      obtain ⟨h1, h2⟩ := parL_sub hw
      exact ⟨hx.of_mem_subs h1, by omega⟩
    exact hstep x hx hxt N hN

/-- 分割の補題（列） -/
theorem cmpList_split : ∀ {pre l : List Tm} {R : Tm}, NFL l → (∀ x, x ∈ pre → WNF x ∧ isPrincipal x = true) →
    cmpList l (pre ++ [R]) = .lt →
    ∃ ll l', l = ll ++ l' ∧ cmpList l (pre ++ l') ≠ .gt ∧ cmpList l' [R] = .lt
  | [], l, R, _, _, h => ⟨[], l, rfl, by
      rw [List.nil_append, cmpList_self _ fun x _ => cmpP_self x]
      decide, h⟩
  | h :: tl, [], R, _, _, _ => ⟨[], [], rfl, by
      rw [List.append_nil, cmpList_nil_cons]
      decide, cmpList_nil_cons _ _⟩
  | h :: tl, u :: us, R, hl, hp, e => by
    have hu := hl.1 u List.mem_cons_self
    have hh := hp h List.mem_cons_self
    cases ec : cmpP u h with
    | lt =>
      exact ⟨u :: us, [], (List.append_nil _).symm, by
        rw [List.append_nil, cmpList_head_lt _ _ ec]
        decide, cmpList_nil_cons _ _⟩
    | gt =>
      rw [List.cons_append, cmpList_cons_cons_ne _ _ (by rw [ec]; decide), ec] at e
      cases e
    | eq =>
      have e1 : u = h := eq_of_cmpP_eqY hu.1 hh.1 hu.2 hh.2 ec
      subst e1
      rw [List.cons_append, cmpList_cons_cons_eq _ _ ec] at e
      obtain ⟨ll, l', e2, h1, h2⟩ := cmpList_split (nfl_tail hl) (fun x hx => hp x (List.mem_cons_of_mem _ hx)) e
      exact ⟨u :: ll, l', by rw [e2]; rfl, by
        rw [List.cons_append, cmpList_cons_cons_eq _ _ ec]
        exact h1, h2⟩

/-- `a < pre ⊕ R` の分割：`a ≤ pre ⊕ a'`、`a' < R`、`a'` の加数は `a` の加数 -/
theorem lt_oadd_split {pre : List Tm} {R a : Tm} (hN : NFL (pre ++ [R])) (ha : WNF a)
    (hlt : Lt a (oadd (ofSummands pre) R)) :
    ∃ a', WNF a' ∧ Lt a' R ∧ (∀ u, u ∈ summands a' → u ∈ summands a) ∧ Le a (oadd (ofSummands pre) a') := by
  have hRN := hN.1 R (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  have hpreN := nfl_append_left hN
  have hge : ∀ s h r, s ∈ pre → summands R = h :: r → leB h s = true := fun s h r hs e => by
    rw [summands_principal hRN.2] at e
    simp only [List.cons.injEq] at e
    rw [← e.1, leB_iff]
    exact le_of_nfl_append (rest := []) hN s hs
  have hs : summands (oadd (ofSummands pre) R) = pre ++ [R] := by
    rw [summands_oadd_pre hpreN hRN.1 hge, summands_principal hRN.2]
  have h1 : cmpList (summands a) (pre ++ [R]) = .lt := by
    have := hlt
    unfold Lt at this
    rwa [cmp_eq, hs] at this
  obtain ⟨ll, l', e, h2, h3⟩ := cmpList_split (nfl_summands ha) hpreN.1 h1
  have hlN : NFL l' := by
    have := nfl_summands ha
    rw [e] at this
    exact nfl_append_right this
  have ha'F := wnf_ofSummands hlN
  have hs' : summands (ofSummands l') = l' := summands_ofSummands _ (nfl_principal hlN)
  have ha'R : Lt (ofSummands l') R := by
    unfold Lt
    rw [cmp_eq, hs', summands_principal hRN.2]
    exact h3
  refine ⟨_, ha'F, ha'R, fun u hu => ?_, ?_⟩
  · rw [hs'] at hu
    rw [e]
    exact List.mem_append_right _ hu
  · refine le_of_ne_gtY ha (wnf_oadd (wnf_ofSummands hpreN) ha'F) ?_
    rw [cmp_eq, summands_oadd_pre hpreN ha'F (head_le_pre (rest := []) hN ha'F ha'R), hs']
    exact h2

/-! ### 閉じた点 -/

theorem Cl.pos {σ β : Tm} (hβ : Cl σ β) (hσ0 : σ ≠ .zero) : β ≠ .zero := fun e => by
  have := hβ.2 .zero WNF.zero (zero_lt hσ0) (fun f hf => by simp [fr] at hf)
  rw [e] at this
  exact not_lt_zero _ this

/-- 閉じた点は列の項以下 -/
theorem Cl.le_big {t σ β : Tm} {s : SeqD} (hβ : Cl σ β) (hU : BigUB t σ s) (hβF : WNF β) (hβσ : Lt β σ) :
    Le β (s.big β) := by
  have hF := (hU.good.1 β hβF hβσ).1
  refine le_of_not_ltY hF hβF fun h => ?_
  have h1 := hU.lo .zero β β hβF hβF hβσ (WFY.inC_of_ltY _ hF hβF h)
  rw [hβ.1 β (Lt.irrefl _)] at h1
  cases h1

/-- 閉じた点の添字の項は `0` でない -/
theorem Cl.big_ne {t σ β : Tm} {s : SeqD} (hβ : Cl σ β) (hU : BigUB t σ s) (hβF : WNF β) (hβσ : Lt β σ) :
    s.big β ≠ .zero := fun e => by
  have h1 := hU.lo .zero .zero β WNF.zero hβF hβσ (by rw [e]; exact inC_zero _ _)
  rw [hβ.1 .zero (not_lt_zero _)] at h1
  cases h1

theorem Cl.of_psi {σ ξ A : Tm} (hβ : WNF (.Psi ξ σ A)) : Cl σ (.Psi ξ σ A) := by
  have hP := hβ.psi
  refine ⟨fun d hd => ?_, fun x hx hxσ hf => ?_⟩
  · cases e : inC (.Psi ξ σ A) .zero d with
    | false => rfl
    | true =>
      rcases inC_psi_iff.mp e with h | ⟨-, -, -, h⟩
      · exact absurd h hd
      · exact absurd h (not_lt_zero _)
  · exact coll_psiY hβ x hx (inC_of_fr_lt hx hP.piF hβ hP.aF hP.aF
      (WFY.inC_of_ltY _ hx hP.piF hxσ) (Or.inr (lt_psi_targetY hβ)) (Or.inl rfl) hf) hxσ

theorem Cl.of_xi {m : Nat} {A : Tm} (hβ : WNF (.Xi m A)) : Cl (.K m) (.Xi m A) := by
  have hn := hβ.xi.1
  have hKF := WNF.K' hn
  have hAF := hβ.xi.2.1
  have hβK : Lt (.Xi m A) (.K m) := (lt_K_iffY hβ hn).mpr (Nat.le_refl _)
  refine ⟨fun d hd => ?_, fun x hx hxσ hf => ?_⟩
  · cases e : inC (.Xi m A) .zero d with
    | false => rfl
    | true =>
      rcases inC_xi_iff.mp e with h | ⟨-, h⟩
      · exact absurd h hd
      · exact absurd h (not_lt_zero _)
  · exact coll_xi0 hβ x hx (inC_of_fr_lt hx hKF hβ hAF hAF (WFY.inC_of_ltY _ hx hKF hxσ) (Or.inr hβK)
      (Or.inl rfl) hf) hxσ

/-! ### 有限個の元の上界 -/

theorem exists_bound {y : Nat → Tm} {P : Tm → Prop} (hyF : ∀ n, WNF (y n)) (hm : ∀ n, Lt (y n) (y (n + 1))) :
    ∀ l : List Tm, (∀ w, w ∈ l → WNF w) → (∀ w, w ∈ l → P w → ∃ n, Lt w (y n)) →
      ∃ N, ∀ w, w ∈ l → P w → Lt w (y N)
  | [], _, _ => ⟨0, fun w hw => by cases hw⟩
  | a :: l, hF, h => by
    obtain ⟨N, hN⟩ := exists_bound (P := P) hyF hm l (fun w hw => hF w (List.mem_cons_of_mem _ hw))
      fun w hw => h w (List.mem_cons_of_mem _ hw)
    by_cases hP : P a
    · obtain ⟨N', hN'⟩ := h a List.mem_cons_self hP
      refine ⟨max N N', fun w hw hwP => ?_⟩
      rcases List.mem_cons.mp hw with rfl | hw'
      · exact lt_of_lt_of_leY (hF _ hw) (hyF N') (hyF _) hN' (mono_le hyF hm (Nat.le_max_right _ _))
      · exact lt_of_lt_of_leY (hF w hw) (hyF N) (hyF _) (hN w hw' hwP)
          (mono_le hyF hm (Nat.le_max_left _ _))
    · exact ⟨N, fun w hw hwP => by
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact absurd hwP hP
        · exact hN w hw' hwP⟩

/-! ### 正則項・和・`Ω_c` -/

theorem seqC_reg {σ b : Tm} (hb : WNF b) : SeqC σ (.reg σ b) := by
  show ∀ x β, WNF x → Lt x σ → WNF β → Lt β σ → Cl σ β → (∀ f, f ∈ fr σ x → Lt f β) → Lt x (oadd b β)
  intro x β hx hxσ hβ _ hC hf
  exact lt_of_lt_of_leY hx hβ (wnf_oadd hb hβ) (hC.2 x hx hxσ hf) (le_oadd_right hb hβ)

/-- `x < a + b` の分解 -/
theorem lt_plus_split {a b x : Tm} (ht : WNF (.plus a b)) (hx : WNF x) (hlt : Lt x (.plus a b)) :
    Le x a ∨ ∃ x', WNF x' ∧ Lt x' b ∧ (∀ u, u ∈ summands x' → u ∈ summands x) ∧ x = oadd a x' := by
  obtain ⟨ha, hb, hap, hb0⟩ := ht.plus
  have hN : NFL [a] := nfl_of_wnf_principal ha hap
  cases hs : summands x with
  | nil =>
    rw [eq_zero_of_summands_nil hs]
    exact Or.inl (zero_le _)
  | cons u us =>
    have hxN := nfl_summands hx
    rw [hs] at hxN
    have hu := hxN.1 u List.mem_cons_self
    cases ec : cmpP u a with
    | lt => exact Or.inl (Or.inr (lt_prin_of_head hs hap hu.2 ((lt_principal_iff hu.2 hap).mpr ec)))
    | gt =>
      exfalso
      have h1 := hlt
      unfold Lt at h1
      rw [cmp_eq, hs, summands_plus, cmpList_cons_cons_ne _ _ (by rw [ec]; decide), ec] at h1
      cases h1
    | eq =>
      have e1 : u = a := eq_of_cmpP_eqY hu.1 ha hu.2 hap ec
      subst e1
      have h1 := hlt
      unfold Lt at h1
      rw [cmp_eq, hs, summands_plus, cmpList_cons_cons_eq _ _ ec] at h1
      have hus : NFL us := nfl_tail hxN
      have hs' : summands (ofSummands us) = us := summands_ofSummands _ (nfl_principal hus)
      have hF := wnf_ofSummands hus
      have hlt' : Lt (ofSummands us) b := by
        unfold Lt
        rw [cmp_eq, hs']
        exact h1
      refine Or.inr ⟨_, hF, hlt', fun w hw => ?_, ?_⟩
      · rw [hs'] at hw
        exact List.mem_cons_of_mem _ hw
      · cases hus' : us with
        | nil =>
          subst hus'
          have e2 : x = u := by
            rw [← ofSummands_summands x hx, hs]
            rfl
          rw [e2]
          rfl
        | cons v vs =>
          subst hus'
          have hple : leB v u = true := by
            rw [leB_iff]
            exact hxN.2.1
          have e2 := oadd_eq_ofSummands ha hF hs'
          rw [e2, summands_principal hap, List.takeWhile_cons_of_pos hple, List.takeWhile_nil, hs']
          rw [← ofSummands_summands x hx, hs]
          rfl

theorem seqC_add {a b : Tm} {s : SeqD} (ht : WNF (.plus a b)) (hI : SeqI b s) (hC : SeqC b s) :
    SeqC (.plus a b) (.add a s) := by
  obtain ⟨ha, hb, hap, hb0⟩ := ht.plus
  unfold SeqI at hI
  unfold SeqC at hC ⊢
  have e : (SeqD.add a s).dom = s.dom := rfl
  rw [e]
  cases hd : s.dom with
  | zero => trivial
  | one => trivial
  | omega =>
    rw [hd] at hI hC
    intro x hx hlt
    have hF := fun n => (hI.1.good n).1
    rcases lt_plus_split ht hx hlt with h | ⟨x', hx', hlt', -, e'⟩
    · exact ⟨0, lt_of_le_of_ltY hx ha (wnf_oadd ha (hF 0)) h (lt_oadd_left ha (hF 0) (hI.1.pos 0))⟩
    · obtain ⟨n, hn⟩ := hC x' hx' hlt'
      refine ⟨n, ?_⟩
      rw [e']
      exact oadd_lt_oadd ha hx' (hF n) hn
  | big σ =>
    rw [hd] at hI hC
    intro x β hx hlt hβ hβσ hCl hf
    have hU := hI.1.1
    have hF := (hU.good.1 β hβ hβσ).1
    rcases lt_plus_split ht hx hlt with h | ⟨x', hx', hlt', hsub, e'⟩
    · exact lt_of_le_of_ltY hx ha (wnf_oadd ha hF) h (lt_oadd_left ha hF (hCl.big_ne hU hβ hβσ))
    · refine (show Lt x (oadd a (s.big β)) from ?_)
      rw [e']
      refine oadd_lt_oadd ha hx' hF (hC x' β hx' hlt' hβ hβσ hCl fun f hf' => hf f ?_)
      obtain ⟨u, hu, hfu⟩ := (mem_fr_iff hx').mp hf'
      exact (mem_fr_iff hx).mpr ⟨u, hsub u hu, hfu⟩

/-- `Ω_c`（`c` 極限）の列 -/
theorem seqC_om {c : Tm} {s : SeqD} (ht : WNF (.Om c)) (hs : ¬ isSucc c = true) (hI : SeqI c s)
    (hC : SeqC c s) : SeqC (.Om c) (.om s) := by
  have hcF := ht.om.1
  -- `Ω_c` 未満の主要項の形
  have hhd : ∀ {h : Tm}, WNF h → isPrincipal h = true → Lt h (.Om c) →
      (∃ d, h = .Om d ∧ Lt d c) ∨ (∃ m, h = .K m ∧ Lt (.K m) c) ∨ h = .one ∨ (IsOF h ∧ Lt h c) ∨
        ∃ d a, h = .Psi .zero (.Om d) a ∧ Lt d c := by
    intro h hF hp hlt
    cases h with
    | zero => cases hp
    | plus a b => cases hp
    | one => exact Or.inr (Or.inr (Or.inl rfl))
    | K m => exact Or.inr (Or.inl ⟨m, rfl, (lt_K_omY hF.k hcF).mp hlt⟩)
    | Om d => exact Or.inl ⟨d, rfl, (lt_om_iffY hF.om.1 hcF).mp hlt⟩
    | Xi m a =>
      have hOF : IsOF (.Xi m a) := Or.inl ⟨m, a, rfl⟩
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hOF, (lt_OF_omG hOF hF hcF).mp hlt⟩)))
    | Psi ξ κ a =>
      by_cases hκ : ∃ d, κ = .Om d
      · obtain ⟨d, rfl⟩ := hκ
        have hQ := hF.psi
        have hξ : ξ = .zero := by
          have := hQ.mlt
          simp only [mi] at this
          exact lt_oneY hQ.xiF this
        subst hξ
        have hd := om_succ_of_tgt hQ.tgt
        rcases (lt_psi_omY hF hcF).mp hlt with e | h'
        · exact absurd (e ▸ hd) hs
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨d, a, rfl, h'⟩)))
      · have hOF : IsOF (.Psi ξ κ a) := IsOF.psi hF fun d e => hκ ⟨d, e⟩
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hOF, (lt_OF_omG hOF hF hcF).mp hlt⟩)))
  have hhead : ∀ {x h : Tm} {r : List Tm}, WNF x → summands x = h :: r → Lt x (.Om c) →
      WNF h ∧ isPrincipal h = true ∧ Lt h (.Om c) := by
    intro x h r hx e hlt
    have hu := (nfl_summands hx).1 h (by rw [e]; exact List.mem_cons_self)
    exact ⟨hu.1, hu.2, lt_of_le_of_ltY hu.1 hx ht (head_leY hx e) hlt⟩
  unfold SeqI at hI
  unfold SeqC at hC ⊢
  have e : (SeqD.om s).dom = s.dom := rfl
  rw [e]
  cases hd : s.dom with
  | zero => trivial
  | one => trivial
  | omega =>
    rw [hd] at hI hC
    have hF := fun n => (hI.1.good n).1
    -- 先頭の加数の上界の添字
    have hbd : ∀ {h : Tm}, WNF h → isPrincipal h = true → Lt h (.Om c) → ∃ n, Lt h (.Om (succT (s.nat n))) := by
      intro h hhF hp hlt
      rcases hhd hhF hp hlt with ⟨d, rfl, hd'⟩ | ⟨m, rfl, hm⟩ | rfl | ⟨hOF, hl⟩ | ⟨d, a, rfl, hd'⟩
      · obtain ⟨n, hn⟩ := hC d hhF.om.1 hd'
        have hsb := succT_WNF (hF n)
        exact ⟨n, (lt_om_iffY hhF.om.1 hsb).mpr (lt_transY hhF.om.1 (hF n) hsb hn (lt_succT _))⟩
      · obtain ⟨n, hn⟩ := hC _ hhF hm
        have hsb := succT_WNF (hF n)
        exact ⟨n, (lt_K_omY hhF.k hsb).mpr (lt_transY hhF (hF n) hsb hn (lt_succT _))⟩
      · exact ⟨0, one_lt_om (WNF.om_succT (hF 0))⟩
      · obtain ⟨n, hn⟩ := hC _ hhF hl
        have hsb := succT_WNF (hF n)
        exact ⟨n, (lt_OF_omG hOF hhF hsb).mpr (lt_transY hhF (hF n) hsb hn (lt_succT _))⟩
      · have hQ := hhF.psi.piF.om.1
        obtain ⟨n, hn⟩ := hC d hQ hd'
        have hsb := succT_WNF (hF n)
        exact ⟨n, (lt_psi_omY hhF hsb).mpr (Or.inr (lt_transY hQ (hF n) hsb hn (lt_succT _)))⟩
    intro x hx hlt
    cases hs' : summands x with
    | nil =>
      refine ⟨0, ?_⟩
      show Lt x (.Om (sc (s.nat 0)))
      rw [eq_zero_of_summands_nil hs']
      exact zero_lt (by intro e'; cases e')
    | cons u us =>
      obtain ⟨huF, hup', hul⟩ := hhead hx hs' hlt
      obtain ⟨n, hn⟩ := hbd huF hup' hul
      exact ⟨n, lt_prin_of_head hs' rfl hup' hn⟩
  | big σ =>
    rw [hd] at hI hC
    have hU := hI.1.1
    intro x β hx hlt hβ hβσ hCl hf
    have hFb := (hU.good.1 β hβ hβσ).1
    have hsb := succT_WNF hFb
    show Lt x (.Om (sc (s.big β)))
    have hle := hCl.le_big hU hβ hβσ
    have hβs : Lt β (.Om (sc (s.big β))) := by
      have h1 : Lt β (succT (s.big β)) := lt_of_le_of_ltY hβ hFb hsb hle (lt_succT _)
      exact lt_transY hβ hsb (WNF.om_succT hFb) h1 (WNF.om_succT hFb).om.2.2
    cases hs' : summands x with
    | nil =>
      rw [eq_zero_of_summands_nil hs']
      exact zero_lt (by intro e'; cases e')
    | cons u us =>
      obtain ⟨huF, hup', hul⟩ := hhead hx hs' hlt
      have hfu : ∀ f, f ∈ fr σ u → Lt f β := fun f hf' =>
        hf f ((mem_fr_iff hx).mpr ⟨u, by rw [hs']; exact List.mem_cons_self, hf'⟩)
      refine lt_prin_of_head hs' rfl hup' ?_
      rcases hhd huF hup' hul with ⟨d, rfl, hd'⟩ | ⟨m, rfl, hm⟩ | rfl | ⟨hOF, hl⟩ | ⟨d, a, rfl, hd'⟩
      · exact (lt_om_iffY huF.om.1 hsb).mpr (lt_transY huF.om.1 hFb hsb
          (hC d β huF.om.1 hd' hβ hβσ hCl fun f h' => hfu f (by rw [fr]; exact h')) (lt_succT _))
      · exact (lt_K_omY huF.k hsb).mpr (lt_transY huF hFb hsb
          (hC _ β huF hm hβ hβσ hCl fun f h' => by simp [fr] at h') (lt_succT _))
      · exact one_lt_om (WNF.om_succT hFb)
      · exact (lt_OF_omG hOF huF hsb).mpr (lt_transY huF hFb hsb
          (hC _ β huF hl hβ hβσ hCl hfu) (lt_succT _))
      · have hQ := huF.psi.piF.om.1
        by_cases huσ : Lt (.Psi .zero (.Om d) a) σ
        · have h1 : Lt (.Psi .zero (.Om d) a) β := hfu _ (by simp [fr, huσ])
          exact lt_transY huF hβ (WNF.om_succT hFb) h1 hβs
        · have h2 : Lt d (s.big β) := hC d β hQ hd' hβ hβσ hCl fun f h' => hfu f (by
            rw [fr]
            simp only [huσ, ↓reduceIte, List.mem_append]
            exact Or.inl (Or.inr (by rw [fr]; exact h')))
          exact (lt_psi_omY huF hsb).mpr (Or.inr (lt_transY hQ hFb hsb h2 (lt_succT _)))

/-! ### 塔の共終性 -/

theorem mono_le' {A : Nat → Tm} (hAF : ∀ n, WNF (A n)) (hm : ∀ n, Le (A n) (A (n + 1))) {m n : Nat}
    (h : m ≤ n) : Le (A m) (A n) := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    rw [this]
    exact Or.inl rfl
  | succ k ih =>
    by_cases e : m = k + 1
    · rw [e]
      exact Or.inl rfl
    · exact le_transY (hAF m) (hAF k) (hAF (k + 1)) (ih (by omega)) (hm k)

/-- 塔：`γ_{n+1}` は `A_n` の崩壊（値は `σ` 未満）で、`T` 未満の引数は `σ` についての前線が塔の中なら `A_n` を越えない -/
structure Tow (σ T : Tm) (γ A : Nat → Tm) : Prop where
  hTF : WNF T
  hγF : ∀ n, WNF (γ n)
  mono : ∀ n, Lt (γ n) (γ (n + 1))
  hC : ∀ n, Clo (γ (n + 1)) (A n) σ
  hAm : ∀ n, Le (A n) (A (n + 1))
  hlt : ∀ n, Lt (γ n) σ
  harg : ∀ b, WNF b → Lt b T → (∀ f, f ∈ fr σ b → ∃ n, Lt f (γ n)) → ∃ n, Lt b (A n)

/-- `C(g, γ_N)`（`g < T`）の `σ` 未満の元は塔の中 -/
theorem Tow.hull {σ T : Tm} {γ A : Nat → Tm} (H : Tow σ T γ A) {g : Tm} {N : Nat} (hg : WNF g) (hgT : Le g T) :
    ∀ z, WNF z → inC z g (γ N) = true → Lt z σ → ∃ n, Lt z (γ n) := by
  intro z
  induction hn : z.size using Nat.strongRecOn generalizing z with
  | ind n ih =>
    intro hz hC hzσ
    by_cases hzN : Lt z (γ N)
    · exact ⟨N, hzN⟩
    have hσF := (H.hC 0).hT
    have hγN := H.hγF N
    have hNz : Le (γ N) z := le_of_not_ltY hz hγN hzN
    -- 部分項
    have hsub : ∀ w, w ∈ parF z → WNF w → inC w g (γ N) = true → Lt w z → ∃ m, Lt w (γ m) := by
      intro w hw hwF hwC hwz
      have := (parL_sub (parF_sub_parL hw)).2
      exact ih w.size (by omega) w rfl hwF hwC (lt_transY hwF hz hσF hwz hzσ)
    have hfrσ : ∀ {b : Tm}, WNF b → b.size < z.size → inC b g (γ N) = true →
        ∀ f, f ∈ fr σ b → ∃ m, Lt f (γ m) := by
      intro b hb hsz hbC f hf
      have hfs := size_le_of_mem_subs (fr_spec hf).1
      have hfC : inC f g (γ N) = true := fr_of_inC b (fun u hu hn' hu' => hn' (lt_transY (hb.of_mem_subs hu)
        hγN hσF hu' (H.hlt N))) hbC f hf
      exact ih f.size (by omega) f rfl (hb.of_mem_subs (fr_spec hf).1) hfC (fr_spec hf).2
    have hparC : ∀ w, w ∈ parF z → inC w g (γ N) = true := by
      intro w hw
      cases z with
      | zero | one | K _ => simp [parF] at hw
      | plus a b =>
        rw [inC_plus, Bool.and_eq_true] at hC
        simp only [parF, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hC.1
        · exact hC.2
      | Om e =>
        rw [inC_om] at hC
        simp only [parF, List.mem_singleton] at hw
        rw [hw]
        exact hC
      | Xi j b =>
        rcases inC_xi_iff.mp hC with h' | ⟨h1, -⟩
        · exact absurd h' hzN
        · have hj := hz.xi.1
          have hKl : Lt (.Xi j b) (.K j) := (lt_K_iffY hz hj).mpr (Nat.le_refl _)
          exact fr_of_inC b (fun u hu hn' hu' => hn' (lt_of_lt_of_leY (hz.xi.2.1.of_mem_subs hu) hγN (WNF.K' hj)
            hu' (Or.inr (lt_of_le_of_ltY hγN hz (WNF.K' hj) hNz hKl)))) h1 w hw
      | Psi s k a =>
        rcases inC_psi_iff.mp hC with h' | ⟨h1, h2, h3, -⟩
        · exact absurd h' hzN
        · have hP := hz.psi
          have hkl : Lt (.Psi s k a) k := lt_psi_targetY hz
          have hNk : Lt (γ N) k := lt_of_le_of_ltY hγN hz hP.piF hNz hkl
          simp only [parF, List.mem_append] at hw
          rcases hw with (hw | hw) | hw
          · exact fr_of_inC a (fun u hu hn' hu' => hn' (lt_transY (hP.aF.of_mem_subs hu) hγN hP.piF hu' hNk))
              h3 w hw
          · exact fr_of_inC s (fun u hu hn' hu' => hn' (lt_transY (hP.xiF.of_mem_subs hu) hγN hP.piF hu' hNk))
              h2 w hw
          · exact fr_of_inC k (fun u hu hn' hu' => hn' (lt_transY (hP.piF.of_mem_subs hu) hγN hP.piF hu' hNk))
              h1 w hw
    have hparF : ∀ w, w ∈ parF z → WNF w := fun w hw => hz.of_mem_subs (parL_sub (parF_sub_parL hw)).1
    obtain ⟨N₁, hN₁⟩ := exists_bound (P := fun _ => True) H.hγF H.mono (parF z) hparF
      fun w hw _ => hsub w hw (hparF w hw) (hparC w hw) (parF_lt hz hw)
    -- 引数
    have harg : ∃ m, ∀ a, argR? z = some a → Lt a (A m) := by
      cases z with
      | Xi j b =>
        rcases inC_xi_iff.mp hC with h' | ⟨h1, h2⟩
        · exact absurd h' hzN
        · obtain ⟨m, hm⟩ := H.harg b hz.xi.2.1 (lt_of_lt_of_leY hz.xi.2.1 hg H.hTF h2 hgT)
            (hfrσ hz.xi.2.1 (by simp only [Tm.size]; omega) h1)
          exact ⟨m, fun a e => by
            cases e
            exact hm⟩
      | Psi s k a =>
        rcases inC_psi_iff.mp hC with h' | ⟨-, -, h3, h4⟩
        · exact absurd h' hzN
        · have haF := hz.psi.aF
          obtain ⟨m, hm⟩ := H.harg a haF (lt_of_lt_of_leY haF hg H.hTF h4 hgT)
            (hfrσ haF (by simp only [Tm.size]; omega) h3)
          exact ⟨m, fun a' e => by
            cases e
            exact hm⟩
      | _ => exact ⟨0, fun a e => by cases e⟩
    obtain ⟨m, hm⟩ := harg
    have hAF : ∀ n, WNF (A n) := fun n => (H.hC n).hA
    refine ⟨max N₁ m + 1, (H.hC (max N₁ m)).lt hz hzσ (fun w hw => ?_) fun a e => ?_⟩
    · exact lt_of_lt_of_leY (hparF w hw) (H.hγF N₁) (H.hγF _) (hN₁ w hw trivial)
        (mono_le H.hγF H.mono (by omega))
    · exact lt_of_lt_of_leY (wnf_of_argR hz e) (hAF m) (hAF _) (hm a e)
        (mono_le' hAF H.hAm (Nat.le_max_right _ _))

end RTKA.Fund
