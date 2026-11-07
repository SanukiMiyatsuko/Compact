import Compact.FS.LadOmLim

/-! 目標が `Ω_c` の崩壊の区間の下界の道具。

* 帯の分類（`band_om`）：`Ω_c` の底と `Ω_c` の間の節点は `Ψ^0_{Ω_c}` の崩壊。
* 閉包の証人（`witness_om`）：`x` が `C(V, Ψ^0_{Ω_c}(V))` に入らなければ、`x` の部分項に `Ψ^0_{Ω_c}(V)` 以上で
  引数が `V` 以上の崩壊がある。
* 閉包の補題（`hull_om`）：`y = Ψ^0_{Ω_c}(A) < z = Ψ^0_{Ω_c}(W)` で、`q = Ψ^0_{Ω_c}(V)` が `A ≤ V` かつ `W` の前線より
  大きく、`A` の崩壊の節点で引数が `[A, W)` にあるものが `W` の前線以下なら、`y ≤ q`。 -/

namespace RTKA.Fund

open Tm W

/-- 帯の分類：`Ω_c` の底と `Ω_c` の間の節点は `Ψ^0_{Ω_c}` の崩壊 -/
theorem band_om {c w : Tm} (hc : WNF (.Om c)) (hs : isSucc c = true) (hw : WNF w)
    (hn : (∃ m a, w = .Xi m a) ∨ (∃ s p a, w = .Psi s p a))
    (h1 : Lt (omBase c) w) (h2 : Lt w (.Om c)) : ∃ V, w = .Psi .zero (.Om c) V := by
  have hcF := hc.om.1
  have hpF := wnf_pred hcF
  have hce : succT (pred c) = c := succT_pred hcF hs
  have hBF := (omBase_wnf hc hs).1
  -- `Ω` の不動点は帯にない
  have hOF : IsOF w → False := fun hO => by
    have h3 : Lt w c := (lt_OF_omG hO hw hcF).mp h2
    have h4 : Le w (pred c) := le_of_lt_succT hw hpF (by rw [hce]; exact h3)
    by_cases hc1 : c = .one
    · have : pred c = .zero := by rw [hc1]; rfl
      rw [this] at h4
      rcases h4 with e | h'
      · rw [e] at hO
        rcases hO with ⟨n, a, e'⟩ | ⟨ξ, π, a, e', -, -⟩ <;> cases e'
      · exact not_lt_zero _ h'
    · have hpd0 : pred c ≠ .zero := pred_ne_zero hcF hs hc1
      have h5 : Le (pred c) (omBase c) := by
        unfold omBase
        rw [ite_eq_right hc1]
        exact le_omHat hpF hpd0
      exact not_lt_of_leY hw hBF (le_transY hw hpF hBF h4 h5) h1
  rcases hn with ⟨m, a, rfl⟩ | ⟨s, p, a, rfl⟩
  · exact (hOF (Or.inl ⟨m, a, rfl⟩)).elim
  rcases hw.shape with ⟨d, rfl, rfl⟩ | hsh
  · have hd := hw.psiOm
    have h3 : Le d c := (lt_psi_omY hw hcF).mp h2
    rcases h3 with e | h3
    · exact ⟨a, by rw [e]⟩
    · exfalso
      have hdF := hd.1
      have h4 : Le d (pred c) := le_of_lt_succT hdF hpF (by rw [hce]; exact h3)
      by_cases hc1 : c = .one
      · have : pred c = .zero := by rw [hc1]; rfl
        rw [this] at h4
        rcases h4 with e | h'
        · rw [e] at hd
          exact absurd hd.2.2.1 (by simp [isSucc, summands])
        · exact not_lt_zero _ h'
      have hpd0 : pred c ≠ .zero := pred_ne_zero hcF hs hc1
      have hB : omBase c = omHat (pred c) := by unfold omBase; rw [ite_eq_right hc1]
      rw [hB] at h1
      rcases omHat_cases hpF hpd0 with ⟨e, -⟩ | ⟨e, ⟨k, hk⟩ | hO⟩
      · rw [e] at h1
        exact not_lt_of_leY hdF hpF h4 ((lt_om_psiY hw).mp h1)
      · rw [e, hk] at h1
        rw [hk] at h4
        have hk1 : 1 ≤ k := by
          have := hpF
          rw [hk] at this
          exact this.k
        have hdK : Lt d (.K k) := by
          rcases h4 with e' | h'
          · rw [e'] at hd
            exact absurd hd.2.2.1 (by simp [isSucc, summands])
          · exact h'
        have hwK : Lt (.Psi .zero (.Om d) a) (.K k) := by
          rw [lt_K_iffY hw hk1]
          simp only [lev]
          exact (lt_K_iffY hdF hk1).mp hdK
        exact Lt.asymmY (WNF.K' hk1) hw h1 hwK
      · rw [e] at h1
        exact not_lt_of_leY hdF hpF h4 ((lt_OF_psiOm hO hpF hw).mp h1)
  · exact (hOF (IsOF.psi hw (notOm_of_shape hsh))).elim

/-- 閉包の証人 -/
theorem witness_om {c V : Tm} (hq : WNF (.Psi .zero (.Om c) V)) :
    ∀ x, WNF (.Psi .zero (.Om c) x) → Le x V → ¬ inC x V (.Psi .zero (.Om c) V) = true →
      ∃ Vu, WNF (.Psi .zero (.Om c) Vu) ∧ Tm.Psi .zero (.Om c) Vu ∈ subs x ∧
        Le (.Psi .zero (.Om c) V) (.Psi .zero (.Om c) Vu) ∧ Le V Vu ∧
        Lt (.Psi .zero (.Om c) Vu) (.Psi .zero (.Om c) x) := by
  intro x
  induction hsz : x.size using Nat.strongRecOn generalizing x with
  | ind N ih =>
  intro hx hxV hn
  have hxF := hx.psi.aF
  have hπ := hx.psi.piF
  have hs : isSucc c = true := (WNF.psiOm hx).2.2.1
  have hVF := hq.psi.aF
  have hqπ : Le (.Psi .zero (.Om c) V) (.Om c) := Or.inr (lt_psi_targetY hq)
  have hiff := inC_frY hxF hπ hq hxF hVF hx.psi.Ca hqπ hxV
  obtain ⟨w, hw, hwn⟩ : ∃ w, w ∈ fr (.Om c) x ∧ ¬ inC w V (.Psi .zero (.Om c) V) = true := by
    refine Classical.byContradiction fun h => hn (hiff.mpr fun w hw => ?_)
    exact Classical.byContradiction fun h' => h ⟨w, hw, h'⟩
  have hwF : WNF w := hxF.of_mem_subs (fr_spec hw).1
  have hwπ : Lt w (.Om c) := (fr_spec hw).2
  have hwy : Lt w (.Psi .zero (.Om c) x) := FWOrder.k2 hx w hw
  have hqw : Le (.Psi .zero (.Om c) V) w :=
    le_of_not_ltY hwF hq fun h => hwn (WFY.inC_of_ltY V hwF hq h)
  obtain ⟨Vw, rfl⟩ := band_om hπ hs hwF (fr_node hw) (lt_of_lt_of_leY (omBase_wnf hπ hs).1 hq hwF
    (omBase_lt_psi hq) hqw) hwπ
  by_cases hVw : Lt Vw V
  · have hn2 : ¬ inC Vw V (.Psi .zero (.Om c) V) = true := fun h => hwn (inC_psi_iff.mpr (Or.inr
      ⟨inC_tgt_of_k2t hq fun u hu => FWOrder.k2t hq u hu, inC_zero _ _, h, hVw⟩))
    have hsz2 : Vw.size < N := by
      have h1 := size_le_of_mem_subs (fr_spec hw).1
      simp only [Tm.size] at h1
      omega
    obtain ⟨Vu, h1, h2, h3, h4, h5⟩ := ih Vw.size hsz2 Vw rfl hwF (Or.inr hVw) hn2
    exact ⟨Vu, h1, subs_trans (fr_spec hw).1 (subs_psi_a h2), h3, h4,
      lt_transY h1 hwF hx h5 hwy⟩
  · exact ⟨Vw, hwF, (fr_spec hw).1, hqw, le_of_not_ltY hwF.psi.aF hVF hVw, hwy⟩

/-- 閉包の補題 -/
theorem hull_om {c A V W : Tm} (hy : WNF (.Psi .zero (.Om c) A)) (hq : WNF (.Psi .zero (.Om c) V))
    (hz : WNF (.Psi .zero (.Om c) W)) (hAV : Le A V)
    (hyz : Lt (.Psi .zero (.Om c) A) (.Psi .zero (.Om c) W))
    (hqW : ∀ f, f ∈ fr (.Om c) W → Lt f (.Psi .zero (.Om c) V))
    (hAvoid : ∀ Vu, WNF (.Psi .zero (.Om c) Vu) → Tm.Psi .zero (.Om c) Vu ∈ subs A → Le A Vu → Lt Vu W →
      ∃ f, f ∈ fr (.Om c) W ∧ Le (.Psi .zero (.Om c) Vu) f) :
    Le (.Psi .zero (.Om c) A) (.Psi .zero (.Om c) V) := by
  refine le_of_not_ltY hq hy fun hlt => ?_
  have hπ := hy.psi.piF
  have hnC : ¬ inC (.Psi .zero (.Om c) A) V (.Psi .zero (.Om c) V) = true := fun h =>
    Lt.asymmY hq hy hlt (coll_psiY hq _ hy h (lt_psi_targetY hy))
  rcases hAV with e | hAVl
  · subst e
    exact Lt.irrefl _ hlt
  have hnA : ¬ inC A V (.Psi .zero (.Om c) V) = true := fun h => hnC (inC_psi_iff.mpr (Or.inr
    ⟨inC_tgt_of_k2t hq fun u hu => FWOrder.k2t hq u hu, inC_zero _ _, h, hAVl⟩))
  have hAV : Le A V := Or.inr hAVl
  obtain ⟨Vu, hu, hus, hqu, hVu, huy⟩ := witness_om hq A hy hAV hnA
  have huz := lt_transY hu hy hz huy hyz
  have hWF := hz.psi.aF
  have hVuF := hu.psi.aF
  have hVuW : Lt Vu W := by
    rcases triY hVuF hWF with h | h | h
    · exact h
    · exfalso
      rw [h] at huz
      exact Lt.irrefl _ huz
    · exact absurd (psi_lt_psi_of_arg hz hu h fun f hf => lt_of_lt_of_leY ((hWF).of_mem_subs (fr_spec hf).1) hq hu
        (hqW f hf) hqu) (Lt.asymmY hu hz huz)
  obtain ⟨f, hf, huf⟩ := hAvoid Vu hu hus (le_transY hy.psi.aF hq.psi.aF hVuF hAV hVu) hVuW
  have hfF := hWF.of_mem_subs (fr_spec hf).1
  exact not_lt_of_leY hq hfF (le_transY hq hu hfF hqu huf) (hqW f hf)

end RTKA.Fund
