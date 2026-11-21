import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

open Filter Topology

namespace GlobalTheory.EvenTheta

theorem exists_entire_of_locally_dvd {F S : ℂ → ℂ} (hS : Dense {z | S z ≠ 0})
    (h : ∀ w, ∃ g : ℂ → ℂ, AnalyticAt ℂ g w ∧ ∀ᶠ z in 𝓝 w, F z = S z * g z) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ z, F z = S z * G z := by
  choose g hg hF using h
  refine ⟨fun w => g w w, fun w => ?_, fun z => (hF z).self_of_nhds⟩
  refine (hg w).differentiableAt.congr_of_eventuallyEq ?_
  filter_upwards [(hg w).eventually_analyticAt, (hF w).eventually_nhds] with z h1 h2
  refine tendsto_nhds_unique_of_frequently_eq (hg z).continuousAt h1.continuousAt ?_
  have h3 : ∃ᶠ y in 𝓝 z, S y ≠ 0 := mem_closure_iff_frequently.1 (hS z)
  refine (h3.and_eventually (h2.and (hF z))).mono fun y hy => ?_
  exact mul_left_cancel₀ hy.1 (hy.2.2.symm.trans hy.2.1)

theorem IsLat.exists_sg_add {Λ : AddSubgroup ℂ} (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) :
    ∃ c : ℂ → ℂ, Differentiable ℂ c ∧ ∀ z, sgStar Λ (z + ω) = c z * sgStar Λ z := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  rw [GlobalTheory.OddTheta.sgStar_eq L Λ hL]
  refine ⟨_, ?_, GlobalTheory.canonicalSigma_add L ((hL ω).1 hω)⟩
  unfold GlobalTheory.latticeForm
  fun_prop

theorem exists_eq_sg_sq_mul : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (k : ℕ) (F : ℂ → ℂ), Differentiable ℂ F → (∀ z, F (-z) = F z) → F 0 = 0 → (∀ ω ∈ Λ, ∀ z, F (z + ω) * sgStar Λ z ^ (2 * (k + 1)) = F z * sgStar Λ (z + ω) ^ (2 * (k + 1))) → ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ z, G (-z) = G z) ∧ (∀ z, F z = sgStar Λ z ^ 2 * G z) ∧ ∀ ω ∈ Λ, ∀ z, G (z + ω) * sgStar Λ z ^ (2 * k) = G z * sgStar Λ (z + ω) ^ (2 * k) := by
  intro Λ hΛ k F hF he h0 hlaw
  have hσ := hΛ.differentiable
  have hσc := hσ.continuous
  have hFc := hF.continuous
  have hne : ∀ z ∉ Λ, sgStar Λ z ≠ 0 := fun z hz => (hΛ.sg_eq_zero z).not.2 hz
  obtain ⟨h, hh, eh⟩ := GlobalTheory.exists_eq_add_sq_mul_of_even (hF.analyticAt 0) he
  have hu : AnalyticAt ℂ (dslope (sgStar Λ) 0) 0 :=
    (differentiableOn_univ.1
      ((Complex.differentiableOn_dslope univ_mem).2 hσ.differentiableOn)).analyticAt 0
  have hu0 : dslope (sgStar Λ) 0 0 ≠ 0 := by
    rw [dslope_same, (GlobalTheory.OddTheta.sgStar_laws Λ hΛ).1.2.1]
    exact one_ne_zero
  have eu : ∀ z, sgStar Λ z = z * dslope (sgStar Λ) 0 z := fun z => by
    have := sub_smul_dslope (sgStar Λ) 0 z
    rw [(hΛ.sg_eq_zero 0).2 Λ.zero_mem] at this
    simpa using this.symm
  obtain ⟨G, hG, eG⟩ := exists_entire_of_locally_dvd (F := F) (S := fun z => sgStar Λ z ^ 2)
    (hΛ.dense_compl.mono fun z hz => pow_ne_zero 2 (hne z hz)) fun w => by
      by_cases hw : w ∈ Λ
      · obtain ⟨c, hc, ec⟩ := hΛ.exists_sg_add hw
        have hcc := hc.continuous
        have eF : ∀ z, F (z + w) = c z ^ (2 * (k + 1)) * F z := fun z => by
          refine congrFun (Continuous.ext_on hΛ.dense_compl (f := fun z => F (z + w))
            (g := fun z => c z ^ (2 * (k + 1)) * F z) (by fun_prop) (by fun_prop) fun z hz => ?_) z
          refine mul_right_cancel₀ (pow_ne_zero (2 * (k + 1)) (hne z hz)) ?_
          beta_reduce
          rw [hlaw w hw, ec]
          ring
        have hs : AnalyticAt ℂ (fun y : ℂ => y - w) w := by fun_prop
        have ha : AnalyticAt ℂ
            (fun z => c z ^ (2 * k) * h z / dslope (sgStar Λ) 0 z ^ 2) 0 :=
          (((hc.analyticAt 0).pow _).mul hh).div (hu.pow 2) (pow_ne_zero 2 hu0)
        refine ⟨_, ha.comp_of_eq hs (sub_self w), ?_⟩
        filter_upwards [(hu.comp_of_eq hs (sub_self w)).continuousAt.eventually_ne
          (y := 0) (by simpa using hu0)] with y hy
        obtain ⟨z, rfl⟩ : ∃ z, y = z + w := ⟨y - w, by ring⟩
        simp only [Function.comp, add_sub_cancel_right] at hy ⊢
        rw [eF, ec, eh, h0, eu z]
        field_simp
        ring
      · refine ⟨fun z => F z / sgStar Λ z ^ 2, (hF.analyticAt w).div ((hσ.analyticAt w).pow 2)
          (pow_ne_zero 2 (hne w hw)), ?_⟩
        filter_upwards [hσc.continuousAt.eventually_ne (hne w hw)] with y hy
        field_simp
  have hGc := hG.continuous
  refine ⟨G, hG, fun z => ?_, eG, fun ω hω z => ?_⟩
  · refine congrFun (Continuous.ext_on hΛ.dense_compl (f := fun z => G (-z)) (by fun_prop) hGc
      fun z hz => ?_) z
    refine mul_left_cancel₀ (pow_ne_zero 2 (hne z hz)) ?_
    have h1 := eG (-z)
    rw [he, hΛ.sg_neg, neg_sq] at h1
    exact h1.symm.trans (eG z)
  · refine congrFun (Continuous.ext_on hΛ.dense_compl
      (f := fun z => G (z + ω) * sgStar Λ z ^ (2 * k))
      (g := fun z => G z * sgStar Λ (z + ω) ^ (2 * k)) (by fun_prop) (by fun_prop)
      fun z hz => ?_) z
    have hz' : z + ω ∉ Λ := fun h' => hz (by simpa using Λ.sub_mem h' hω)
    refine mul_left_cancel₀
      (mul_ne_zero (pow_ne_zero 2 (hne z hz)) (pow_ne_zero 2 (hne _ hz'))) ?_
    have h1 := hlaw ω hω z
    rw [eG z, eG (z + ω)] at h1
    beta_reduce at h1 ⊢
    linear_combination h1

end GlobalTheory.EvenTheta
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem exists_wpF_eq : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ r : ℂ, ∃ Q, Q ∉ Λ ∧ wpF Λ Q = r := by
  intro Λ h r
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  obtain ⟨z, hz, e⟩ := GlobalTheory.exists_weierstrassP_eq L r
  exact ⟨z, (hL z).not.2 hz, (GlobalTheory.OddTheta.wpF_eq L Λ hL z).trans e⟩

end GlobalTheory.EvenTheta
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

open Polynomial

variable {Λ : AddSubgroup ℂ}

theorem IsLat.wpF_add_of_mem (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) (z : ℂ) :
    wpF Λ (z + ω) = wpF Λ z := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  rw [GlobalTheory.OddTheta.wpF_eq L Λ hL, GlobalTheory.OddTheta.wpF_eq L Λ hL]
  exact L.weierstrassP_add_coe z ⟨ω, (hL ω).1 hω⟩

theorem IsLat.entire_eq_of_periodic (h : IsLat Λ) {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hper : ∀ ω ∈ Λ, ∀ z, F (z + ω) = F z) (z : ℂ) : F z = F 0 := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  exact hF.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L.lattice _ hF.continuous
      fun z w hw => hper w ((hL w).2 hw) z).isBounded z 0

theorem IsLat.sqTh_law (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) {ω : ℂ} (hω : ω ∈ Λ) (z : ℂ) :
    sqTh Λ v (z + ω) * sgStar Λ z ^ 2 = sqTh Λ v z * sgStar Λ (z + ω) ^ 2 := by
  by_cases hz : z ∈ Λ
  · rw [(h.sg_eq_zero z).2 hz, (h.sg_eq_zero _).2 (add_mem hz hω)]
    simp
  · have hz' : z + ω ∉ Λ := fun h' => hz (by simpa using sub_mem h' hω)
    rw [h.sqTh_eq hv hz, h.sqTh_eq hv hz', h.wpF_add_of_mem hω]
    ring

theorem IsLat.exists_poly_wp (h : IsLat Λ) (k : ℕ) : ∀ F : ℂ → ℂ, Differentiable ℂ F →
    (∀ z, F (-z) = F z) →
    (∀ ω ∈ Λ, ∀ z, F (z + ω) * sgStar Λ z ^ (2 * k) = F z * sgStar Λ (z + ω) ^ (2 * k)) →
    ∃ P : ℂ[X], P.natDegree ≤ k ∧ P.coeff k = F 0 ∧
      ∀ z ∉ Λ, F z = sgStar Λ z ^ (2 * k) * P.eval (wpF Λ z) := by
  induction k with
  | zero =>
    intro F hF _ hlaw
    refine ⟨C (F 0), by simp, by simp, fun z _ => ?_⟩
    simpa using h.entire_eq_of_periodic hF (fun ω hω z => by simpa using hlaw ω hω z) z
  | succ k ih =>
    intro F hF he hlaw
    obtain ⟨v, hv⟩ := h.dense_compl.nonempty
    have hv : v ∉ Λ := hv
    have hd := h.differentiable_sqTh v
    obtain ⟨G, hG, hGe, hFG, hGl⟩ := GlobalTheory.EvenTheta.exists_eq_sg_sq_mul Λ h k
      (fun z => F z - F 0 * sqTh Λ v z ^ (k + 1)) (by fun_prop)
      (fun z => by simp only [he, sqTh_neg]) (by simp [h.sqTh_zero hv])
      (fun ω hω z => by
        have h1 := congrArg (· ^ (k + 1)) (h.sqTh_law hv hω z)
        simp only [mul_pow, ← pow_mul] at h1
        linear_combination hlaw ω hω z - F 0 * h1)
    obtain ⟨P, hP, -, hPG⟩ := ih G hG hGe hGl
    have hm : ((X - C (wpF Λ v)) ^ (k + 1) : ℂ[X]).Monic := (monic_X_sub_C _).pow _
    have hdeg : ((X - C (wpF Λ v)) ^ (k + 1) : ℂ[X]).natDegree = k + 1 := by
      rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
    refine ⟨C (F 0) * (X - C (wpF Λ v)) ^ (k + 1) + P, ?_, ?_, fun z hz => ?_⟩
    · refine natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans hdeg.le) (by omega)
    · have h1 := hm.coeff_natDegree
      rw [hdeg] at h1
      rw [coeff_add, coeff_C_mul, h1, coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < k + 1)]
      simp
    · have h1 := hFG z
      simp only [hPG z hz, h.sqTh_eq hv hz, mul_pow, ← pow_mul] at h1
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_X]
      linear_combination h1

theorem exists_eval_eq_prod_fin {k : ℕ} {P : ℂ[X]} (hP : P.natDegree ≤ k) (h1 : P.coeff k = 1) :
    ∃ r : Fin k → ℂ, ∀ x, P.eval x = ∏ i, (x - r i) := by
  have hdeg : P.natDegree = k := natDegree_eq_of_le_of_coeff_ne_zero hP (by rw [h1]; exact one_ne_zero)
  have hm : P.Monic := by rw [Monic, leadingCoeff, hdeg, h1]
  have hs : P.Splits := IsAlgClosed.splits P
  have he := hs.eq_prod_roots_of_monic hm
  have hc := hs.natDegree_eq_card_roots
  obtain ⟨l, hl⟩ := Quotient.exists_rep P.roots
  have hl : (l : Multiset ℂ) = P.roots := hl
  rw [← hl] at he hc
  rw [hdeg, Multiset.coe_card] at hc
  subst hc
  refine ⟨fun i => l[i.1]'i.2, fun x => ?_⟩
  rw [he, eval_multiset_prod, Multiset.map_map, Multiset.map_coe, Multiset.prod_coe]
  simp only [Function.comp_def, eval_sub, eval_X, eval_C]
  exact (Fin.prod_univ_fun_getElem l fun a => x - a).symm

theorem exists_eq_prod_sqTh : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (k : ℕ) (F : ℂ → ℂ), Differentiable ℂ F → (∀ z, F (-z) = F z) → F 0 = 1 → (∀ ω ∈ Λ, ∀ z, F (z + ω) * sgStar Λ z ^ (2 * k) = F z * sgStar Λ (z + ω) ^ (2 * k)) → ∃ Q : Fin k → ℂ, (∀ i, Q i ∉ Λ) ∧ ∀ z, F z = ∏ i, sqTh Λ (Q i) z := by
  intro Λ h k F hF he h0 hlaw
  obtain ⟨P, hP, hc, hPF⟩ := h.exists_poly_wp k F hF he hlaw
  obtain ⟨r, hr⟩ := exists_eval_eq_prod_fin hP (hc.trans h0)
  choose Q hQ hQr using fun i => GlobalTheory.EvenTheta.exists_wpF_eq Λ h (r i)
  refine ⟨Q, hQ, fun z => ?_⟩
  refine congrFun (Continuous.ext_on h.dense_compl hF.continuous
    (g := fun z => ∏ i, sqTh Λ (Q i) z)
    (continuous_finsetProd _ fun i _ => (h.differentiable_sqTh (Q i)).continuous) fun z hz => ?_) z
  have hz : z ∉ Λ := hz
  beta_reduce
  simp only [h.sqTh_eq (hQ _) hz, hQr, hPF z hz, hr, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul]

end GlobalTheory.EvenTheta
end
