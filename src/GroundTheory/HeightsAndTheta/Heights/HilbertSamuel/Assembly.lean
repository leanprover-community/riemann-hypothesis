import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAnResToAnalyticRes
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageChi
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.SupStMonoNormSqPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStE
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFSMass
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStB
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjectionBounds
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullFSExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameBasePtFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CNormSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRealGramComparison
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionSup
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResSymGram
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResChiBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStF
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseMonoBasis

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory Module

noncomputable section

namespace MonomialDegree

def blockEquiv (D : ℕ) : Fin (D + 1) ≃ Ix (Fin (D + 1)) where
  toFun i := ⟨(), i⟩
  invFun p := p.2
  left_inv _ := rfl
  right_inv _ := rfl

def monoForm (D n : ℕ) (i : Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card) :
    MvPolynomial (Ix (Fin (D + 1))) ℚ :=
  map (Int.castRingHom ℚ) (rename (blockEquiv D) (monoZ (adtEnum D n i)))

def ptEquiv (D : ℕ) : (Fin (D + 1) → ℂ) ≃ᵐ (Ix (Fin (D + 1)) → ℂ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (blockEquiv D)

theorem ptEquiv_apply (D : ℕ) (w : Fin (D + 1) → ℂ) (t : Fin (D + 1)) :
    ptEquiv D w (blockEquiv D t) = w t := by
  rfl

theorem comp_ptEquiv (D : ℕ) (w : Fin (D + 1) → ℂ) : ptEquiv D w ∘ blockEquiv D = w :=
  funext (ptEquiv_apply D w)

theorem card_ix (D : ℕ) : Fintype.card (Ix (Fin (D + 1))) = D + 1 := by
  simp [Ix, GlobalTheory, Fintype.card_sigma]

theorem sum_ix_norm (D : ℕ) (w : Fin (D + 1) → ℂ) : ∑ j, ‖ptEquiv D w j‖ ^ 2 = sqN w := by
  rw [← (blockEquiv D).sum_comp]
  simp only [ptEquiv_apply]
  rfl

theorem gaussMeasure_eq (D : ℕ) :
    gaussMeasure (Ix (Fin (D + 1))) = (gaussC (D + 1)).map (ptEquiv D) := by
  have hmp : MeasurePreserving (ptEquiv D) volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Ix (Fin (D + 1)) => ℂ) (blockEquiv D)
  ext s hs
  rw [Measure.map_apply (ptEquiv D).measurable hs, gaussMeasure, gaussC, withDensity_apply _ hs,
    withDensity_apply _ ((ptEquiv D).measurable hs), ← hmp.map_eq,
    setLIntegral_map hs (by fun_prop) (ptEquiv D).measurable]
  refine lintegral_congr fun w => ?_
  rw [sum_ix_norm, card_ix, zpow_neg, zpow_natCast]

theorem secFun_monoForm (D n : ℕ) (i : Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card)
    (z : Ix (Fin (D + 1)) → ℂ) : secFun (monoForm D n i) z = monoC (adtEnum D n i) (z ∘ blockEquiv D) := by
  rw [monoForm, secFun_map_intQ, eval_map_int, aeval_rename, aeval_monoZ]
  rfl

theorem fs_rho_ptEquiv (D : ℕ) (w : Fin (D + 1) → ℂ) :
    (fsMetric (Ix (Fin (D + 1)))).ρ (ptEquiv D w) = Real.sqrt (sqN w) := by
  change ‖WithLp.toLp 2 (ptEquiv D w)‖ = _
  rw [EuclideanSpace.norm_eq]
  rw [← sum_ix_norm]

theorem integral_gaussC_mono (D n : ℕ) {a b : Fin (D + 1) → ℕ} (ha : ∑ i, a i = n) (hb : ∑ i, b i = n) :
    ∫ w, starRingEnd ℂ (monoC a w) * monoC b w * ((((Real.sqrt (sqN w)) ^ (2 * n))⁻¹ : ℝ) : ℂ)
        ∂(gaussC (D + 1)) =
      ∫ w, starRingEnd ℂ (monoC a w) * monoC b w ∂(sphProb (D + 1)) := by
  rw [sphMonom_integral_sphProb _ (sphMonom_continuous_f a b)]
  unfold gaussC
  simp only [ENNReal.ofReal]
  have hm : Measurable fun z : Fin (D + 1) → ℂ =>
      Real.toNNReal ((Real.pi ^ (D + 1))⁻¹ * Real.exp (-sqN z)) :=
    (measurable_const.mul (Real.measurable_exp.comp
      sphMonom_continuous_sqN.measurable.neg)).real_toNNReal
  rw [integral_withDensity_eq_integral_smul hm, ← integral_const_mul]
  congr 1
  funext z
  rw [sphMonom_f_smul, ha, hb, NNReal.smul_def, Real.coe_toNNReal _ (by positivity),
    Complex.real_smul]
  push_cast
  rw [inv_pow, two_mul]
  ring

theorem integrable_monoForm (D n : ℕ) (i j : Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card) :
    Integrable (fun z => starRingEnd ℂ (secFun (monoForm D n i) z) * secFun (monoForm D n j) z *
      (wgt (fsMetric (Ix (Fin (D + 1)))) n z : ℂ)) (gaussMeasure (Ix (Fin (D + 1)))) := by
  rw [gaussMeasure_eq, integrable_map_equiv]
  have hfun : (fun z => starRingEnd ℂ (secFun (monoForm D n i) z) * secFun (monoForm D n j) z *
      (wgt (fsMetric (Ix (Fin (D + 1)))) n z : ℂ)) ∘ ptEquiv D = fun w =>
      starRingEnd ℂ (monoC (adtEnum D n i) w) * monoC (adtEnum D n j) w *
        ((((Real.sqrt (sqN w)) ^ (2 * n))⁻¹ : ℝ) : ℂ) := by
    funext w
    simp only [Function.comp, secFun_monoForm, comp_ptEquiv, wgt, fs_rho_ptEquiv]
  rw [hfun]
  refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
  · exact ((sphMonom_continuous_f _ _).measurable.mul (Complex.measurable_ofReal.comp
      ((sphMonom_continuous_sqN.measurable.sqrt.pow_const _).inv))).aestronglyMeasurable
  · have ha := norm_monoC_sq_le (adtEnum D n i) w
    have hb := norm_monoC_sq_le (adtEnum D n j) w
    rw [adtEnum_sum] at ha hb
    have hs : 0 ≤ sqN w := sphMonom_sqN_nonneg w
    have hS : Real.sqrt (sqN w) ^ (2 * n) = sqN w ^ n := by rw [pow_mul, Real.sq_sqrt hs]
    rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs, hS,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hs n))]
    have h0 : 0 ≤ ‖monoC (adtEnum D n i) w‖ * ‖monoC (adtEnum D n j) w‖ := by positivity
    have hq : 0 ≤ sqN w ^ n := pow_nonneg hs n
    have h2 : (‖monoC (adtEnum D n i) w‖ * ‖monoC (adtEnum D n j) w‖) ^ 2 ≤ (sqN w ^ n) ^ 2 := by
      rw [mul_pow, sq (sqN w ^ n)]
      exact mul_le_mul ha hb (by positivity) hq
    have hP : ‖monoC (adtEnum D n i) w‖ * ‖monoC (adtEnum D n j) w‖ ≤ sqN w ^ n := by nlinarith
    rcases hq.eq_or_lt with h | h
    · rw [← h, inv_zero, mul_zero]
      norm_num
    · rw [← div_eq_mul_inv]
      exact div_le_one_of_le₀ hP h.le

theorem bGram_monoForm (D n : ℕ) :
    bGram (gaussMeasure (Ix (Fin (D + 1)))) (fun k => secFun (monoForm D n k))
        (wgt (fsMetric (Ix (Fin (D + 1)))) n) =
      Matrix.diagonal fun k => ((monoNormSq (adtEnum D n k) : ℝ) : ℂ) := by
  ext i j
  rw [bGram, Matrix.of_apply, gaussMeasure_eq, integral_map_equiv]
  simp only [secFun_monoForm, comp_ptEquiv, wgt, fs_rho_ptEquiv]
  rw [integral_gaussC_mono D n (adtEnum_sum D n i) (adtEnum_sum D n j), supSt_gram, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, (adtEnum_injective D n).ne hij]

variable {Ω : Type} [Field Ω] {D : ℕ}

theorem coordIdeal_comp_eq_bot {x : Ix (Fin (D + 1)) → Ω} (hx : coordIdeal ℤ x = ⊥) :
    coordIdeal ℤ (x ∘ blockEquiv D) = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  have h1 : rename (blockEquiv D) f ∈ coordIdeal ℤ x := by
    rw [coordIdeal, RingHom.mem_ker] at hf ⊢
    rw [← hf]
    simp only [coneMap, aeval_rename]
    rfl
  rw [hx, Ideal.mem_bot] at h1
  rw [Ideal.mem_bot]
  exact rename_injective _ (blockEquiv D).injective (by rw [h1, map_zero])

theorem eq_of_aeval_eq {x : Ix (Fin (D + 1)) → Ω} (hx : coordIdeal ℤ x = ⊥) {n : ℕ}
    {f g : MvPolynomial (Ix (Fin (D + 1))) ℤ} (hf : f.IsHomogeneous n) (hg : g.IsHomogeneous n)
    (h : aeval x f = aeval x g) : f = g := by
  have := mem_coordIdeal_of_isHomogeneous ℤ x (hf.sub hg) (by rw [map_sub, h, sub_self])
  rwa [hx, Ideal.mem_bot, sub_eq_zero] at this

variable [CharZero Ω]

theorem aeval_monoForm (x : Ix (Fin (D + 1)) → Ω) (n : ℕ)
    (i : Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card) :
    aeval x (monoForm D n i) = ∏ t, (x ∘ blockEquiv D) t ^ adtEnum D n i t := by
  rw [monoForm, aeval_map_intQ, aeval_rename, aeval_monoZ]

theorem isSecBasis_monoForm {x : Ix (Fin (D + 1)) → Ω} (hx : coordIdeal ℤ x = ⊥) (n : ℕ) :
    IsSecBasis x n (monoForm D n) := by
  refine ⟨fun i => ⟨_, (monoZ_isHomogeneous (adtEnum_sum D n i)).rename_isHomogeneous, rfl⟩, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro u hu i
    have h0 := eq_zero_of_sum_mono (coordIdeal_comp_eq_bot hx) u
      (by simpa only [aeval_monoForm, zsmul_eq_mul] using hu)
    exact congrFun h0 i
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.mem_map.mpr ⟨rename (blockEquiv D) (monoZ (adtEnum D n i)),
        (mem_homogeneousSubmodule _ _).mpr (monoZ_isHomogeneous (adtEnum_sum D n i)).rename_isHomogeneous,
        by simp only [AlgHom.toLinearMap_apply, monoForm, aeval_map_intQ]⟩
    · rintro _ ⟨f, hf, rfl⟩
      have hf' : f.IsHomogeneous n := (mem_homogeneousSubmodule _ _).mp hf
      have hg : (rename (blockEquiv D).symm f).IsHomogeneous n := hf'.rename_isHomogeneous
      have hfx : (aeval x : MvPolynomial (Ix (Fin (D + 1))) ℤ →ₐ[ℤ] Ω).toLinearMap f =
          aeval (x ∘ blockEquiv D) (rename (blockEquiv D).symm f) := by
        rw [AlgHom.toLinearMap_apply, aeval_rename]
        congr 1
      rw [hfx, aeval_eq_sum_adt _ hg]
      refine Submodule.sum_mem _ fun a ha => ?_
      have hai : adtEnum D n ((Finset.Nat.antidiagonalTuple (D + 1) n).equivFin ⟨a, ha⟩) = a := by
        simp [adtEnum]
      rw [← zsmul_eq_mul, ← hai, ← aeval_monoForm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem exists_change {x : Ix (Fin (D + 1)) → Ω} (hx : coordIdeal ℤ x = ⊥) {n : ℕ}
    {b' : Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card → MvPolynomial (Ix (Fin (D + 1))) ℚ}
    (hb' : IsSecBasis x n b') :
    ∃ A : Matrix (Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card)
        (Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card) ℤ,
      (∀ k z, secFun (b' k) z = ∑ l, (A k l : ℂ) * secFun (monoForm D n l) z) ∧ A.det ^ 2 = 1 := by
  have hM := isSecBasis_monoForm hx n
  have hA : ∀ k, ∃ c : Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card → ℤ,
      ∑ l, c l • aeval x (monoForm D n l) = aeval x (b' k) := fun k =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp (by rw [hM.2.2, ← hb'.2.2]; exact Submodule.subset_span ⟨k, rfl⟩)
  have hB : ∀ l, ∃ c : Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card → ℤ,
      ∑ m, c m • aeval x (b' m) = aeval x (monoForm D n l) := fun l =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp (by rw [hb'.2.2, ← hM.2.2]; exact Submodule.subset_span ⟨l, rfl⟩)
  choose A hA using hA
  choose B hB using hB
  refine ⟨Matrix.of A, fun k z => ?_, ?_⟩
  · obtain ⟨f', hf', hbf'⟩ := hb'.1 k
    have heq : f' = ∑ l, C (A k l) * rename (blockEquiv D) (monoZ (adtEnum D n l)) := by
      refine eq_of_aeval_eq hx hf' (IsHomogeneous.sum _ _ _ fun l _ => ?_) ?_
      · simpa using (isHomogeneous_C _ (A k l)).mul (monoZ_isHomogeneous (adtEnum_sum D n l)).rename_isHomogeneous
      · calc aeval x f' = aeval x (b' k) := by rw [hbf', aeval_map_intQ]
          _ = ∑ l, A k l • aeval x (monoForm D n l) := (hA k).symm
          _ = _ := by
            simp only [map_sum, map_mul, map_intCast, eq_intCast, zsmul_eq_mul, monoForm,
              aeval_map_intQ]
    rw [hbf', secFun_map_intQ, heq]
    simp only [monoForm, secFun_map_intQ, Matrix.of_apply, map_sum, map_mul, map_intCast, eq_intCast]
  · have hAB : Matrix.of A * Matrix.of B = 1 := by
      ext k m
      have h1 : ∑ m, (Matrix.of A * Matrix.of B) k m • aeval x (b' m) = aeval x (b' k) := by
        simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul, mul_smul]
        rw [Finset.sum_comm]
        simp only [← Finset.smul_sum, hB]
        exact hA k
      have h2 : ∑ m, (1 : Matrix (Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card)
          (Fin (Finset.Nat.antidiagonalTuple (D + 1) n).card) ℤ) k m • aeval x (b' m) = aeval x (b' k) := by
        simp [Matrix.one_apply]
      have hli := Fintype.linearIndependent_iff.mp hb'.2.1
        (fun m => (Matrix.of A * Matrix.of B) k m - (1 : Matrix _ _ ℤ) k m)
        (by simp only [sub_smul, Finset.sum_sub_distrib, h1, h2, sub_self]) m
      exact sub_eq_zero.mp hli
    have hd := congrArg Matrix.det hAB
    rw [Matrix.det_mul, Matrix.det_one] at hd
    exact Int.isUnit_sq (isUnit_iff_exists_inv.mpr ⟨_, hd⟩)

theorem chi_coord {x : Ix (Fin (D + 1)) → Ω} (hx : coordIdeal ℤ x = ⊥) (n : ℕ) :
    chi x (fsMetric (Ix (Fin (D + 1)))) (gaussMeasure (Ix (Fin (D + 1)))) n = chiP D n := by
  classical
  have hM := isSecBasis_monoForm hx n
  have h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix (Fin (D + 1))) ℚ), IsSecBasis x n p.2 :=
    ⟨⟨_, monoForm D n⟩, hM⟩
  unfold chi
  rw [dif_pos h]
  have hp := h.choose_spec
  generalize h.choose = p at hp ⊢
  obtain ⟨r', b'⟩ := p
  have hp' : IsSecBasis x n b' := hp
  have hr : r' = (Finset.Nat.antidiagonalTuple (D + 1) n).card := hp'.card_eq.trans hM.card_eq.symm
  subst hr
  obtain ⟨A, hA, hdet⟩ := exists_change hx hp'
  have hG := bGram_change (μ := gaussMeasure (Ix (Fin (D + 1)))) (fun k => secFun (monoForm D n k))
    (fun k => secFun (b' k)) (wgt (fsMetric (Ix (Fin (D + 1)))) n) A (integrable_monoForm D n)
    (fun k => Filter.Eventually.of_forall (hA k))
  rw [bGram_monoForm] at hG
  have hw : (Height.totalWeight ℚ : ℝ) = 1 := by
    rw [NumberField.totalWeight_eq_finrank, Module.finrank_self, Nat.cast_one]
  have hcast : A.map (Int.cast : ℤ → ℂ) = (A.map (Int.cast : ℤ → ℝ)).map Complex.ofRealHom := by
    rw [Matrix.map_map]
    congr 1
  have hR : realGram (K := ℚ) (fun _ => fsMetric (Ix (Fin (D + 1)))) (fun _ => gaussMeasure (Ix (Fin (D + 1))))
      n b' = A.map (Int.cast : ℤ → ℝ) * Matrix.diagonal (fun k => monoNormSq (adtEnum D n k)) *
        (A.map (Int.cast : ℤ → ℝ)).transpose := by
    have hC : A.map (Int.cast : ℤ → ℂ) * Matrix.diagonal (fun k => ((monoNormSq (adtEnum D n k) : ℝ) : ℂ)) *
        (A.map (Int.cast : ℤ → ℂ)).transpose =
        (A.map (Int.cast : ℤ → ℝ) * Matrix.diagonal (fun k => monoNormSq (adtEnum D n k)) *
          (A.map (Int.cast : ℤ → ℝ)).transpose).map Complex.ofRealHom := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hcast,
        Matrix.diagonal_map (map_zero _)]
      rfl
    ext k l
    rw [realGram_eq, hG, hC, Matrix.map_apply, Complex.ofRealHom_eq_coe, Complex.ofReal_re]
  have hdA : (A.map (Int.cast : ℤ → ℝ)).det = (A.det : ℝ) := ((Int.castRingHom ℝ).map_det A).symm
  have hdet' : (A.det : ℝ) ^ 2 = 1 := by exact_mod_cast hdet
  simp only [l2Degree, hw, div_one]
  rw [hR, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, hdA]
  have hprod : (A.det : ℝ) * (∏ k, monoNormSq (adtEnum D n k)) * (A.det : ℝ) =
      ∏ k, monoNormSq (adtEnum D n k) := by
    linear_combination (∏ k, monoNormSq (adtEnum D n k)) * hdet'
  rw [hprod, Real.log_prod (fun k _ => (monoNormSq_pos (adtEnum D n k)).ne'), chiP,
    sum_adtEnum D n (fun a => Real.log (monoNormSq a))]
  ring

theorem bounds (D : ℕ) : ∃ C : ℝ, ∀ n : ℕ, 0 ≤ chiP D n ∧ chiP D n ≤ C * (n : ℝ) ^ (D + 1) ∧
    0 ≤ chiP D (n + 1) - chiP D n ∧
      (1 ≤ n → chiP D (n + 1) - chiP D n ≤ C * (n : ℝ) ^ D * Real.log (n + 1)) := by
  obtain ⟨C₁, h₁⟩ := exists_chiP_le D
  obtain ⟨C₂, h₂⟩ := exists_chiP_succ_sub_le D
  refine ⟨max C₁ C₂, fun n => ⟨chiP_nonneg D n, (h₁ n).trans ?_, chiP_succ_sub_nonneg D n,
    fun hn => (h₂ n hn).trans ?_⟩⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hl : 0 ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) hl

end MonomialDegree

theorem MonomialDegree.proof : MonomialDegree.Statement :=
  ⟨fun _ _ _ _ _ hx n => MonomialDegree.chi_coord hx n, MonomialDegree.bounds⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem ProjFSMass.proof : ProjFSMass.Statement := by
  intro D Ω _ _ κ _ x e m hfr hFS
  exact ⟨gbPsi e, gb_isGoodProj hfr, gb_ptsIntegralAt hfr hFS⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4 ProjLine
open scoped Topology

noncomputable section

namespace PullFSExtension

theorem leviForm_comp_clm {E F : Type} [Fintype E] [Fintype F] (L : (E → ℂ) →L[ℂ] (F → ℂ))
    (φ : (F → ℂ) → ℝ) (z w : E → ℂ) (hφ : ContDiffAt ℝ 2 φ (L z)) :
    leviForm (fun y => φ (L y)) z w = leviForm φ (L z) (L w) := by
  set Lr : (E → ℂ) →L[ℝ] (F → ℂ) := L.restrictScalars ℝ with hLr
  have hLr' : ∀ y, Lr y = L y := fun _ => rfl
  have hev : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 φ (L y) :=
    (L.continuous.tendsto z).eventually (hφ.eventually (by simp))
  have hfd : fderiv ℝ (fun y => φ (L y)) =ᶠ[𝓝 z]
      fun y => (ContinuousLinearMap.compL ℝ (E → ℂ) (F → ℂ) ℝ).flip Lr (fderiv ℝ φ (Lr y)) := by
    filter_upwards [hev] with y hy
    have h := (hy.differentiableAt (by norm_num)).hasFDerivAt.comp y Lr.hasFDerivAt
    exact h.fderiv
  have hd2 : DifferentiableAt ℝ (fderiv ℝ φ) (Lr z) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hD : HasFDerivAt
      (fun y => (ContinuousLinearMap.compL ℝ (E → ℂ) (F → ℂ) ℝ).flip Lr (fderiv ℝ φ (Lr y)))
      (((ContinuousLinearMap.compL ℝ (E → ℂ) (F → ℂ) ℝ).flip Lr).comp
        ((fderiv ℝ (fderiv ℝ φ) (Lr z)).comp Lr)) z :=
    ((ContinuousLinearMap.compL ℝ (E → ℂ) (F → ℂ) ℝ).flip Lr).hasFDerivAt.comp z
      (hd2.hasFDerivAt.comp z Lr.hasFDerivAt)
  unfold leviForm
  rw [hfd.fderiv_eq, hD.fderiv]
  have hI : Lr (Complex.I • w) = Complex.I • L w := by rw [hLr']; exact L.map_smul _ _
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, hI]
  rfl

theorem leviForm_congr {E : Type} [Fintype E] {φ ψ : (E → ℂ) → ℝ} {z : E → ℂ} (h : φ =ᶠ[𝓝 z] ψ)
    (w : E → ℂ) : leviForm φ z w = leviForm ψ z w := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ := by
    filter_upwards [h.eventuallyEq_nhds] with y hy
    exact hy.fderiv_eq
  unfold leviForm
  rw [h1.fderiv_eq]

theorem normSqE_eq {J : Type} [Fintype J] (z : J → ℂ) : normSqE z = ∑ i, ‖z i‖ ^ 2 := by
  unfold normSqE
  rw [eL_apply, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

theorem normSqE_smul {J : Type} [Fintype J] (c : ℂ) (z : J → ℂ) :
    normSqE (c • z) = ‖c‖ ^ 2 * normSqE z := by
  simp only [normSqE_eq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

theorem normSqE_conj {J : Type} [Fintype J] (z : J → ℂ) :
    normSqE (fun i => (starRingEnd ℂ) (z i)) = normSqE z := by
  simp only [normSqE_eq, Complex.norm_conj]

theorem normSqE_zero {J : Type} [Fintype J] : normSqE (0 : J → ℂ) = 0 := by
  simp [normSqE_eq]

theorem contDiff_normSqE {J : Type} [Fintype J] {n : WithTop ℕ∞} : ContDiff ℝ n (normSqE (J := J)) := by
  have : normSqE (J := J) = fun z => ‖eL z‖ ^ 2 := rfl
  rw [this]
  exact (contDiff_norm_sq ℝ).comp (eL (J := J)).contDiff

variable {κ : Type} [Fintype κ] {D : ℕ}

def pr (e : Fin (D + 1) → Ix κ) : (Ix κ → ℂ) →L[ℂ] (Fin (D + 1) → ℂ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (e k)

def ratio (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) : ℝ := normSqE (pr e z) / normSqE z

theorem ratio_smul (e : Fin (D + 1) → Ix κ) {c : ℂ} (hc : c ≠ 0) (z : Ix κ → ℂ) :
    ratio e (c • z) = ratio e z := by
  unfold ratio
  rw [map_smul, normSqE_smul, normSqE_smul]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))

theorem ratio_conj (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) :
    ratio e (fun i => (starRingEnd ℂ) (z i)) = ratio e z := by
  unfold ratio
  have : pr e (fun i => (starRingEnd ℂ) (z i)) = fun k => (starRingEnd ℂ) (pr e z k) := rfl
  rw [this, normSqE_conj, normSqE_conj]

theorem contDiffAt_ratio (e : Fin (D + 1) → Ix κ) {z : Ix κ → ℂ} (hz : z ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (ratio e) z :=
  (contDiff_normSqE.comp ((pr e).restrictScalars ℝ).contDiff).contDiffAt.div contDiff_normSqE.contDiffAt
    (normSqE_pos hz).ne'

def cut (δ t : ℝ) : ℝ := Real.smoothTransition ((t - δ / 4) / (δ / 4))

theorem cut_of_le {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ δ / 4) : cut δ t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

theorem cut_of_ge {δ t : ℝ} (hδ : 0 < δ) (ht : δ / 2 ≤ t) : cut δ t = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (by linarith)).mpr (by linarith))

def gfac (δ t : ℝ) : ℝ := Real.exp (cut δ t * Real.log t / 2)

theorem contDiff_gfac {δ : ℝ} (hδ : 0 < δ) {n : ℕ∞} : ContDiff ℝ n (gfac δ) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t < δ / 4
  · have : gfac δ =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      simp [gfac, cut_of_le hδ (le_of_lt hs)]
    exact contDiffAt_const.congr_of_eventuallyEq this
  · have ht0 : t ≠ 0 := by intro h; subst h; linarith
    have hcut : ContDiff ℝ n (cut δ) := by
      have : cut δ = Real.smoothTransition ∘ fun t => (t - δ / 4) / (δ / 4) := rfl
      rw [this]
      exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
    exact Real.contDiff_exp.contDiffAt.comp t
      (((hcut.contDiffAt.mul (Real.contDiffAt_log.mpr ht0))).div_const _)

theorem gfac_of_ge {δ t : ℝ} (hδ : 0 < δ) (ht : δ / 2 ≤ t) : gfac δ t = Real.sqrt t := by
  have ht0 : 0 < t := by linarith
  rw [gfac, cut_of_ge hδ ht, one_mul, ← Real.log_sqrt ht0.le, Real.exp_log (Real.sqrt_pos.mpr ht0)]

def metric (e : Fin (D + 1) → Ix κ) (δ : ℝ) : ConeMetric ℂ (Ix κ) where
  ρ z := Real.sqrt (normSqE z) * gfac δ (ratio e z)
  pos z hz := mul_pos (Real.sqrt_pos.mpr (normSqE_pos hz)) (Real.exp_pos _)
  smul c z := by
    by_cases hc : c = 0
    · subst hc
      simp [normSqE_zero]
    rw [ratio_smul e hc, normSqE_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), mul_assoc]

theorem metric_rho (e : Fin (D + 1) → Ix κ) (δ : ℝ) (z : Ix κ → ℂ) :
    (metric e δ).ρ z = Real.sqrt (normSqE z) * gfac δ (ratio e z) := rfl

theorem metric_of_ge (e : Fin (D + 1) → Ix κ) {δ : ℝ} (hδ : 0 < δ) {z : Ix κ → ℂ} (hz : z ≠ 0)
    (hr : δ / 2 ≤ ratio e z) : (metric e δ).ρ z = Real.sqrt (normSqE (pr e z)) := by
  rw [metric_rho, gfac_of_ge hδ hr, ← Real.sqrt_mul (normSqE_pos hz).le, ratio,
    mul_div_cancel₀ _ (normSqE_pos hz).ne']

theorem isSmoothMetric_metric (e : Fin (D + 1) → Ix κ) {δ : ℝ} (hδ : 0 < δ) :
    IsSmoothMetric (metric e δ) := by
  intro z hz
  have hz' : z ≠ 0 := hz
  refine ContDiffAt.contDiffWithinAt ?_
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => Real.sqrt (normSqE y)) z :=
    contDiff_normSqE.contDiffAt.sqrt (normSqE_pos hz').ne'
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => gfac δ (ratio e y)) z :=
    (contDiff_gfac hδ).contDiffAt.comp z (contDiffAt_ratio e hz')
  exact h1.mul h2

theorem isConjInvariant_metric (e : Fin (D + 1) → Ix κ) (δ : ℝ) : IsConjInvariant (metric e δ) := by
  intro z
  rw [metric_rho, metric_rho, normSqE_conj, ratio_conj]

variable {Ω : Type} [Field Ω] [CharZero Ω] {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ}

theorem pr_ne_zero (hBP : ProjFrameBasePtFree.Statement) (hfr : IsProjFrame x e) {z : Ix κ → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) : pr e z ≠ 0 := by
  intro h0
  apply hz.1
  funext i
  obtain ⟨u, j⟩ := i
  cases u
  obtain ⟨N, hN⟩ := hBP D Ω κ x e hfr () (fun _ => j)
  set ψ : MvPolynomial (Ix κ) ℤ →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ)) with hψ
  have hle : coordIdeal ℤ x ⊔ Ideal.span (Set.range fun k : Fin (D + 1) =>
      linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨(), k⟩) ≤ RingHom.ker ψ := by
    refine sup_le (fun f hf => RingHom.mem_ker.mpr (hz.2 f hf)) (Ideal.span_le.mpr ?_)
    rintro _ ⟨k, rfl⟩
    have hk : z (e k) = 0 := congrFun h0 k
    have he : (⟨(), (e k).2⟩ : Ix κ) = e k := rfl
    simp only [SetLike.mem_coe, RingHom.mem_ker, hψ, RingHom.comp_apply, linForm, map_sum, map_mul,
      map_C, map_X, eval_C, eval_X, projMat]
    simp only [eq_intCast, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single (e k).2 (fun i _ hi => if_neg (Ne.symm hi))
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, he]
    exact hk
  have h1 := hle hN
  rw [RingHom.mem_ker] at h1
  simp only [hψ, RingHom.comp_apply, map_pow, map_X, eval_X, Finset.univ_unique,
    Finset.prod_singleton] at h1
  exact eq_zero_of_pow_eq_zero h1

theorem ratio_pos (hBP : ProjFrameBasePtFree.Statement) (hfr : IsProjFrame x e) {z : Ix κ → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) : 0 < ratio e z :=
  div_pos (normSqE_pos (pr_ne_zero hBP hfr hz)) (normSqE_pos hz.1)

theorem exists_ratio_lb (hBP : ProjFrameBasePtFree.Statement) (hfr : IsProjFrame x e) :
    ∃ δ > 0, ∀ z ∈ pts (coordIdeal ℤ x), δ ≤ ratio e z := by
  set S : Set (Ix κ → ℂ) :=
    {z | (∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0) ∧ normSqE z = 1} with hSdef
  have hSpts : ∀ z ∈ S, z ∈ pts (coordIdeal ℤ x) := fun z hz =>
    ⟨fun h0 => by
      have h1 := hz.2
      rw [h0, normSqE_zero] at h1
      exact zero_ne_one h1, hz.1⟩
  have hnorm : ∀ z ∈ pts (coordIdeal ℤ x), ∃ z' ∈ S, ratio e z' = ratio e z := by
    intro z hz
    have hq := normSqE_pos hz.1
    have hs := Real.sqrt_pos.mpr hq
    set c : ℂ := (((Real.sqrt (normSqE z))⁻¹ : ℝ) : ℂ) with hcdef
    have hcn : ‖c‖ = (Real.sqrt (normSqE z))⁻¹ := by
      rw [hcdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
    have hc : c ≠ 0 := by
      intro h
      rw [h, norm_zero] at hcn
      exact (inv_pos.mpr hs).ne' hcn.symm
    refine ⟨c • z, ⟨(smul_mem_pts_coord x hz hc).2, ?_⟩, ratio_smul e hc z⟩
    rw [normSqE_smul, hcn, inv_pow, Real.sq_sqrt hq.le, inv_mul_cancel₀ hq.ne']
  have hSc : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have hA : IsClosed
          {z : Ix κ → ℂ | ∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0} := by
        have h : {z : Ix κ → ℂ | ∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0} =
            ⋂ f ∈ coordIdeal ℤ x, {z | eval z (map (Int.castRingHom ℂ) f) = 0} := by
          ext z
          simp
        rw [h]
        exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
      exact hA.inter (isClosed_eq (contDiff_normSqE (n := 0)).continuous continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : Ix κ → ℂ)) (r := 1)).subset fun z hz => ?_
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
      have h1 : ‖z i‖ ^ 2 ≤ 1 := by
        rw [← hz.2, normSqE_eq]
        exact Finset.single_le_sum (f := fun i => ‖z i‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      nlinarith [norm_nonneg (z i)]
  have hcont : ContinuousOn (ratio e) S := fun z hz =>
    (contDiffAt_ratio e (hSpts z hz).1 (n := 0)).continuousAt.continuousWithinAt
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, fun z hz => ?_⟩
    obtain ⟨z', hz', -⟩ := hnorm z hz
    rw [hS] at hz'
    simp at hz'
  · obtain ⟨z0, hz0, hmin⟩ := hSc.exists_isMinOn hS hcont
    refine ⟨ratio e z0, ratio_pos hBP hfr (hSpts z0 hz0), fun z hz => ?_⟩
    obtain ⟨z', hz', hr⟩ := hnorm z hz
    rw [← hr]
    exact hmin hz'

end PullFSExtension

open PullFSExtension in

theorem PullFSExtension.proof (hBP : ProjFrameBasePtFree.Statement) : PullFSExtension.Statement := by
  intro D Ω _ _ κ _ x e hfr
  obtain ⟨δ, hδ, hlb⟩ := exists_ratio_lb hBP hfr
  have hsm := isSmoothMetric_metric e hδ
  refine ⟨metric e δ, hsm, isConjInvariant_metric e δ, ⟨?_, ?_⟩, ?_⟩
  · refine hsm.mono fun z hz => ?_
    obtain ⟨i, hi⟩ := hz ()
    exact fun h0 => hi (congrFun h0 _)
  · intro z hz w _
    have hzp : z ∈ pts (coordIdeal ℤ x) :=
      ⟨fun h0 => by obtain ⟨i, hi⟩ := hz.1 (); exact hi (congrFun h0 _), hz.2⟩
    have hpz := pr_ne_zero hBP hfr hzp
    have hev : (fun y => Real.log ((HermLine.ofCone (metric e δ)).h y)) =ᶠ[𝓝 z]
        fun y => Real.log ((fsMetric (Fin (D + 1))).ρ (pr e y)) := by
      have hr : ∀ᶠ y in 𝓝 z, δ / 2 < ratio e y :=
        (contDiffAt_ratio e hzp.1 (n := 0)).continuousAt.eventually
          (lt_mem_nhds (by linarith [hlb z hzp]))
      filter_upwards [hr, isOpen_ne.mem_nhds hzp.1] with y hy hy0
      change Real.log ((metric e δ).ρ y) = _
      rw [metric_of_ge e hδ hy0 hy.le, congrFun log_fs_eq (pr e y),
        Real.log_sqrt (by rw [normSqE_eq]; positivity)]
      ring
    have hφ : ContDiffAt ℝ 2 (fun u => Real.log ((fsMetric (Fin (D + 1))).ρ u)) (pr e z) := by
      rw [log_fs_eq]
      exact contDiffAt_const.mul (contDiff_normSqE.contDiffAt.log (normSqE_pos hpz).ne')
    have key := leviForm_comp_clm (pr e) (fun u => Real.log ((fsMetric (Fin (D + 1))).ρ u)) z w hφ
    beta_reduce at key
    rw [leviForm_congr hev w, key]
    exact leviForm_log_fs_nonneg hpz (pr e w)
  · intro z hz
    rw [metric_of_ge e hδ hz.1 (by linarith [hlb z hz]), normSqE_eq]
    rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace RealGramComparison

open MvPolynomial MeasureTheory Filter Asymptotics Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder ComplexConjugate Matrix

noncomputable section

set_option linter.unusedSectionVars false

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def dVGram (d : HSMDatum D Ω κ) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Ix κ) ℚ) :
    Matrix (Fin r) (Fin r) ℂ :=
  bGram d.dV (fun k y => secFun (b k) (resPt d y)) fun y => wgt d.m n (resPt d y)

theorem pairVal_eq (m : ConeMetric ℂ (Ix κ)) (n : ℕ) (b b' : MvPolynomial (Ix κ) ℚ) (z : Ix κ → ℂ) :
    pairVal m n b b' z = starRingEnd ℂ (secFun b' z) * secFun b z * (wgt m n z : ℂ) := by
  simp only [pairVal, secFun, wgt, div_eq_mul_inv]
  push_cast
  ring

theorem resCGram_eq (d : HSMDatum D Ω κ) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Ix κ) ℚ) :
    resCGram d n b = (dVGram d n b).transpose := by
  ext k l
  simp only [resCGram, dVGram, bGram, Matrix.transpose_apply, Matrix.of_apply, pairVal_eq]

theorem integrable_dV (d : HSMDatum D Ω κ) {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b k = map (Int.castRingHom ℚ) f)
    (i j : Fin r) :
    Integrable (fun y => starRingEnd ℂ (secFun (b i) (resPt d y)) * secFun (b j) (resPt d y) *
      (wgt d.m n (resPt d y) : ℂ)) d.dV := by
  have := d.vol.1
  have hc := ResSym.continuous_degZero_resPt d (ResSym.continuousOn_gramFun d.smooth n (b i) (b j))
    fun c z hc => ResSym.gramFun_smul (hb i) (hb j) c z hc
  exact integrableOn_univ.1 (hc.continuousOn.integrableOn_compact isCompact_univ)

theorem quad_bGram {X : Type*} [MeasurableSpace X] (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ)
    (hint : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ) (c : Fin r → ℂ) :
    (star c ⬝ᵥ (bGram μ s w *ᵥ c)).re = bNormSq μ s w c := by
  rw [dot_bGram μ s w hint c, Complex.ofReal_re]

theorem isHermitian_ofReal_smul {r : ℕ} {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.IsHermitian) (t : ℝ) :
    ((t : ℂ) • A).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hA.eq, Complex.star_def, Complex.conj_ofReal]

theorem re_det_ofReal_smul {r : ℕ} (t : ℝ) (A : Matrix (Fin r) (Fin r) ℂ) :
    ((t : ℂ) • A).det.re = t ^ r * A.det.re := by
  rw [Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

theorem re_det_le_of_quad {r : ℕ} {A B : Matrix (Fin r) (Fin r) ℂ} (hA : A.PosSemidef) (hB : B.IsHermitian)
    (t : ℝ) (h : ∀ c : Fin r → ℂ, (star c ⬝ᵥ (A *ᵥ c)).re ≤ t * (star c ⬝ᵥ (B *ᵥ c)).re) :
    A.det.re ≤ t ^ r * B.det.re := by
  have hsub := psd_sub_of_quad_le (isHermitian_ofReal_smul hB t) hA.isHermitian fun c => by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
    exact h c
  have := GroundTheory.Heights₂.Heights.MCDet.re_det_mono hA hsub
  simp only [RCLike.re_to_complex] at this
  rwa [re_det_ofReal_smul] at this

theorem abs_sub_le (hR : ResolutionSupBound.Statement) (d : HSMDatum D Ω κ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, 1 ≤ n →
      |resChi d n - resCChi d n| ≤
        (finrank ℤ (sec ℤ d.x n) : ℝ) * (Real.log 2 + Real.log K + D * Real.log n) := by
  classical
  obtain ⟨C, hC⟩ := hR D Ω κ d
  refine ⟨max (C ^ 2) 1, le_max_right _ _, fun n hn => ?_⟩
  set K := max (C ^ 2) 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogK := Real.log_nonneg hK1
  have hlogn := Real.log_nonneg hn1
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL : 0 ≤ Real.log 2 + Real.log K + D * Real.log n := by positivity
  by_cases h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2
  swap
  · simp only [resChi, resCChi, dif_neg h, sub_zero, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hL
  rw [ResSym.resChi_eq d n h]
  simp only [resCChi, dif_pos h]
  have hp := h.choose_spec
  generalize h.choose = p at hp ⊢
  obtain ⟨r, b⟩ := p
  have hb : IsSecBasis d.x n b := hp
  have hrk : (r : ℝ) = finrank ℤ (sec ℤ d.x n) := by exact_mod_cast hb.card_eq
  rw [resCGram_eq, Matrix.det_transpose, ← hrk]
  have hintG := integrable_dV d hb.1
  have hintH := ResSym.integrable_gram d hb.1
  have key : ∀ c : Fin r → ℂ,
      bNormSq d.dV (fun k y => secFun (b k) (resPt d y)) (fun y => wgt d.m n (resPt d y)) c ≤
        2 * bNormSq (ResSym.symMeasure d) (fun k => secFun (b k)) (wgt d.m n) c ∧
      bNormSq (ResSym.symMeasure d) (fun k => secFun (b k)) (wgt d.m n) c ≤
        K * (n : ℝ) ^ D *
          bNormSq d.dV (fun k y => secFun (b k) (resPt d y)) (fun y => wgt d.m n (resPt d y)) c := by
    intro c
    have := d.vol.1
    set g : (Ix κ → ℂ) → ℝ := fun z => ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt d.m n z with hg
    have hnn : ∀ z, 0 ≤ g z := fun z =>
      mul_nonneg (by positivity) (inv_nonneg.mpr (pow_nonneg (d.m.nonneg z) _))
    have hcont : ContinuousOn g {0}ᶜ := continuousOn_normSq d.smooth b c
    have hdeg : ∀ (a : ℂ) z, a ≠ 0 → g (a • z) = g z := fun a z ha => isDegZero_normSq hb.1 c a z ha
    have eG : bNormSq d.dV (fun k y => secFun (b k) (resPt d y)) (fun y => wgt d.m n (resPt d y)) c =
        ∫ y, g (resPt d y) ∂d.dV := rfl
    have eH : bNormSq (ResSym.symMeasure d) (fun k => secFun (b k)) (wgt d.m n) c =
        2⁻¹ * ((∫ y, g (resPt d y) ∂d.dV) + ∫ y, g (conjPt (resPt d y)) ∂d.dV) := by
      rw [← smul_eq_mul, ← ResSym.integral_symMeasure d hcont hdeg]
      rfl
    have hA : 0 ≤ ∫ y, g (resPt d y) ∂d.dV := integral_nonneg fun y => hnn _
    have hB : 0 ≤ ∫ y, g (conjPt (resPt d y)) ∂d.dV := integral_nonneg fun y => hnn _
    refine ⟨by rw [eG, eH]; linarith, ?_⟩

    set f : MvPolynomial (Ix κ) ℂ := ∑ k, MvPolynomial.C (c k) * map (algebraMap ℚ ℂ) (b k) with hf
    have hfh : f.IsHomogeneous n := by
      refine MvPolynomial.IsHomogeneous.sum _ _ _ fun k _ => ?_
      obtain ⟨g', hg', hgb⟩ := hb.1 k
      rw [hgb, MvPolynomial.map_map]
      exact (hg'.map _).C_mul _
    have hevf : ∀ w, eval w f = ∑ i, c i * secFun (b i) w := by
      intro w
      simp [hf, secFun, map_sum]
    have hpt : ∀ w : Ix κ → ℂ, w ≠ 0 → ptNorm d.m (RingHom.id ℂ) n f w ^ 2 = g w := by
      intro w hw
      rw [ptNorm, MvPolynomial.map_id, hevf]
      simp only [hg, wgt]
      rw [div_pow, ← pow_mul, mul_comm n 2, div_eq_mul_inv]
    have hL2 : resolutionVolumeL2Complex d n f ^ 2 = ∫ y, g (resPt d y) ∂d.dV := by
      rw [resolutionVolumeL2Complex, Real.sq_sqrt (integral_nonneg fun y => sq_nonneg _)]
      exact integral_congr_ae (Eventually.of_forall fun y => hpt _ (ResSym.resPt_mem_pts d y).1)
    have hpow : ((n : ℝ) ^ ((D : ℝ) / 2)) ^ 2 = (n : ℝ) ^ D := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n),
        show (D : ℝ) / 2 * ((2 : ℕ) : ℝ) = (D : ℝ) by push_cast; ring, Real.rpow_natCast]
    set S := K * (n : ℝ) ^ D * ∫ y, g (resPt d y) ∂d.dV with hS
    have hsup : ∀ z ∈ pts (coordIdeal ℤ d.x), g z ≤ S := by
      intro z hz
      have h1 := hC n hn f hfh z hz
      have h0 : 0 ≤ ptNorm d.m (RingHom.id ℂ) n f z :=
        div_nonneg (norm_nonneg _) (pow_nonneg (d.m.nonneg z) _)
      have h2 := pow_le_pow_left₀ h0 h1 2
      rw [hpt z hz.1] at h2
      calc g z ≤ (C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f) ^ 2 := h2
        _ = C ^ 2 * (n : ℝ) ^ D * ∫ y, g (resPt d y) ∂d.dV := by rw [mul_pow, mul_pow, hpow, hL2]
        _ ≤ S := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hA
    have hi1 : Integrable (fun y => g (resPt d y)) d.dV :=
      integrableOn_univ.1 ((ResSym.continuous_degZero_resPt d hcont hdeg).continuousOn.integrableOn_compact
        isCompact_univ)
    have hi2 : Integrable (fun y => g (conjPt (resPt d y))) d.dV :=
      integrableOn_univ.1 ((ResSym.continuous_degZero_conj_resPt d hcont hdeg).continuousOn.integrableOn_compact
        isCompact_univ)
    have hS1 : ∫ y, g (resPt d y) ∂d.dV ≤ S := by
      have := integral_mono hi1 (integrable_const S) fun y => hsup _ (ResSym.resPt_mem_pts d y)
      simpa using this
    have hS2 : ∫ y, g (conjPt (resPt d y)) ∂d.dV ≤ S := by
      have := integral_mono hi2 (integrable_const S) fun y =>
        hsup _ (ResSym.conjPt_mem_pts (ResSym.resPt_mem_pts d y))
      simpa using this
    rw [eH, eG]
    rw [hS] at hS1 hS2
    linarith
  have hGpsd : (dVGram d n b).PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (bGram_isHermitian _ _ _) fun c => by
      rw [dVGram, dot_bGram _ _ _ hintG c]
      exact Complex.zero_le_real.mpr (integral_nonneg fun y =>
        mul_nonneg (by positivity) (inv_nonneg.mpr (pow_nonneg (d.m.nonneg _) _)))
  have hHpd := ResSym.posDef_gram d hb
  have d1 := re_det_le_of_quad hGpsd (bGram_isHermitian (ResSym.symMeasure d) (fun k => secFun (b k))
    (wgt d.m n)) 2 fun c => by
      rw [dVGram, quad_bGram _ _ _ hintG, quad_bGram _ _ _ hintH]
      exact (key c).1
  have d2 := re_det_le_of_quad hHpd.posSemidef (bGram_isHermitian d.dV
    (fun k y => secFun (b k) (resPt d y)) fun y => wgt d.m n (resPt d y)) (K * (n : ℝ) ^ D) fun c => by
      rw [quad_bGram _ _ _ hintG, quad_bGram _ _ _ hintH]
      exact (key c).2
  rw [← dVGram] at d2
  set G := dVGram d n b with hG
  set H := bGram (ResSym.symMeasure d) (fun k => secFun (b k)) (wgt d.m n) with hH
  have hHpos : 0 < H.det.re := by
    have := GroundTheory.Heights₂.Heights.MCDet.re_det_pos hHpd
    simpa using this
  have hKn : 0 < K * (n : ℝ) ^ D := by positivity
  have hGpos : 0 < G.det.re := by
    by_contra hle
    push Not at hle
    have : (K * (n : ℝ) ^ D) ^ r * G.det.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
    linarith
  have l1 : Real.log G.det.re ≤ r * Real.log 2 + Real.log H.det.re := by
    have := Real.log_le_log hGpos d1
    rwa [Real.log_mul (by positivity) hHpos.ne', Real.log_pow] at this
  have l2 : Real.log H.det.re ≤ r * (Real.log K + D * Real.log n) + Real.log G.det.re := by
    have := Real.log_le_log hHpos d2
    rwa [Real.log_mul (by positivity) hGpos.ne', Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow] at this
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have a1 := mul_nonneg hr0 hlog2
  have a2 := mul_nonneg hr0 (add_nonneg hlogK (mul_nonneg (Nat.cast_nonneg D) hlogn))
  rw [abs_le]
  constructor <;> nlinarith

theorem rank_le (hP : ProjectionBounds.Statement) (hF : PullFSExtension.Statement) (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ) (hfr : IsProjFrame d.x e) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, (finrank ℤ (sec ℤ d.x n) : ℝ) ≤ A * ((n : ℝ) + 1) ^ D := by
  obtain ⟨m₀, hs, hc, hp, hpull⟩ := hF D Ω κ d.x e hfr
  obtain ⟨k, E, C, -, -, -, -, hrank, -⟩ := hP D Ω κ (d.withMetric m₀ ⊥ hs hc bot_le hp) e hfr hpull
  refine ⟨(projDeg d.x e : ℝ) / D.factorial + |C|, by positivity, fun n => ?_⟩
  have h1 : (finrank ℤ (sec ℤ d.x n) : ℝ) - (projDeg d.x e : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ) ≤
      C * ((n : ℝ) + 1) ^ (D - 1) := (abs_le.mp (hrank n)).2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n + 1 := by linarith
  have h2 : (n : ℝ) ^ D ≤ ((n : ℝ) + 1) ^ D := pow_le_pow_left₀ hn0 (by linarith) D
  have h3 : ((n : ℝ) + 1) ^ (D - 1) ≤ ((n : ℝ) + 1) ^ D := pow_le_pow_right₀ hn1 (Nat.sub_le D 1)
  have h4 : C * ((n : ℝ) + 1) ^ (D - 1) ≤ |C| * ((n : ℝ) + 1) ^ D :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h3 (abs_nonneg C))
  have h5 : (projDeg d.x e : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ) ≤
      (projDeg d.x e : ℝ) / D.factorial * ((n : ℝ) + 1) ^ D := by
    rw [div_mul_eq_mul_div]
    gcongr
  rw [add_mul]
  linarith

theorem proof (hR : ResolutionSupBound.Statement) (hP : ProjectionBounds.Statement)
    (hF : PullFSExtension.Statement) : RealGramComparison.Statement := by
  intro D Ω _ _ κ _ d e hfr
  obtain ⟨K, hK1, hK⟩ := abs_sub_le hR d
  obtain ⟨A, hA0, hA⟩ := rank_le hP hF d e hfr
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK := Real.log_nonneg hK1
  set B := (Real.log 2 + Real.log K) / Real.log 2 + D with hB
  have hB0 : 0 ≤ B := by positivity
  refine IsBigO.of_bound (A * 2 ^ D * B) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn0 := Real.log_nonneg hn1
  have hlog21 : Real.log 2 ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by norm_num) (by linarith)
  have hlogn : Real.log n ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
  have hlog1 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hL : Real.log 2 + Real.log K + D * Real.log n ≤ B * Real.log ((n : ℝ) + 1) := by
    have h1 : Real.log 2 + Real.log K ≤ (Real.log 2 + Real.log K) / Real.log 2 * Real.log ((n : ℝ) + 1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      nlinarith
    have h2 : (D : ℝ) * Real.log n ≤ D * Real.log ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hlogn (Nat.cast_nonneg _)
    rw [hB, add_mul]
    linarith
  have hL0 : 0 ≤ Real.log 2 + Real.log K + D * Real.log n := by positivity
  have hpow : ((n : ℝ) + 1) ^ D ≤ 2 ^ D * (n : ℝ) ^ D := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) D
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ D * Real.log ((n : ℝ) + 1))]
  calc |resChi d n - resCChi d n|
      ≤ (finrank ℤ (sec ℤ d.x n) : ℝ) * (Real.log 2 + Real.log K + D * Real.log n) := hK n hn
    _ ≤ (A * ((n : ℝ) + 1) ^ D) * (B * Real.log ((n : ℝ) + 1)) :=
        mul_le_mul (hA n) hL hL0 (by positivity)
    _ ≤ (A * (2 ^ D * (n : ℝ) ^ D)) * (B * Real.log ((n : ℝ) + 1)) := by
        gcongr
    _ = A * 2 ^ D * B * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by ring

end

end RealGramComparison

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ResChiSandwich

open MvPolynomial MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjectionBounds
open scoped ComplexOrder Matrix

noncomputable section

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem trace_comb_le {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) {N r : ℕ}
    (f : Fin r → MvPolynomial (Ix κ) ℤ) (g : Fin r → MvPolynomial (Fin (D + 1)) ℤ)
    (hf : ∀ k, (f k).IsHomogeneous N) (hg : ∀ k, (g k).IsHomogeneous N)
    (htr : ∀ k, aeval (x ∘ e) (g k) = secTrace x e N (aeval x (f k))) (c : Fin r → ℂ) {S : ℝ}
    (hS : ∀ z ∈ pts (coordIdeal ℤ x),
      ‖∑ k, c k * eval z (map (Int.castRingHom ℂ) (f k))‖ ≤ S * pnorm e z ^ N)
    (w : Fin (D + 1) → ℂ) :
    ‖∑ k, c k * eval w (map (Int.castRingHom ℂ) (g k))‖ ≤
      (projDeg x e : ℝ) * S * Real.sqrt (sqN w) ^ N := by
  classical
  obtain ⟨Δ, hΔ0, hΔ⟩ := exists_isDiscr hfr
  have hFc : Continuous fun w : Fin (D + 1) → ℂ => ‖∑ k, c k * eval w (map (Int.castRingHom ℂ) (g k))‖ :=
    (continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_eval _)).norm
  have hGc : Continuous fun w : Fin (D + 1) → ℂ => (projDeg x e : ℝ) * S * Real.sqrt (sqN w) ^ N := by
    unfold sqN
    fun_prop
  have hgood : ∀ w ∈ {w : Fin (D + 1) → ℂ | eval w Δ ≠ 0},
      w ∈ {w : Fin (D + 1) → ℂ | ‖∑ k, c k * eval w (map (Int.castRingHom ℂ) (g k))‖ ≤
        (projDeg x e : ℝ) * S * Real.sqrt (sqN w) ^ N} := by
    intro w hw
    obtain ⟨hfin, hcard, -, htrace⟩ := hΔ w hw
    simp only [Set.mem_ofPred_eq]
    have hsum : ∑ k, c k * eval w (map (Int.castRingHom ℂ) (g k)) =
        ∑ z ∈ hfin.toFinset, ∑ k, c k * eval z (map (Int.castRingHom ℂ) (f k)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [htrace N (f k) (g k) (hf k) (hg k) (htr k), finsum_mem_eq_finite_toFinset_sum _ hfin,
        Finset.mul_sum]
    rw [hsum]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ z ∈ hfin.toFinset,
        ‖∑ k, c k * eval z (map (Int.castRingHom ℂ) (f k))‖ ≤ S * Real.sqrt (sqN w) ^ N := by
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      have h := hS z hz.1
      have hw' : z ∘ e = w := funext hz.2
      rwa [pnorm_eq_sqN, hw'] at h
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin, hcard, mul_assoc]
  have hcl := closure_minimal hgood (isClosed_le hFc hGc)
  rw [(dense_eval_ne_zero hΔ0).closure_eq] at hcl
  exact hcl (Set.mem_univ w)

theorem quad_upper_pull {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) (hFS : IsPullFS x e m)
    {n k r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ} (hb : IsSecBasis x n b)
    (H : Fin (projDeg x e) → MvPolynomial (Ix κ) ℤ) (hH : ∀ l, (H l).IsHomogeneous k)
    (g : Fin r → Fin (projDeg x e) → MvPolynomial (Fin (D + 1)) ℤ)
    (hgh : ∀ j l, (g j l).IsHomogeneous (n + k))
    (hgv : ∀ j l, aeval (x ∘ e) (g j l) = secTrace x e (n + k) (aeval x (b j) * aeval x (H l)))
    {Cε : ℝ} (hCε : ∀ l, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ Cε * m.ρ z ^ k)
    {B : ℝ} (hB : 0 ≤ B) (hsup : ∀ c : Fin r → ℂ, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖∑ j, c j * secFun (b j) z‖ ^ 2 * wgt m n z ≤ B * bNormSq μ (fun j => secFun (b j)) (wgt m n) c)
    (c : Fin r → ℂ) :
    (star c ⬝ᵥ (((traceMat D (n + k) g).map (Int.cast : ℤ → ℂ))ᴴ * monoDiag D (n + k) (projDeg x e) *
      (traceMat D (n + k) g).map (Int.cast : ℤ → ℂ)) *ᵥ c).re ≤
      (projDeg x e : ℝ) ^ 3 * Cε ^ 2 * B * bNormSq μ (fun j => secFun (b j)) (wgt m n) c := by
  classical
  choose F hFh hFb using hb.1
  set β := bNormSq μ (fun j => secFun (b j)) (wgt m n) c with hβ
  have hβ0 : 0 ≤ β := bNormSq_nonneg' μ m _ c
  set S := Cε * Real.sqrt (B * β) with hSdef
  have hl : ∀ l, ∫ w, ‖∑ j, c j * eval w (map (Int.castRingHom ℂ) (g j l))‖ ^ 2 ∂(sphProb (D + 1)) ≤
      ((projDeg x e : ℝ) * S) ^ 2 := by
    intro l
    have htr : ∀ j, aeval (x ∘ e) (g j l) = secTrace x e (n + k) (aeval x (F j * H l)) := fun j => by
      rw [hgv, map_mul, hFb j, aeval_map_intQ]
    have hS : ∀ z ∈ pts (coordIdeal ℤ x),
        ‖∑ j, c j * eval z (map (Int.castRingHom ℂ) (F j * H l))‖ ≤ S * pnorm e z ^ (n + k) := by
      intro z hz
      have hmz : m.ρ z = pnorm e z := hFS z hz
      have e1 : ∑ j, c j * eval z (map (Int.castRingHom ℂ) (F j * H l)) =
          (∑ j, c j * secFun (b j) z) * eval z (map (Int.castRingHom ℂ) (H l)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, map_mul, hFb j, secFun_map_intQ]; ring
      rw [e1, norm_mul, hSdef, pow_add, ← hmz]
      have h1 := norm_le_of_sq_wgt_le hz.1 (norm_nonneg _) (mul_nonneg hB hβ0) (hsup c z hz)
      have h2 := hCε l z hz
      calc ‖∑ j, c j * secFun (b j) z‖ * ‖eval z (map (Int.castRingHom ℂ) (H l))‖
          ≤ (Real.sqrt (B * β) * m.ρ z ^ n) * (Cε * m.ρ z ^ k) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by have := m.nonneg z; positivity)
        _ = Cε * Real.sqrt (B * β) * (m.ρ z ^ n * m.ρ z ^ k) := by ring
    refine integral_sphProb_le _ (fun w => sq_nonneg _) fun w hw => ?_
    have ht := trace_comb_le hfr (fun j => F j * H l) (fun j => g j l)
      (fun j => (hFh j).mul (hH l)) (fun j => hgh j l) htr c hS w
    rw [hw, Real.sqrt_one, one_pow, mul_one] at ht
    exact pow_le_pow_left₀ (norm_nonneg _) ht 2
  rw [quad_conj, quad_monoDiag]
  simp_rw [sum_monoNormSq_traceMat g hgh c]
  calc ∑ l : Fin (projDeg x e), ∫ w, ‖∑ j, c j * eval w (map (Int.castRingHom ℂ) (g j l))‖ ^ 2 ∂(sphProb (D + 1))
      ≤ ∑ _l : Fin (projDeg x e), ((projDeg x e : ℝ) * S) ^ 2 := Finset.sum_le_sum fun l _ => hl l
    _ = (projDeg x e : ℝ) ^ 3 * Cε ^ 2 * B * β := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hSdef, mul_pow, mul_pow,
        Real.sq_sqrt (mul_nonneg hB hβ0)]
      ring

theorem upper {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) (hFS : IsPullFS x e m)
    (hint : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b → ∀ i j,
      Integrable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt m n z : ℂ)) μ)
    (hpd : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b →
      (bGram μ (fun k => secFun (b k)) (wgt m n)).PosDef)
    (hsup : ∃ K : ℝ, ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), 1 ≤ n → IsSecBasis x n b →
      ∀ (c : Fin r → ℂ), ∀ z ∈ pts (coordIdeal ℤ x),
        ‖∑ k, c k * secFun (b k) z‖ ^ 2 * wgt m n z ≤
          K * (n : ℝ) ^ D * bNormSq μ (fun k => secFun (b k)) (wgt m n) c) :
    ∃ (k : ℕ) (C : ℝ), ∀ n : ℕ, 1 ≤ n → ∀ (r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b →
      -(1 / 2) * Real.log (bGram μ (fun j => secFun (b j)) (wgt m n)).det.re ≤
        (projDeg x e : ℝ) * chiP D (n + k) + C * (n : ℝ) ^ D * Real.log (n + 1) := by
  classical
  have hrat := hfr.isRatProjFrame
  obtain ⟨k, ε, hε, hli⟩ := exists_indep_sections x e hrat
  have hεH : ∀ l, ∃ Hl : MvPolynomial (Ix κ) ℤ, Hl.IsHomogeneous k ∧ aeval x Hl = ε l := fun l => by
    obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.mp (hε l)
    exact ⟨p, (mem_homogeneousSubmodule _ _).mp hp, hpe⟩
  choose H hHh hHe using hεH
  have hHe' : (fun l => aeval x (H l)) = ε := funext hHe
  have hCl : ∀ l, ∃ S : ℝ, 0 ≤ S ∧ ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ S * pnorm e z ^ k :=
    fun l => form_le_pnorm hfr k _ ((hHh l).map _)
  choose Cl _ hCl using hCl
  set Cε := ∑ l, |Cl l| with hCεdef
  have hCε : ∀ l, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ Cε * m.ρ z ^ k := fun l z hz => by
    have hmz : m.ρ z = pnorm e z := hFS z hz
    rw [hmz]
    exact (hCl l z hz).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Cl i|) (fun i _ => abs_nonneg _) (Finset.mem_univ l)))
      (pow_nonneg (pnorm_nonneg e z) _))
  obtain ⟨K, hK⟩ := hsup
  obtain ⟨k', hk'⟩ := finrank_sec_le x e hfr
  set T : ℝ := max 1 ((projDeg x e : ℝ) ^ 3 * Cε ^ 2 * |K|) with hTdef
  have hT1 : 1 ≤ T := le_max_left _ _
  refine ⟨k, (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * ((1 / 2) * (Real.log T / Real.log 2 + D)),
    fun n hn r b hb => ?_⟩
  obtain rfl := hb.card_eq
  choose F hFh hFb using hb.1
  have hbF : ∀ j, aeval x (b j) = aeval x (F j) := fun j => by rw [hFb j, aeval_map_intQ]
  have hgex : ∀ j l, ∃ p : MvPolynomial (Fin (D + 1)) ℤ, p.IsHomogeneous (n + k) ∧
      aeval (x ∘ e) p = secTrace x e (n + k) (aeval x (b j) * aeval x (H l)) := fun j l => by
    have hmem : aeval x (b j) * aeval x (H l) ∈ sec ℤ x (n + k) := by
      rw [hbF j, ← map_mul]
      exact Submodule.mem_map.mpr ⟨F j * H l, (mem_homogeneousSubmodule _ _).mpr ((hFh j).mul (hHh l)), rfl⟩
    obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.mp (secTrace_mem x e hfr (n + k) hmem)
    exact ⟨p, (mem_homogeneousSubmodule _ _).mp hp, hpe⟩
  choose g hgh hgv using hgex
  have hinj := traceMat_injective hrat hb H hHh (by rw [hHe']; exact hli) g hgh hgv
  have hr := le_of_injective_mulVec _ hinj
  have hG' := hpd n _ b hb
  have hG := monoDiag_posDef D (n + k) (projDeg x e)
  set A := Real.sqrt (T * (n : ℝ) ^ D) with hAdef
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hTn : 1 ≤ T * (n : ℝ) ^ D := one_le_mul_of_one_le_of_one_le hT1 (one_le_pow₀ hn1)
  have hA : 0 < A := Real.sqrt_pos.mpr (by linarith)
  have hA2 : A ^ 2 = T * (n : ℝ) ^ D := Real.sq_sqrt (by linarith)
  have hnorm : (((A : ℂ) ^ 2) • bGram μ (fun j => secFun (b j)) (wgt m n) -
      ((traceMat D (n + k) g).map (Int.cast : ℤ → ℂ))ᴴ * monoDiag D (n + k) (projDeg x e) *
        (traceMat D (n + k) g).map (Int.cast : ℤ → ℂ)).PosSemidef := by
    refine psd_sub_of_quad_le (isHermitian_sq_smul hG'.isHermitian A)
      (Matrix.isHermitian_conjTranspose_mul_mul _ hG.isHermitian) fun c => ?_
    have hq := quad_upper_pull hfr hFS hb H hHh g hgh hgv hCε (mul_nonneg (abs_nonneg K)
      (pow_nonneg (Nat.cast_nonneg n) D)) (fun c z hz => (hK n _ b hn hb c z hz).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K)
          (pow_nonneg (Nat.cast_nonneg n) D)) (bNormSq_nonneg' μ m _ c))) c
    have hβ0 := bNormSq_nonneg' μ m (n := n) (fun j => secFun (b j)) c
    have hre : (star c ⬝ᵥ (((A : ℂ) ^ 2) • bGram μ (fun j => secFun (b j)) (wgt m n)) *ᵥ c).re =
        A ^ 2 * bNormSq μ (fun j => secFun (b j)) (wgt m n) c := by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
        bNormSq_eq_re μ _ _ (hint n _ b hb)]
    rw [hre, hA2]
    refine hq.trans (mul_le_mul_of_nonneg_right ?_ hβ0)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (Nat.cast_nonneg n) D)
  have hsmall : ∀ i, ((((1 : Matrix (Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n + k)).card))
      (Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n + k)).card)) ℤ).map (Int.cast : ℤ → ℂ))ᴴ *
      monoDiag D (n + k) (projDeg x e) *
      (1 : Matrix (Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n + k)).card))
      (Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n + k)).card)) ℤ).map (Int.cast : ℤ → ℂ)) i i).re
      ≤ (1 : ℝ) ^ 2 := by
    intro i
    rw [Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one, monoDiag, Matrix.diagonal_apply_eq, Complex.ofReal_re, one_pow]
    exact monoNormSq_le_one _
  have key := neg_log_det_le hr hG' hG _ hinj 1 (by simp) hA one_pos hnorm hsmall
  rw [Real.log_one, mul_zero, add_zero, neg_log_det_monoDiag] at key
  obtain ⟨hL0, hL⟩ := log_sqrt_bound D hT1 hn
  have hrb : ((finrank ℤ (sec ℤ x n) : ℕ) : ℝ) ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D := by
    have h1 : ((finrank ℤ (sec ℤ x n) : ℕ) : ℝ) ≤ (projDeg x e : ℝ) * (((n + k' + D).choose D : ℕ) : ℝ) := by
      exact_mod_cast hk' n
    rw [mul_assoc]
    exact h1.trans (mul_le_mul_of_nonneg_left (choose_bound k' D hn) (Nat.cast_nonneg _))
  have hX : 0 ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D := by positivity
  have h3 : ((finrank ℤ (sec ℤ x n) : ℕ) : ℝ) * Real.log A ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D *
      ((1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1)) :=
    (mul_le_mul_of_nonneg_right hrb hL0).trans (mul_le_mul_of_nonneg_left hL hX)
  have h4 : (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D *
      ((1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1)) =
      (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * ((1 / 2) * (Real.log T / Real.log 2 + D)) *
        (n : ℝ) ^ D * Real.log (n + 1) := by ring
  linarith

end

end ResChiSandwich

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ResChiSandwich

open MvPolynomial MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjectionBounds
open scoped ComplexOrder Matrix

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem bNormSq_le_of_pts_of {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    [IsProbabilityMeasure μ] (hcar : μ (pts (coordIdeal ℤ x))ᶜ = 0) {n r : ℕ}
    (s : Fin r → (Ix κ → ℂ) → ℂ) (c : Fin r → ℂ) {B : ℝ}
    (h : ∀ z ∈ pts (coordIdeal ℤ x), ‖∑ j, c j * s j z‖ ^ 2 * wgt m n z ≤ B) :
    bNormSq μ s (wgt m n) c ≤ B := by
  have hae : ∀ᵐ z ∂μ, z ∈ pts (coordIdeal ℤ x) := ae_iff.mpr hcar
  unfold bNormSq
  calc ∫ z, ‖∑ j, c j * s j z‖ ^ 2 * wgt m n z ∂μ ≤ ∫ _z, B ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun z => ?_) (integrable_const B) ?_
        · exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (pow_nonneg (m.nonneg z) _))
        · filter_upwards [hae] with z hz using h z hz
    _ = B := by simp

theorem form_le_rho {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {e : Fin (D + 1) → Ix κ}
    (hfr : IsProjFrame x e) (hFS : IsPullFS x e m) (k : ℕ) (f : MvPolynomial (Ix κ) ℂ) (hf : f.IsHomogeneous k) :
    ∃ S : ℝ, ∀ z ∈ pts (coordIdeal ℤ x), ‖eval z f‖ ≤ S * m.ρ z ^ k := by
  obtain ⟨S, -, hS⟩ := form_le_pnorm hfr k f hf
  refine ⟨S, fun z hz => ?_⟩
  have hmz : m.ρ z = pnorm e z := hFS z hz
  rw [hmz]
  exact hS z hz

theorem lower {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) (hFS : IsPullFS x e m)
    [IsProbabilityMeasure μ] (hcar : μ (pts (coordIdeal ℤ x))ᶜ = 0)
    (hint : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b → ∀ i j,
      Integrable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt m n z : ℂ)) μ)
    (hpd : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b →
      (bGram μ (fun k => secFun (b k)) (wgt m n)).PosDef) :
    ∃ (k : ℕ) (C : ℝ), ∀ n : ℕ, k + 1 ≤ n → ∀ (r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b →
      (projDeg x e : ℝ) * chiP D (n - k) - C * (n : ℝ) ^ D * Real.log (n + 1) ≤
        -(1 / 2) * Real.log (bGram μ (fun j => secFun (b j)) (wgt m n)).det.re := by
  classical
  obtain ⟨kε, ε, hε, hli⟩ := exists_indep_sections x e hfr.isRatProjFrame
  have hεH : ∀ l, ∃ Hl : MvPolynomial (Ix κ) ℤ, Hl.IsHomogeneous kε ∧ aeval x Hl = ε l := fun l => by
    obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.mp (hε l)
    exact ⟨p, (mem_homogeneousSubmodule _ _).mp hp, hpe⟩
  choose H hHh hHe using hεH
  have hliH : LinearIndependent (fnField (x ∘ e)) fun l => aeval x (H l) := by
    rw [show (fun l => aeval x (H l)) = ε from funext hHe]; exact hli
  have hCl : ∀ l, ∃ S : ℝ, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ S * m.ρ z ^ kε :=
    fun l => form_le_rho hfr hFS kε _ ((hHh l).map _)
  choose Cl hCl using hCl
  set Cε := ∑ l, |Cl l| with hCεdef
  have hCε0 : 0 ≤ Cε := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hCε : ∀ l, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ Cε * m.ρ z ^ kε := fun l z hz =>
    (hCl l z hz).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Cl i|) (fun i _ => abs_nonneg _) (Finset.mem_univ l)))
      (pow_nonneg (m.nonneg z) _))
  obtain ⟨k₀, hk₀⟩ := exists_sec_eq_mul x e hfr
  obtain ⟨tb, htb⟩ := exists_isSecBasis x k₀
  choose Tf hTfh hTfb using htb.1
  have hCt : ∀ i, ∃ S : ℝ, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (Tf i))‖ ≤ S * m.ρ z ^ k₀ :=
    fun i => form_le_rho hfr hFS k₀ _ ((hTfh i).map _)
  choose Cti hCti using hCt
  set Ct := ∑ i, |Cti i| with hCtdef
  have hCt : ∀ i, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (Tf i))‖ ≤ Ct * m.ρ z ^ k₀ := fun i z hz =>
    (hCti i z hz).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Cti i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)))
      (pow_nonneg (m.nonneg z) _))
  have hCt0 : 0 ≤ Ct := Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨k', hk'⟩ := finrank_sec_le x e hfr
  set T : ℝ := max 1 (Cε ^ 2 * (projDeg x e : ℝ) * ((1 + 0 + D : ℕ) : ℝ) ^ D) with hTdef
  have hT1 : 1 ≤ T := le_max_left _ _
  set lam : ℝ := max 1 Ct with hlamdef
  have hlam1 : 1 ≤ lam := le_max_left _ _
  have hloglam : 0 ≤ Real.log lam := Real.log_nonneg hlam1
  refine ⟨max kε k₀, (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D *
    ((1 / 2) * (Real.log T / Real.log 2 + D) + Real.log lam / Real.log 2), fun n hn r b hb => ?_⟩
  obtain rfl := hb.card_eq
  have hn1 : 1 ≤ n := by omega
  have hnk : n - kε + kε = n := Nat.sub_add_cancel (by omega)
  have hnk₀ : n - k₀ + k₀ = n := Nat.sub_add_cancel (by omega)
  obtain ⟨crd, hcrd1, hcrd2⟩ := exists_crd hb

  have hQh : ∀ p : Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n - kε)).card),
      (prodForm e (adtEnum D (n - kε) (finProdFinEquiv.symm p).2) (H (finProdFinEquiv.symm p).1)).IsHomogeneous n :=
    fun p => by
      have := prodForm_isHomogeneous e (adtEnum_sum D (n - kε) (finProdFinEquiv.symm p).2)
        (hHh (finProdFinEquiv.symm p).1)
      rwa [hnk] at this
  have hQm : ∀ p, aeval x (prodForm e (adtEnum D (n - kε) (finProdFinEquiv.symm p).2)
      (H (finProdFinEquiv.symm p).1)) ∈ sec ℤ x n := fun p =>
    Submodule.mem_map.mpr ⟨_, (mem_homogeneousSubmodule _ _).mpr (hQh p), rfl⟩
  set M : Matrix (Fin (finrank ℤ (sec ℤ x n)))
      (Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n - kε)).card)) ℤ :=
    Matrix.of fun j p => crd ⟨_, hQm p⟩ j with hMdef
  have hM : ∀ p, ∑ j, (M j p : Ω) * aeval x (b j) = aeval x (prodForm e
      (adtEnum D (n - kε) (finProdFinEquiv.symm p).2) (H (finProdFinEquiv.symm p).1)) :=
    fun p => hcrd1 ⟨_, hQm p⟩
  have hinj := injective_map_of_int_ker M (alphaMat_ker hfr H hliH M hM)
  have hr := le_of_injective_mulVec _ hinj
  have hG' := monoDiag_posDef D (n - kε) (projDeg x e)
  have hG := hpd n _ b hb
  set A := Real.sqrt (T * (n : ℝ) ^ D) with hAdef
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hTn : 1 ≤ T * (n : ℝ) ^ D := one_le_mul_of_one_le_of_one_le hT1 (one_le_pow₀ hn1')
  have hA : 0 < A := Real.sqrt_pos.mpr (by linarith)
  have hA2 : A ^ 2 = T * (n : ℝ) ^ D := Real.sq_sqrt (by linarith)
  have hnorm : (((A : ℂ) ^ 2) • monoDiag D (n - kε) (projDeg x e) -
      (M.map (Int.cast : ℤ → ℂ))ᴴ * bGram μ (fun j => secFun (b j)) (wgt m n) *
        M.map (Int.cast : ℤ → ℂ)).PosSemidef := by
    refine psd_sub_of_quad_le (isHermitian_sq_smul hG'.isHermitian A)
      (Matrix.isHermitian_conjTranspose_mul_mul _ hG.isHermitian) fun c => ?_
    rw [quad_conj, ← bNormSq_eq_re μ _ _ (hint n _ b hb), Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← Complex.ofReal_pow, Complex.re_ofReal_mul, quad_monoDiag]
    have hq0 : 0 ≤ ∑ l : Fin (projDeg x e), ∑ i, monoNormSq (adtEnum D (n - kε) i) *
        ‖c (finProdFinEquiv (l, i))‖ ^ 2 := Finset.sum_nonneg fun l _ =>
      Finset.sum_nonneg fun i _ => mul_nonneg (monoNormSq_pos _).le (sq_nonneg _)
    refine bNormSq_le_of_pts_of hcar _ _ fun z hz => ?_
    rw [sum_mulVec_secFun hb M _ hQh hM c z hz]
    have h1 := pt_lower hFS H hCε0 hCε c hz
    rw [hnk] at h1
    refine h1.trans ?_
    have hswap : ∑ l : Fin (projDeg x e), ∑ i, ‖c (finProdFinEquiv (l, i))‖ ^ 2 *
        monoNormSq (adtEnum D (n - kε) i) = ∑ l : Fin (projDeg x e), ∑ i,
        monoNormSq (adtEnum D (n - kε) i) * ‖c (finProdFinEquiv (l, i))‖ ^ 2 :=
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hswap, hA2]
    refine mul_le_mul_of_nonneg_right ?_ hq0
    have hB1 : (((n - kε + D).choose D : ℕ) : ℝ) ≤ (((n + 0 + D).choose D : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_le_choose D (by omega)
    have hB2 := choose_bound 0 D hn1
    calc Cε ^ 2 * (projDeg x e : ℝ) * (((n - kε + D).choose D : ℕ) : ℝ)
        ≤ Cε ^ 2 * (projDeg x e : ℝ) * (((1 + 0 + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D) :=
          mul_le_mul_of_nonneg_left (hB1.trans hB2) (by positivity)
      _ = (Cε ^ 2 * (projDeg x e : ℝ) * ((1 + 0 + D : ℕ) : ℝ) ^ D) * (n : ℝ) ^ D := by ring
      _ ≤ T * (n : ℝ) ^ D := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

  have hQ'h : ∀ s : Fin (Finset.Nat.antidiagonalTuple (D + 1) (n - k₀)).card × Fin (finrank ℤ (sec ℤ x k₀)),
      (prodForm e (adtEnum D (n - k₀) s.1) (Tf s.2)).IsHomogeneous n := fun s => by
    have := prodForm_isHomogeneous e (adtEnum_sum D (n - k₀) s.1) (hTfh s.2)
    rwa [hnk₀] at this
  have hwm : ∀ s : Fin (Finset.Nat.antidiagonalTuple (D + 1) (n - k₀)).card × Fin (finrank ℤ (sec ℤ x k₀)),
      aeval x (prodForm e (adtEnum D (n - k₀) s.1) (Tf s.2)) ∈ sec ℤ x n := fun s =>
    Submodule.mem_map.mpr ⟨_, (mem_homogeneousSubmodule _ _).mpr (hQ'h s), rfl⟩
  have hspan := crd_span hcrd2 hb _ hwm (sec_le_span_prod (hk₀ n (by omega)) htb Tf hTfb)
  obtain ⟨f, hfdet⟩ := exists_cols_det_ne_zero _ hspan
  set Nm : Matrix (Fin (finrank ℤ (sec ℤ x n))) (Fin (finrank ℤ (sec ℤ x n))) ℤ :=
    Matrix.of fun p q => crd ⟨_, hwm (f q)⟩ p with hNm
  have hsmall : ∀ i, (((Nm.map (Int.cast : ℤ → ℂ))ᴴ * bGram μ (fun j => secFun (b j)) (wgt m n) *
      Nm.map (Int.cast : ℤ → ℂ)) i i).re ≤ lam ^ 2 := by
    intro i
    rw [diag_conj_eq, ← bNormSq_eq_re μ _ _ (hint n _ b hb)]
    refine bNormSq_le_of_pts_of hcar _ _ fun z hz => ?_
    have hv : Nm.map (Int.cast : ℤ → ℂ) *ᵥ Pi.single i 1 =
        fun p => ((crd ⟨_, hwm (f i)⟩ p : ℤ) : ℂ) := by
      funext p
      simp [hNm, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hv, sum_secFun_eq' hb _ (hQ'h (f i)) _ (hcrd1 ⟨_, hwm (f i)⟩) z hz]
    have h1 := pt_small hFS (adtEnum_sum D (n - k₀) (f i).1) (Tf (f i).2) (hCt (f i).2) hz
    rw [hnk₀] at h1
    exact h1.trans (pow_le_pow_left₀ hCt0 (le_max_right _ _) 2)
  have key := neg_log_det_le hr hG' hG M hinj _ hfdet hA (by linarith) hnorm hsmall
  rw [neg_log_det_monoDiag] at key

  have hmono : Monotone (chiP D) := monotone_nat_of_le_succ fun n => by
    have := chiP_succ_sub_nonneg D n; linarith
  have hm := mul_le_mul_of_nonneg_left (hmono (show n - max kε k₀ ≤ n - kε by omega))
    (Nat.cast_nonneg (projDeg x e) : (0 : ℝ) ≤ projDeg x e)
  obtain ⟨hL0, hL⟩ := log_sqrt_bound D hT1 hn1
  have hll := log_le_div_mul hloglam hn1
  set R' := projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n - kε)).card
  set r := finrank ℤ (sec ℤ x n)
  have hrR : (R' : ℝ) ≤ r := by exact_mod_cast hr
  have hR0 : (0 : ℝ) ≤ R' := Nat.cast_nonneg _
  have hrb : (r : ℝ) ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D := by
    have h1 : (r : ℝ) ≤ (projDeg x e : ℝ) * (((n + k' + D).choose D : ℕ) : ℝ) := by
      exact_mod_cast hk' n
    rw [mul_assoc]
    exact h1.trans (mul_le_mul_of_nonneg_left (choose_bound k' D hn1) (Nat.cast_nonneg _))
  have hX : 0 ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D := by positivity
  have hlogn : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have h3 : (R' : ℝ) * Real.log A ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D *
      ((1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1)) :=
    (mul_le_mul_of_nonneg_right (hrR.trans hrb) hL0).trans (mul_le_mul_of_nonneg_left hL hX)
  have h4 : ((r : ℝ) - R') * Real.log lam ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D *
      (n : ℝ) ^ D * (Real.log lam / Real.log 2 * Real.log (n + 1)) :=
    (mul_le_mul_of_nonneg_right (by linarith) hloglam).trans (mul_le_mul_of_nonneg_left hll hX)
  have h5 : (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D *
      ((1 / 2) * (Real.log T / Real.log 2 + D) + Real.log lam / Real.log 2) * (n : ℝ) ^ D *
        Real.log (n + 1) = (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D *
      ((1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1)) +
      (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D *
      (Real.log lam / Real.log 2 * Real.log (n + 1)) := by ring
  linarith

end

end ResChiSandwich

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder

noncomputable section

theorem ResChiBounds.proof (hR : ResolutionSupBound.Statement) : ResChiBounds.Statement := by
  intro D Ω _ _ κ _ d e hfr hFS
  have hint : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n b → ∀ i j,
      Integrable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt d.m n z : ℂ))
        (ResSym.symMeasure d) := fun n r b hb => ResSym.integrable_gram d hb.1
  have hpd : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n b →
      (bGram (ResSym.symMeasure d) (fun k => secFun (b k)) (wgt d.m n)).PosDef :=
    fun n r b hb => ResSym.posDef_gram d hb
  obtain ⟨k₁, C₁, h₁⟩ := ResChiSandwich.upper hfr hFS hint hpd (ResSym.sup_le_gram hR d)
  obtain ⟨k₂, C₂, h₂⟩ := ResChiSandwich.lower hfr hFS (ResSym.symMeasure_compl_pts d) hint hpd
  have hmono : Monotone (chiP D) := monotone_nat_of_le_succ fun n => by
    have := chiP_succ_sub_nonneg D n; linarith
  have hδ : (0 : ℝ) ≤ (projDeg d.x e : ℝ) := Nat.cast_nonneg _
  refine ⟨max k₁ k₂, max C₁ C₂, fun n hn => ?_⟩
  obtain ⟨b₀, hb₀⟩ := exists_isSecBasis d.x n
  have h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2 := ⟨⟨_, b₀⟩, hb₀⟩
  rw [ResSym.resChi_eq d n h]
  have hX : 0 ≤ (n : ℝ) ^ D * Real.log (n + 1) :=
    mul_nonneg (by positivity) (Real.log_nonneg (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith))
  have hu := h₁ n (by omega) _ _ h.choose_spec
  have hl := h₂ n (by omega) _ _ h.choose_spec
  constructor
  · have hm : chiP D (n - max k₁ k₂) ≤ chiP D (n - k₂) := hmono (by omega)
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    have hc : C₂ * (n : ℝ) ^ D * Real.log (n + 1) ≤ max C₁ C₂ * (n : ℝ) ^ D * Real.log (n + 1) := by
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hX
    linarith
  · have hm : chiP D (n + k₁) ≤ chiP D (n + max k₁ k₂) := hmono (by omega)
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    have hc : C₁ * (n : ℝ) ^ D * Real.log (n + 1) ≤ max C₁ C₂ * (n : ℝ) ^ D * Real.log (n + 1) := by
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX
    linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem AnResToAnalyticRes.full : GroundTheory.Heights₂.Heights.HilbertSamuel.AnResToAnalyticRes.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.AnResToAnalyticRes.proof NonvanishingDense.full

theorem BlockImageChi.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageChi.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageChi.proof

theorem ResChiBounds.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiBounds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiBounds.proof ResolutionSupBound.full

theorem ProjectionBounds.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjectionBounds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjectionBounds.proof ResChiBounds.full

theorem PullFSExtension.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PullFSExtension.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PullFSExtension.proof ProjFrameBasePtFree.full

theorem ProjFSMass.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFSMass.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFSMass.proof

theorem RealGramComparison.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RealGramComparison.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RealGramComparison.proof ResolutionSupBound.full ProjectionBounds.full PullFSExtension.full

theorem MonomialDegree.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MonomialDegree.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MonomialDegree.proof

theorem ResChiIndex.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiIndex.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiIndex.proof

theorem VeroneseMonoBasis.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseMonoBasis.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseMonoBasis.proof

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
