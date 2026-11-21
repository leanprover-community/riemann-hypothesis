import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFirstCoords
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian

section
section
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop

noncomputable section

namespace GlobalTheory.SphereMeanDrop

theorem measurePreserving_polar_gaussProb (n : ℕ) (hn : 0 < n) :
    MeasurePreserving (fun p : UnitSphereC n × Ioi (0:ℝ) => (p.2 : ℝ) • (p.1 : EuclideanSpace ℂ (Fin n)))
      ((sphereProb n).prod (radProb n)) (gaussProb n) := by
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclidean_complex]; omega)
  set f : UnitSphereC n × Ioi (0:ℝ) → EuclideanSpace ℂ (Fin n) :=
    fun p => (p.2 : ℝ) • (p.1 : EuclideanSpace ℂ (Fin n)) with hf_def
  set S := (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere with hS
  set R0 := Measure.volumeIoiPow (2 * n - 1) with hR0
  set h : Ioi (0:ℝ) → ENNReal := fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2)) with hh_def
  set g : EuclideanSpace ℂ (Fin n) → ENNReal := fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) with hg_def
  have hfm : Measurable f := by
    apply Continuous.measurable
    exact (continuous_subtype_val.comp continuous_snd).smul (continuous_subtype_val.comp continuous_fst)
  have hhm : Measurable h := Measurable.ennreal_ofReal (by fun_prop)
  have hgm : Measurable g := Measurable.ennreal_ofReal (by fun_prop)

  have hA : MeasurePreserving f (S.prod R0) volume := by
    have h1 := Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (EuclideanSpace ℂ (Fin n)))
    rw [finrank_euclidean_complex] at h1
    have h2 : MeasurePreserving (homeomorphUnitSphereProd (EuclideanSpace ℂ (Fin n))).toMeasurableEquiv
      _ _ := h1
    have h3 := h2.symm
    have h4 : MeasurePreserving (Subtype.val : ({(0 : EuclideanSpace ℂ (Fin n))}ᶜ : Set _) → _)
        ((volume : Measure (EuclideanSpace ℂ (Fin n))).comap Subtype.val) volume := by
      refine ⟨measurable_subtype_coe, ?_⟩
      rw [map_comap_subtype_coe (measurableSet_singleton _).compl, restrict_compl_singleton]
    have h5 := h4.comp h3
    convert h5 using 1
    funext p
    simp [hf_def]

  have hB : MeasurePreserving f (S.prod (R0.withDensity h))
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g) := by
    refine ⟨hfm, ?_⟩
    rw [prod_withDensity_right hhm]
    ext s hs
    rw [Measure.map_apply hfm hs, withDensity_apply _ (hfm hs), withDensity_apply _ hs]
    have hpt : ∀ z : UnitSphereC n × Ioi (0:ℝ), h z.2 = g (f z) := by
      intro z
      simp only [hh_def, hg_def, hf_def, norm_smul, Real.norm_eq_abs, abs_of_pos (show (0:ℝ) < z.2 from z.2.2)]
      have : ‖(z.1 : EuclideanSpace ℂ (Fin n))‖ = 1 := by simp
      rw [this, mul_one]
    simp_rw [hpt]
    exact hA.setLIntegral_comp_preimage hs hgm

  have ha0 : S univ ≠ 0 := by
    rw [hS, Measure.toSphere_apply_univ, finrank_euclidean_complex]
    exact mul_ne_zero (by simp; omega) (Metric.measure_ball_pos _ _ one_pos).ne'
  have haT : S univ ≠ ⊤ := measure_ne_top _ _
  have hsph : sphereProb n = (S univ)⁻¹ • S := sphereProb_eq n
  have hrad : radProb n = ((R0.withDensity h) univ)⁻¹ • R0.withDensity h := by
    simp only [radProb, ProbabilityTheory.cond, Measure.restrict_univ]; rfl
  have hgau : gaussProb n = (((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g) univ)⁻¹ •
      (volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g := by
    simp only [gaussProb, ProbabilityTheory.cond, Measure.restrict_univ]; rfl
  have hmass : ((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g) univ
      = S univ * (R0.withDensity h) univ := by
    rw [← hB.map_eq, Measure.map_apply hfm MeasurableSet.univ, preimage_univ, ← univ_prod_univ,
      Measure.prod_prod]
  refine ⟨hfm, ?_⟩
  rw [hsph, hrad, hgau, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_smul, hB.map_eq, hmass, ENNReal.mul_inv (Or.inl ha0) (Or.inl haT)]

end GlobalTheory.SphereMeanDrop
end
end

open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurePreserving_polar_gaussianProbabilityComplexSpace : ∀ (n : ℕ), 0 < n → MeasurePreserving (fun p : UnitSphereC n × Ioi (0:ℝ) => (p.2 : ℝ) • (p.1 : EuclideanSpace ℂ (Fin n))) ((sphereProb n).prod (radProb n)) (gaussProb n) := by
  atlas_forward_decl GlobalTheory.SphereMeanDrop.measurePreserving_polar_gaussProb
end

section
section
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop

namespace GlobalTheory.SphereMeanDrop

theorem radProb_log_mean : ∀ (n : ℕ), 0 < n → IsProbabilityMeasure (radProb n) ∧
    Integrable (fun r : Ioi (0:ℝ) => Real.log r) (radProb n) ∧
    ∫ r, Real.log (r : ℝ) ∂(radProb n) = radK (2 * n - 1) / radJ (2 * n - 1) := by
  intro n hn
  set μ0 := Measure.volumeIoiPow (2 * n - 1) with hμ0
  set f : Ioi (0:ℝ) → NNReal := fun r => Real.toNNReal (Real.exp (-(r : ℝ) ^ 2)) with hf
  have hfm : Measurable f := by
    rw [hf]; exact (by fun_prop : Measurable fun r : Ioi (0:ℝ) => Real.exp (-(r : ℝ) ^ 2)).real_toNNReal
  have hν : (μ0.withDensity fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2)))
      = μ0.withDensity fun r => (f r : ENNReal) := rfl
  have hJi : Integrable (fun r : Ioi (0 : ℝ) ↦ Real.exp (-(r : ℝ) ^ 2)) μ0 :=
    integrable_volumeIoiPow (k := 2 * n - 1) (g := fun r ↦ Real.exp (-r ^ 2)) (integrableOn_radJ _)
  have hKo : IntegrableOn (fun r : ℝ ↦ r ^ (2 * n - 1) * (Real.log r * Real.exp (-r ^ 2))) (Ioi 0) := by
    refine (integrableOn_radK (k := 2 * n - 1) (by omega)).congr_fun (fun r _ ↦ ?_)
      measurableSet_Ioi
    ring
  have hKi : Integrable (fun r : Ioi (0 : ℝ) ↦ Real.log r * Real.exp (-(r : ℝ) ^ 2)) μ0 :=
    integrable_volumeIoiPow (k := 2 * n - 1) (g := fun r ↦ Real.log r * Real.exp (-r ^ 2)) hKo
  have hJv : ∫ r : Ioi (0 : ℝ), Real.exp (-(r : ℝ) ^ 2) ∂μ0 = radJ (2 * n - 1) := by
    rw [hμ0, integral_volumeIoiPow (2 * n - 1) (fun r ↦ Real.exp (-r ^ 2))]; rfl
  have hKv : ∫ r : Ioi (0 : ℝ), Real.log r * Real.exp (-(r : ℝ) ^ 2) ∂μ0 = radK (2 * n - 1) := by
    rw [hμ0, integral_volumeIoiPow (2 * n - 1) (fun r ↦ Real.log r * Real.exp (-r ^ 2)), radK]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ ↦ ?_
    ring

  have hmass : (μ0.withDensity fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) univ
      = ENNReal.ofReal (radJ (2 * n - 1)) := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ← hJv,
      ofReal_integral_eq_lintegral_ofReal hJi (Filter.Eventually.of_forall fun r => (Real.exp_pos _).le)]
  have hJpos := radJ_pos (2 * n - 1)
  have hm0 : (μ0.withDensity fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) univ ≠ 0 := by
    rw [hmass]; exact ENNReal.ofReal_pos.2 hJpos |>.ne'
  have hmt : (μ0.withDensity fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) univ ≠ ⊤ := by
    rw [hmass]; exact ENNReal.ofReal_ne_top
  have hcond : radProb n = ((μ0.withDensity fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) univ)⁻¹ •
      (μ0.withDensity fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) := by
    rw [radProb, ProbabilityTheory.cond, Measure.restrict_univ]
  refine ⟨?_, ?_, ?_⟩
  · rw [radProb]; exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite hm0 hmt
  · rw [hcond]
    refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 hm0)
    rw [hν, integrable_withDensity_iff_integrable_smul hfm]
    refine hKi.congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [hf, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.exp_pos _).le]
    ring
  · rw [hcond, integral_smul_measure, hmass, hν, integral_withDensity_eq_integral_smul hfm]
    have : ∫ r : Ioi (0:ℝ), f r • Real.log (r : ℝ) ∂μ0 = radK (2 * n - 1) := by
      rw [← hKv]
      refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
      simp only [hf, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.exp_pos _).le]
      ring
    rw [this, ENNReal.toReal_inv, ENNReal.toReal_ofReal hJpos.le, smul_eq_mul, div_eq_inv_mul]

end GlobalTheory.SphereMeanDrop
end

open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianRadialLawProbability_log_integrable_mean : ∀ (n : ℕ), 0 < n → IsProbabilityMeasure (radProb n) ∧ Integrable (fun r : Ioi (0:ℝ) => Real.log r) (radProb n) ∧ ∫ r, Real.log (r : ℝ) ∂(radProb n) = radK (2 * n - 1) / radJ (2 * n - 1) := by
  atlas_forward_decl GlobalTheory.SphereMeanDrop.radProb_log_mean
end

section
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop

noncomputable section

namespace GlobalTheory.GaussMarginal

open Real

theorem lintegral_pi_fin {E : Type*} [MeasurableSpace E] (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (f : Fin n → E → ENNReal) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    rw [← h.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), Fin.prod_univ_succ,
      ← ih (fun i => f i.succ) (fun i => hf _), ← lintegral_prod_mul (hf 0).aemeasurable
        (Finset.measurable_prod _ fun i _ => (hf i.succ).comp (measurable_pi_apply i)).aemeasurable]
    refine lintegral_congr fun q => ?_
    simp [Fin.prod_univ_succ, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

theorem lintegral_pi_prod {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : ι → E → ENNReal) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  let e := (Fintype.equivFin ι).symm
  have h := measurePreserving_piCongrLeft (fun _ : ι => μ) e
  rw [← h.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), ← e.prod_comp,
    ← lintegral_pi_fin _ μ (fun i => f (e i)) (fun i => hf _)]
  refine lintegral_congr fun q => ?_
  rw [← e.prod_comp]
  simp [MeasurableEquiv.coe_piCongrLeft]

theorem pi_withDensity_const {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E)
    [SigmaFinite μ] (f : E → ENNReal) (hf : Measurable f) [SigmaFinite (μ.withDensity f)] :
    (Measure.pi fun _ : ι => μ.withDensity f) =
      (Measure.pi fun _ : ι => μ).withDensity fun x => ∏ i, f (x i) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [withDensity_apply _ (hs _), ← lintegral_indicator (hs _)]
  rw [← lintegral_pi_prod μ (fun i => (s i).indicator f) (fun i => hf.indicator (hs i))]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ Set.univ.pi s
  · rw [Set.indicator_of_mem hx]
    exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hx i trivial) _).symm
  · rw [Set.indicator_of_notMem hx]
    obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by simpa [Set.mem_pi] using hx
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

theorem isProbabilityMeasure_complexGaussian_one :
    IsProbabilityMeasure (GlobalTheory.complexGaussian ℂ 1) :=
  GlobalTheory.isProbabilityMeasure_complexGaussian (by simp [Complex.finrank_real_complex])

theorem gaussProb_eq_complexGaussian (k : ℕ) :
    gaussProb k = GlobalTheory.complexGaussian (EuclideanSpace ℂ (Fin k)) k := by
  have hP := GlobalTheory.isProbabilityMeasure_complexGaussian (E := EuclideanSpace ℂ (Fin k)) (g := k)
    (by rw [GlobalTheory.finrank_real_euclideanSpace_complex, Fintype.card_fin])
  set ν := (volume : Measure (EuclideanSpace ℂ (Fin k))).withDensity
    fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) with hν
  have hm : Measurable fun x : EuclideanSpace ℂ (Fin k) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) := by
    fun_prop
  have hc : GlobalTheory.complexGaussian (EuclideanSpace ℂ (Fin k)) k = ENNReal.ofReal ((π ^ k)⁻¹) • ν := by
    ext s hs
    rw [Measure.smul_apply, GlobalTheory.complexGaussian, withDensity_apply _ hs, hν, withDensity_apply _ hs,
      smul_eq_mul, ← lintegral_const_mul _ hm]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_mul (by positivity)]
  have h1 := hP.measure_univ
  rw [hc, Measure.smul_apply, smul_eq_mul] at h1
  rw [gaussProb, ProbabilityTheory.cond, Measure.restrict_univ, hc, ← hν,
    ← ENNReal.eq_inv_of_mul_eq_one_left h1]

theorem map_ofLp_gaussProb (k : ℕ) :
    (gaussProb k).map (WithLp.ofLp (p := 2) (V := Fin k → ℂ)) =
      Measure.pi fun _ : Fin k => GlobalTheory.complexGaussian ℂ 1 := by
  haveI := isProbabilityMeasure_complexGaussian_one
  have hmp := GlobalTheory.volume_preserving_ofLp_complex (Fin k)
  set f1 : ℂ → ENNReal := fun z => ENNReal.ofReal ((π ^ 1)⁻¹ * Real.exp (-‖z‖ ^ 2)) with hf1
  have hf1m : Measurable f1 := by fun_prop
  haveI : SigmaFinite ((volume : Measure ℂ).withDensity f1) :=
    inferInstanceAs (SigmaFinite (GlobalTheory.complexGaussian ℂ 1))
  have hG : Measurable fun y : Fin k → ℂ => ∏ i, f1 (y i) := by fun_prop
  ext s hs
  rw [Measure.map_apply hmp.measurable hs, gaussProb_eq_complexGaussian, GlobalTheory.complexGaussian,
    withDensity_apply _ (hmp.measurable hs), show GlobalTheory.complexGaussian ℂ 1 = (volume : Measure ℂ).withDensity f1 from rfl,
    pi_withDensity_const _ f1 hf1m, ← volume_pi, withDensity_apply _ hs,
    ← hmp.setLIntegral_comp_preimage hs hG]
  refine lintegral_congr fun x => ?_
  simp only [hf1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity), Finset.prod_mul_distrib,
    ← Real.exp_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin, EuclideanSpace.norm_sq_eq,
    ← Finset.sum_neg_distrib, pow_one, inv_pow]

theorem measurePreserving_restrict_castLE {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {N n : ℕ} (h : N ≤ n) :
    MeasurePreserving (fun (y : Fin n → α) (j : Fin N) => y (Fin.castLE h j))
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have hr : Measurable fun (y : Fin (N + m) → α) (j : Fin N) => y (Fin.castLE h j) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  refine ⟨hr, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hr (MeasurableSet.univ_pi hs)]
  have hpre : (fun (y : Fin (N + m) → α) (j : Fin N) => y (Fin.castLE h j)) ⁻¹' univ.pi s =
      univ.pi (Fin.append s fun _ : Fin m => (univ : Set α)) := by
    ext y
    simp only [mem_preimage, mem_univ_pi]
    constructor
    · intro hy i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hy j
      · rw [Fin.append_right]; exact mem_univ _
    · intro hy j
      have := hy (Fin.castAdd m j)
      rwa [Fin.append_left] at this
  rw [hpre, Measure.pi_pi, Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem measurePreserving_firstCoords_gaussProb :
    ∀ (N n : ℕ) (h : N ≤ n), MeasurePreserving (firstCoords h) (gaussProb n) (gaussProb N) := by
  intro N n h
  haveI := isProbabilityMeasure_complexGaussian_one
  have hofn : Measurable (WithLp.ofLp (p := 2) (V := Fin n → ℂ)) :=
    (GlobalTheory.volume_preserving_ofLp_complex (Fin n)).measurable
  have hofN : Measurable (WithLp.ofLp (p := 2) (V := Fin N → ℂ)) :=
    (GlobalTheory.volume_preserving_ofLp_complex (Fin N)).measurable
  have htoN : Measurable (WithLp.toLp 2 : (Fin N → ℂ) → EuclideanSpace ℂ (Fin N)) := by fun_prop
  have e1 : MeasurePreserving (WithLp.ofLp (p := 2) (V := Fin n → ℂ)) (gaussProb n)
      (Measure.pi fun _ : Fin n => GlobalTheory.complexGaussian ℂ 1) := ⟨hofn, map_ofLp_gaussProb n⟩
  have e3 : MeasurePreserving (WithLp.toLp 2 : (Fin N → ℂ) → EuclideanSpace ℂ (Fin N))
      (Measure.pi fun _ : Fin N => GlobalTheory.complexGaussian ℂ 1) (gaussProb N) := by
    refine ⟨htoN, ?_⟩
    rw [← map_ofLp_gaussProb N, Measure.map_map htoN hofN]
    convert Measure.map_id
    funext x
    rfl
  exact e3.comp ((measurePreserving_restrict_castLE _ h).comp e1)

end GlobalTheory.GaussMarginal
end
end

section
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_first_coords_measure_preserving : ∀ (N n : ℕ) (h : N ≤ n), MeasurePreserving (firstCoords h) (gaussProb n) (gaussProb N) := by
  first | exact @GlobalTheory.GaussMarginal.measurePreserving_firstCoords_gaussProb | exact GlobalTheory.GaussMarginal.measurePreserving_firstCoords_gaussProb | (intros; apply GlobalTheory.GaussMarginal.measurePreserving_firstCoords_gaussProb <;> assumption)
end

section
section
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop

noncomputable section

namespace GlobalTheory.SphereMeanNull

theorem exists_blockSphere_eval_ne_zero {B n : ℕ} (hn : 0 < n) {a : Fin B → ℕ}
    {g : MvPolynomial (Fin B × Fin n) ℂ} (hg0 : g ≠ 0) (hg : IsMultiHomogeneous a g) :
    ∃ u : BlockSphere B n, eval (blockPoint u) g ≠ 0 := by
  obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp hg0
  obtain ⟨z, hz1, hz⟩ := exists_torus_coeff_le g s
  set r : ℝ := (Real.sqrt n)⁻¹ with hrdef
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hnR)
  have hr2 : r ^ 2 * n = 1 := by
    rw [hrdef, inv_pow, Real.sq_sqrt hnR.le, inv_mul_cancel₀ hnR.ne']
  let u : BlockSphere B n := fun b => ⟨WithLp.toLp 2 (fun j => (r : ℂ) * z (b, j)), by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, hz1, mul_one]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm, hr2,
      Real.sqrt_one]⟩
  have hbp : blockPoint u = fun p => (r : ℂ) * z p := rfl
  have heval : eval (blockPoint u) g = (r : ℂ) ^ (∑ b, a b) * eval z g := by
    rw [hbp]; exact eval_mul_of_isMultiHomogeneous hg _ z
  have hne : eval z g ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (norm_pos_iff.mpr hs) hz)
  exact ⟨u, by rw [heval]; exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hr.ne')) hne⟩

theorem blockSphereProb_zeroSet_eq_zero : ∀ (B n : ℕ) (a : Fin B → ℕ)
    (g : MvPolynomial (Fin B × Fin n) ℂ), 0 < n → g ≠ 0 → IsMultiHomogeneous a g →
    blockSphereProb B n {z | eval (blockPoint z) g = 0} = 0 := by
  intro B n a g hn hg0 hg
  obtain ⟨u, hu⟩ := exists_blockSphere_eval_ne_zero hn hg0 hg
  exact null_of_logBound hn ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable
    (blockSphere_logMean_bound ReciprocityTheory.MultiplicativeHeights.Closed.sj ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable hn B)
    a g u hg hu

end GlobalTheory.SphereMeanNull
end
end

open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockSphereProb_zeroSet_eq_zero_of_ne_zero : ∀ (B n : ℕ) (a : Fin B → ℕ) (g : MvPolynomial (Fin B × Fin n) ℂ), 0 < n → g ≠ 0 → IsMultiHomogeneous a g → blockSphereProb B n {z | eval (blockPoint z) g = 0} = 0 := by
  atlas_forward_decl GlobalTheory.SphereMeanNull.blockSphereProb_zeroSet_eq_zero
end

section
noncomputable section

namespace GlobalTheory.SphereMeanDrop

open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights

theorem isProbabilityMeasure_gaussProb {n : ℕ} (hn : 0 < n) : IsProbabilityMeasure (gaussProb n) := by
  have hp := GlobalTheory.T.measurePreserving_polar_gaussianProbabilityComplexSpace n hn
  haveI := (GlobalTheory.T.gaussianRadialLawProbability_log_integrable_mean n hn).1
  haveI : IsProbabilityMeasure (sphereProb n) := isProbabilityMeasure_sphereProb hn
  rw [← hp.map_eq]
  exact Measure.isProbabilityMeasure_map hp.measurable.aemeasurable

theorem eval_blockScale {B n : ℕ} (a : Fin B → ℕ) (g : MvPolynomial (Fin B × Fin n) ℂ)
    (hm : IsMultiHomogeneous a g) (r : Fin B → ℂ) (x : Fin B × Fin n → ℂ) :
    eval (fun p => r p.1 * x p) g = (∏ b, r b ^ a b) * eval x g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [eval_monomial, eval_monomial]
  have h1 : (s.prod fun p e => (r p.1 * x p) ^ e) =
      (s.prod fun p e => r p.1 ^ e) * s.prod fun p e => x p ^ e := by
    rw [← Finsupp.prod_mul]
    congr 1
    funext p e
    rw [mul_pow]
  have h2 : (s.prod fun p e => r p.1 ^ e) = ∏ b, r b ^ a b := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun b _ => ?_
    show ∏ y, r b ^ s (b, y) = _
    rw [Finset.prod_pow_eq_pow_sum, hm s hs b]
  rw [h1, h2]
  ring

theorem linSubst_incl {B N n : ℕ} (h : N ≤ n) (f : MvPolynomial (Fin B × Fin N) ℂ) :
    GlobalTheory.ChowHt.linSubst (Matrix.of fun (j : Fin N) (k : Fin n) =>
                 if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) f =
      rename (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2)) f := by
  unfold GlobalTheory.ChowHt.linSubst
  have hfun : (fun p : Fin B × Fin N => ∑ k : Fin n, C ((Matrix.of fun (j : Fin N) (k : Fin n) =>
      if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) p.2 k) * X (p.1, k)) =
      fun p => X (p.1, Fin.castLE h p.2) := by
    funext p
    rw [Fintype.sum_eq_single (Fin.castLE h p.2)]
    · simp
    · intro k hk
      have hne : (p.2 : ℕ) ≠ (k : ℕ) := fun he => hk (Fin.ext (by rw [Fin.coe_castLE]; exact he.symm))
      simp [Matrix.of_apply, hne]
  rw [hfun]
  have hal : (aeval fun p : Fin B × Fin N => (X (p.1, Fin.castLE h p.2) : MvPolynomial (Fin B × Fin n) ℂ)) =
      rename (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2)) :=
    MvPolynomial.algHom_ext fun p => by simp
  rw [hal]

theorem isMultiHomogeneous_rename_castLE {B N n : ℕ} (h : N ≤ n) (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin N) ℂ) (hm : IsMultiHomogeneous a f) :
    IsMultiHomogeneous a (rename (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2)) f) := by
  have he : Function.Injective (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2)) := by
    intro p q hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (Fin.castLE_injective h hpq.2)
  intro s hs b
  rw [support_rename_of_injective he, Finset.mem_image] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  rw [← hm t ht b]
  let emb : Fin N ↪ Fin n := ⟨Fin.castLE h, Fin.castLE_injective h⟩
  have hsub : (Finset.univ.map emb) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_subset hsub ?_]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Finsupp.mapDomain_apply he t (b, j)
  · intro j _ hj
    apply Finsupp.mapDomain_notin_range
    rintro ⟨q, hq⟩
    apply hj
    simp only [Prod.mk.injEq] at hq
    rw [Finset.mem_map]
    exact ⟨q.2, Finset.mem_univ _, hq.2⟩

theorem gauss_blockMean {B n : ℕ} (hn : 0 < n) (δ : ℕ) (g : MvPolynomial (Fin B × Fin n) ℂ)
    (hg : g ≠ 0) (hm : IsMultiHomogeneous (fun _ => δ) g) :
    Integrable (fun x : Fin B → EuclideanSpace ℂ (Fin n) =>
        Real.log ‖eval (fun p => WithLp.ofLp (x p.1) p.2) g‖) (Measure.pi fun _ => gaussProb n) ∧
    ∫ x, Real.log ‖eval (fun p => WithLp.ofLp (x p.1) p.2) g‖ ∂(Measure.pi fun _ => gaussProb n) =
      blockSphereMean B n g + (B : ℝ) * δ * (radK (2 * n - 1) / radJ (2 * n - 1)) := by
  obtain ⟨hρ, hlogi, hlog⟩ := GlobalTheory.T.gaussianRadialLawProbability_log_integrable_mean n hn
  haveI := hρ
  haveI : IsProbabilityMeasure (sphereProb n) := isProbabilityMeasure_sphereProb hn
  haveI : IsProbabilityMeasure (gaussProb n) := isProbabilityMeasure_gaussProb hn
  have hΦm : Measurable fun x : Fin B → EuclideanSpace ℂ (Fin n) =>
      Real.log ‖eval (fun p => WithLp.ofLp (x p.1) p.2) g‖ :=
    Real.measurable_log.comp (Continuous.measurable
      (continuous_norm.comp ((continuous_eval g).comp (by fun_prop))))

  have hpol : MeasurePreserving
      (fun q : (Fin B → UnitSphereC n) × (Fin B → Ioi (0:ℝ)) =>
        fun b => ((q.2 b : ℝ)) • ((q.1 b : EuclideanSpace ℂ (Fin n))))
      ((Measure.pi fun _ : Fin B => sphereProb n).prod (Measure.pi fun _ : Fin B => radProb n))
      (Measure.pi fun _ : Fin B => gaussProb n) := by
    have h1 := measurePreserving_pi (fun _ : Fin B => (sphereProb n).prod (radProb n))
      (fun _ => gaussProb n) (fun _ => GlobalTheory.T.measurePreserving_polar_gaussianProbabilityComplexSpace n hn)
    have h2 := MeasurePreserving.symm _ (measurePreserving_arrowProdEquivProdArrow (UnitSphereC n)
      (Ioi (0:ℝ)) (Fin B) (fun _ => sphereProb n) (fun _ => radProb n))
    exact h1.comp h2

  have hpt : ∀ q : (Fin B → UnitSphereC n) × (Fin B → Ioi (0:ℝ)), eval (blockPoint q.1) g ≠ 0 →
      Real.log ‖eval (fun p => WithLp.ofLp (((q.2 p.1 : ℝ)) • ((q.1 p.1 : EuclideanSpace ℂ (Fin n)))) p.2) g‖ =
        Real.log ‖eval (blockPoint q.1) g‖ + ∑ b, (δ : ℝ) * Real.log (q.2 b : ℝ) := by
    intro q hq
    have hr : ∀ b, (0:ℝ) < q.2 b := fun b => (q.2 b).2
    have hfun : (fun p : Fin B × Fin n =>
        WithLp.ofLp (((q.2 p.1 : ℝ)) • ((q.1 p.1 : EuclideanSpace ℂ (Fin n)))) p.2) =
        fun p => ((q.2 p.1 : ℝ) : ℂ) * blockPoint q.1 p := by
      funext p
      simp [blockPoint, spherePoint, Complex.real_smul]
    have hprod : ‖∏ b, (((q.2 b : ℝ) : ℂ)) ^ δ‖ = ∏ b, ((q.2 b : ℝ)) ^ δ := by
      rw [norm_prod]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr b)]
    have hs := eval_blockScale (fun _ => δ) g hm (fun b => ((q.2 b : ℝ) : ℂ)) (blockPoint q.1)
    rw [hfun, hs, norm_mul, hprod,
      Real.log_mul (Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hr b).ne')
        (norm_ne_zero_iff.2 hq),
      Real.log_prod (fun b _ => pow_ne_zero _ (hr b).ne')]
    simp only [Real.log_pow]
    ring
  have hnull := GlobalTheory.T.blockSphereProb_zeroSet_eq_zero_of_ne_zero B n _ g hn hg hm
  have hae : ∀ᵐ q ∂((Measure.pi fun _ : Fin B => sphereProb n).prod (Measure.pi fun _ : Fin B => radProb n)),
      Real.log ‖eval (fun p => WithLp.ofLp (((q.2 p.1 : ℝ)) • ((q.1 p.1 : EuclideanSpace ℂ (Fin n)))) p.2) g‖ =
        Real.log ‖eval (blockPoint q.1) g‖ + ∑ b, (δ : ℝ) * Real.log (q.2 b : ℝ) := by
    have h0 : ((Measure.pi fun _ : Fin B => sphereProb n).prod (Measure.pi fun _ : Fin B => radProb n))
        {q | eval (blockPoint q.1) g = 0} = 0 := by
      have hs : {q : (Fin B → UnitSphereC n) × (Fin B → Ioi (0:ℝ)) | eval (blockPoint q.1) g = 0} =
          {z | eval (blockPoint z) g = 0} ×ˢ univ := by
        ext q; simp
      rw [hs, Measure.prod_prod]
      have : (Measure.pi fun _ : Fin B => sphereProb n) {z | eval (blockPoint z) g = 0} = 0 := hnull
      rw [this, zero_mul]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with q hq using hpt q hq

  have hA : Integrable (fun z : Fin B → UnitSphereC n => Real.log ‖eval (blockPoint z) g‖)
      (Measure.pi fun _ : Fin B => sphereProb n) :=
    ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable B n _ g hg hm
  have hRi : ∀ b : Fin B, Integrable (fun r : Fin B → Ioi (0:ℝ) => Real.log (r b : ℝ))
      (Measure.pi fun _ => radProb n) := by
    intro b
    have he := measurePreserving_eval (fun _ : Fin B => radProb n) b
    exact (he.integrable_comp hlogi.aestronglyMeasurable).2 hlogi
  have hRint : ∀ b : Fin B, ∫ r, Real.log ((r : Fin B → Ioi (0:ℝ)) b : ℝ)
      ∂(Measure.pi fun _ => radProb n) = radK (2 * n - 1) / radJ (2 * n - 1) := by
    intro b
    have he := measurePreserving_eval (fun _ : Fin B => radProb n) b
    have hm' : AEStronglyMeasurable (fun r : Ioi (0:ℝ) => Real.log (r : ℝ))
        (Measure.map (Function.eval b) (Measure.pi fun _ : Fin B => radProb n)) :=
      (Real.measurable_log.comp measurable_subtype_coe).aestronglyMeasurable
    have := integral_map he.measurable.aemeasurable hm'
    rw [he.map_eq] at this
    rw [← hlog, this]
  have hAi : Integrable (fun q : (Fin B → UnitSphereC n) × (Fin B → Ioi (0:ℝ)) =>
      Real.log ‖eval (blockPoint q.1) g‖)
      ((Measure.pi fun _ : Fin B => sphereProb n).prod (Measure.pi fun _ : Fin B => radProb n)) :=
    hA.comp_fst _
  have hRsum : Integrable (fun r : Fin B → Ioi (0:ℝ) => ∑ b, (δ : ℝ) * Real.log (r b : ℝ))
      (Measure.pi fun _ => radProb n) :=
    integrable_finset_sum _ fun b _ => (hRi b).const_mul _
  have hRi' : Integrable (fun q : (Fin B → UnitSphereC n) × (Fin B → Ioi (0:ℝ)) =>
      ∑ b, (δ : ℝ) * Real.log (q.2 b : ℝ))
      ((Measure.pi fun _ : Fin B => sphereProb n).prod (Measure.pi fun _ : Fin B => radProb n)) :=
    hRsum.comp_snd _
  have hcomp := (hAi.add hRi').congr (hae.mono fun q h => h.symm)
  refine ⟨(hpol.integrable_comp hΦm.aestronglyMeasurable).1 hcomp, ?_⟩
  rw [← hpol.map_eq, integral_map hpol.measurable.aemeasurable hΦm.aestronglyMeasurable,
    integral_congr_ae hae, integral_add hAi hRi',
    integral_fun_fst (fun z : Fin B → UnitSphereC n => Real.log ‖eval (blockPoint z) g‖),
    integral_fun_snd (fun r : Fin B → Ioi (0:ℝ) => ∑ b, (δ : ℝ) * Real.log (r b : ℝ)),
    integral_finset_sum _ fun b _ => (hRi b).const_mul _]
  simp only [probReal_univ, one_smul, integral_const_mul, hRint, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [blockSphereMean, blockSphereProb]
  ring

theorem radRatio_sub {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    radK (2 * N - 1) / radJ (2 * N - 1) - radK (2 * n - 1) / radJ (2 * n - 1) =
      ((harmonic (N - 1) : ℝ) - (harmonic (n - 1) : ℝ)) / 2 := by
  obtain ⟨a, rfl⟩ : ∃ a, N = a + 1 := ⟨N - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = b + 1 := ⟨n - 1, by omega⟩
  have e1 : 2 * (a + 1) - 1 = 2 * a + 1 := by omega
  have e2 : 2 * (b + 1) - 1 = 2 * b + 1 := by omega
  rw [e1, e2, radRatio_odd, radRatio_odd]
  simp only [Nat.add_sub_cancel]
  ring

theorem blockSphereMean_incl (B N n δ : ℕ) (f : MvPolynomial (Fin B × Fin N) ℂ) (hN : 0 < N)
    (hNn : N ≤ n) (hf : f ≠ 0) (hm : IsMultiHomogeneous (fun _ => δ) f) :
    blockSphereMean B n (GlobalTheory.ChowHt.linSubst (Matrix.of fun (j : Fin N) (k : Fin n) =>
        if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) f) =
      blockSphereMean B N f + (B : ℝ) * δ * ((harmonic (N - 1) : ℝ) - (harmonic (n - 1) : ℝ)) / 2 := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  rw [linSubst_incl hNn]
  set e : Fin B × Fin N → Fin B × Fin n := fun p => (p.1, Fin.castLE hNn p.2) with he
  have heinj : Function.Injective e := by
    intro p q hpq
    simp only [he, Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (Fin.castLE_injective hNn hpq.2)
  set g := rename e f with hgdef
  have hg : g ≠ 0 := fun h0 => hf (rename_injective e heinj (by rw [← hgdef, h0, map_zero]))
  have hgm : IsMultiHomogeneous (fun _ => δ) g := isMultiHomogeneous_rename_castLE hNn _ f hm
  have hIn := (gauss_blockMean hn δ g hg hgm).2
  have hIN := (gauss_blockMean hN δ f hf hm).2
  haveI : IsProbabilityMeasure (gaussProb N) := isProbabilityMeasure_gaussProb hN
  have hproj : MeasurePreserving (fun (x : Fin B → EuclideanSpace ℂ (Fin n)) b => firstCoords hNn (x b))
      (Measure.pi fun _ => gaussProb n) (Measure.pi fun _ => gaussProb N) :=
    measurePreserving_pi _ _ fun _ => GlobalTheory.T.gaussian_first_coords_measure_preserving N n hNn
  have hev : ∀ x : Fin B → EuclideanSpace ℂ (Fin n),
      eval (fun p => WithLp.ofLp (x p.1) p.2) g =
        eval (fun p => WithLp.ofLp (firstCoords hNn (x p.1)) p.2) f := by
    intro x
    rw [hgdef, eval_rename]
    rfl
  have hmeas : Measurable fun y : Fin B → EuclideanSpace ℂ (Fin N) =>
      Real.log ‖eval (fun p => WithLp.ofLp (y p.1) p.2) f‖ := by
    refine Real.measurable_log.comp (Continuous.measurable ?_)
    exact continuous_norm.comp ((continuous_eval f).comp (by fun_prop))
  have hchange : ∫ x, Real.log ‖eval (fun p => WithLp.ofLp (x p.1) p.2) g‖
        ∂(Measure.pi fun _ => gaussProb n) =
      ∫ y, Real.log ‖eval (fun p => WithLp.ofLp (y p.1) p.2) f‖
        ∂(Measure.pi fun _ => gaussProb N) := by
    simp_rw [hev]
    rw [← hproj.map_eq, integral_map hproj.measurable.aemeasurable hmeas.aestronglyMeasurable]
  rw [hchange, hIN] at hIn
  have hr := radRatio_sub hN hn
  linear_combination hIn.symm + (B : ℝ) * δ * hr

end GlobalTheory.SphereMeanDrop
end
end
