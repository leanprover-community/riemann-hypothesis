import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ContinuousConstantTerm

section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.constantTerm_convolution_arch :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (μ : Measure (archGroup K n)) [μ.IsHaarMeasure] (φ ψ : AdelicGLn.AdelicGL K n → ℂ) (D : archGroup K n → ℂ), Continuous φ → Continuous D → HasCompactSupport D → (∀ g, ψ g = ∫ y, φ (g * infEmb K n y) * D y ∂μ) → ∀ g, constantTerm r ψ g = ∫ y, constantTerm r φ (g * infEmb K n y) * D y ∂μ := by
  intro K _ _ n r _ _ μ _ φ ψ D hφ hD hDc hψ g
  obtain ⟨C, hC, hFC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  let f : (UPos n r → AdeleRing (𝓞 K) K) × archGroup K n → ℂ :=
    fun p => φ (unipGL p.1 * g * infEmb K n p.2) * D p.2
  have hfc : Continuous f := by
    refine Continuous.mul (hφ.comp ?_) (hD.comp continuous_snd)
    exact ((continuous_unipGL.comp continuous_fst).mul continuous_const).mul
      (continuous_infEmb.comp continuous_snd)
  have hint : Integrable f (((unipMeasure K n r).restrict (unipFundamentalDomain K n r)).prod μ) := by
    have h1 : IntegrableOn f (C ×ˢ tsupport D) ((unipMeasure K n r).prod μ) :=
      hfc.continuousOn.integrableOn_compact (hC.prod hDc)
    have h2 : IntegrableOn f (unipFundamentalDomain K n r ×ˢ Set.univ) ((unipMeasure K n r).prod μ) := by
      refine h1.of_forall_diff_eq_zero (measurableSet_unipFundamentalDomain.prod MeasurableSet.univ) ?_
      rintro ⟨X, y⟩ ⟨⟨hX, -⟩, hn⟩
      have hy : y ∉ tsupport D := fun hy => hn ⟨hFC hX, hy⟩
      show φ (unipGL X * g * infEmb K n y) * D y = 0
      rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    have h3 : ((unipMeasure K n r).restrict (unipFundamentalDomain K n r)).prod μ
        = ((unipMeasure K n r).prod μ).restrict (unipFundamentalDomain K n r ×ˢ Set.univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [h3]
    exact h2
  have key := integral_integral_swap (f := fun X y => φ (unipGL X * g * infEmb K n y) * D y) hint
  show ∫ X in unipFundamentalDomain K n r, ψ (unipGL X * g) ∂unipMeasure K n r
    = ∫ y, (∫ X in unipFundamentalDomain K n r, φ (unipGL X * (g * infEmb K n y)) ∂unipMeasure K n r) * D y ∂μ
  simp_rw [hψ]
  refine key.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ∫ X in unipFundamentalDomain K n r, φ (unipGL X * g * infEmb K n y) * D y ∂unipMeasure K n r
    = (∫ X in unipFundamentalDomain K n r, φ (unipGL X * (g * infEmb K n y)) ∂unipMeasure K n r) * D y
  rw [← integral_mul_const]
  simp_rw [mul_assoc]
end

section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.constantTerm_archSmooth :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (φ : archSmooth K n), IsAutomorphicForm φ.1 → ∃ hs : IsArchSmooth (constantTerm r φ.1), ∀ X : (isExpLieAlgebra K n).lieSubalgebra, (uAction (UniversalEnvelopingAlgebra.ι ℝ X) ⟨constantTerm r φ.1, hs⟩).1 = constantTerm r (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ).1 := by
  intro K _ _ n r φ hφ
  let μ : Measure (archGroup K n) := Measure.haar
  obtain ⟨d, b, ε, B, h1, h2, h3, h4, h5⟩ := exists_archCartanData K n
  obtain ⟨P, hPm, hPd, hP⟩ :=
    hφ.isSmoothKZ.exists_aeval_laplacian_sliceL_eq_zero b ε B h1 h2 h3 h4 h5
  obtain ⟨κ, hκs, hκc, -, hκ⟩ :=
    (isExpLieAlgebra K n).exists_kernel_eq_conv_of_aeval_laplacian μ b P hPm hPd
      (U := Set.univ) Filter.univ_mem
  have hκcont : Continuous κ :=
    IsExpLieAlgebra.IsTestFunction.continuous (isExpLieAlgebra K n) ⟨hκs, hκc⟩
  have rep : ∀ g y, archSlice φ.1 g y = ∫ z, archSlice φ.1 g (y * z) * κ z ∂μ :=
    fun g y => hκ _ (hP g) y
  have repφ : ∀ g, φ.1 g = ∫ z, φ.1 (g * infEmb K n z) * κ z ∂μ := by
    intro g
    have := rep g 1
    simpa [archSlice_apply] using this
  have hc : Continuous φ.1 := hφ.continuous
  have hct := UpperTheory.constantTerm_convolution_arch K n r μ φ.1 φ.1 κ hc hκcont hκc repφ
  have hctc := UpperTheory.continuous_constantTerm K n r φ.1 hc
  have hsliceC : ∀ g, Continuous (archSlice (constantTerm r φ.1) g) := by
    intro g
    show Continuous fun x => constantTerm r φ.1 (g * infEmb K n x)
    exact hctc.comp (continuous_const.mul continuous_infEmb)
  have repct : ∀ g y, archSlice (constantTerm r φ.1) g y
      = ∫ z, archSlice (constantTerm r φ.1) g (y * z) * κ z ∂μ := by
    intro g y
    simp only [archSlice_apply]
    rw [hct (g * infEmb K n y)]
    simp [mul_assoc, map_mul]
  have hs : IsArchSmooth (constantTerm r φ.1) := by
    intro g
    have hfun : archSlice (constantTerm r φ.1) g
        = fun y => ∫ z, archSlice (constantTerm r φ.1) g (y * z) * κ z ∂μ := funext (repct g)
    rw [hfun]
    exact (isExpLieAlgebra K n).isSmoothFun_integral_mul μ (hsliceC g) ⟨hκs, hκc⟩
  refine ⟨hs, fun X => ?_⟩
  funext g
  have hD := (isExpLieAlgebra K n).continuous_convDeriv hκs ((isExpLieAlgebra K n).ofLie X)
  have hDc := (isExpLieAlgebra K n).hasCompactSupport_convDeriv hκc ((isExpLieAlgebra K n).ofLie X)
  have repU : ∀ h, (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ).1 h
      = ∫ y, φ.1 (h * infEmb K n y)
          * (isExpLieAlgebra K n).convDeriv ((isExpLieAlgebra K n).ofLie X) κ y ∂μ := by
    intro h
    rw [uAction_ι_apply,
      IsExpLieAlgebra.rightDeriv_eq_integral_convDeriv hκs hκc (φ.2 h) (rep h)]
    simp [archSlice_apply]
  rw [uAction_ι_apply,
    IsExpLieAlgebra.rightDeriv_eq_integral_convDeriv hκs hκc (hs g) (repct g),
    UpperTheory.constantTerm_convolution_arch K n r μ φ.1 _ _ hc hD hDc repU g]
  simp [archSlice_apply]
end

section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.exists_constantTerm_linearMap_equivariant_universalEnveloping :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ), ∃ f : automorphicForms K n →ₗ[ℂ] archSmooth K n, (∀ φ, (f φ).1 = constantTerm r φ.1) ∧ ∀ u φ, f (uActionAF K n u φ) = uAction u (f φ) := by
  intro K _ _ n r
  have h := fun φ : automorphicForms K n =>
    UpperTheory.constantTerm_archSmooth K n r ⟨φ.1, automorphicForms_le_archSmooth φ.2⟩ φ.2
  choose hs hX using h
  let f : automorphicForms K n →ₗ[ℂ] archSmooth K n :=
    { toFun := fun φ => ⟨constantTerm r φ.1, hs φ⟩
      map_add' := fun φ ψ => Subtype.ext (funext fun g =>
        constantTerm_add (IsAutomorphicForm.continuous φ.2) (IsAutomorphicForm.continuous ψ.2) g)
      map_smul' := fun c φ => Subtype.ext (funext fun g => constantTerm_smul c φ.1 g) }
  refine ⟨f, fun _ => rfl, fun u => ?_⟩
  induction u using UEnv.induction with
  | halg c =>
    intro φ
    have e : uActionAF K n (algebraMap ℝ (UEnv K n) c) φ = (c : ℂ) • φ :=
      Subtype.ext (coe_uAction_algebraMap c ⟨φ.1, automorphicForms_le_archSmooth φ.2⟩)
    rw [e, map_smul]
    exact Subtype.ext (coe_uAction_algebraMap c (f φ)).symm
  | hι X => exact fun φ => Subtype.ext (hX φ X).symm
  | hmul a b ha hb =>
    intro φ
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  | hadd a b ha hb =>
    intro φ
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, ha, hb]
end
