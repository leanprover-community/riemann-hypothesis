import Development.AutomorphicArithmetic.AdelicSL2.IsOpenEmbeddingProjection
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.MeasurableSetUS
import Development.AutomorphicArithmetic.AdelicSL2.ExistsHaarRestrictRangeSl2IdeleMapEqSmulProd

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical ENNReal NNReal

private lemma eq_one_of_mul' {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  have := mul_le_mul' (le_refl a) hb
  rwa [h, mul_one] at this

private lemma mem_UU_of_pos {y : IdeleGroup ℚ} (hy : y ∈ RationalIdeles.positiveSubgroup)
    (hm : (IdeleGroup.ideleModule ℚ y : ℝ) = 1) : y ∈ UU := by
  obtain ⟨h1, h2⟩ := RationalIdeles.mem_positiveSubgroup.1 hy
  rw [IdeleGroup.ideleModule_apply, IdeleGroup.finiteModule_eq_one_of_mem h1, mul_one,
    IdeleGroup.infiniteModule, Fintype.prod_unique,
    InfinitePlace.IsReal.mult_eq_one (RationalIdeles.isReal_infinitePlace default), pow_one] at hm
  refine ⟨?_, fun v => ?_⟩
  · have hn : ‖(RationalIdeles.realPart y : ℝ)‖ = 1 := by
      rw [RationalIdeles.coe_realPart, RationalIdeles.realEquiv_apply, ← hm]
      exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).norm_map_of_map_zero
        (map_zero _) _
    rw [Real.norm_eq_abs, abs_of_pos h2, RationalIdeles.coe_realPart] at hn
    exact RationalIdeles.realEquiv.injective (hn.trans (map_one _).symm)
  · obtain ⟨ha, hb⟩ := (IdeleGroup.mem_standardOpenSubgroup ℚ).1 h1 v
    refine eq_one_of_mul' ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha)
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb) ?_
    rw [← map_mul]
    have h := congrArg (fun x : NumberField.AdeleRing (𝓞 ℚ) ℚ => x.2 v) (Units.mul_inv y)
    have h' : (y : NumberField.AdeleRing (𝓞 ℚ) ℚ).2 v *
        ((y⁻¹ : IdeleGroup ℚ) : NumberField.AdeleRing (𝓞 ℚ) ℚ).2 v = 1 := h
    exact (congrArg _ h').trans (map_one _)

theorem UpperTheory.exists_gl2Rat_smul_mem_range_adelicSL2IdeleMap :
    ∀ x : GG, ∃ γ : Ga, γ • x ∈ Set.range pm := by
  intro x
  obtain ⟨⟨q, y⟩, hq⟩ := RationalIdeles.mulMap_bijective.2
    (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x : GL (Fin 2) (A ℚ)))
  rw [RationalIdeles.mulMap_apply] at hq
  dsimp only at hq
  have hx := GroundTheory.Automorphic.Reduction.mem_normOneGL.1 x.2
  rw [← hq, map_mul, IdeleGroup.ideleModule_diagonal, one_mul] at hx
  have hy : (y : IdeleGroup ℚ) ∈ UU := mem_UU_of_pos y.2 hx
  obtain ⟨r, hr⟩ : ∃ r : GL (Fin 2) ℚ, Matrix.GeneralLinearGroup.det r = q⁻¹ := by
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, ((q⁻¹ : ℚˣ) : ℚ)] ?_, Units.ext ?_⟩
    · simp [Matrix.det_fin_two_of]
    · simp [Matrix.det_fin_two_of]
  have h : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r) =
      IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) := by
    refine Units.ext ?_
    rw [GroundTheory.Automorphic.AdelicGLn.coe_det, IdeleGroup.coe_diagonal]
    exact (RingHom.map_det (algebraMap ℚ (NumberField.AdeleRing (𝓞 ℚ) ℚ))
      (r : Matrix (Fin 2) (Fin 2) ℚ)).symm
  refine ⟨⟨⟨GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r,
    GroundTheory.Automorphic.Reduction.rationalGL_le_normOneGL ⟨r, rfl⟩⟩, ⟨r, rfl⟩⟩, ?_⟩
  rw [range_pm]
  change GroundTheory.Automorphic.AdelicGLn.det ℚ 2
    (GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r * (x : GL (Fin 2) (A ℚ))) ∈ UU
  rw [map_mul, h, hr, ← hq, map_inv, inv_mul_cancel_left]
  exact hy
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Classical ENNReal NNReal

private theorem us_pos (x : US) : ((x : (A ℚ)ˣ) : IdeleGroup ℚ) ∈ RationalIdeles.positiveSubgroup := by
  obtain ⟨h1, h2⟩ := x.2
  set t : IdeleGroup ℚ := (x : (A ℚ)ˣ) with ht
  have hinv : ∀ v : H.P ℚ, Valued.v ((((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v) * Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := by
    intro v
    rw [← map_mul]
    have h := congrArg (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => x v) (Units.inv_mul (IdeleGroup.toFinite ℚ t))
    have h' : (((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v *
        ((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := h
    rw [h', map_one]
  refine RationalIdeles.mem_positiveSubgroup.2 ⟨?_, ?_⟩
  · change IdeleGroup.toFinite ℚ t ∈ finiteIntegralUnits ℚ
    refine (mem_finiteIntegralUnits ℚ).2 fun v => ?_
    have hv : Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := h2 v
    have hi := hinv v
    rw [hv, mul_one] at hi
    exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hv.le,
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hi.le⟩
  · rw [RationalIdeles.coe_realPart]
    have h1' : (t : NumberField.AdeleRing (𝓞 ℚ) ℚ).1 = 1 := h1
    rw [h1', map_one]
    exact one_pos

theorem UpperTheory.eq_sl2Rat_mul_of_gl2Rat_smul_adelicSL2IdeleMap_eq :
    ∀ (γ : Ga) (p q : G1 ℚ × US), γ • pm p = pm q → q.2 = p.2 ∧ ∃ s : SpecialLinearGroup (Fin 2) ℚ, q.1 = ratS ℚ s * p.1 ∧ ((γ : GG) : GL (Fin 2) (A ℚ)) = gl (ratS ℚ s) := by
  intro γ p q h
  obtain ⟨r, hr⟩ := γ.2
  have h1 : GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r * (gl p.1 * dM (p.2 : (A ℚ)ˣ)) = gl q.1 * dM (q.2 : (A ℚ)ˣ) := by
    rw [hr]
    exact congrArg Subtype.val h
  have hdet : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r) =
      IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) := by
    refine Units.ext ?_
    rw [GroundTheory.Automorphic.AdelicGLn.coe_det, IdeleGroup.coe_diagonal]
    exact (RingHom.map_det (algebraMap ℚ _) (r : Matrix (Fin 2) (Fin 2) ℚ)).symm
  have h2 : IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) * (p.2 : (A ℚ)ˣ) = (q.2 : (A ℚ)ˣ) := by
    have := congrArg (GroundTheory.Automorphic.AdelicGLn.det ℚ 2) h1
    rwa [map_mul, det_el, det_el, hdet] at this
  have h3 : IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) = ((q.2 * p.2⁻¹ : US) : (A ℚ)ˣ) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, ← h2, mul_inv_cancel_right]
  have h4 : IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) = 1 := by
    have hm : IdeleGroup.diagonal ℚ (Matrix.GeneralLinearGroup.det r) ∈
        RationalIdeles.positiveSubgroup ⊓ (IdeleGroup.diagonal ℚ).range :=
      ⟨h3 ▸ us_pos _, ⟨_, rfl⟩⟩
    rw [RationalIdeles.positiveSubgroup_inf_diagonal_range] at hm
    exact hm
  have h5 : (q.2 : (A ℚ)ˣ) = (p.2 : (A ℚ)ˣ) := by rw [← h2, h4, one_mul]
  have h6 : (r : Matrix (Fin 2) (Fin 2) ℚ).det = 1 := by
    have := congrArg Units.val h4
    rw [IdeleGroup.coe_diagonal, Units.val_one] at this
    apply NumberField.AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ
    rw [map_one]
    exact this
  let s : SpecialLinearGroup (Fin 2) ℚ := ⟨r.val, h6⟩
  have h7 : GroundTheory.Automorphic.AdelicGLn.diagonal ℚ 2 r = gl (ratS ℚ s) := by
    apply Units.ext
    ext i j
    rfl
  refine ⟨Subtype.ext h5, s, ?_, hr.symm.trans h7⟩
  rw [h5, h7, ← mul_assoc] at h1
  have h8 : gl (ratS ℚ s) * gl p.1 = gl q.1 := mul_right_cancel h1
  apply Subtype.ext
  have := congrArg Units.val h8
  exact this.symm
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
open scoped Pointwise Classical ENNReal NNReal

theorem UpperTheory.isFundamentalDomain_image_sl2Domain_prod_ideles :
    ∀ (M : Meas ℚ) (U : UMeas) (μ : Measure GG) [μ.IsHaarMeasure], IsFundamentalDomain Ga (pm '' (M.D ×ˢ Set.univ)) μ := by
  intro M U μ _
  haveI := M.haar
  have emb : MeasurableEmbedding pm := UpperTheory.isOpenEmbedding_projection.measurableEmbedding
  obtain ⟨c, hc⟩ := UpperTheory.exists_haar_restrict_range_sl2IdeleMap_eq_smul_prod M U μ
  have null : ∀ N : Set (G1 ℚ), M.μ N = 0 → μ (pm '' (N ×ˢ Set.univ)) = 0 := fun N hN => by
    rw [← Measure.restrict_eq_self μ (Set.image_subset_range _ _), hc, Measure.smul_apply, emb.map_apply,
      Set.preimage_image_eq _ emb.injective, Measure.prod_prod, hN, zero_mul, smul_zero]
  have lift : ∀ s : SpecialLinearGroup (Fin 2) ℚ, ∃ γ : Ga, ∀ p : G1 ℚ × US, γ • pm p = pm (ratS ℚ s * p.1, p.2) := fun s => by
    refine ⟨⟨pm (ratS ℚ s, 1), ?_⟩, fun p => Subtype.ext ?_⟩
    · refine Subgroup.mem_subgroupOf.2 ⟨SpecialLinearGroup.toGL s, Units.ext ?_⟩
      change _ = (ratS ℚ s).1 * !![1, 0; 0, (1 : A ℚ)]
      rw [← Matrix.one_fin_two, mul_one]
      rfl
    · change gl (ratS ℚ s) * dM 1 * (gl p.1 * dM p.2.1) = gl (ratS ℚ s * p.1) * dM p.2.1
      have : dM (1 : (A ℚ)ˣ) = 1 := Units.ext Matrix.one_fin_two.symm
      rw [this, mul_one, ← mul_assoc, ← map_mul]
  refine ⟨(emb.measurableSet_image.2 (M.meas.prod MeasurableSet.univ)).nullMeasurableSet, ?_, fun γ γ' hne => ?_⟩
  · have h0 := null _ (ae_iff.1 M.fund.ae_covers)
    rw [ae_iff]
    refine measure_mono_null (t := ⋃ γ : Ga, (fun x : GG => (γ : GG) * x) ⁻¹'
      (pm '' ({g | ¬ ∃ s : Gam ℚ, s • g ∈ M.D} ×ˢ Set.univ))) (fun x hx => ?_)
      (measure_iUnion_null fun γ => by rw [measure_preimage_mul]; exact h0)
    obtain ⟨γ, p, hp⟩ := UpperTheory.exists_gl2Rat_smul_mem_range_adelicSL2IdeleMap x
    refine Set.mem_iUnion.2 ⟨γ, p, ⟨?_, trivial⟩, hp⟩
    rintro ⟨⟨_, s, rfl⟩, hs⟩
    obtain ⟨δ, hδ⟩ := lift s
    exact hx ⟨δ * γ, (ratS ℚ s * p.1, p.2), ⟨hs, trivial⟩, by rw [mul_smul, ← hp, hδ]⟩
  · haveI : Countable (Matrix (Fin 2) (Fin 2) ℚ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
    haveI : Countable (SpecialLinearGroup (Fin 2) ℚ) := Subtype.countable
    have hN : M.μ (⋃ s : {s : SpecialLinearGroup (Fin 2) ℚ // ratS ℚ s ≠ 1},
        ((⟨ratS ℚ s.1, s.1, rfl⟩ : Gam ℚ) • M.D ∩ (1 : Gam ℚ) • M.D)) = 0 :=
      measure_iUnion_null fun s => M.fund.aedisjoint fun h => s.2 (congrArg Subtype.val h)
    refine measure_mono_null (t := (fun x : GG => ((γ'⁻¹ : Ga) : GG) * x) ⁻¹' (pm '' (_ ×ˢ Set.univ))) ?_
      (by rw [measure_preimage_mul]; exact null _ hN)
    rintro x ⟨⟨_, ⟨p, hp, rfl⟩, e⟩, ⟨_, ⟨q, hq, rfl⟩, e'⟩⟩
    have e1 : (γ'⁻¹ * γ) • pm p = pm q := by
      rw [mul_smul, inv_smul_eq_iff]
      exact e.trans e'.symm
    obtain ⟨-, s, h1, h2⟩ := UpperTheory.eq_sl2Rat_mul_of_gl2Rat_smul_adelicSL2IdeleMap_eq _ p q e1
    have hs : ratS ℚ s ≠ 1 := fun h => hne (by
      rw [h] at h2
      exact (inv_mul_eq_one.1 (Subtype.ext (Subtype.ext (h2.trans (Units.ext rfl))))).symm)
    refine ⟨q, ⟨Set.mem_iUnion.2 ⟨⟨s, hs⟩, ⟨p.1, hp.1, h1.symm⟩, by rw [one_smul]; exact hq.1⟩, trivial⟩, ?_⟩
    change pm q = γ'⁻¹ • x
    rw [eq_inv_smul_iff]
    exact e'
end
