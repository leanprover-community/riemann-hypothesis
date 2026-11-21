import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex

section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_exp_smul_sub_le_norm_derivOp :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E) (v : E) (X : 𝔤), (∀ g w, ‖π g w‖ = ‖w‖) → h.IsSmoothVector π v → ‖π (h.expG X) v - v‖ ≤ ‖h.derivOp π X v‖ := by
  intro 𝔸 _ _ _ _ G 𝔤 h E _ _ π v X hπ hv
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => π (h.expG (s • X)) v)
      (π (h.expG (t • X)) (h.derivOp π X v)) t := by
    intro t
    have h2 := ((π (h.expG (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (h.hasDerivAt_derivOp π hv X)
    have h3 : HasDerivAt (fun s : ℝ => π (h.expG ((t + s) • X)) v)
        (π (h.expG (t • X)) (h.derivOp π X v)) (t - t) := by
      rw [sub_self]
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
      rw [h.expG_add_smul, BanachRep.map_mul_apply]
    have h4 := h3.comp_sub_const t t
    simpa only [add_sub_cancel] using h4
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => π (h.expG (s • X)) v)
    (f' := fun t : ℝ => π (h.expG (t • X)) (h.derivOp π X v)) (C := ‖h.derivOp π X v‖)
    (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => (hπ _ _).le)
  simpa using hm
end

section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_nhds_displacement_le_half_of_derivOp_bound :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ h.lieSubalgebra) (C : ℝ), ∃ N ∈ 𝓝 (1 : G), ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E) (v : E), (∀ g w, ‖π g w‖ = ‖w‖) → h.IsSmoothVector π v → (∀ i, ‖h.derivOp π (h.ofLie (b i)) v‖ ≤ C * ‖v‖) → ∀ a ∈ N, ‖π a v - v‖ ≤ 1 / 2 * ‖v‖ := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b C
  let T : 𝔤 →ₗ[ℝ] h.lieSubalgebra :=
    { toFun := h.toLie, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let S : h.lieSubalgebra →ₗ[ℝ] 𝔤 :=
    { toFun := h.ofLie, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hST : ∀ X : 𝔤, S (T X) = X := fun _ => rfl
  let f : 𝔤 → ℝ := fun X => (∑ i, |b.repr (h.toLie X) i|) * |C|
  have hf : Continuous f := by
    refine Continuous.mul (continuous_finset_sum _ fun i _ => ?_) continuous_const
    exact (LinearMap.continuous_of_finiteDimensional ((b.coord i) ∘ₗ T)).abs
  have hf0 : f 0 = 0 := by
    have : h.toLie 0 = 0 := rfl
    simp [f, this]
  have hO : {X : 𝔤 | f X < 1 / 2} ∈ 𝓝 (0 : 𝔤) :=
    (isOpen_lt hf continuous_const).mem_nhds (by simp [hf0])
  have h0 : (0 : 𝔤) ∈ (h.chart 1).symm.source := h.zero_mem_nhd
  have hexp0 : h.expG 0 = 1 := by
    apply Subtype.ext; apply Units.ext
    simp [IsExpLieAlgebra.coe_expG]
  refine ⟨h.expG '' {X : 𝔤 | f X < 1 / 2}, ?_, ?_⟩
  · have h1 := (h.chart 1).symm.image_mem_nhds h0 hO
    have e1 : (h.chart 1).symm 0 = 1 := by
      show 1 * h.expG 0 = 1
      rw [hexp0, one_mul]
    rw [e1] at h1
    refine Filter.mem_of_superset h1 ?_
    rintro _ ⟨X, hX, rfl⟩
    refine ⟨X, hX, ?_⟩
    show h.expG X = 1 * h.expG X
    rw [one_mul]
  · rintro E _ _ π v hπ hv hb _ ⟨X, hX, rfl⟩
    refine (UpperTheory.norm_exp_smul_sub_le_norm_derivOp 𝔸 G 𝔤 h E π v X hπ hv).trans ?_
    have hsum : X = ∑ i, b.repr (h.toLie X) i • h.ofLie (b i) := by
      conv_lhs => rw [← hST X]
      show S (h.toLie X) = _
      conv_lhs => rw [← b.sum_repr (h.toLie X)]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul S _ _
    have hD : h.derivOp π X v =
        ∑ i, b.repr (h.toLie X) i • h.derivOp π (h.ofLie (b i)) v := by
      show fderiv ℝ (h.expOrbit π v) 0 X = ∑ i, b.repr (h.toLie X) i •
        fderiv ℝ (h.expOrbit π v) 0 (h.ofLie (b i))
      conv_lhs => rw [hsum]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
    have hbound : ‖h.derivOp π X v‖ ≤ f X * ‖v‖ := by
      rw [hD]
      refine (norm_sum_le _ _).trans ?_
      simp only [f, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, Real.norm_eq_abs, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact (hb i).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg v))
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_of_lt hX) (norm_nonneg v))
end

section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_nhds_one_normOneGL_factorization :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (N : Set (archGroup K n)) (U : Subgroup (AdelicGLn.integralFiniteGL K n)), N ∈ 𝓝 (1 : archGroup K n) → IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) → ∃ N' ∈ 𝓝 (1 : normOneGL K n), ∀ g ∈ N', ∃ a ∈ N, ∃ u ∈ U, g = archP K n a * retractOne (finEmb K n (u : AdelicGLn.integralFiniteGL K n)) := by
  intro K _ _ n N U hN hU
  have hU' : IsOpen (Subtype.val '' (U : Set (AdelicGLn.integralFiniteGL K n))) :=
    (AdelicGLn.isOpen_integralFiniteGL K n).isOpenMap_subtype_val _ hU
  have hp : Continuous fun g : normOneGL K n => AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n) :=
    (AdelicGLn.prodEquiv K n).continuous.comp continuous_subtype_val
  have ha : Continuous fun g : normOneGL K n =>
      archEquiv K n (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).1 :=
    (archEquiv K n).continuous.comp hp.fst
  have hf : Continuous fun g : normOneGL K n =>
      (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).2 := hp.snd
  refine ⟨(fun g : normOneGL K n =>
      archEquiv K n (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).1) ⁻¹' N ∩
    (fun g : normOneGL K n => (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).2) ⁻¹'
      (Subtype.val '' (U : Set (AdelicGLn.integralFiniteGL K n))), Filter.inter_mem ?_ ?_, ?_⟩
  · refine ha.continuousAt.preimage_mem_nhds ?_
    simpa only [OneMemClass.coe_one, map_one, Prod.fst_one] using hN
  · refine (hU'.preimage hf).mem_nhds ⟨1, U.one_mem, ?_⟩
    simp only [OneMemClass.coe_one, map_one, Prod.snd_one]
  · rintro g ⟨hg, u, hu, e⟩
    refine ⟨_, hg, u, hu, ?_⟩
    have e' : (u : AdelicGLn.FiniteAdelicGL K n) = (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).2 := e
    rw [e']
    calc g = retractOne (g : AdelicGLn.AdelicGL K n) := (retractOne_coe g).symm
      _ = retractOne (infEmb K n (archEquiv K n (AdelicGLn.prodEquiv K n g).1) *
            finEmb K n (AdelicGLn.prodEquiv K n g).2) := by rw [infEmb_mul_finEmb]
      _ = _ := by rw [retractOne_mul, retract_infEmb]
end

section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_approximate_identity_integrated :
    ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [OpensMeasurableSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] (N : Set G), N ∈ 𝓝 (1 : G) → ∃ f : CompactlySupportedContinuousMap G ℂ, ∀ (v : H) (r : ℝ), (∀ g ∈ N, ‖π g v - v‖ ≤ r) → ‖π.integrated μ (UnitaryRep.ccToL1 μ f) v - v‖ ≤ r := by
  intro G H _ _ _ _ _ _ _ _ _ _ π μ _ _ N hN
  obtain ⟨U, hUsub, hUo, h1U⟩ := mem_nhds_iff.1 hN
  obtain ⟨h, h1, h0, hcs, hrange⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : G))) hUo.isClosed_compl
    (Set.disjoint_singleton_left.2 fun h => h h1U)
  have hnn : ∀ g, 0 ≤ h g := fun g => (hrange g).1
  set c : ℝ := ∫ g, h g ∂μ with hc
  have hcpos : 0 < c := h.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hnn
    (by rw [h1 (Set.mem_singleton 1)]; exact one_ne_zero)
  let k : G → ℝ := fun g => c⁻¹ * h g
  have hkc : Continuous k := continuous_const.mul h.continuous
  have hkcs : HasCompactSupport k := by
    have : k = (fun _ => c⁻¹) * (h : G → ℝ) := rfl
    rw [this]
    exact hcs.mul_left
  have hknn : ∀ g, 0 ≤ k g := fun g => mul_nonneg (inv_nonneg.2 hcpos.le) (hnn g)
  have hkint : Integrable k μ := hkc.integrable_of_hasCompactSupport hkcs
  have hk1 : ∫ g, k g ∂μ = 1 := by
    simp only [k]
    rw [integral_const_mul, ← hc, inv_mul_cancel₀ hcpos.ne']
  let f : CompactlySupportedContinuousMap G ℂ :=
    ⟨⟨fun g => (k g : ℂ), by fun_prop⟩, hkcs.comp_left Complex.ofReal_zero⟩
  have hfg : ∀ g, f g = (k g : ℂ) := fun _ => rfl
  refine ⟨f, fun v r hr => ?_⟩
  have hint1 : Integrable (fun g => f g • π g v) μ :=
    (f.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport
      f.hasCompactSupport.smul_right
  have hint2 : Integrable (fun g => f g • v) μ :=
    (f.continuous.smul continuous_const).integrable_of_hasCompactSupport
      f.hasCompactSupport.smul_right
  have hv : ∫ g, f g • v ∂μ = v := by
    rw [integral_smul_const]
    simp only [hfg]
    have : ∫ g, (k g : ℂ) ∂μ = ((1 : ℝ) : ℂ) := by
      rw [← hk1]; exact integral_ofReal
    rw [this]
    simp
  have key : π.integrated μ (UnitaryRep.ccToL1 μ f) v - v = ∫ g, f g • (π g v - v) ∂μ := by
    simp only [smul_sub]
    rw [integral_sub hint1 hint2, hv, UnitaryRep.integrated_ccToL1_apply]
  have hbound : ‖∫ g, f g • (π g v - v) ∂μ‖ ≤ ∫ g, k g * r ∂μ := by
    refine norm_integral_le_of_norm_le (hkint.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_smul, hfg, Complex.norm_real, Real.norm_of_nonneg (hknn g)]
    by_cases hg : g ∈ U
    · exact mul_le_mul_of_nonneg_left (hr g (hUsub hg)) (hknn g)
    · have : k g = 0 := by
        simp only [k]
        rw [h0 hg]
        simp
      rw [this]
      simp
  rw [key]
  rw [integral_mul_const, hk1, one_mul] at hbound
  exact hbound
end

section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.finiteDimensional_of_compact_near_identity :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (S : Submodule ℂ H), IsCompactOperator T → (∀ v ∈ S, ‖T v - v‖ ≤ 1 / 2 * ‖v‖) → FiniteDimensional ℂ S := by
  intro H _ _ _ T S hT hS
  have hcl : IsClosed {v : H | ‖T v - v‖ ≤ 1 / 2 * ‖v‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hS' : ∀ v ∈ S.topologicalClosure, ‖T v - v‖ ≤ 1 / 2 * ‖v‖ := by
    intro v hv
    have : closure (S : Set H) ⊆ {v : H | ‖T v - v‖ ≤ 1 / 2 * ‖v‖} :=
      closure_minimal (fun w hw => hS w hw) hcl
    exact this hv
  haveI : CompleteSpace S.topologicalClosure :=
    S.isClosed_topologicalClosure.completeSpace_coe
  let f : S.topologicalClosure →L[ℂ] H := T.comp S.topologicalClosure.subtypeL
  have hf : ∀ x : S.topologicalClosure, ‖x‖ ≤ ((2 : NNReal) : ℝ) * ‖f x‖ := by
    intro x
    have h1 := hS' x.1 x.2
    have h2 : ‖(x : H)‖ ≤ ‖T x‖ + ‖T x - x‖ := by
      have : (x : H) = T x - (T x - x) := by abel
      calc ‖(x : H)‖ = ‖T x - (T x - x)‖ := congrArg norm this
        _ ≤ _ := norm_sub_le _ _
    have h3 : ‖x‖ = ‖(x : H)‖ := rfl
    have h4 : f x = T x := rfl
    rw [h3, h4]
    push_cast
    linarith
  have hanti : AntilipschitzWith 2 f := f.antilipschitz_of_bound hf
  have hemb : IsClosedEmbedding f := hanti.isClosedEmbedding f.uniformContinuous
  obtain ⟨K, hK, hKsub⟩ := IsCompactOperator.image_closedBall_subset_compact (f := (T : H →ₗ[ℂ] H)) hT 1
  have hc : IsCompact (Metric.closedBall (0 : S.topologicalClosure) 1) := by
    refine (hemb.isCompact_preimage hK).of_isClosed_subset Metric.isClosed_closedBall ?_
    intro x hx
    apply hKsub
    refine ⟨(x : H), ?_, rfl⟩
    rw [mem_closedBall_zero_iff] at hx ⊢
    exact hx
  haveI : FiniteDimensional ℂ S.topologicalClosure :=
    FiniteDimensional.of_isCompact_closedBall₀ ℂ one_pos hc
  exact Submodule.finiteDimensional_of_le S.le_topologicalClosure
end

section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.finiteDimensional_cuspForms_of_level_and_derivOp_bound :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (d : ℕ) (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra) (C : ℝ) (U : Subgroup (AdelicGLn.integralFiniteGL K n)) (S : Submodule ℂ (cuspForms K n)), IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) → S ≤ centralCuspForms K n → (∀ φ ∈ S, ∀ u ∈ U, finRepCusp K n (u : AdelicGLn.integralFiniteGL K n) φ = φ) → (∀ φ ∈ S, ∀ i, ‖cuspVecL μ ((gkModuleCusp K n).ρ (b i) φ)‖ ≤ C * ‖cuspVecL μ φ‖) → FiniteDimensional ℂ S := by
  intro K _ _ n μ _ d b C U S hU hS hfix hbound
  obtain ⟨N, hN, hNv⟩ := UpperTheory.exists_nhds_displacement_le_half_of_derivOp_bound _ _ _ (isExpLieAlgebra K n) d b C
  obtain ⟨N', hN', hN'd⟩ := UpperTheory.exists_nhds_one_normOneGL_factorization K n N U hN hU
  obtain ⟨f, hf⟩ := UpperTheory.exists_approximate_identity_integrated (normOneGL K n) (CuspL2 μ) (cuspRepT μ) μ N' hN'
  have key : ∀ v ∈ S.map (cuspVecL μ),
      ‖(cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ f) v - v‖ ≤ 1 / 2 * ‖v‖ := by
    rintro _ ⟨φ, hφ, rfl⟩
    refine hf _ _ fun g hg => ?_
    obtain ⟨a, ha, u, hu, rfl⟩ := hN'd g hg
    have hφ' : φ ∈ centralCuspForms K n := hS hφ
    have hfx : cuspRepT μ (retractOne (finEmb K n (u : AdelicGLn.integralFiniteGL K n))) (cuspVecL μ φ) =
        cuspVecL μ φ := by
      rw [← cuspToL2_finRepCusp μ _ hφ', hfix φ hφ u hu]
    rw [(cuspRepT μ).map_mul_apply, hfx, ← archRepT_apply]
    refine hNv (CuspL2 μ) (archRepT μ) (cuspVecL μ φ) (fun g w => ?_)
      (isSmoothVector_cuspToL2 μ hφ') (fun i => ?_) a ha
    · rw [archRepT_apply]
      exact UnitaryRep.norm_map _ _ _
    · rw [derivOp_cuspVecL μ hφ']
      exact hbound φ hφ i
  haveI : FiniteDimensional ℂ (S.map (cuspVecL μ)) :=
    UpperTheory.finiteDimensional_of_compact_near_identity (CuspL2 μ) _ (S.map (cuspVecL μ)) (isCompactOperator_cuspRep μ f) key
  exact UnitaryAdmissible.finiteDimensional_of_map_mem (E := S.map (cuspVecL μ)) (cuspVecL μ)
    (fun x hx => Submodule.mem_map_of_mem hx)
    (fun x hx h => eq_zero_of_cuspVecL_eq_zero (μ := μ) (hS hx) h)
end
