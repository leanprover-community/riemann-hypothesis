import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Master
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SwapInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BfFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SecFun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.DenseCc

section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private def ctKer {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (r : ℕ) :
    Submodule ℂ (L2 μ) where
  carrier := {w | constantTermL2 μ r w =ᵐ[μ] 0}
  zero_mem' := by
    change constantTermL2 μ r 0 =ᵐ[μ] 0
    filter_upwards [ae_constantTermL2_sub μ r 0 0] with y hy
    rw [sub_self, sub_self] at hy
    exact hy
  add_mem' := fun {φ ψ} hφ hψ => by
    change constantTermL2 μ r (φ + ψ) =ᵐ[μ] 0
    have h1 : constantTermL2 μ r φ =ᵐ[μ] 0 := hφ
    have h2 : constantTermL2 μ r ψ =ᵐ[μ] 0 := hψ
    filter_upwards [ae_constantTermL2_add μ r φ ψ, h1, h2] with y e1 e2 e3
    rw [e1, e2, e3]
    simp
  smul_mem' := fun c φ hφ => by
    change constantTermL2 μ r (c • φ) =ᵐ[μ] 0
    have h1 : constantTermL2 μ r φ =ᵐ[μ] 0 := hφ
    filter_upwards [ae_constantTermL2_smul μ r c φ, h1] with y e1 e2
    rw [e1, e2]
    simp

private theorem ctKer_closed {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (r : ℕ) : IsClosed (ctKer μ r : Set (L2 μ)) := by
  refine isClosed_of_closure_subset fun φ hφ => ?_
  change constantTermL2 μ r φ =ᵐ[μ] 0
  refine ae_of_forall_isCompact μ fun S hS => ?_
  obtain ⟨C, hC, hCφ⟩ := exists_lintegral_constantTermL2_sq_le μ r hS
  set I := ∫⁻ y in S, ‖constantTermL2 μ r φ y‖ₑ ∂μ
  have hle : ∀ ε : ℝ, 0 < ε → I ^ 2 ≤ C * ENNReal.ofReal ε ^ 2 := by
    intro ε hε
    obtain ⟨ψ, hψ, hdist⟩ := Metric.mem_closure_iff.1 hφ ε hε
    have hψ' : constantTermL2 μ r ψ =ᵐ[μ] 0 := hψ
    have hI : I = ∫⁻ y in S, ‖constantTermL2 μ r (φ - ψ) y‖ₑ ∂μ := by
      refine lintegral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [ae_constantTermL2_sub μ r φ ψ, hψ'] with y h1 h2
      rw [h1, h2, Pi.zero_apply, sub_zero]
    rw [hI]
    refine (hCφ (φ - ψ)).trans ?_
    gcongr
    rw [← ofReal_norm, ← dist_eq_norm]
    exact ENNReal.ofReal_le_ofReal hdist.le
  have hI0 : I ^ 2 = 0 := by
    refine le_antisymm ?_ zero_le
    have ht : Tendsto (fun ε : ℝ => C * ENNReal.ofReal ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun ε : ℝ => ENNReal.ofReal ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
        have := (((ENNReal.continuous_pow 2).comp ENNReal.continuous_ofReal).tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
        simpa [Function.comp_def] using this
      simpa using ENNReal.Tendsto.const_mul h1 (Or.inr hC)
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => hle ε hε)
  have hI' : I = 0 := pow_eq_zero_iff two_ne_zero |>.1 hI0
  have hm : AEMeasurable (fun y => ‖constantTermL2 μ r φ y‖ₑ) (μ.restrict S) :=
    (stronglyMeasurable_ctFun r (Lp.stronglyMeasurable φ)).measurable.enorm.aemeasurable
  filter_upwards [(lintegral_eq_zero_iff' hm).1 hI'] with y hy
  simpa using hy

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.ctClosed :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (r : ℕ), ∃ S : Submodule ℂ (L2 μ), IsClosed (S : Set (L2 μ)) ∧
      ∀ w, w ∈ S ↔ constantTermL2 μ r w =ᵐ[μ] 0 := by
  intro K _ _ n μ _ r
  exact ⟨ctKer μ r, ctKer_closed μ r, fun _ => Iff.rfl⟩
end

section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem ae4 {A B C D : Type} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (α : Measure A) (β : Measure B) (γ : Measure C) (δ : Measure D) [SFinite β] [SFinite γ] [SFinite δ]
    (H : A × B × C × D → ℝ≥0∞) (hH : Measurable H)
    (h0 : ∫⁻ a, ∫⁻ b, ∫⁻ c, ∫⁻ d, H (a, b, c, d) ∂δ ∂γ ∂β ∂α = 0) :
    ∀ᵐ a ∂α, ∀ᵐ b ∂β, ∀ᵐ c ∂γ, ∀ᵐ d ∂δ, H (a, b, c, d) = 0 := by
  have h1 : ∫⁻ p, H p ∂α.prod (β.prod (γ.prod δ)) = 0 := by
    rw [lintegral_prod _ hH.aemeasurable, ← h0]
    refine lintegral_congr fun a => ?_
    have ha : Measurable fun q : B × C × D => H (a, q) := hH.comp measurable_prodMk_left
    rw [lintegral_prod _ ha.aemeasurable]
    refine lintegral_congr fun b => ?_
    have hb : Measurable fun q : C × D => H (a, b, q) := ha.comp measurable_prodMk_left
    rw [lintegral_prod _ hb.aemeasurable]
  rw [lintegral_eq_zero_iff hH] at h1
  filter_upwards [Measure.ae_ae_of_ae_prod h1] with a ha
  filter_upwards [Measure.ae_ae_of_ae_prod ha] with b hb
  filter_upwards [Measure.ae_ae_of_ae_prod hb] with c hc
  exact hc

private theorem int0 {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    {α : Measure A} {β : Measure B} [SFinite α] [SFinite β] {f : A × B → ℂ} (hf : Integrable f (α.prod β))
    (h : ∀ᵐ a ∂α, Integrable (fun b => f (a, b)) β → ∫ b, f (a, b) ∂β = 0) : ∫ p, f p ∂α.prod β = 0 := by
  rw [integral_prod _ hf]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [h, hf.prod_right_ae] with a ha hi
  exact ha hi

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.orthCt :
    ∀ {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (F : G1 K (2 + 2) → ℂ), Continuous F → (∀ γ ∈ PK K, ∀ g, F (γ * g) = F g) → InBand F → Decays F → (∀ X g, F (nn X * g) = F g) → ∀ v w : L2 μ, Reps μ v (th F) →
      constantTermL2 μ 2 w =ᵐ[μ] 0 → ⟪v, w⟫_ℂ = 0 := by
  intro K _ _ μ _ F hFc hFP hFB hFD hFN v w hv hw
  obtain ⟨-, -, -, hlv, -, -, -, -, -, -, -, hcpt⟩ := blkLaws (K := K)
  haveI : CompactSpace (KG K (2 + 2)) := isCompact_iff_compactSpace.mp (hcpt (2 + 2)).1
  let μ₂ : Measure (G1 K 2) := Measure.haar
  let κ : Measure (KG K (2 + 2)) := Measure.haar
  haveI : SecondCountableTopology (G1 K 2) := inferInstance
  haveI : SecondCountableTopology (G1 K (2 + 2)) := inferInstance
  haveI : SecondCountableTopology (KG K (2 + 2)) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace (G1 K 2) := inferInstance
  haveI : BorelSpace (KG K (2 + 2)) := Subtype.borelSpace _
  haveI : BorelSpace (ℝ × KG K (2 + 2)) := Prod.borelSpace
  haveI : BorelSpace (G1 K 2 × ℝ × KG K (2 + 2)) := Prod.borelSpace
  haveI : BorelSpace (G1 K 2 × G1 K 2 × ℝ × KG K (2 + 2)) := Prod.borelSpace
  haveI : SFinite μ₂ := inferInstance
  haveI : SFinite κ := inferInstance
  haveI : SFinite (fd μ₂) := inferInstance
  haveI : SFinite ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2)) := inferInstance
  haveI : SFinite (κ.prod ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2))) :=
    Measure.prod.instSFinite
  haveI : SFinite ((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-4 * t))) := inferInstance
  haveI : SFinite (((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-4 * t))).prod
      (κ.prod ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2)))) := Measure.prod.instSFinite
  haveI : SFinite ((fd μ₂).prod (((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-4 * t))).prod
      (κ.prod ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2))))) := Measure.prod.instSFinite
  obtain ⟨⟨c, hc⟩, -⟩ := unf μ μ₂ κ
  obtain ⟨hint, heq, -⟩ := master μ μ₂ κ c hc F hFc hFP hFB hFD v w hv
  obtain ⟨c', hc', hiw⟩ := iwaInt μ μ₂ κ
  have hm : Measurable (constantTermL2 μ 2 w) :=
    (stronglyMeasurable_ctFun 2 (Lp.stronglyMeasurable w)).measurable
  have h0 := hiw (fun g => ‖constantTermL2 μ 2 w g‖ₑ) hm.enorm
  have hL : ∫⁻ g, ‖constantTermL2 μ 2 w g‖ₑ ∂μ = 0 := by
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [hw] with g hg
    simp [hg]
  rw [hL, eq_comm, mul_eq_zero] at h0
  have h1 := h0.resolve_left (ENNReal.ofReal_pos.mpr hc').ne'
  simp only [mul_assoc, CuspidalProjection.constantTermL2_unipotent_mul, lintegral_const] at h1
  have hcont : Continuous fun p : G1 K 2 × G1 K 2 × ℝ × KG K (2 + 2) =>
      lv p.1 p.2.1 p.2.2.1 * (p.2.2.2 : G1 K (2 + 2)) :=
    (hlv.comp (f := fun p : G1 K 2 × G1 K 2 × ℝ × KG K (2 + 2) => (p.1, p.2.1, p.2.2.1)) (by fun_prop)).mul
      (continuous_subtype_val.comp (by fun_prop))
  have h2 := ae4 μ₂ μ₂ volume κ (fun p : G1 K 2 × G1 K 2 × ℝ × KG K (2 + 2) =>
      ‖constantTermL2 μ 2 w (lv p.1 p.2.1 p.2.2.1 * (p.2.2.2 : G1 K (2 + 2)))‖ₑ *
        (ENNReal.ofReal (Real.exp (-4 * p.2.2.1)) * unipMeasure K (2 + 2) 2 univ))
    ((hm.comp hcont.measurable).enorm.mul (Measurable.mul_const (by fun_prop) _)) h1
  have hU : unipMeasure K (2 + 2) 2 univ ≠ 0 := NeZero.ne _
  rw [heq]
  refine mul_eq_zero_of_right _ ?_
  unfold parM at hint ⊢
  refine int0 hint ?_
  filter_upwards [ae_restrict_of_ae h2] with m₁ h3 hi₁
  refine int0 hi₁ ?_
  filter_upwards [ae_restrict_of_ae h3] with m₂ h4 hi₂
  refine int0 hi₂ ?_
  filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le h4] with t h5 hi₃
  refine int0 hi₃ ?_
  filter_upwards [h5] with k h6 _
  have h7 : constantTermL2 μ 2 w (lv m₁ m₂ t * (k : G1 K (2 + 2))) = 0 := by
    rcases mul_eq_zero.mp h6 with h | h
    · exact enorm_eq_zero.mp h
    · exact absurd h (mul_ne_zero (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' hU)
  simp only [pt, mul_assoc, hFN]
  rw [integral_const_mul]
  exact mul_eq_zero_of_right _ h7
end

section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

set_option synthInstance.maxHeartbeats 400000 in
private theorem intD {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) {E : Type} [NormedAddCommGroup E]
    {h : G1 K n → E} (hh : Continuous h) : Integrable h D.ν := by
  have := D.prob
  have h1 : IntegrableOn h (D.U : Set (G1 K n)) D.ν := hh.continuousOn.integrableOn_compact (typeFin D).1
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem D.supp] at h1

private theorem intR {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] (w : L2 μ) : Integrable (fun k => D.e k • rightRegularRep (Gam K n) μ k w) D.ν :=
  intD D (D.cont.smul ((rightRegularRep (Gam K n) μ).continuous_orbit w))

private theorem fixClosed {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] : ∃ S : Submodule ℂ (L2 μ), IsClosed (S : Set (L2 μ)) ∧ ∀ w, w ∈ S ↔ D.FixedByTypeProjector μ w := by
  let T₀ : L2 μ →ₗ[ℂ] L2 μ :=
    { toFun := fun w => ∫ k, D.e k • rightRegularRep (Gam K n) μ k w ∂D.ν
      map_add' := fun a b => by
        rw [← integral_add (intR D μ a) (intR D μ b)]
        simp only [map_add, smul_add]
      map_smul' := fun c a => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        simp only [smul_comm c] }
  have hb : ∀ w, ‖T₀ w‖ ≤ (∫ k, ‖D.e k‖ ∂D.ν) * ‖w‖ := by
    intro w
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    rw [← integral_mul_const]
    congr 1
    ext k
    rw [norm_smul, UnitaryRep.norm_map]
  let T : L2 μ →L[ℂ] L2 μ := T₀.mkContinuous _ hb
  refine ⟨LinearMap.eqLocus (T : L2 μ →ₗ[ℂ] L2 μ) LinearMap.id, isClosed_eq T.continuous continuous_id, fun w => Iff.rfl⟩

set_option synthInstance.maxHeartbeats 400000 in
private theorem fixRep {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] {v : L2 μ} {Φ : G1 K n → ℂ} (h : IsContRep μ v Φ) {C : ℝ} (hC : ∀ g, ‖Φ g‖ ≤ C)
    (hfix : D.Fix Φ) : D.FixedByTypeProjector μ v := by
  have := D.prob
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  have hQ := h.ae_eq_quotFun
  have hQc := continuous_quotFun h.2.1 h.1
  set Q := quotFun Φ h.2.1 with hQd
  have hQb : ∀ x, ‖Q x‖ ≤ C := fun x => by
    obtain ⟨y, rfl⟩ := mk_surjective (Gam K n) x
    exact hC y
  refine ext_inner_left ℂ fun w => ?_
  have hw : Integrable (fun x => conj (w x)) (quotientMeasure (Gam K n) μ) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp ((Lp.memLp w).integrable one_le_two)
  have hcoef : ∀ k, ⟪w, D.e k • rightRegularRep (Gam K n) μ k v⟫_ℂ =
      ∫ x, D.e k * conj (w x) * Q (rightMul (Gam K n) k x) ∂quotientMeasure (Gam K n) μ := by
    intro k
    rw [inner_smul_right, L2.inner_def, ← integral_const_mul]
    have h2 : (fun x => v (rightMul (Gam K n) k x)) =ᵐ[quotientMeasure (Gam K n) μ]
        fun x => Q (rightMul (Gam K n) k x) :=
      (measurePreserving_rightMul μ k).quasiMeasurePreserving.ae_eq_comp hQ
    refine integral_congr_ae ?_
    filter_upwards [coeFn_rightRegularRep (Gam K n) μ k v, h2] with x h3 h4
    rw [h3, h4, RCLike.inner_apply', mul_assoc]
  have hI : Integrable (Function.uncurry fun k x => D.e k * conj (w x) * Q (rightMul (Gam K n) k x))
      (D.ν.prod (quotientMeasure (Gam K n) μ)) := by
    have h0 : Integrable D.e D.ν := intD D D.cont
    have h1 : Integrable (fun p : G1 K n × RightCosetSpace (Gam K n) => D.e p.1 * conj (w p.2))
        (D.ν.prod (quotientMeasure (Gam K n) μ)) := Integrable.mul_prod (f := D.e) (g := fun x => conj (w x)) h0 hw
    have hc : Continuous fun p : G1 K n × RightCosetSpace (Gam K n) => Q (rightMul (Gam K n) p.1 p.2) := by
      have hr : Continuous fun p : RightCosetSpace (Gam K n) × G1 K n => rightMul (Gam K n) p.2 p.1 :=
        continuous_rightMul_prod (Gam K n)
      have h3 : Continuous fun p : G1 K n × RightCosetSpace (Gam K n) => (p.2, p.1) :=
        continuous_snd.prodMk continuous_fst
      have h4 := hr.comp h3
      have h5 := hQc.comp h4
      exact h5
    have h2 := Integrable.mul_bdd (c := C) h1 hc.aestronglyMeasurable (Eventually.of_forall fun p => hQb _)
    exact h2
  rw [← integral_inner (intR D μ v)]
  simp only [hcoef]
  rw [integral_integral_swap hI, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hQ] with x hx
  rw [RCLike.inner_apply', hx]
  obtain ⟨y, rfl⟩ := mk_surjective (Gam K n) x
  simp only [rightMul_mk, hQd, quotFun_mk]
  rw [← hfix y, ← integral_const_mul]
  congr 1
  ext k
  ring

private theorem thFix {K : Type} [Field K] [NumberField K] (D : TypeDat K (2 + 2)) {F : G1 K (2 + 2) → ℂ}
    (hF : Continuous F)
    (hfin : ∀ C : Set (G1 K (2 + 2)), IsCompact C → {q : Cos K | ∃ g ∈ C, F ((q.out : G1 K (2 + 2)) * g) ≠ 0}.Finite)
    (hfix : D.Fix F) : D.Fix (th F) := by
  intro g
  have hc : IsCompact ((fun k => g * k) '' (D.U : Set (G1 K (2 + 2)))) :=
    (typeFin D).1.image (continuous_const_mul g)
  have hS := hfin _ hc
  have hs : ∀ k ∈ D.U, th F (g * k) = ∑ q ∈ hS.toFinset, F ((q.out : G1 K (2 + 2)) * g * k) := by
    intro k hk
    simp only [mul_assoc]
    refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
    rw [Finite.coe_toFinset]
    exact ⟨g * k, ⟨k, hk, rfl⟩, hq⟩
  have h1 := hs 1 D.U.one_mem
  simp only [mul_one] at h1
  rw [h1, ← Finset.sum_congr rfl fun q _ => hfix ((q.out : G1 K (2 + 2)) * g), ← integral_finset_sum]
  · refine integral_congr_ae ?_
    filter_upwards [D.supp] with k hk
    rw [hs k hk, Finset.mul_sum]
  · intro q _
    exact intD D (D.cont.mul (hF.comp (continuous_const_mul _)))

private theorem bfFix {K : Type} [Field K] [NumberField K] (D : TypeDat K (2 + 2)) (β : ℝ → ℂ) {f : G1 K (2 + 2) → ℂ}
    (hfix : D.Fix f) : D.Fix (bf β f) := by
  intro g
  unfold bf
  rw [← hfix g, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [D.supp] with k hk
  have h1 : HP 2 2 (g * k) = HP 2 2 g := (hpSpec.2.1 k ((typeFin D).2.1 hk)).2 g
  rw [h1]
  ring

private theorem ctRep {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] {v : L2 μ} {Φ : G1 K n → ℂ} (h : IsContRep μ v Φ) (r : ℕ)
    (h0 : ∀ g, ∫ X in unipFundamentalDomain K n r, Φ (unipOne K n r X * g) ∂unipMeasure K n r = 0) :
    constantTermL2 μ r v =ᵐ[μ] 0 := by
  filter_upwards [ae_ctFun_congr μ r h.ae_eq_quotFun] with y hy
  rw [constantTermL2, hy]
  exact h0 y

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.ctZero :
    CtZeroC := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP D d d' A A'
  obtain ⟨S₀, hS₀, h₀⟩ := fixClosed D μ
  obtain ⟨S₁, hS₁, h₁⟩ := ctClosed μ 1
  obtain ⟨S₃, hS₃, h₃⟩ := ctClosed μ 3
  let S : Submodule ℂ (L2 μ) := (cuspidalL2 μ)ᗮ ⊓ (S₀ ⊓ (S₁ ⊓ S₃))
  have hS : IsClosed (S : Set (L2 μ)) :=
    (Submodule.isClosed_orthogonal _).inter (hS₀.inter (hS₁.inter hS₃))
  have hgen : Submodule.span ℂ {u : L (Eu d) | ∃ (β : ℝ → ℂ) (v : Eu d), Continuous β ∧ HasCompactSupport β ∧
      ∀ᵐ x : ℝ, u x = β x • v} ≤ S.comap A.J.toLinearMap := by
    rw [Submodule.span_le]
    rintro u ⟨β, v, hβ, hβc, hu⟩
    have hrep : Reps μ (A.J u) (th (bf β (A.sec v))) := A.spec β v u hβ hβc hu
    obtain ⟨hsec, hfix⟩ := (A.onto (A.sec v)).1 ⟨v, rfl⟩
    obtain ⟨hp, hband, hdec⟩ := bfFun _ β (secFun μ₂ τ₁ τ₂ D hP.irr₁ hP.irr₂ _ hsec hfix) hβ hβc
    obtain ⟨hfin, hcont, hinv, hb⟩ := thBasic μ _ hp.cont hp.rat hband
    obtain ⟨-, ⟨C, hC⟩, -⟩ := hb hdec
    have hcr : IsContRep μ (A.J u) (th (bf β (A.sec v))) := ⟨hcont, hinv, hrep⟩
    refine ⟨?_, (h₀ _).2 ?_, (h₁ _).2 ?_, (h₃ _).2 ?_⟩
    · refine (Submodule.mem_orthogonal' _ _).2 fun w hw => ?_
      exact orthCt μ _ hp.cont hp.rat hband hdec hp.unip _ w hrep (hw 2 (by norm_num) (by norm_num))
    · exact fixRep D μ hcr hC (thFix D hp.cont hfin (bfFix D β hfix))
    · exact ctRep μ hcr 1 fun g => (thCt _ hp hband g).1
    · exact ctRep μ hcr 3 fun g => (thCt _ hp hband g).2.1
  intro u
  have hu : A.J u ∈ S :=
    closure_minimal (s := _) (t := A.J ⁻¹' (S : Set (L2 μ))) hgen (hS.preimage A.J.continuous) ((denseCc d).1 u)
  obtain ⟨e, e₀, e₁, e₃⟩ := hu
  exact ⟨(Submodule.starProjection_apply_eq_zero_iff _).2 e, (h₀ _).1 e₀, (h₁ _).1 e₁, (h₃ _).1 e₃⟩
end
