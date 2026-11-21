import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp

section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.cutSpec :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (s : Set ℝ), MeasurableSet s → ∀ u : L V, ∀ᵐ x : ℝ, cut V s u x = s.indicator u x := by
  intro V _ _ _ _ s hs
  have hm : ∀ u : L V, MemLp (s.indicator (u : ℝ → V)) 2 volume := fun u => (Lp.memLp u).indicator hs
  let A : L V →ₗ[ℂ] L V :=
    { toFun := fun u => (hm u).toLp _
      map_add' := fun u v => Lp.ext (by
        filter_upwards [(hm (u + v)).coeFn_toLp, (hm u).coeFn_toLp, (hm v).coeFn_toLp, Lp.coeFn_add u v,
          Lp.coeFn_add ((hm u).toLp _) ((hm v).toLp _)] with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3]
        by_cases hx : x ∈ s
        · simp only [indicator_of_mem hx]; exact h4
        · simp [hx])
      map_smul' := fun c u => Lp.ext (by
        filter_upwards [(hm (c • u)).coeFn_toLp, (hm u).coeFn_toLp, Lp.coeFn_smul c u,
          Lp.coeFn_smul c ((hm u).toLp _)] with x h1 h2 h4 h5
        rw [h1, RingHom.id_apply, h5, Pi.smul_apply, h2]
        by_cases hx : x ∈ s <;> simp [hx, h4]) }
  have hb : ∀ u, ‖A u‖ ≤ 1 * ‖u‖ := fun u => by
    rw [one_mul]
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [(hm u).coeFn_toLp] with x h
    show ‖((hm u).toLp _ : ℝ → V) x‖ ≤ _
    rw [h]
    exact norm_indicator_le_norm_self _ _
  exact Classical.epsilon_spec (p := fun C : L V →L[ℂ] L V => ∀ u, ∀ᵐ x : ℝ, C u x = s.indicator u x)
    ⟨A.mkContinuous 1 hb, fun u => (hm u).coeFn_toLp⟩
end

section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.cutLaws :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (s t : Set ℝ), MeasurableSet s → MeasurableSet t →
      cut V s ∘L cut V t = cut V (s ∩ t) ∧ IsSelfAdjoint (cut V s) ∧ (Disjoint s t → cut V (s ∪ t) = cut V s + cut V t) ∧ cut V univ = 1 ∧ cut V ∅ = 0 ∧
      (∀ u, ‖cut V s u‖ ≤ ‖u‖) ∧ (∀ a : ℝ, sh V a ∘L cut V s = cut V ((fun x => x + a) ⁻¹' s) ∘L sh V a) ∧
      (∀ u : L V, cut V s u = u ↔ ∀ᵐ x : ℝ, x ∉ s → u x = 0) ∧ ∀ u : L V, ‖cut V s u‖ ^ 2 = ∫ x in s, ‖u x‖ ^ 2 := by
  intro V _ _ _ _ s t hs ht
  have c := cutSpec (V := V)
  have nsq : ∀ u : L V, ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := fun u => by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner u u)]
    simp only [inner_self_eq_norm_sq]
  refine ⟨?_, ?_, fun hd => ?_, ?_, ?_, fun u => ?_, fun a => ?_, fun u => ?_, fun u => ?_⟩
  · refine ContinuousLinearMap.ext fun u => Lp.ext ?_
    filter_upwards [c s hs (cut V t u), c t ht u, c _ (hs.inter ht) u] with x h1 h2 h3
    rw [ContinuousLinearMap.comp_apply, h1, h3]
    by_cases a : x ∈ s <;> by_cases b : x ∈ t <;> simp [a, b, h2]
  · refine LinearMap.IsSymmetric.isSelfAdjoint fun u v => ?_
    simp only [ContinuousLinearMap.coe_coe, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [c s hs u, c s hs v] with x h1 h2
    rw [h1, h2]
    by_cases a : x ∈ s <;> simp [a]
  · refine ContinuousLinearMap.ext fun u => Lp.ext ?_
    filter_upwards [c s hs u, c t ht u, c _ (hs.union ht) u, Lp.coeFn_add (cut V s u) (cut V t u)] with x h1 h2 h3 h4
    rw [ContinuousLinearMap.add_apply, h3, h4, Pi.add_apply, h1, h2, indicator_union_of_disjoint hd]
  · refine ContinuousLinearMap.ext fun u => Lp.ext ?_
    filter_upwards [c _ .univ u] with x h1
    rw [h1]; simp
  · refine ContinuousLinearMap.ext fun u => Lp.ext ?_
    filter_upwards [c _ .empty u, Lp.coeFn_zero V 2 (volume : Measure ℝ)] with x h1 h2
    rw [h1, ContinuousLinearMap.zero_apply, h2]; simp
  · refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [c s hs u] with x h
    rw [h]; exact norm_indicator_le_norm_self _ _
  · refine ContinuousLinearMap.ext fun u => Lp.ext ?_
    filter_upwards [sh_ae V a (cut V s u), (measurePreserving_add_right volume a).quasiMeasurePreserving.ae (c s hs u),
      c _ (measurable_add_const a hs) (sh V a u), sh_ae V a u] with x h1 h2 h3 h4
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h1, h2, h3]
    by_cases b : x + a ∈ s <;> simp [b, h4]
  · constructor
    · intro h
      filter_upwards [c s hs u] with x h1 hx
      rw [h] at h1
      rw [h1, indicator_of_notMem hx]
    · intro h
      refine Lp.ext ?_
      filter_upwards [c s hs u, h] with x h1 h2
      rw [h1]
      by_cases b : x ∈ s
      · simp [b]
      · simp [b, h2 b]
  · rw [nsq, ← integral_indicator hs]
    refine integral_congr_ae ?_
    filter_upwards [c s hs u] with x h
    rw [h]
    by_cases b : x ∈ s <;> simp [b]
end
