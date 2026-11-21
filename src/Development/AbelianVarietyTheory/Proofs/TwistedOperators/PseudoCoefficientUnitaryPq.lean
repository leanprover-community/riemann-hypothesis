import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleUnitaryAdmissible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KFiniteCoefficientsAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CharacterRegularityFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspidalOrbitalIntegrals
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleAdmissibleFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientExistence
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixConclIffOfIsDS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryKFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteApproximateIdentity

section
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory

theorem unitaryRep_inner_map {n : ℕ} {ε : Fin n → Bool} {U : Type} [NormedAddCommGroup U]
    [InnerProductSpace ℂ U] {π : UJ ε →* (U →L[ℂ] U)} (hπ : IsUnitaryRep π) (h : UJ ε) (x y : U) :
    ⟪π h x, π h y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let L : U →ₗᵢ[ℂ] U := ⟨(π h).toLinearMap, hπ.norm_apply h⟩
  exact L.inner_map_map x y

theorem isMulRightInvariant_haar_UJ {n : ℕ} (ε : Fin n → Bool) (μ : Measure (UJ ε))
    [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  haveI : (muG ε).IsHaarMeasure := by unfold muG; infer_instance
  have hμ := Measure.isMulLeftInvariant_eq_smul μ (muG ε)
  constructor
  intro g
  rw [hμ, Measure.map_smul, indefinite_unitary_unimodular n ε g]

theorem span_orbit_coeff_memLp {n : ℕ} {ε : Fin n → Bool} (μ : Measure (UJ ε)) [μ.IsHaarMeasure]
    {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] {π : UJ ε →* (U →L[ℂ] U)}
    (hπ : IsUnitaryRep π) (q : ℝ≥0∞) (v : U) (hv : MemLp (fun g => ⟪v, π g v⟫_ℂ) q μ)
    (u : U) (hu : u ∈ Submodule.span ℂ (Set.range fun g => π g v))
    (u' : U) (hu' : u' ∈ Submodule.span ℂ (Set.range fun g => π g v)) :
    MemLp (fun g => ⟪u', π g u⟫_ℂ) q μ := by
  haveI := isMulRightInvariant_haar_UJ ε μ

  have gen : ∀ h g₀ : UJ ε, MemLp (fun g => ⟪π h v, π g (π g₀ v)⟫_ℂ) q μ := by
    intro h g₀
    have e : (fun g => ⟪π h v, π g (π g₀ v)⟫_ℂ) =
        (fun g => ⟪v, π g v⟫_ℂ) ∘ (fun g => h⁻¹ * g) ∘ (fun g => g * g₀) := by
      funext g
      simp only [Function.comp]
      rw [← ContinuousLinearMap.mul_apply, ← map_mul,
        ← unitaryRep_inner_map hπ h⁻¹ (π h v), ← ContinuousLinearMap.mul_apply, ← map_mul,
        ← ContinuousLinearMap.mul_apply (π h⁻¹), ← map_mul, inv_mul_cancel, map_one,
        ContinuousLinearMap.one_apply]
    rw [e]
    exact (hv.comp_measurePreserving (measurePreserving_mul_left μ h⁻¹)).comp_measurePreserving
      (measurePreserving_mul_right μ g₀)
  have step1 : ∀ h : UJ ε, ∀ u ∈ Submodule.span ℂ (Set.range fun g => π g v),
      MemLp (fun g => ⟪π h v, π g u⟫_ℂ) q μ := by
    intro h u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g₀, rfl⟩ := hx
      exact gen h g₀
    | zero =>
      have : (fun g => ⟪π h v, π g (0 : U)⟫_ℂ) = 0 := by funext g; simp
      rw [this]; exact MemLp.zero
    | add x y _ _ hx hy =>
      have : (fun g => ⟪π h v, π g (x + y)⟫_ℂ) =
          (fun g => ⟪π h v, π g x⟫_ℂ) + (fun g => ⟪π h v, π g y⟫_ℂ) := by
        funext g; simp [map_add, inner_add_right]
      rw [this]; exact hx.add hy
    | smul c x _ hx =>
      have : (fun g => ⟪π h v, π g (c • x)⟫_ℂ) = c • (fun g => ⟪π h v, π g x⟫_ℂ) := by
        funext g; simp [map_smul, inner_smul_right]
      rw [this]; exact hx.const_smul c
  induction hu' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    exact step1 h u hu
  | zero =>
    have : (fun g => ⟪(0 : U), π g u⟫_ℂ) = 0 := by funext g; simp
    rw [this]; exact MemLp.zero
  | add x y _ _ hx hy =>
    have : (fun g => ⟪x + y, π g u⟫_ℂ) = (fun g => ⟪x, π g u⟫_ℂ) + (fun g => ⟪y, π g u⟫_ℂ) := by
      funext g; simp [inner_add_left]
    rw [this]; exact hx.add hy
  | smul c x _ hx =>
    have : (fun g => ⟪c • x, π g u⟫_ℂ) = (starRingEnd ℂ c) • (fun g => ⟪x, π g u⟫_ℂ) := by
      funext g; simp [inner_smul_left, mul_comm]
    rw [this]; exact hx.const_smul _

theorem span_orbit_coeff_integrable : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → ∀ (p : ℝ), 1 ≤ p → ∀ v : U, Integrable (fun g => ‖⟪v, π g v⟫_ℂ‖ ^ p) μ → ∀ u ∈ Submodule.span ℂ (Set.range fun g => π g v), ∀ u' ∈ Submodule.span ℂ (Set.range fun g => π g v), Integrable (fun g => ‖⟪u', π g u⟫_ℂ‖ ^ p) μ := by
  intro n ε μ _ U _ _ π hπ p hp v hv u hu u' hu'
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hqt : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have cont : ∀ a b : U, Continuous fun g => ⟪a, π g b⟫_ℂ := fun a b =>
    continuous_const.inner (hπ.continuous_apply b)
  have hv' : MemLp (fun g => ⟪v, π g v⟫_ℂ) (ENNReal.ofReal p) μ := by
    rw [← integrable_norm_rpow_iff (cont v v).aestronglyMeasurable hq0 hqt, hpr]
    exact hv
  have h := span_orbit_coeff_memLp μ hπ _ v hv' u hu u' hu'
  rw [← integrable_norm_rpow_iff (cont u' u).aestronglyMeasurable hq0 hqt, hpr] at h
  exact h

end GlobalTheory
end

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_matrixCoeff_cyclic_span : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → ∀ (p : ℝ), 1 ≤ p → ∀ v : U, Integrable (fun g => ‖⟪v, π g v⟫_ℂ‖ ^ p) μ → ∀ u ∈ Submodule.span ℂ (Set.range fun g => π g v), ∀ u' ∈ Submodule.span ℂ (Set.range fun g => π g v), Integrable (fun g => ‖⟪u', π g u⟫_ℂ‖ ^ p) μ := by
  atlas_forward_decl GlobalTheory.span_orbit_coeff_integrable
end

section
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.AvgRightLp

theorem integrable_of_continuous_K {n : ℕ} {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E]
    {h : KG ε → E} (hh : Continuous h) : Integrable h (muK ε) :=
  integrableOn_univ.mp (hh.continuousOn.integrableOn_compact isCompact_univ)

instance isProbabilityMeasure_muK {n : ℕ} (ε : Fin n → Bool) : IsProbabilityMeasure (muK ε) :=
  ⟨by simpa [muK] using Measure.haarMeasure_self (G := KG ε) (K₀ := ⊤)⟩

theorem integrable_coeff_avg_right : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → ∀ (p : ℝ), 1 ≤ p → ∀ φ : KG ε → ℂ, Continuous φ → ∀ u u' : U, Integrable (fun g => ‖⟪u', π g u⟫_ℂ‖ ^ p) μ → Integrable (fun g => ‖⟪u', π g (∫ k, φ k • π k u ∂(muK ε))⟫_ℂ‖ ^ p) μ := by
  intro n ε μ _ U _ _ _ π hπ p hp φ hφ u u' hf
  haveI : μ.IsMulRightInvariant := by
    have hG : (muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
    rw [Measure.isMulLeftInvariant_eq_smul μ (muG ε)]
    infer_instance
  have hp0 : (0 : ℝ) ≤ p := by linarith
  set f : UJ ε → ℂ := fun g => ⟪u', π g u⟫_ℂ with hfdef
  have hfc : Continuous f := continuous_const.inner (hπ.continuous_apply u)
  have hvc : Continuous fun k : KG ε => φ k • π (k : UJ ε) u :=
    hφ.smul ((hπ.continuous_apply u).comp continuous_subtype_val)
  have hvi := integrable_of_continuous_K hvc
  have hF : ∀ g, ⟪u', π g (∫ k, φ k • π k u ∂(muK ε))⟫_ℂ = ∫ k, φ k * f (g * k) ∂(muK ε) := by
    intro g
    rw [← (π g).integral_comp_comm hvi, ← integral_inner ((π g).integrable_comp hvi) u']
    congr 1
    funext k
    simp only [hfdef, map_smul, inner_smul_right, map_mul, ContinuousLinearMap.mul_apply]
  set M : ℝ := ‖BoundedContinuousFunction.mkOfCompact (⟨φ, hφ⟩ : C(KG ε, ℂ))‖ with hMdef
  have hM : ∀ k, ‖φ k‖ ≤ M := fun k =>
    (BoundedContinuousFunction.mkOfCompact (⟨φ, hφ⟩ : C(KG ε, ℂ))).norm_coe_le_norm k
  have hM0 : 0 ≤ M := norm_nonneg _
  have hjc : ∀ g : UJ ε, Continuous fun k : KG ε => f (g * k) := fun g =>
    hfc.comp (continuous_const.mul continuous_subtype_val)

  have hpt : ∀ g, ‖⟪u', π g (∫ k, φ k • π k u ∂(muK ε))⟫_ℂ‖ ^ p ≤
      M ^ p * ∫ k, ‖f (g * k)‖ ^ p ∂(muK ε) := by
    intro g
    rw [hF g]
    have h1 : ‖∫ k, φ k * f (g * k) ∂(muK ε)‖ ≤ M * ∫ k, ‖f (g * k)‖ ∂(muK ε) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_const_mul]
      refine integral_mono (integrable_of_continuous_K (hφ.mul (hjc g)).norm)
        (integrable_of_continuous_K (continuous_const.mul (hjc g).norm)) fun k => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM k) (norm_nonneg _)
    have hJ : (∫ k, ‖f (g * k)‖ ∂(muK ε)) ^ p ≤ ∫ k, ‖f (g * k)‖ ^ p ∂(muK ε) :=
      (convexOn_rpow hp).map_integral_le (Real.continuous_rpow_const hp0).continuousOn isClosed_Ici
        (ae_of_all _ fun k => norm_nonneg (f (g * k)))
        (integrable_of_continuous_K (hjc g).norm)
        (integrable_of_continuous_K ((hjc g).norm.rpow_const fun _ => Or.inr hp0))
    calc ‖∫ k, φ k * f (g * k) ∂(muK ε)‖ ^ p ≤ (M * ∫ k, ‖f (g * k)‖ ∂(muK ε)) ^ p :=
          Real.rpow_le_rpow (norm_nonneg _) h1 hp0
      _ = M ^ p * (∫ k, ‖f (g * k)‖ ∂(muK ε)) ^ p :=
          Real.mul_rpow hM0 (integral_nonneg fun k => norm_nonneg _)
      _ ≤ M ^ p * ∫ k, ‖f (g * k)‖ ^ p ∂(muK ε) :=
          mul_le_mul_of_nonneg_left hJ (Real.rpow_nonneg hM0 p)

  have hprod : Integrable (fun q : UJ ε × KG ε => ‖f (q.1 * q.2)‖ ^ p) (μ.prod (muK ε)) := by
    have hqc : Continuous fun q : UJ ε × KG ε => ‖f (q.1 * q.2)‖ ^ p :=
      (hfc.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))).norm.rpow_const
        fun _ => Or.inr hp0
    rw [integrable_prod_iff' hqc.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun k => hf.comp_mul_right (k : UJ ε), ?_⟩
    have : (fun k : KG ε => ∫ x, ‖‖f (x * k)‖ ^ p‖ ∂μ) = fun _ => ∫ x, ‖‖f x‖ ^ p‖ ∂μ :=
      funext fun k => integral_mul_right_eq_self (fun x => ‖‖f x‖ ^ p‖) (k : UJ ε)
    rw [this]
    exact integrable_const _
  have hdom : Integrable (fun g => M ^ p * ∫ k, ‖f (g * k)‖ ^ p ∂(muK ε)) μ :=
    hprod.integral_prod_left.const_mul _
  refine hdom.mono' ?_ (ae_of_all _ fun g => ?_)
  · exact ((continuous_const.inner (hπ.continuous_apply _)).norm.rpow_const
      fun _ => Or.inr hp0).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) p)]
    exact hpt g

end GlobalTheory.AvgRightLp
end
end

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_matrixCoeff_K_average_right : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → ∀ (p : ℝ), 1 ≤ p → ∀ φ : KG ε → ℂ, Continuous φ → ∀ u u' : U, Integrable (fun g => ‖⟪u', π g u⟫_ℂ‖ ^ p) μ → Integrable (fun g => ‖⟪u', π g (∫ k, φ k • π k u ∂(muK ε))⟫_ℂ‖ ^ p) μ := by
  atlas_forward_decl GlobalTheory.AvgRightLp.integrable_coeff_avg_right
end

section
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory

theorem integrable_inner_rpow_avg_left : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → ∀ (p : ℝ), 1 ≤ p → ∀ φ : KG ε → ℂ, Continuous φ → ∀ u u' : U, Integrable (fun g => ‖⟪u', π g u⟫_ℂ‖ ^ p) μ → Integrable (fun g => ‖⟪∫ k, φ k • π k u' ∂(muK ε), π g u⟫_ℂ‖ ^ p) μ := by
  intro n ε μ _ U _ _ _ π hπ p hp φ hφ u u' hf
  have hp0 : (0:ℝ) ≤ p := by linarith
  set f : ↥(UJ ε) → ℂ := fun g => ⟪u', π g u⟫_ℂ with hfdef
  have hfc : Continuous f := continuous_const.inner (hπ.continuous_apply u)
  have key : ∀ z : ℂ, ‖(‖z‖ ^ p)‖ₑ = ‖z‖ₑ ^ p := by
    intro z
    rw [Real.enorm_eq_ofReal (by positivity), ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0,
      ofReal_norm_eq_enorm]
  have hI : ∫⁻ g, ‖f g‖ₑ ^ p ∂μ < ∞ := by
    have h2 := hf.2
    unfold HasFiniteIntegral at h2
    simpa only [key] using h2
  have hinner : ∀ (a b : U) (g : ↥(UJ ε)), ⟪π g a, π g b⟫_ℂ = ⟪a, b⟫_ℂ := by
    intro a b g
    let L : U →ₗᵢ[ℂ] U := { toLinearMap := ((π g : U →L[ℂ] U) : U →ₗ[ℂ] U), norm_map' := hπ.norm_apply g }
    exact L.inner_map_map a b
  have hshift : ∀ (g : ↥(UJ ε)) (k : ↥(KG ε)),
      ‖⟪π g u, π (k : ↥(UJ ε)) u'⟫_ℂ‖ = ‖f ((k : ↥(UJ ε))⁻¹ * g)‖ := by
    intro g k
    have h1 : π g u = π (k : ↥(UJ ε)) (π ((k : ↥(UJ ε))⁻¹ * g) u) := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel_left]
    rw [h1, hinner, norm_inner_symm]
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuousOn
  set v := ∫ k, φ k • π (k : ↥(UJ ε)) u' ∂(muK ε) with hv
  have hint : Integrable (fun k : ↥(KG ε) => φ k • π (k : ↥(UJ ε)) u') (muK ε) := by
    have hc : Continuous (fun k : ↥(KG ε) => φ k • π (k : ↥(UJ ε)) u') :=
      hφ.smul ((hπ.continuous_apply u').comp continuous_subtype_val)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpt : ∀ g, ‖⟪v, π g u⟫_ℂ‖ₑ ≤
      ENNReal.ofReal C * ∫⁻ k, ‖f ((k : ↥(UJ ε))⁻¹ * g)‖ₑ ∂(muK ε) := by
    intro g
    have e1 : ‖⟪v, π g u⟫_ℂ‖ₑ = ‖∫ k, ⟪π g u, φ k • π (k : ↥(UJ ε)) u'⟫_ℂ ∂(muK ε)‖ₑ := by
      rw [integral_inner hint, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, norm_inner_symm]
    rw [e1, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun k => ?_)
    rw [inner_smul_right, enorm_mul, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm (f _),
      ← ofReal_norm_eq_enorm, hshift]
    rw [← ENNReal.ofReal_mul (norm_nonneg _)]
    refine le_of_le_of_eq (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hC k (Set.mem_univ _)) (norm_nonneg (f ((k : ↥(UJ ε))⁻¹ * g))))) ?_
    exact ENNReal.ofReal_mul' (norm_nonneg _)
  have hJ : ∀ g, (∫⁻ k, ‖f ((k : ↥(UJ ε))⁻¹ * g)‖ₑ ∂(muK ε)) ^ p ≤
      ∫⁻ k, ‖f ((k : ↥(UJ ε))⁻¹ * g)‖ₑ ^ p ∂(muK ε) := by
    intro g
    have hm : AEStronglyMeasurable (fun k : ↥(KG ε) => f ((k : ↥(UJ ε))⁻¹ * g)) (muK ε) :=
      (hfc.comp ((continuous_subtype_val.inv).mul continuous_const)).aestronglyMeasurable
    have h1 := eLpNorm_le_eLpNorm_of_exponent_le (μ := muK ε) (p := 1) (q := ENNReal.ofReal p)
      (by simpa using hp) hm
    rw [eLpNorm_one_eq_lintegral_enorm,
      eLpNorm_eq_lintegral_rpow_enorm (by simp; linarith) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp0, one_div] at h1
    exact (ENNReal.le_rpow_inv_iff (by linarith)).1 h1
  refine ⟨(Continuous.aestronglyMeasurable ?_), ?_⟩
  · exact ((continuous_const.inner (hπ.continuous_apply u)).norm).rpow_const (fun _ => Or.inr hp0)
  unfold HasFiniteIntegral
  simp only [key]
  have hmeas : AEMeasurable (Function.uncurry fun (g : ↥(UJ ε)) (k : ↥(KG ε)) =>
      ‖f ((k : ↥(UJ ε))⁻¹ * g)‖ₑ ^ p) (μ.prod (muK ε)) := by
    have hc : Continuous (fun x : ↥(UJ ε) × ↥(KG ε) => f ((x.2 : ↥(UJ ε))⁻¹ * x.1)) :=
      hfc.comp ((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst)
    exact (hc.measurable.enorm.pow_const p).aemeasurable
  have hCp : ENNReal.ofReal C ^ p ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp0 ENNReal.ofReal_ne_top
  calc ∫⁻ g, ‖⟪v, π g u⟫_ℂ‖ₑ ^ p ∂μ
      ≤ ∫⁻ g, ENNReal.ofReal C ^ p * ∫⁻ k, ‖f ((k : ↥(UJ ε))⁻¹ * g)‖ₑ ^ p ∂(muK ε) ∂μ := by
        refine lintegral_mono fun g => (ENNReal.rpow_le_rpow (hpt g) hp0).trans ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0]
        gcongr
        exact hJ g
    _ = ENNReal.ofReal C ^ p * ∫⁻ g, ∫⁻ k, ‖f ((k : ↥(UJ ε))⁻¹ * g)‖ₑ ^ p ∂(muK ε) ∂μ :=
        lintegral_const_mul' _ _ hCp
    _ = ENNReal.ofReal C ^ p * ∫⁻ k, ∫⁻ g, ‖f ((k : ↥(UJ ε))⁻¹ * g)‖ₑ ^ p ∂μ ∂(muK ε) := by
        rw [lintegral_lintegral_swap hmeas]
    _ = ENNReal.ofReal C ^ p * ∫⁻ k : ↥(KG ε), ∫⁻ g, ‖f g‖ₑ ^ p ∂μ ∂(muK ε) := by
        congr 1
        refine lintegral_congr fun k => ?_
        exact lintegral_mul_left_eq_self (fun g => ‖f g‖ₑ ^ p) _
    _ < ∞ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top hCp.lt_top (ENNReal.mul_lt_top hI (measure_lt_top _ _))

end GlobalTheory
end

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_matrixCoeff_K_average_left : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → ∀ (p : ℝ), 1 ≤ p → ∀ φ : KG ε → ℂ, Continuous φ → ∀ u u' : U, Integrable (fun g => ‖⟪u', π g u⟫_ℂ‖ ^ p) μ → Integrable (fun g => ‖⟪∫ k, φ k • π k u' ∂(muK ε), π g u⟫_ℂ‖ ^ p) μ := by
  atlas_forward_decl GlobalTheory.integrable_inner_rpow_avg_left
end

section
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

noncomputable section
namespace GlobalTheory.KAvgFinite

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Kt : Type}

def FinMult (s : Kt → (H →L[ℂ] H)) : Prop :=
  ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → (∀ k, ∀ w ∈ S, s k w ∈ S) →
    (∀ S' : Submodule ℂ H, S' ≤ S → (∀ k, ∀ w ∈ S', s k w ∈ S') → S' = ⊥ ∨ S' = S) →
    FiniteDimensional ℂ (sSup {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧ ∀ k, ∀ w ∈ S, T (s k w) = s k (T w)} :
      Submodule ℂ H)

theorem orth_stable {s : Kt → (H →L[ℂ] H)} (hs : ∀ k v, ‖s k v‖ = ‖v‖) (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] (hW : ∀ k, ∀ w ∈ W, s k w ∈ W) (k : Kt) : ∀ y ∈ Wᗮ, s k y ∈ Wᗮ := by
  intro y hy
  let L : W →ₗ[ℂ] W := (s k : H →ₗ[ℂ] H).restrict (hW k)
  have hinj : Function.Injective L := by
    intro a b hab
    have h1 : s k ((a : H) - b) = 0 := by
      have := congrArg Subtype.val hab
      simp only [L, LinearMap.restrict_apply] at this
      rw [map_sub]
      exact sub_eq_zero.2 this
    have h2 : ‖(a : H) - b‖ = 0 := by rw [← hs k, h1, norm_zero]
    exact Subtype.ext (sub_eq_zero.1 (norm_eq_zero.1 h2))
  have hsurj : Function.Surjective L := LinearMap.injective_iff_surjective.1 hinj
  let I : H →ₗᵢ[ℂ] H := ⟨(s k : H →ₗ[ℂ] H), fun v => hs k v⟩
  rw [Submodule.mem_orthogonal]
  intro w hw
  obtain ⟨w', hw'⟩ := hsurj ⟨w, hw⟩
  have e : w = s k w' := (congrArg Subtype.val hw').symm
  rw [e]
  have := I.inner_map_map (w' : H) y
  simp only [I, LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe] at this
  rw [this]
  exact (Submodule.mem_orthogonal _ _).1 hy _ w'.2

theorem starProjection_comm {s : Kt → (H →L[ℂ] H)} (hs : ∀ k v, ‖s k v‖ = ‖v‖) (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] (hW : ∀ k, ∀ w ∈ W, s k w ∈ W) (k : Kt) (y : H) :
    W.starProjection (s k y) = s k (W.starProjection y) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal (hW k _ (W.starProjection_apply_mem y))
  rw [← map_sub]
  exact orth_stable hs W hW k _ (W.sub_starProjection_mem_orthogonal y)

theorem finiteDimensional_iSup_range {s : Kt → (H →L[ℂ] H)} (hs : ∀ k v, ‖s k v‖ = ‖v‖) (hA : FinMult s) :
    ∀ (d : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E], Module.finrank ℂ E ≤ d →
    ∀ (ρ : Kt → Module.End ℂ E) (ι : Type) (T : ι → E →ₗ[ℂ] H), (∀ i k x, T i (ρ k x) = s k (T i x)) →
    FiniteDimensional ℂ (⨆ i, LinearMap.range (T i) : Submodule ℂ H) := by
  intro d
  induction d with
  | zero =>
    intro E _ _ _ hd ρ ι T hT
    have hsub : Subsingleton E := (Module.finrank_zero_iff (R := ℂ) (M := E)).1 (by omega)
    have : (⨆ i, LinearMap.range (T i)) = ⊥ := by
      refine iSup_eq_bot.2 fun i => ?_
      rw [LinearMap.range_eq_bot]
      ext x
      rw [Subsingleton.elim x 0]
      simp
    rw [this]
    infer_instance
  | succ d ih =>
    intro E _ _ _ hd ρ ι T hT
    by_cases hirr : ∀ E' : Submodule ℂ E, (∀ k, ∀ x ∈ E', ρ k x ∈ E') → E' = ⊥ ∨ E' = ⊤
    · by_cases h0 : ∀ i, T i = 0
      · have : (⨆ i, LinearMap.range (T i)) = ⊥ := by
          refine iSup_eq_bot.2 fun i => ?_
          rw [h0 i, LinearMap.range_zero]
        rw [this]
        infer_instance
      push_neg at h0
      obtain ⟨i0, hi0⟩ := h0
      have hker : LinearMap.ker (T i0) = ⊥ := by
        rcases hirr (LinearMap.ker (T i0)) (fun k x hx => by
          rw [LinearMap.mem_ker] at hx ⊢
          rw [hT, hx, map_zero]) with h | h
        · exact h
        · exact absurd (LinearMap.ker_eq_top.1 h) hi0
      set S := LinearMap.range (T i0) with hSdef
      have hSst : ∀ k, ∀ w ∈ S, s k w ∈ S := by
        rintro k _ ⟨x, rfl⟩
        exact ⟨ρ k x, hT i0 k x⟩
      have hSirr : ∀ S' : Submodule ℂ H, S' ≤ S → (∀ k, ∀ w ∈ S', s k w ∈ S') → S' = ⊥ ∨ S' = S := by
        intro S' hle hst
        rcases hirr (S'.comap (T i0)) (fun k x hx => by
          show T i0 (ρ k x) ∈ S'
          rw [hT]
          exact hst k _ hx) with h | h
        · left
          rw [eq_bot_iff]
          intro y hy
          obtain ⟨x, rfl⟩ := hle hy
          have : x ∈ S'.comap (T i0) := hy
          rw [h, Submodule.mem_bot] at this
          rw [this, map_zero]
          exact Submodule.zero_mem _
        · right
          apply le_antisymm hle
          rintro _ ⟨x, rfl⟩
          have : x ∈ S'.comap (T i0) := by rw [h]; trivial
          exact this
      haveI hfin := hA S inferInstance hSst hSirr
      refine Submodule.finiteDimensional_of_le
        (S₂ := sSup {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧ ∀ k, ∀ w ∈ S, T (s k w) = s k (T w)})
        (iSup_le fun i => ?_)
      let e := LinearEquiv.ofInjective (T i0) (LinearMap.ker_eq_bot.1 hker)
      obtain ⟨C, hC⟩ := Submodule.exists_isCompl S
      let P : H →ₗ[ℂ] S := Submodule.linearProjOfIsCompl S C hC
      let B : H →ₗ[ℂ] H := T i ∘ₗ e.symm.toLinearMap ∘ₗ P
      have hB : ∀ x, B (T i0 x) = T i x := by
        intro x
        have h1 : (e x : H) = T i0 x := LinearEquiv.ofInjective_apply _ _
        have h2 : P (T i0 x) = e x := by
          rw [← h1]
          exact Submodule.linearProjOfIsCompl_apply_left hC (e x)
        simp only [B, LinearMap.comp_apply, LinearEquiv.coe_coe, h2, LinearEquiv.symm_apply_apply]
      have hR : LinearMap.range (T i) = S.map B := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨T i0 x, ⟨x, rfl⟩, hB x⟩
        · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
          exact ⟨x, (hB x).symm⟩
      apply le_sSup
      refine ⟨B, hR, ?_⟩
      rintro k _ ⟨x, rfl⟩
      rw [← hT i0 k x, hB, hB, hT]
    · push_neg at hirr
      obtain ⟨E', hE'st, hbot, htop⟩ := hirr
      have h1 : Module.finrank ℂ E' < Module.finrank ℂ E := Submodule.finrank_lt htop
      let ρ' : Kt → Module.End ℂ E' := fun k => (ρ k).restrict (hE'st k)
      let T' : ι → E' →ₗ[ℂ] H := fun i => T i ∘ₗ E'.subtype
      have hT' : ∀ i k x, T' i (ρ' k x) = s k (T' i x) := fun i k x => hT i k x
      haveI hW' := ih E' (by omega) ρ' ι T' hT'
      set W' := ⨆ i, LinearMap.range (T' i) with hW'def
      have hW'st : ∀ k, ∀ w ∈ W', s k w ∈ W' := by
        intro k w hw
        refine Submodule.iSup_induction _ (motive := fun w => s k w ∈ W') hw ?_ ?_ ?_
        · rintro i _ ⟨x, rfl⟩
          exact Submodule.mem_iSup_of_mem i ⟨ρ' k x, hT' i k x⟩
        · rw [map_zero]; exact Submodule.zero_mem _
        · intro a b ha hb
          rw [map_add]
          exact Submodule.add_mem _ ha hb
      let Q : H →ₗ[ℂ] H := LinearMap.id - (W'.starProjection : H →ₗ[ℂ] H)
      have hQ : ∀ y, Q y = y - W'.starProjection y := fun y => rfl
      have hQK : ∀ k y, Q (s k y) = s k (Q y) := by
        intro k y
        rw [hQ, hQ, map_sub, starProjection_comm hs W' hW'st]
      have hQW : ∀ w ∈ W', Q w = 0 := by
        intro w hw
        rw [hQ, Submodule.starProjection_eq_self_iff.2 hw, sub_self]
      have hle : ∀ i, E' ≤ LinearMap.ker (Q ∘ₗ T i) := by
        intro i x hx
        rw [LinearMap.mem_ker, LinearMap.comp_apply]
        exact hQW _ (Submodule.mem_iSup_of_mem i ⟨⟨x, hx⟩, rfl⟩)
      let ρ'' : Kt → Module.End ℂ (E ⧸ E') := fun k => E'.mapQ E' (ρ k) (fun x hx => hE'st k x hx)
      let T'' : ι → (E ⧸ E') →ₗ[ℂ] H := fun i => E'.liftQ (Q ∘ₗ T i) (hle i)
      have hT'' : ∀ i k x, T'' i (ρ'' k x) = s k (T'' i x) := by
        intro i k x
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          simp only [ρ'', T'', Submodule.mapQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply]
          rw [hT, hQK]
      have h2 : Module.finrank ℂ (E ⧸ E') < Module.finrank ℂ E := by
        have := Submodule.finrank_quotient_add_finrank E'
        have h3 : Module.finrank ℂ E' ≠ 0 := fun h => hbot (Submodule.finrank_eq_zero.1 h)
        omega
      haveI hW'' := ih (E ⧸ E') (by omega) ρ'' ι T'' hT''
      refine Submodule.finiteDimensional_of_le (S₂ := W' ⊔ ⨆ i, LinearMap.range (T'' i)) (iSup_le fun i => ?_)
      rintro _ ⟨x, rfl⟩
      have e : T i x = W'.starProjection (T i x) + Q (T i x) := by rw [hQ]; abel
      rw [e]
      refine Submodule.add_mem_sup (W'.starProjection_apply_mem _) ?_
      exact Submodule.mem_iSup_of_mem i ⟨Submodule.Quotient.mk x, by simp [T'']⟩

end GlobalTheory.KAvgFinite

namespace GlobalTheory.KAvgFinite

open GlobalTheory.SchurProjCompare (onMatrices onMatrices_umat isURepOn_iff)

variable {n : ℕ} {ε : Fin n → Bool} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem onMatrices_kg (π : UJ ε →* (U →L[ℂ] U)) (k : KG ε) : onMatrices (⇑π) (toMK k) = π k :=
  onMatrices_umat _ _

theorem isURepOn_onMatrices {π : UJ ε →* (U →L[ℂ] U)} (hπ : IsUnitaryRep π) :
    IsURepOn (UJset ε) (onMatrices ⇑π) := by
  rw [isURepOn_iff]
  have e : (fun g : UJ ε => onMatrices (⇑π) (umat g)) = ⇑π := funext (onMatrices_umat _)
  rw [e]
  exact ⟨π.map_one, π.map_mul, hπ.norm_apply, hπ.continuous_apply⟩

theorem isIrredOn_onMatrices {π : UJ ε →* (U →L[ℂ] U)} (hI : IsTopIrreducible π) :
    IsIrredOn (UJset ε) (onMatrices ⇑π) := by
  intro S hS hst
  exact hI.2 S ⟨hS, fun g v hv => by
    have := hst (umat g) g.2 v hv
    rwa [onMatrices_umat] at this⟩

theorem finMult_of_isAdmOn {π : UJ ε →* (U →L[ℂ] U)} (h : GlobalTheory.LinRed.IsAdmOn (UJset ε) (onMatrices ⇑π)) :
    FinMult (fun k : KG ε => π (k : UJ ε)) := by
  intro S hS hst hirr
  have hK : ∀ S' : Submodule ℂ U, GlobalTheory.LinRed.IsKStable (UJset ε) (onMatrices ⇑π) S' ↔
      ∀ k : KG ε, ∀ w ∈ S', π k w ∈ S' := by
    intro S'
    unfold GlobalTheory.LinRed.IsKStable
    rw [GlobalTheory.HCUnitary.maxCpt_UJset, ← range_toMK]
    constructor
    · intro h k w hw
      rw [← onMatrices_kg]
      exact h _ ⟨k, rfl⟩ w hw
    · rintro h _ ⟨k, rfl⟩ w hw
      rw [onMatrices_kg]
      exact h k w hw
  haveI := h.2.2.2 S hS ((hK S).2 hst) (fun S' hle h' => hirr S' hle ((hK S').1 h'))
  refine Submodule.finiteDimensional_of_le (S₂ := sSup {S' | ∃ T : U →ₗ[ℂ] U, S' = S.map T ∧
    ∀ k ∈ GlobalTheory.LinRed.maxCpt (UJset ε), ∀ w ∈ S, T (onMatrices (⇑π) k w) = onMatrices (⇑π) k (T w)})
    (sSup_le_sSup ?_)
  rintro _ ⟨T, rfl, hT⟩
  refine ⟨T, rfl, ?_⟩
  rw [GlobalTheory.HCUnitary.maxCpt_UJset, ← range_toMK]
  rintro _ ⟨k, rfl⟩ w hw
  rw [onMatrices_kg]
  exact hT k w hw

end GlobalTheory.KAvgFinite

namespace GlobalTheory.KAvgFinite

open GlobalTheory.SchurProjCompare (onMatrices)

variable {n : ℕ} {ε : Fin n → Bool} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem integrable_avg {π : UJ ε →* (U →L[ℂ] U)} (hπ : IsUnitaryRep π) {ψ : KG ε → ℂ} (hψ : Continuous ψ)
    (u : U) : Integrable (fun k : KG ε => ψ k • π k u) (muK ε) :=
  (hψ.smul ((hπ.continuous_apply u).comp continuous_subtype_val)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

variable [CompleteSpace U]

theorem exists_fix {π : UJ ε →* (U →L[ℂ] U)} (hπ : IsUnitaryRep π) (S : Submodule ℂ U) [FiniteDimensional ℂ S]
    (hS : ∀ k ∈ KG ε, ∀ u ∈ S, π k u ∈ S) :
    ∃ e : KG ε → ℂ, GlobalTheory.TypeSum.KFinFun ε e ∧ ∀ s ∈ S, ∫ k, e k • π k s ∂(muK ε) = s := by
  let b := Module.finBasis ℂ S
  let m := Module.finrank ℂ S
  let w : Fin m → KG ε → S := fun i k => ⟨π k (b i), hS k k.2 _ (b i).2⟩
  have hwc : ∀ i, Continuous (w i) := fun i =>
    ((hπ.continuous_apply (b i : U)).comp continuous_subtype_val).subtype_mk _
  let F : Fin m × Fin m → KG ε → ℂ := fun p k => b.coord p.2 (w p.1 k)
  have hFc : ∀ p, Continuous (F p) := fun p =>
    (LinearMap.continuous_of_finiteDimensional (b.coord p.2)).comp (hwc p.1)
  have hV : (fun p => F p 1) ∈ GlobalTheory.KFinReproduce.intSpace F hFc := by
    have hcl : IsClosed ((GlobalTheory.KFinReproduce.intSpace F hFc : Submodule ℂ _) : Set (Fin m × Fin m → ℂ)) :=
      Submodule.closed_of_finiteDimensional _
    refine hcl.closure_subset (Metric.mem_closure_iff.2 fun δ hδ => ?_)
    obtain ⟨e, he, hb⟩ := GlobalTheory.KFinApprox.approx_identity n ε (Fin m × Fin m) F
      (continuous_prod_of_discrete_left.2 fun p => hFc p) Set.univ isCompact_univ δ hδ
    refine ⟨fun p => ∫ k, e k * F p k ∂(muK ε), ⟨e, he, fun p => rfl⟩, ?_⟩
    rw [dist_pi_lt_iff hδ]
    intro p
    rw [dist_eq_norm]
    exact hb p trivial
  obtain ⟨e, he, hej⟩ := hV
  have hec := GlobalTheory.KFinReproduce.continuous_of_kFinFun he
  refine ⟨e, he, ?_⟩
  have hexp : ∀ i (k : KG ε), π k (b i : U) = ∑ j, F (i, j) k • (b j : U) := by
    intro i k
    have h := b.sum_repr (w i k)
    have h2 : π k (b i : U) = ((w i k : S) : U) := rfl
    conv_lhs => rw [h2, ← h]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul]
    rfl
  have hbasis : ∀ i, ∫ k, e k • π k (b i : U) ∂(muK ε) = b i := by
    intro i
    calc ∫ k, e k • π k (b i : U) ∂(muK ε) = ∫ k, ∑ j, (e k * F (i, j) k) • (b j : U) ∂(muK ε) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only [hexp, Finset.smul_sum, smul_smul]
      _ = ∑ j, (∫ k, e k * F (i, j) k ∂(muK ε)) • (b j : U) := by
          rw [integral_finset_sum _ fun j _ =>
            ((GlobalTheory.KFinReproduce.integrable_mul hec (hFc (i, j))).smul_const _)]
          simp only [integral_smul_const]
      _ = ∑ j, F (i, j) 1 • (b j : U) := by simp only [hej]
      _ = b i := by
          rw [← hexp i 1]
          simp
  let A : U →ₗ[ℂ] U :=
    { toFun := fun v => ∫ k, e k • π k v ∂(muK ε)
      map_add' := fun x y => by
        simp only [map_add, smul_add]
        exact integral_add (integrable_avg hπ hec x) (integrable_avg hπ hec y)
      map_smul' := fun c x => by
        simp only [map_smul, smul_comm (e _) c, RingHom.id_apply]
        exact integral_smul c _ }
  have hext : A ∘ₗ S.subtype = S.subtype := b.ext fun i => hbasis i
  intro s hs
  exact LinearMap.congr_fun hext ⟨s, hs⟩

theorem finiteDimensional_range {π : UJ ε →* (U →L[ℂ] U)} (hπ : IsUnitaryRep π)
    (hA : FinMult (fun k : KG ε => π (k : UJ ε))) {e : KG ε → ℂ} (he : GlobalTheory.TypeSum.KFinFun ε e) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun u : U => ∫ k, e k • π k u ∂(muK ε))) := by
  obtain ⟨F, hFf, heF, hFc, hFt⟩ := he
  let ρ : KG ε → Module.End ℂ F := fun k₀ =>
    { toFun := fun ψ => ⟨fun k => (ψ : KG ε → ℂ) (k₀⁻¹ * k), (hFt ψ ψ.2 k₀⁻¹).1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let T : U → F →ₗ[ℂ] U := fun u =>
    { toFun := fun ψ => ∫ k, (ψ : KG ε → ℂ) k • π k u ∂(muK ε)
      map_add' := fun ψ χ => by
        simp only [Submodule.coe_add, Pi.add_apply, add_smul]
        exact integral_add (integrable_avg hπ (hFc ψ ψ.2) u) (integrable_avg hπ (hFc χ χ.2) u)
      map_smul' := fun c ψ => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact integral_smul c _ }
  have hT : ∀ u k₀ ψ, T u (ρ k₀ ψ) = π k₀ (T u ψ) := by
    intro u k₀ ψ
    show ∫ k, (ψ : KG ε → ℂ) (k₀⁻¹ * k) • π k u ∂(muK ε) = π k₀ (∫ k, (ψ : KG ε → ℂ) k • π k u ∂(muK ε))
    rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_avg hπ (hFc ψ ψ.2) u)]
    rw [← integral_mul_left_eq_self (fun k => (ψ : KG ε → ℂ) (k₀⁻¹ * k) • π k u) k₀]
    congr 1
    funext k
    simp only [inv_mul_cancel_left, map_smul, Subgroup.coe_mul, map_mul, ContinuousLinearMap.mul_apply]
  haveI := finiteDimensional_iSup_range (s := fun k : KG ε => π (k : UJ ε)) (fun k v => hπ.norm_apply k v) hA
    (Module.finrank ℂ F) F le_rfl ρ U T (fun u k ψ => hT u k ψ)
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ u, LinearMap.range (T u)) (Submodule.span_le.2 ?_)
  rintro _ ⟨u, rfl⟩
  exact Submodule.mem_iSup_of_mem u ⟨⟨e, heF⟩, rfl⟩

end GlobalTheory.KAvgFinite

open GlobalTheory.SchurProjCompare (onMatrices) in

theorem GlobalTheory.KAvgFinite.fix_and_finite_range : GlobalTheory.Published.IrreducibleUnitaryAdmissible → ∀ (n : ℕ) (ε : Fin n → Bool) (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → IsTopIrreducible π → ∀ S : Submodule ℂ U, FiniteDimensional ℂ S → (∀ k ∈ KG ε, ∀ u ∈ S, π k u ∈ S) → ∃ φ : KG ε → ℂ, Continuous φ ∧ (∀ s ∈ S, ∫ k, φ k • π k s ∂(muK ε) = s) ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun u : U => ∫ k, φ k • π k u ∂(muK ε))) := by
  intro hadm n ε U _ _ _ π hπ hI S hS hst
  have hA := GlobalTheory.KAvgFinite.finMult_of_isAdmOn (hadm n (UJset ε) (GlobalTheory.HCUnitary.isLinRed_UJset ε) U
    (onMatrices ⇑π) (GlobalTheory.KAvgFinite.isURepOn_onMatrices hπ) (GlobalTheory.KAvgFinite.isIrredOn_onMatrices hI))
  obtain ⟨e, he, hfix⟩ := GlobalTheory.KAvgFinite.exists_fix hπ S hst
  exact ⟨e, GlobalTheory.KFinReproduce.continuous_of_kFinFun he, hfix, GlobalTheory.KAvgFinite.finiteDimensional_range hπ hA he⟩
end
end

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_K_projector_finite_dim : GlobalTheory.Published.IrreducibleUnitaryAdmissible → ∀ (n : ℕ) (ε : Fin n → Bool) (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → IsTopIrreducible π → ∀ S : Submodule ℂ U, FiniteDimensional ℂ S → (∀ k ∈ KG ε, ∀ u ∈ S, π k u ∈ S) → ∃ φ : KG ε → ℂ, Continuous φ ∧ (∀ s ∈ S, ∫ k, φ k • π k s ∂(muK ε) = s) ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun u : U => ∫ k, φ k • π k u ∂(muK ε))) := by
  atlas_forward_decl GlobalTheory.KAvgFinite.fix_and_finite_range
end

section
section
noncomputable section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
namespace GlobalTheory.TempKFin

theorem isTemperedKFin_of_isTempered : GlobalTheory.Published.IrreducibleUnitaryAdmissible → ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → IsTopIrreducible π → GlobalTheory.Orb.IsTempered μ π → IsTemperedKFin ε μ π := by
  intro hadm n ε μ _ U _ _ _ π hπ hirr ⟨v, hv0, hv⟩ S hS hSK s hs s' hs' e he
  obtain ⟨φ, hφc, hφS, hφR⟩ := GlobalTheory.T.exists_K_projector_finite_dim hadm n ε U π hπ hirr S hS hSK
  set D : Submodule ℂ U := Submodule.span ℂ (Set.range fun g => π g v) with hD
  have hDdense : D.topologicalClosure = ⊤ := by
    have hinv : ∀ g, ∀ w ∈ D.topologicalClosure, π g w ∈ D.topologicalClosure := by
      intro g w hw
      have hmap : ∀ x ∈ (D : Set U), π g x ∈ (D : Set U) := by
        intro x hx
        have hle : D ≤ D.comap ((π g : U →L[ℂ] U) : U →ₗ[ℂ] U) := by
          rw [hD, Submodule.span_le]
          rintro _ ⟨h, rfl⟩
          exact Submodule.subset_span ⟨g * h, by simp [map_mul]⟩
        exact hle hx
      have hw' : w ∈ closure (D : Set U) := by rwa [← Submodule.topologicalClosure_coe]
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
      exact map_mem_closure (π g).continuous hw' hmap
    rcases hirr.2 D.topologicalClosure ⟨D.isClosed_topologicalClosure, hinv⟩ with h | h
    · exfalso
      apply hv0
      have : v ∈ D.topologicalClosure := D.le_topologicalClosure (Submodule.subset_span ⟨1, by simp⟩)
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
    · exact h
  have hint : ∀ u : U, Integrable (fun k : KG ε => φ k • π k u) (muK ε) := fun u =>
    (hφc.smul ((hπ.continuous_apply u).comp continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let T : U →ₗ[ℂ] U :=
    { toFun := fun u => ∫ k, φ k • π k u ∂(muK ε)
      map_add' := fun a b => by
        simp only [map_add, smul_add]
        exact integral_add (hint a) (hint b)
      map_smul' := fun c a => by
        simp only [map_smul, RingHom.id_apply]
        simp only [smul_comm (φ _) c]
        exact integral_smul c _ }
  have hTapp : ∀ u, T u = ∫ k, φ k • π k u ∂(muK ε) := fun u => rfl
  have hTc : Continuous T := by
    refine AddMonoidHomClass.continuous_of_bound T (∫ k, ‖φ k‖ ∂(muK ε)) fun u => ?_
    calc ‖T u‖ ≤ ∫ k, ‖φ k‖ * ‖u‖ ∂(muK ε) :=
          norm_integral_le_of_norm_le ((hφc.norm.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)).mul_const _)
            (Eventually.of_forall fun k => by rw [norm_smul, hπ.norm_apply])
      _ = (∫ k, ‖φ k‖ ∂(muK ε)) * ‖u‖ := integral_mul_const _ _
  haveI hR : FiniteDimensional ℂ (LinearMap.range T) := by
    rw [← Submodule.span_eq (LinearMap.range T), LinearMap.coe_range]
    exact hφR
  have hsurj : ∀ x : U, ∃ u ∈ D, T u = T x := by
    intro x
    haveI : FiniteDimensional ℂ (D.map T) := Submodule.finiteDimensional_of_le (LinearMap.map_le_range)
    have hcl : IsClosed ((D.map T : Submodule ℂ U) : Set U) := Submodule.closed_of_finiteDimensional _
    have hx : x ∈ closure (D : Set U) := by
      rw [← Submodule.topologicalClosure_coe, hDdense]; trivial
    have : T x ∈ closure ((D.map T : Submodule ℂ U) : Set U) := by
      rw [Submodule.map_coe]
      exact image_closure_subset_closure_image hTc ⟨x, hx, rfl⟩
    rw [hcl.closure_eq] at this
    obtain ⟨u, hu, hTu⟩ := this
    exact ⟨u, hu, hTu⟩
  obtain ⟨u, hu, hTu⟩ := hsurj s
  obtain ⟨u', hu', hTu'⟩ := hsurj s'
  rw [hTapp, hTapp, hφS s hs] at hTu
  rw [hTapp, hTapp, hφS s' hs'] at hTu'
  have hp : (1 : ℝ) ≤ 2 + e := by linarith
  have h0 := GlobalTheory.T.integrable_matrixCoeff_cyclic_span n ε μ U π hπ (2 + e) hp v (hv e he) u hu u' hu'
  have h1 := GlobalTheory.T.integrable_matrixCoeff_K_average_right n ε μ U π hπ (2 + e) hp φ hφc u u' h0
  have h2 := GlobalTheory.T.integrable_matrixCoeff_K_average_left n ε μ U π hπ (2 + e) hp φ hφc (∫ k, φ k • π k u ∂(muK ε)) u' h1
  rw [hTu, hTu'] at h2
  exact h2

end GlobalTheory.TempKFin

end
end

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tempered_K_finite_coefficients : GlobalTheory.Published.IrreducibleUnitaryAdmissible → ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → IsTopIrreducible π → GlobalTheory.Orb.IsTempered μ π → IsTemperedKFin ε μ π := by
  atlas_forward_decl GlobalTheory.TempKFin.isTemperedKFin_of_isTempered
end

section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.Published

theorem pseudoCoefficientUpq_of_hypotheses (hUA : IrreducibleUnitaryAdmissible) (hKA : KFiniteCoefficientsAnalytic)
    (hCR : CharacterRegularityFiniteLength) (hPE : PseudoCoefficientExistence) (hCO : CuspidalOrbitalIntegrals) :
    PseudoCoefficientUpq := by
  intro n ε X _ _ σ h μ _
  haveI := h.1
  obtain ⟨f, hf, hbi, hpt⟩ := hPE n ε X σ h μ
  have hadm : IsAdmRep ε σ := (GlobalTheory.T.admissible_unitary_K_finite.1 hUA) n ε X σ h.2.2.1 h.2.2.2.1
  have hfl : HasFiniteLength ε σ := (GlobalTheory.T.irreducible_admissible_finite_length hKA n ε X σ ⟨h.2.1, hadm, h.2.2.2.1⟩).2
  obtain ⟨Θ, hΘ⟩ := hCR n ε μ X σ hadm hfl
  have hch : IsCharFn (ujMat ε) μ (ujRep h.2.2.1) Θ := hΘ.1
  refine ⟨f, hbi, ⟨hf, hpt.1, ?_, ?_, ⟨Θ, hch, ?_⟩⟩⟩
  · intro U _ _ _ π hu hi ht hne
    exact hpt.2 U π hu hi (GlobalTheory.T.tempered_K_finite_coefficients hUA n ε μ U π hu hi ht) hne
  · intro s hs hnc dt _ _
    exact (hCO n ε X σ h μ f hf hbi hpt Θ hch s hs dt).2 hnc
  · intro s hs hc dt _ _
    exact (hCO n ε X σ h μ f hf hbi hpt Θ hch s hs dt).1 hc

end GlobalTheory.Published

end
end
