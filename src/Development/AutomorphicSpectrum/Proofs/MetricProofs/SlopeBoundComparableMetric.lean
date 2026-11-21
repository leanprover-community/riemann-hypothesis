import Mathlib
import Development.WeilBound.CoreStatements.AmpleLineBundles.SlopeMaxLeOfComparableMetric
import BuildAid.ForwardExisting

section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

theorem basis_slope_degree_bound : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (r : ℕ) (b : Module.Basis (Fin r) (𝓞 K) E.carrier) (C : ℝ), 1 ≤ C → (∀ (σ : K →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ∧ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ≤ C * ∑ a, ‖w a‖ ^ 2) → E.slopeMax ≤ ((Real.log C / 2 : ℝ) : EReal) ∧ |E.normDegree ⊤| ≤ r / 2 * Real.log C :=
  @CoverDenseAlt.slopeMax_le_of_comparable_metric

end GlobalTheory.CompanionTheory.Ar
end
end

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slope_bound_comparable_metric : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (r : ℕ) (b : Module.Basis (Fin r) (𝓞 K) E.carrier) (C : ℝ), 1 ≤ C → (∀ (σ : K →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ∧ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ≤ C * ∑ a, ‖w a‖ ^ 2) → E.slopeMax ≤ ((Real.log C / 2 : ℝ) : EReal) ∧ |E.normDegree ⊤| ≤ r / 2 * Real.log C := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.basis_slope_degree_bound
