import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinConstantTermPartDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraNormRatGaussianExtensionOfPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGaussianExtensionUnitsQuotUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableGaussianExtensionNormRpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeSummandWeightTwoBound

section
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem GlobalTheory.HeckeTwo.summable_eisClass_two : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
    Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 2 σ z) := by
  intro F _ _ _ 𝔞 𝔟 σ hσ z hz
  obtain ⟨C, hC⟩ := GlobalTheory.T.hilbertEisensteinLatticeSummand_weightTwo_bound F σ hσ z hz
  have hS := (GlobalTheory.T.summable_gaussianExtension_norm_rpow F 𝔞 𝔟 (1 + σ.re) (by linarith) (GlobalTheory.T.finite_gaussianExtension_units_quot_units F)).mul_left C
  refine Summable.of_norm_bounded hS fun c => ?_
  have hp : c.out.1 ≠ 0 := c.out.2.2.2
  have e : |((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F c.out.1) : ℚ) : ℝ)| =
      ∏ τ : F →+* ℝ, ((τ c.out.1.1) ^ 2 + (τ c.out.1.2) ^ 2) := by
    rw [GlobalTheory.T.algebraNorm_rat_gaussianExtensionOfPair F c.out.1.1 c.out.1.2]
    exact abs_of_nonneg (Finset.prod_nonneg fun τ _ => by positivity)
  rw [e]
  exact hC _ hp
end

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_hilbertEisensteinLatticeClass_weight_two : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 2 σ z) := by
  atlas_forward_decl GlobalTheory.HeckeTwo.summable_eisClass_two
