import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoIsGoodOfTsum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnHeckeEisensteinFourierTermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFourierTermWirtingerWordDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoTermIteratedFDerivSummableBound

section
noncomputable section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo

theorem bOne_isGood : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    GlobalTheory.HeckeTwo.IsGood (GlobalTheory.HeckeTwo.bOne 𝔞 𝔟) := by
  intro F _ _ _ 𝔞 𝔟
  refine GlobalTheory.T.heckeWeightTwo_isGood_of_tsum F _ (fun p σ z => fTerm σ z (p : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) ×
      NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F)).1.out.1 p.2.1) _
    (fun p σ hσ => GlobalTheory.T.contDiffOn_heckeEisensteinFourierTerm F _ _ p.1.out.2.2 σ hσ) (fun p w z hz => GlobalTheory.T.heckeFourierTerm_wirtingerWord_differentiableOn F _ _ p.1.out.2.2 w z hz)
    (GlobalTheory.T.heckeWeightTwo_term_iteratedFDeriv_summable_bound F 𝔞 𝔟) ?_
  intro σ hσ z hz
  obtain ⟨u, hu, hb⟩ := GlobalTheory.T.heckeWeightTwo_term_iteratedFDeriv_summable_bound F 𝔞 𝔟 {σ} isCompact_singleton (by simpa using hσ) {z} isCompact_singleton
    (by simpa using hz) 0
  have hs : Summable (fun p : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) =>
      fTerm σ z p.1.out.1 p.2.1) := by
    refine Summable.of_norm_bounded hu fun p => ?_
    have := hb p σ rfl z rfl
    rwa [norm_iteratedFDeriv_zero] at this
  unfold bOne
  exact (hs.tsum_prod' fun c => hs.prod_factor c).symm

end GlobalTheory.HeckeTwo
end
end

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeEisensteinNonconstantFourierSum_smoothHolomorphic : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), GlobalTheory.HeckeTwo.IsGood (GlobalTheory.HeckeTwo.bOne 𝔞 𝔟) := by
  atlas_forward_decl GlobalTheory.HeckeTwo.bOne_isGood
