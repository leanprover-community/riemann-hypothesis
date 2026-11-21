import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerGaugeBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerLinearity

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.DampedWhittakerLimit

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem continuous_mp (s : ℂ) : Continuous fun h : Fˣ => mp h s := by
  have hc : Continuous fun h : Fˣ => (((modulus (h : F) : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.comp
      (NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val))
  simp only [mp]
  refine hc.cpow continuous_const fun h => ?_
  have h0 : (0 : ℝ) < (modulus (h : F) : ℝ) := by exact_mod_cast modulus_pos h.ne_zero
  exact Complex.ofReal_mem_slitPlane.2 h0



end

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]


end GlobalTheory.CompanionTheory.DampedWhittakerLimit

