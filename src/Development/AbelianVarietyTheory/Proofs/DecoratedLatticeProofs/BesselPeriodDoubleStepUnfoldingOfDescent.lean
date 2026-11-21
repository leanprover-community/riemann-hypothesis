import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodThetaLiftUnfoldingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiPeriodUnfoldingOfWittDescent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselDoubleStepUnfoldingOfUnfoldingsAndLink
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLevelStepFourierJacobiPeriodLink

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem doubleStep_of_descent : ∀ D : D7, Descent D → DoubleStep D := fun D hD =>
  GlobalTheory.T.besselDoubleStepUnfolding_of_unfoldings_and_link D (GlobalTheory.T.besselPeriod_thetaLift_unfolding D hD) (GlobalTheory.T.fourierJacobi_period_unfolding_of_witt_descent D hD) (GlobalTheory.T.bessel_level_step_fourierJacobi_period_link D) (GlobalTheory.T.fourierJacobiHandOff_automorphic D) (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D)

end GlobalTheory.Unf
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriod_double_step_unfolding_of_descent : ∀ D : D7, Descent D → DoubleStep D := by
  atlas_forward_decl GlobalTheory.Unf.doubleStep_of_descent
