module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodDoubleStepUnfoldingOfDescentStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodEvaluationUnfoldingOfWittDescentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodThetaLiftUnfoldingStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftPeriodRankZeroFubiniCompactQuotientStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepEqTwoThetaColumnLiftsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiPeriodUnfoldingOfWittDescentStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedThetaUnfoldingOfWeilDatumDescentStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawThetaIdentityStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCoreStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem unfoldings_of_chain :
    ∀ D : D7, UnfBF D ∧ EvalBF D ∧ UnfFB D ∧ DoubleStep D ∧ LastLaw D ∧ IT D ∧ ContrLaw D ∧ SeeLast D := by
  intro D
  have hD : Descent D := GlobalTheory.T.weilDatum_descends_to_wittCore D
  exact ⟨GlobalTheory.T.besselPeriod_thetaLift_unfolding D hD, GlobalTheory.T.bessel_period_evaluation_unfolding_of_witt_descent D hD, GlobalTheory.T.fourierJacobi_period_unfolding_of_witt_descent D hD, GlobalTheory.T.besselPeriod_double_step_unfolding_of_descent D hD,
    GlobalTheory.T.doubleLiftPeriod_rankZero_fubini_compactQuotient D, GlobalTheory.T.iteratedThetaUnfolding_of_weilDatumDescent D hD, GlobalTheory.T.doubleStep_eq_two_thetaColumnLifts D, GlobalTheory.T.lastSeeSaw_thetaIdentity D⟩

end GlobalTheory.Unf
