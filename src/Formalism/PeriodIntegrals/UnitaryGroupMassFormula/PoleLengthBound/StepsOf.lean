module

public import Formalism.PeriodIntegrals.LengthPoleInLift
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PiBallFromAlt
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FiltLenF
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SumAntidiagonalTuple
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.AALeAAp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Closed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.FiltOk
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.LiftMul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PiBallFrom
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PiLenHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.RestrictedDerivativeLinear
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Taylor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Vanish
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

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

theorem steps_of (hBQ : BallQuot) : Steps := by
  intro D B P j X ka wL wF G la Q S CRm T e c hOk hw hL
  have h3 := unit_columns_holds G la Q S CRm T c hOk hw
  exact ⟨image_filtration_decreasing G la T,
    pole_length_assemble G la Q S CRm T e c hOk hw hL (hasse_preserves_kernel G la) (vanishingOnQuadric G la) h3 (taylor_holds G la)
      (column_derivative G la) (restricted_derivative_linear G la) (liftMul_of Q T hOk.2.1 h3),
    ball_product_length piLen_holds hBQ G la Q S CRm T e c hOk⟩

theorem pole_length_bound_of_balls (hBQ : BallQuot) : PI.LengthPoleInLift := target filtration_length_bound sum_antidiagonalTuple (steps_of hBQ)

end PI.PoleLengthCount
