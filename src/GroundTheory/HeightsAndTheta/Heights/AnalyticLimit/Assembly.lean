module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StBoundingKaehler
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassError
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassReplace
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassStep
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.GreenMassZero
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBoundingKaehler
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassZero
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UniformIntegrability
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open GroundTheory.Heights₂.Heights.LowerBoundFree

theorem BoundingKaehler.full : BoundingKaehler.Statement := BoundingKaehler.proof

theorem GreenMassZero.full : GreenMassZero.Statement := GreenMassZero.proof

theorem UniformIntegrability.of_greenMass (h₁ : GreenMassStep.Statement)
    (h₂ : GreenMassReplace.Statement) (h₃ : GreenMassError.Statement) :
    UniformIntegrability.Statement :=
  UniformIntegrability.proof GreenMassZero.full h₁ h₂ h₃

end GroundTheory.Heights₂.Heights.AnalyticLimit
