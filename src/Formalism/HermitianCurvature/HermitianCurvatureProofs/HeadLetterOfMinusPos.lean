module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHL2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLMinusZeroOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLPlusZeroOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLTorus
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EventuallyLevelPointMemOpen
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Hpart1SingleEs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftRuleLevelPoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutHL

theorem headLetter_of_minusPos (hMP : MinusPosOfParts) : LevelPointCoordinates.HeadLetter :=
  headLetter_of_rest Formalism.FourierDecayAlt.P.LevelPointCoordinates.left_rule_level_point torus_action_x0 Formalism.FourierDecayAlt.P.star_rule_x0 star_torus_x0
    Formalism.FourierDecayAlt.P.LevelPointCoordinates.plusPosOfParts Formalism.FourierDecayAlt.P.plus_zero_of_parts hMP Formalism.FourierDecayAlt.P.minus_zero_of_parts

end Formalism.FourierDecayAlt.P.CutHL
