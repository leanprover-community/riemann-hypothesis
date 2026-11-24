module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsDimensionInequality
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsDimensionInequalitySteps
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsReesAlgebraDim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimensionInequality
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimensionInequalityOneGenerator
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPolynomialDimensionInequality
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPolynomialPrimeOverZeroHeight
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PQuotientHeightAddOne
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PReesAlgebraDim
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

theorem PolynomialDimensionInequality.full : PolynomialDimensionInequality.Statement.{u} :=
  PolynomialDimensionInequality.proof PolynomialPrimeOverZeroHeight.proof.{u}

theorem DimensionInequalityOneGenerator.full : DimensionInequalityOneGenerator.Statement.{u, v} :=
  DimensionInequalityOneGenerator.proof PolynomialDimensionInequality.full.{u}
    QuotientHeightAddOne.proof.{u}

theorem DimensionInequality.full : DimensionInequality.Statement.{u, v} :=
  DimensionInequality.proof DimensionInequalityOneGenerator.full.{u, v}
    DimensionInequalityOneGenerator.full.{v, v}

theorem ReesAlgebraDim.full : ReesAlgebraDim.Statement.{u} :=
  ReesAlgebraDim.proof DimensionInequality.full.{u, u}

theorem BlowUpModel.full : BlowUpModel.Statement.{u} :=
  BlowUpModel.proof ReesAlgebraDim.full.{u}

end GroundTheory.Heights₂.Heights.NumbersDVR
