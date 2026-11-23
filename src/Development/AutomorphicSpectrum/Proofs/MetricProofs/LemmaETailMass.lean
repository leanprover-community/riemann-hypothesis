module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailMass
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaEEnergy
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaEScale
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETailMass
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETrunc
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETruncMass
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETruncTail
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaEWeight
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLogNormSecIntegrable
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Giv


open GroundTheory.Heights₂.Heights.AnalyticLimit in
theorem lemmaETailMass : GroundTheory.Heights₂.Heights.AnalyticLimit.LemmaETailMass.Statement :=
  LemmaETailMass.proof LemmaETrunc.proof LemmaETruncMass.proof
    (LemmaETruncTail.proof LemmaEScale.proof LemmaEEnergy.proof LemmaEWeight.proof
      LogNormSecIntegrable.proof)

end GlobalTheory.CompanionTheory.Ar.Giv
