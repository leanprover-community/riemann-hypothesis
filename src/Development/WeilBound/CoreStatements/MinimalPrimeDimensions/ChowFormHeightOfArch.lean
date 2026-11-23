module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfKnownTheorem
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.GenIdeal
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.ChowDegreeSection
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.DescEval
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.FormHeightOneEq
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.IsClosedOfCoheight
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.ResGAppLE
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.SpecializesIff
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.SumNormSqUnitary
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.OfLeaves
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace ChowFormHeightComparison₂.CF

open GroundTheory.Heights₂.Heights in
theorem chowFormHeight_of_arch (hA : StArch) (hM : MahlerSection.Statement) (hE : GlobalTheory.Published.ArExists) :
    PositivityTheory.UnitarySelfGeneration.ChowFormHeight :=
  glue (stMain_of (stVert stPts stPull stDiv) hA
    (ChowHeightRecursion.of_leaves ChowFormSectionVertical.full hM ChowFormBaseChange.full BaseChangeAvoid.full)
    ChowFormSection.full ChowHeightMul.full ProjPrimeHasPoint.full) stModel stForm hE

end ChowFormHeightComparison₂.CF
