module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.RealSqrt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField in
theorem _root_.GlobalTheory.lawsAndExpansions :
    _root_.GlobalTheory.UT.LL ∧ _root_.ReciprocityTheory.ChartRestriction.G.DVR.TwistBCSpanStatement ∧ _root_.ReciprocityTheory.ChartRestriction.G.DVR.TWM.VRatioGtStatement ∧ _root_.ReciprocityTheory.ChartRestriction.G.DVR.TWStatement ∧ _root_.ReciprocityTheory.ChartRestriction.G.DVR.UUStatement := by
  have hLaws := _root_.GlobalTheory.allSixLaws
  have hU : _root_.ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt := _root_.GlobalTheory.laws_without_cohomology.1
  have hS : _root_.ReciprocityTheory.ChartRestriction.G.DVR.TwistBaseChangeStatement := _root_.GlobalTheory.twistBaseChange
  have hR : _root_.ReciprocityTheory.ChartRestriction.G.DVR.TwistBCSpanStatement := _root_.ReciprocityTheory.ChartRestriction.G.DVR.twistBCSpan_of hS
  have hA : _root_.ReciprocityTheory.ChartRestriction.G.DVR.TWM.VRatioGtStatement := _root_.GlobalTheory.RatioVal.main
  refine ⟨?_, hR, hA, _root_.ReciprocityTheory.ChartRestriction.G.DVR.TWM.tw_of hU hR hA, _root_.GlobalTheory.UnitBallFree.main hU hS⟩
  unfold _root_.GlobalTheory.UT.LL
  exact ⟨hLaws.1, hLaws.2.1, hLaws.2.2.1, hLaws.2.2.2.1, hLaws.2.2.2.2.1⟩

end GlobalTheory
