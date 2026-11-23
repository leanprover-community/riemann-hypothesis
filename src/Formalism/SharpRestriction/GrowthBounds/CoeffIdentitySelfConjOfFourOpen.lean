module

public import Formalism.LocalToGlobal.CharacterGerms.CoefficientIdentitySelfConjugate
public import Formalism.SharpRestriction.GrowthBounds.PowerSeriesFrobeniusCongruence
public import Formalism.LocalToGlobal.CharacterGerms.FrobPowSmul
public import Formalism.LocalToGlobal.CharacterGerms.MmMulSeries
public import Formalism.SharpRestriction.GrowthBounds.AlongCvSmul
import Formalism.SharpRestriction.GrowthBounds.CoeffIdentityPlainChartOfThree
public import Formalism.SharpRestriction.GrowthBounds.CoeffOneAlongCvLg
public import Formalism.SharpRestriction.GrowthBounds.ConstantCoeffUnshiftLogarithm
public import Formalism.SharpRestriction.GrowthBounds.R1sExpLowHolds
public import Formalism.SharpRestriction.GrowthBounds.SumRescaleTySTwo
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

@[expose] public section

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

theorem r1sFrob_holds : PowerSeriesFrobeniusCongruence := frobPow_smul

theorem r1sRoots_holds : RootsOfUnityProductCongruence := fun C _ V ζ hζ j f hf μ => rootsProd C V ζ hζ j f hf μ

theorem coeffIdentity_selfConj_of_four_open (hHL : GaugeLeadingTermLinear) (hHR : GaugeRescalingSymmetry) (hHI : IntegralUnitFamilies) (hGe : GenericPointUnitCongruence) : CoefficientIdentitySelfConjugate :=
  coeffIdentity_selfConj_of_four good_curve_closed r1sRestB_holds
    (r1sRestC_of r1sFrob_holds r1sRoots_holds r1sExpLow_holds hHL hHR hHI hGe) biadditive_on_columns

end Formalism.L2.FormalSeriesBounds
