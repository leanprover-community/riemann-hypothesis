module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RankTwoAutomorphyDescendsFromAbelianCMToRat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RankTwoDescentSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TGapTwo
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section




section
theorem UpperTheory.V.Af.rankTwoAutomorphyDescends_of_printsH :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Pr.RankTwoAutomorphyDescendsFromAbelianCMToRat := fun P =>
  Or.elim P.cyc2 (fun h => _root_.UpperTheory.V.Z.Bc.isAutR_of_isAutC_comp_galEmb_of_odd_quadratic_char P P.cyc h (_root_.UpperTheory.V.Z.Bc.gapTwo_alt P))
    fun h L Ω _ _ _ _ _ _ _ _ l _ ι W h1 h2 h3 h4 h5 => h L Ω l ι W h1 h2 h3 h4 h5
end
