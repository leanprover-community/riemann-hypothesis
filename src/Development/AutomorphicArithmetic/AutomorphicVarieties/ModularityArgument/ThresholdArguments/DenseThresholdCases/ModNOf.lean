module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelRelationTwoX
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NumJ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CountE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RadOfDense
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
namespace UpperTheory.V.Z.J.D
theorem numJ'_alt : _root_.UpperTheory.V.Z.J.D.NumJAlt := fun hH hM hC l _ L Ω _ _ _ _ _ _ s n hn V hS h4 Q c r ι B Λ R K J _ =>
  _root_.UpperTheory.V.Z.Desc.V0.numJEDenseThresholdCases hH hM hC l L Ω s n hn V hS h4 Q c r ι B Λ R K J
theorem modularity_n_of_printed_mult_comp (hH : _root_.UpperTheory.V.Af.HypothesesH') (hM : Mult.Mult) (hC : Mult.CompOf) : _root_.UpperTheory.V.J.ModNAlt := _root_.UpperTheory.V.Z.J.D.modularity_n_of_num_j_printed_mult_comp _root_.UpperTheory.V.Z.J.D.numJ'_alt hH hM hC
end UpperTheory.V.Z.J.D
end
