module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroCJDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPCuspSupp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPProdIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPSpCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPSpOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPSpPiSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPSpSupp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPSpTop
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpLat
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpLift
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpPiEta
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpRes
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpTwBasic
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpUniq
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorVector

@[expose] public section




section
namespace UpperTheory.TNZ.Grp
theorem step_suppProd_alt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : G.Step_suppProd_alt :=
  _root_.UpperTheory.TNZ.Grp.step_spTop_alt G UpperTheory.TNZ.step_spLat (step_spUniq G) (_root_.UpperTheory.TNZ.Grp.step_spCount_alt G) (step_spLift G) (step_spTwBasic G) (step_spRes G)
    (step_spPiEta G) _root_.UpperTheory.TNZ.Grp.step_spOrd_alt (_root_.UpperTheory.TNZ.Grp.step_spPiSub_alt G) (_root_.UpperTheory.TNZ.Grp.step_spSupp_alt G) _root_.UpperTheory.TNZ.step_cuspSupp_alt _root_.UpperTheory.TNZ.step_prodIrr_alt
    UpperTheory.TNZ.step_tensorVec
end UpperTheory.TNZ.Grp
end
