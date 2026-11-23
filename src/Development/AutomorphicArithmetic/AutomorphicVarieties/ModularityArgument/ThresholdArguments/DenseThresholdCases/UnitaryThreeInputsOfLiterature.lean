module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WStmtxx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.CompatTOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.PlainRec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.ResidualAutomorphyOfLinkedEnds
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdjointLiftFromEisensteinSeedOfHyps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BciNarrowSwap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GalUnitaryT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JPTRow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MemLevelOfLocalDepth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MemOfUnder
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPropEGW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSeedInW
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.LevUnion

@[expose] public section




section
namespace UpperTheory.V.Z.Sym.W
theorem weight_compatible_descent (hH : _root_.UpperTheory.V.Af.HypothesesH') (hR : Z.Win.RowT) : _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility :=
  ⟨hH.toClassicalTheorems, _root_.UpperTheory.V.Z.Win.Gu.galUnitaryT_of_printsH_of_bcSpeh_of_rT hH (_root_.UpperTheory.BaseChangeIdentities.bcSpeh_alt (_root_.UpperTheory.BaseChangeIdentities.bridge hH.litN.aut.bc hH.litN.loc.bern)) hR,
    Z.Win.compatTOf hR Z.Win.plainRec, _root_.UpperTheory.V.Z.Desc.W.same_of_prints_of_rT hH.toClassicalTheorems hR, Z.Win.plainRec, Top.descUse_of_weak hH.descU⟩
theorem adjoint_automorphy_w_of_printed_hida_window (hH : _root_.UpperTheory.V.Af.HypothesesH') (hR : Z.Win.RowT) : AdAutW := _root_.UpperTheory.V.Z.Sym.W.adjoint_automorphy_w_of_pure_weight_adjoint_lift (_root_.UpperTheory.V.Z.Sym.W.weight_compatible_descent hH hR) (_root_.UpperTheory.V.Z.Sym.W.adjoint_lift_w_of_literal_automorphy_spec_out hH.litN specOutS)
theorem unitary_three_automorphy_dense_of_prints_and_row (hH : _root_.UpperTheory.V.Af.HypothesesH') (hR : Z.Win.RowT) : _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense := _root_.UpperTheory.V.Z.Sym.W.adjoint_lift_from_eisenstein_of_propagation (_root_.UpperTheory.V.Z.Sym.W.prop_eg_w_of_printed_hida hH) (_root_.UpperTheory.V.Z.Sym.W.seedInW_alt hH) (_root_.UpperTheory.V.Z.Sym.W.adjoint_automorphy_w_of_printed_hida_window hH hR)
theorem unitary_three_automorphy_dense_of_prints (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense := _root_.UpperTheory.V.Z.Sym.W.unitary_three_automorphy_dense_of_prints_and_row hH (_root_.UpperTheory.Gal.SV.rowOf' hH.litN.aut.gal)
end UpperTheory.V.Z.Sym.W
end
