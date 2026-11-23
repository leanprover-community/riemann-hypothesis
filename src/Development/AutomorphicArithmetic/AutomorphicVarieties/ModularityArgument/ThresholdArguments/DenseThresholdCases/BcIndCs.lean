module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsHilbertModularFormCongrOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CyclicLiftRankTwoOfCyclicBaseChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.WsIIOfPrintsH
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsPrimeIndex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IndAutLOfSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SeedIIZ
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
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HilbertEisensteinWeightOneHolds

@[expose] public section




section
namespace UpperTheory.V.Z.Bc
theorem seedIIs_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Ws.SeedIIAlt :=
  have hA := hH.toClassicalTheorems
  _root_.UpperTheory.V.Z.Bc.seedII_Z_alt ⟨hH, Published.hilbert_eisenstein_weight_one_holds, Lit.oneUse⟩
    (_root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutLP_of_printsH_upQuad_upSol_indCs hH (_root_.UpperTheory.V.Z.Bc.upQuadI_of_alt hA (quadLiftRealToComplex_of_base_change hH.bc)) (_root_.UpperTheory.V.Z.Bc.upSolI_of_alt hA (cyclicLiftRankTwo_of_cyclic_base_change hH.cyc)) indCs)
end UpperTheory.V.Z.Bc
end
