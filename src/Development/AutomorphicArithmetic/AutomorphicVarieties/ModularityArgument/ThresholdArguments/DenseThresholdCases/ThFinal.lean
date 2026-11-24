module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicPointGalois
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdLOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVFinalU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TOrdVan
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.PhiAll
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
open UpperTheory.Top UpperTheory.V.HV
namespace UpperTheory.V.Th
theorem core_alt_bis (hH : _root_.UpperTheory.V.Af.HypothesesH') (hC : Pa.CohP) : _root_.UpperTheory.V.Th.DenseThresholdMainCase := _root_.UpperTheory.V.Th.core_of_ord_vanishing_two_phi_all (_root_.UpperTheory.V.Th.ordinary_vanishing_two_of_printed_hida hH) (W.phiAll hC)
theorem adjoint_lifting_of_cohomology (hH : _root_.UpperTheory.V.Af.HypothesesH') (hC : Pa.CohP) : _root_.UpperTheory.V.Th.AdjointLiftingTheorem := _root_.UpperTheory.V.Th.adjointLiftingTheorem_of_locPrints_of_core (_root_.UpperTheory.V.HV.U.locPrints_of_litN hH.litN) (_root_.UpperTheory.V.Th.core_alt_bis hH hC)
end UpperTheory.V.Th
end
