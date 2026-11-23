module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SdStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LogarithmicNormBounds.LinkedUnlEOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.TanA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.CompOfFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVCore
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocPublished
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ModNOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThFinal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryRankTwoFlags
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.LamEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.PhiAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.ProModularRingExists
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.WeilCharactersModular.SgnEqOne
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ArthurClozelDescent

@[expose] public section




section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.Z.J
open UpperTheory.V.HV UpperTheory.V.Lit UpperTheory.V.W UpperTheory.V.J
theorem linkedUnlE_holds_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') (s2 : _root_.UpperTheory.V.Sd.Seed2Alt) (s3 : _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense) : LinkedUnlE :=
  have hN := hH.litN
  have hA := hH.toClassicalTheorems
  _root_.UpperTheory.Gal.projectedFormsSystemPart.linkedUnlE_alt hN.aut.art (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN) (_root_.UpperTheory.V.HV.Core.modU_of_printsH hH) (_root_.UpperTheory.V.Z.J.D.modularity_n_of_printed_mult_comp hH Z.Mult.mult_free Z.Mult.compOf_free) levEx
    (lamEx (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN)) (b0Ex (phiAll (_root_.UpperTheory.V.W.cohP_alt hN))) s3 s2 (_root_.UpperTheory.V.Sd.twist_of_printed_results hA) (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hA) (_root_.UpperTheory.V.Sd.alg_restriction_of_printed_results hA)
    (tanA (_root_.UpperTheory.V.W.global_compat_printed_of_literal_automorphy_n hN) (_root_.UpperTheory.V.W.locPrints_of_litN hN)) (_root_.UpperTheory.V.Th.core_alt_bis hH (_root_.UpperTheory.V.W.cohP_alt hN))
end UpperTheory.V.Z.J
end
