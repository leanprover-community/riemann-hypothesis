module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingComponentUniqueness
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteSumReduction
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepDirectSumAwayFromPlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeParametersComplexConjugate
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SpehParameterStrings
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TwistLocalComponentsCompatible
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TwistedDualFrobeniusCompatibility
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.FrobTwT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.GdLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.HalfG
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.MemOfProdEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.PlainGd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.RecTotT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.SumFamG
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.SumHTAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Assemble
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuFrobTotT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuIrrCaseT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuPolG
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuProdT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuSpehT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuSumTwoG
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SatakeGaloisCompatibilityOfHeckeEigensystem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TIsoOfFrob
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
open UpperTheory.V.Af UpperTheory.V.Af.Gu
namespace UpperTheory.V.Z.Win.Gu
theorem half_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (hR : RowT) : HalfG := halfG UpperTheory.twist_local_components_compatible (_root_.UpperTheory.V.Z.Win.Gu.polG_of_printsH_of_rT H hR)
theorem recTotT_of_printsH (H : _root_.UpperTheory.V.Af.HypothesesH') : RecTotT := recTotT (_root_.UpperTheory.V.Z.Win.Gu.prodT_alt H extraV) (_root_.UpperTheory.V.Z.Win.Gu.spehT_alt H extraV)
theorem galUnitaryT_of_printsH_of_bcSpeh_of_rT (H : _root_.UpperTheory.V.Af.HypothesesH') (hB : GlobalTheory.BcSpeh.BcSpeh) (hR : RowT) : GalUnitaryT :=
  _root_.UpperTheory.V.Z.Win.Gu.assemble_s H hB (sumFamG (_root_.UpperTheory.V.Z.Win.Gu.sumTwoG_of_printsH_gdLaws_sumAway_sumHTAt H gdLaws UpperTheory.galoisRep_direct_sum_away_from_places sumHTAt) UpperTheory.finiteSum_reduction) (_root_.UpperTheory.V.Z.Win.Gu.half_alt H hR) UpperTheory.speh_parameter_strings UpperTheory.building_component_uniqueness
    (_root_.UpperTheory.V.Z.Win.Gu.recTotT_of_printsH H) (_root_.UpperTheory.V.Z.Win.Gu.frobTotT_alt H extraV gdLaws) (UpperTheory.twistedDual_frobenius_compatibility (_root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results H.toClassicalTheorems)) (_root_.UpperTheory.satake_galois_link_of_printed_hida H) UpperTheory.satake_parameters_complex_conjugate
    (_root_.UpperTheory.V.Z.Win.Gu.irrCaseT_alt H) plainGd
theorem endShapeT' (H : _root_.UpperTheory.V.Af.HypothesesH') (hB : GlobalTheory.BcSpeh.BcSpeh) (hR : RowT) :
    type_of% (endShape_of hB (_root_.UpperTheory.satake_galois_link_of_printed_hida H) (_root_.UpperTheory.V.Z.Win.Gu.half_alt H hR) (_root_.UpperTheory.V.Z.Win.Gu.recTotT_of_printsH H) (_root_.UpperTheory.V.Z.Win.Gu.frobTotT_alt H extraV gdLaws) (frobTwT extraV gdLaws)) :=
  endShape_of hB (_root_.UpperTheory.satake_galois_link_of_printed_hida H) (_root_.UpperTheory.V.Z.Win.Gu.half_alt H hR) (_root_.UpperTheory.V.Z.Win.Gu.recTotT_of_printsH H) (_root_.UpperTheory.V.Z.Win.Gu.frobTotT_alt H extraV gdLaws) (frobTwT extraV gdLaws)
end UpperTheory.V.Z.Win.Gu
end
