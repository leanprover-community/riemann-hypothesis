module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisTwistType
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemLocalProperty
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjSelfDualGaloisRepCMDatum
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BlockTypeSplitProp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibilityCMDatum
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalBesselMultiplicityOne
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemLocalPropertyExplicit
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FirstTermConditionAllStages
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DepthZeroTypeGlobalOfRegularLocal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DepthZeroTypeGlobalOfSeriesLocal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRepresentationComponent
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GlobalArtinReciprocityTrivial
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodFTAllStA
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LabelTameCharacter
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowTruthOfLabelTie
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameUniformizerPower
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
section
namespace UpperTheory.Lit.Dz
theorem dz_swap_compatible_alt : _root_.GlobalTheory.T.ConjSelfDualGaloisRepCMDatumThirdPlace :=
  fun hL => _root_.DiscreteGroups.sglob.DzType.Rt.tame_uniformizer_power_alt (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem localGlobalCompatibility_cmDatum_alt : _root_.GlobalTheory.T.LocalGlobalCompatibilityCMDatum' :=
  fun hL => _root_.DiscreteGroups.sglob.DzType.Rt.labAt_ofDet_tame_eq_X_sub_C (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem blockTypeSplitProp : _root_.GlobalTheory.T.BlockTypeSplitThirdPlace :=
  fun a hL => _root_.DiscreteGroups.sglob.DzType.Rt.regLoc_of_depth_zero_inertia_big_greenLab a (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem nonGaloisTwistType : _root_.GlobalTheory.T.NonGaloisTwistType' :=
  fun a b hL => _root_.DiscreteGroups.sglob.DzType.Rt.exists_representation_component_alt a b (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem firstTermCondition_all_stages : _root_.GlobalTheory.GoodFirst.FirstTermConditionAllStagesAlt :=
  fun a b hL => _root_.DiscreteGroups.sglob.DzType.Rt.goodFTAll_stA_alt a b (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem compatibleSystemLocalProperty : _root_.GlobalTheory.T.CompatibleSystemLocalPropertyThirdPlace :=
  fun a b c hL => _root_.DiscreteGroups.sglob.DzType.Rt.serLoc_of_tame_coupled_and_cenLoc a b c (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem compatibleSystemLocalProperty_explicit : _root_.GlobalTheory.SerSys.Assembly.CompatibleSystemLocalPropertyExplicitAlt :=
  fun a b c hL => _root_.DiscreteGroups.sglob.DzType.Rt.depthZeroType_series_local_explicit_alt a b c (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem localBesselMultiplicityOne : _root_.GlobalTheory.T.LocalBesselMultiplicityOne' :=
  fun a b hL => _root_.DiscreteGroups.sglob.DzType.Rt.rowTruth_of_labelTie_alt a b (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
end UpperTheory.Lit.Dz
end
end
