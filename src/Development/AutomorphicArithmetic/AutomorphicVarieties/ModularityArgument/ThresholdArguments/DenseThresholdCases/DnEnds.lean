module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutEnd3AltAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThmS6CoreS
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PlDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.LocalConditionRankThreeEvenLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LogarithmicNormBounds.LinkedUnlEOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.GdEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HostEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.FlagAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.IneOfKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.InertiaConditionRankTwoLinkOfInertia
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.LocalConditionRankThreeLinkOfInertiaOrdinary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.PotTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BrAutNew
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DnDown
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DnHost
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GalRepDescentAlongQuadraticExtension
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GdEndOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocPublished
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymmetricCubeTheoremOfEndomorphisms
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistConjugateSelfDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryThreeInputsOfLiterature
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.ConjLeftPosAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.NormalValuationBounds.CharpolyScalar
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
namespace UpperTheory.V.Z.Win.Dn
open UpperTheory.V.Lit UpperTheory.V.W UpperTheory.V.HV UpperTheory.V.Z.Sym.Pl
theorem ends_rank_three_of_local' (hH : _root_.UpperTheory.V.Af.HypothesesH') (hU : J.LinkedUnlE) : LocalConditionRankThreeEvenLevel := fun Ω _ _ _ l _ c _ N _ e ψ hev η σ g₁ B M h =>
  Keep.keeps3E (_root_.UpperTheory.V.W.locPrints_of_litN hH.litN) hU Ω l c N e ψ η σ g₁ B M h hev
theorem ends_of_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') (hE : _root_.UpperTheory.V.Z.Sym.Pl.LinkedEndEAlt) (hU : J.LinkedUnlE) : _root_.UpperTheory.V.Pr.GdEndAlt ∧ _root_.UpperTheory.V.Aut.ThmS6Core_s :=
  have h3 := localConditionRankThreeLink_of_inertia_ordinary ineOfKer_of flagAll_of
  ⟨_root_.UpperTheory.V.Z.Win.Dn.gdEnd_of_frame_linkedEnd_downCsdK_descent hH h3 (_root_.UpperTheory.V.Z.Win.Dn.ends_rank_three_of_local' hH hU) potTwo_of (inertiaConditionRankTwoLink_of_inertia UpperTheory.V.Keep.ineOf) (Fr.gd_ex (_root_.UpperTheory.V.W.global_compat_printed_of_literal_automorphy_n hH.litN)) hE (_root_.UpperTheory.V.Z.Win.Dn.downCsdK_of_printsH hH) (_root_.UpperTheory.V.Af.rankTwoAutomorphyDescends_of_printsH hH)
      (_root_.UpperTheory.V.Br.autNewformA_of_printsH hH) (_root_.UpperTheory.V.Sd.twist_conjugate_selfDual hH.toClassicalTheorems) (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hH.toClassicalTheorems),
    _root_.UpperTheory.V.Pr.symmetric_cube_theorem_of_endomorphisms_alt (_root_.UpperTheory.V.Z.Win.Dn.hostEnd_of_loc3_frame_linkedEnd_downCsdK h3 (_root_.UpperTheory.V.Z.Win.Dn.ends_rank_three_of_local' hH hU) (Fr.host_ex (_root_.UpperTheory.V.W.global_compat_printed_of_literal_automorphy_n hH.litN)) hE (_root_.UpperTheory.V.Z.Win.Dn.downCsdK_of_printsH hH))⟩
theorem ends_u_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') (hU : J.LinkedUnlE) : _root_.UpperTheory.V.Pr.GdEndAlt ∧ _root_.UpperTheory.V.Aut.ThmS6Core_s :=
  _root_.UpperTheory.V.Z.Win.Dn.ends_of_alt hH (_root_.UpperTheory.V.Z.Sym.Top.linkedEnd_alt hH (_root_.UpperTheory.V.Z.Win.Birth.seed2_alt hH) (_root_.UpperTheory.V.Z.Sym.W.unitary_three_automorphy_dense_of_prints hH)) hU
end UpperTheory.V.Z.Win.Dn
end
