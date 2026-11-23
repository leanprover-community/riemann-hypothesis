module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdjointLiftingOfCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CohInp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DnEndsTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVCore
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KFinal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KatoTwoWOfPublishedH
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkedUnlE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PublishedHypothesesFromPatching
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Sp4In0
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.HasOfSplit
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

@[expose] public section




section
open UpperTheory.Top
namespace UpperTheory.V.HV.DescentVanishingReductions
theorem vwin_of_hypotheses_H_E_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') : VWin :=
  have hK := _root_.UpperTheory.V.ZK.lemmaK_litN_alt hH.litN
  have hE := _root_.UpperTheory.V.Z.Win.Dn.ends0_alt hH
  have h4 := _root_.UpperTheory.V.HV.DescentVanishingReductions.countII_and_countIII_of_printsH_of_sp4In hH hK (_root_.UpperTheory.V.HV.DescentVanishingReductions.sp4In0_alt hH)
  _root_.UpperTheory.V.HV.Core.of_four_alt hH.litN hK (_root_.UpperTheory.V.Z.J.count_i_of_printed_bound_k_kato_automorphy hH hK (_root_.UpperTheory.V.Z.Kato.WeilSphericalRecords.katoTwoW_of_printsH hH) (_root_.UpperTheory.V.HV.Core0.automorphyUnramified_of_litN_of_gdEnd hH.litN hE.1)) h4.1 h4.2 (_root_.UpperTheory.V.Z.J.count_v_of_printed_bound_k_reduced_unitary_lift hH hK hE.2)
theorem v_window_of_automorphy_csd_ss_mono_odd (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : VWin :=
  _root_.UpperTheory.V.HV.DescentVanishingReductions.vwin_of_hypotheses_H_E_alt (_root_.UpperTheory.V.HV.DescentVanishingReductions.published_hypotheses_from_patching_alt hN UpperTheory.V.Z.Tf.SR.descWeak)
end UpperTheory.V.HV.DescentVanishingReductions
theorem UpperTheory.V.v_window_of_literal_automorphy_n (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : VWin :=
  _root_.UpperTheory.V.HV.DescentVanishingReductions.v_window_of_automorphy_csd_ss_mono_odd hN
end
