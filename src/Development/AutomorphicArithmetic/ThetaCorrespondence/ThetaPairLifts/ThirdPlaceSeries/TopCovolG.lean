module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeEstimateHypotheses
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AnchorHoldsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreLeOfGramMeasRatStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringBadLocusOfDescentSteps
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringCutOfLocalTraces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringDegreeMultiplicative
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringDescentMapsCompatible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringGramMatrixOfLocalTraces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringLambdaInvariantBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringLowDefectBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringMeasureReductionBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringMinGenusBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringRankOfDescentSteps
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringRationalOfLocalTraces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CovolXOfStepsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeepGoodReductionStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsDeepCoveringLevel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatBoundOfAnchor
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatDegreeStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeightLowerBoundGeneral
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HilbertSamuelLowerBoundOfComponents
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowOfCoverHypothesesStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecAtOfGramAtStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingOfCoveringDescent
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareStatementOfKnownTheorems
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizeAltBisStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumCOfDeepGoodStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ULowOfStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
section
open GlobalTheory.CovTop GlobalTheory.BigTop
namespace SelfIntersectionVolumeEstimates

theorem topCovolG_alt_alt : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses → GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.CompanionTheory.Ar.Plug.DeepStR → _root_.GlobalTheory.CovTop.CovolumeBoundOfX :=
  by
  intro hSB hX hP hH hGD hQ hD
  have hS := hH.sieg
  have hK := hX.ks
  have hN := hX.lie
  have gram := _root_.GlobalTheory.T.covering_gram_of_prints hP
  have size := _root_.GlobalTheory.T.cov_size_bound
  have meas := _root_.GlobalTheory.T.covering_meas_of_prints hP
  have anc := _root_.GlobalTheory.T.anchor_bound
  have dex := _root_.GlobalTheory.T.covering_deepEx_of_prints hP
  have dg := _root_.GlobalTheory.T.deepGood_of_toroidal_and_semiabelian hP hGD hQ hS hK hN
  have fd := _root_.GlobalTheory.T.flatDeg_of_scholzeWeinstein_of_prints hP
  have deg := _root_.GlobalTheory.T.coverDegree_of_grothendieck_deformation hX hP hS hK hGD hQ hN dg size fd
  have sh := _root_.GlobalTheory.T.share_of_deep_good_size_flat_deg_cover_degree hX hP hS hK hGD hQ hN dg size fd deg
  have ht := _root_.SelfIntersectionVolumeEstimates.height_lower_bound_general_alt hSB hX hGD hQ hP hH hD dg size deg fd
  have hs := _root_.GlobalTheory.T.coverHeightSum_of_flatDeg_coverDegree_share hX hP hGD hQ hS hK hN dg size fd deg sh
  have ul := _root_.GlobalTheory.T.uniform_lower_bound_of_sums' dg size deg sh ht hs (_root_.GlobalTheory.T.sum_c_of_deep_good dg)
  have low := _root_.GlobalTheory.T.liftLowBound_of_cover_estimates size (_root_.GlobalTheory.T.lowDef_of_gram_of_anchor hP gram anc) dex dg (_root_.GlobalTheory.T.covering_ring_of_prints_gram_deepGood hP gram dg) (_root_.GlobalTheory.T.covering_maps_of_gram_deep_size_flatDeg hP hGD hQ hS hK hN gram dg size fd) (_root_.GlobalTheory.T.coverRank_of_coverDegree_and_share hX hP hGD hQ hS hK hN dg size fd deg sh) (_root_.GlobalTheory.T.covering_gmin_of_prints_gram_deep_size hP gram dg size) (_root_.GlobalTheory.T.flat_of_prints_deepGood_flatDeg_anchor hP dg fd anc) ul
  exact _root_.GlobalTheory.T.covolX_of_truncation_badSet_lambda_lowBound gram (_root_.GlobalTheory.T.lift_recursion_of_gram_bound gram) (_root_.GlobalTheory.T.liftTruncation_of_prints hP) (_root_.GlobalTheory.T.liftBadSet_of_deep_size_flatDeg_share hX hP hGD hQ hS hK hN hX.green gram dex dg size fd deg sh) (_root_.GlobalTheory.T.liftLambdaBound_of_gram_meas hP gram meas) size (_root_.GlobalTheory.T.coreLe_of_gram_meas_liftRational gram meas (_root_.GlobalTheory.T.liftRational_of_prints hP)) low
end SelfIntersectionVolumeEstimates
end
end
