module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesExact
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.ConclusionOfSmooth
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NotSubsetOfDenseCompl
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelongInv
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.SmallGeneratedCountUpperOfUse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalChartsOfSiegelOfForFan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenCuspidalCharsByRegularCharsProof
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumRangeEqRoots
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ChowFormHeightComparison
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.FubiniStudyChowHeightFormula
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.SmallSectionsInjective
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopCovolG
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNonvanishingOfToroidal
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.BridgesMore
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.AhSlimU
public import Development.WeilBound.CoreStatements.NefModelVolumes.ChowFormHyperplaneSection
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive

@[expose] public section



section
section
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Indef.Tree
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] GlobalTheory.CompHt.fintypePsi
namespace SelfIntersectionVolumeEstimates

theorem topCovolSlim2_use_alt_alt : GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero → GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero → GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv → PositivityTheory.MbHsUse.HSUse → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → HT.FarguesExact → GR.ZarhinStatement → Pub.NefRR → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.Published.PointSeparationPair → GlobalTheory.Published.ArDegree → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → _root_.GlobalTheory.CovTop.CovolumeBoundOfX :=
  fun h₁ h₂ hPL hU hBig hFar hZar hRR hS hK hN hSep hDeg hP hGD =>
    have hX : GlobalTheory.CovTop.HypothesesX := ⟨hK, hN, GlobalTheory.GreenBridge.green_of_regular GlobalTheory.greenRegularCharacters_holds, hSep, _root_.FubiniStudyChowHeightFormula₂.fubiniStudy_chowHeight_formula hP⟩
    have hF := PositivityTheory.Prw.toroidalChartsForFan_of hK
    have hH : GlobalTheory.CovHt.HypothesesH := ⟨hS, hF, GlobalTheory.Published.toroidalCharts_of_siegel_of_forFan hS hF, hDeg⟩
    _root_.SelfIntersectionVolumeEstimates.topCovolG_alt_alt ⟨_root_.ChowFormHeightComparison₂.chow_form_height_comparison, _root_.PositivityTheory.Xj7N.small_sections_injective (GlobalTheory.CompanionTheory.Ar.Rec.exists_nonvanishing_of_toroidal hH.sieg hX.ks)⟩ hX hP hH hGD ⟨hP.q6, hP.q8, hP.q13, hP.q7, hP.q10, GlobalTheory.Published.chowFormIntExists_holds, ChowFormCompatibility.chow_form_hyperplane_section, hP.q12⟩
      (PositivityTheory.HtPt.Ah.deep_slim_use h₁ h₂ hPL hU hBig hFar hZar hRR)
end SelfIntersectionVolumeEstimates
end
end
