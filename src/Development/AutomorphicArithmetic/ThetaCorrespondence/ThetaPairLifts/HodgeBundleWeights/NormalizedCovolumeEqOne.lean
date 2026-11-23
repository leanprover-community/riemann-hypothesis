module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLowestKTypeWeylDimensionLeOfSizeBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeDimAtStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CovolumeRatioEqIndex
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HaarMeasureFundamentalDomainNeZeroOfCocompact
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LevelSubgroupIndexBounded
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LogMeasureRatioBounded
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.PlugPairs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeFundamentalDomainNeTopOfFiniteCovolume
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
namespace GlobalTheory.OneMeasureAll
theorem covolume_measure_eq_one : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D := by
  intro hP D Tu C t0 hC i P
  refine ⟨_root_.GlobalTheory.T.level_subgroup_index_bounded hP D Tu C t0 hC i P, fun τ => GlobalTheory.T.one_le_dimAt' D i τ, fun μ 𝓕 hF =>
    ⟨_root_.GlobalTheory.T.fundamentalDomain_volume_ne_zero hP D Tu C t0 hC i P μ 𝓕 hF, _root_.GlobalTheory.T.quotient_measure_lt_top_of_finite_covolume hP D Tu C t0 hC i P μ 𝓕 hF,
      _root_.GlobalTheory.T.covolume_ratio_eq_index hP D Tu C t0 hC i P μ 𝓕 hF, fun L hL =>
        ⟨fun τ => GlobalTheory.T.log_lowestKTypeWeylDimension_le_of_sizeBounds D i L hL τ, _root_.MainStatements.Tam.Plug.tamagawa_pairs_compatible hP D Tu C t0 hC i P μ 𝓕 hF L hL,
          _root_.GlobalTheory.T.log_measure_ratio_bounded hP D Tu C t0 hC i P μ 𝓕 hF L hL⟩⟩⟩
end GlobalTheory.OneMeasureAll
end

section

theorem _root_.GlobalTheory.T.normalized_covolume_eq_one : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.OneMeasure D := by
  first | exact @_root_.GlobalTheory.OneMeasureAll.covolume_measure_eq_one | exact _root_.GlobalTheory.OneMeasureAll.covolume_measure_eq_one | (intros; apply _root_.GlobalTheory.OneMeasureAll.covolume_measure_eq_one <;> assumption)
end
