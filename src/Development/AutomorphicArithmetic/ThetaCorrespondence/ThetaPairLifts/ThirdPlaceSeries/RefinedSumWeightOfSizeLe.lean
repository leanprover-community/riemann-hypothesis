module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefTheta
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefCoreOfSumPtStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefThetaOfRefCoreStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefinedSumWeightOfRefinedTheta
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumPtOfSizeStatement
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
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
namespace GlobalTheory.RefSum
theorem refinedSum_weight_of_size_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.RefSum.ReferenceWeight :=
  fun hP _ hS hF => _root_.GlobalTheory.T.refW_of_prints_size_flatDeg_refTheta hP hS hF (_root_.GlobalTheory.T.refTheta_of_size_refCore hS (_root_.GlobalTheory.T.reference_core_of_size_and_sum_point hS (_root_.GlobalTheory.T.sum_pt_of_size hS)))
end GlobalTheory.RefSum
end
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

theorem _root_.GlobalTheory.T.refW_of_prints_deepGood_size_flatDeg : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.RefSum.ReferenceWeight := by
  first | exact @_root_.GlobalTheory.RefSum.refinedSum_weight_of_size_alt | exact _root_.GlobalTheory.RefSum.refinedSum_weight_of_size_alt | (intros; apply _root_.GlobalTheory.RefSum.refinedSum_weight_of_size_alt <;> assumption)
end
end
