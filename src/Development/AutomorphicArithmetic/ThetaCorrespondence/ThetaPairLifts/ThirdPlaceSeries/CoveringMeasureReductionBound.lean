module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.NormalizedCovolumeEqOne
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CovolumeLowerBoundOfCover
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExactAtOfRowsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatAtUpperStatement
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf

@[expose] public section



section
section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
namespace GlobalTheory.CovTop.MeasRd
theorem covering_measure_reduction_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.MeasureCondition := by
  intro h
  have h2 := _root_.GlobalTheory.T.normalized_covolume_eq_one h
  refine Closed.imp (Closed.and (_root_.GlobalTheory.T.exists_log_ratAt_le_mul_unitE h2) (_root_.GlobalTheory.T.exists_neg_unitE_le_log_ratAt h)) ?_
  intro _ Fm _ _ hh
  obtain ⟨⟨K1, hK1, a, ha⟩, ⟨K2, hK2, b, hb⟩⟩ := hh
  refine ⟨(K1 + K2) / 2, by positivity, max a b, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨hr, hu⟩ := ha x hx ((le_max_left _ _).trans hle) ι p hp i
  have hl := hb x hx ((le_max_right _ _).trans hle) ι p hp i
  exact measAt_of p i (_root_.GlobalTheory.T.exactAt_of_oneMeasure p hp.1 (h2 _) i) hr hK1 hK2 hu hl
end GlobalTheory.CovTop.MeasRd
end
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.covering_meas_of_prints : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.MeasureCondition := by
  first | exact @_root_.GlobalTheory.CovTop.MeasRd.covering_measure_reduction_alt | exact _root_.GlobalTheory.CovTop.MeasRd.covering_measure_reduction_alt | (intros; apply _root_.GlobalTheory.CovTop.MeasRd.covering_measure_reduction_alt <;> assumption)
end
end
