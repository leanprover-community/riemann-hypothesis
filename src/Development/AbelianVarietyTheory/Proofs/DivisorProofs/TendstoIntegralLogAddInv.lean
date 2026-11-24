module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem tendsto_integral_log_add_inv : ∀ (T : Type) [MeasurableSpace T] (μ : Measure T) [IsFiniteMeasure μ] (w : T → ℝ) (C : ℝ), Measurable w → (∀ x, 0 ≤ w x ∧ w x ≤ C) → (∀ᵐ x ∂μ, 0 < w x) → Integrable (fun x => Real.log (w x) / 2) μ → Tendsto (fun n : ℕ => ∫ x, Real.log (w x + 1 / ((n : ℝ) + 1)) ∂μ) atTop (𝓝 (2 * ∫ x, Real.log (w x) / 2 ∂μ)) := by
  intro T _ μ _ w C hw hwC hpos hint
  have hint' : Integrable (fun x => Real.log (w x)) μ := by
    refine (hint.const_mul 2).congr (Eventually.of_forall fun x => ?_)
    simp only; ring
  have hlim : 2 * ∫ x, Real.log (w x) / 2 ∂μ = ∫ x, Real.log (w x) ∂μ := by
    rw [← integral_const_mul]; congr 1; ext x; ring
  rw [hlim]
  refine tendsto_integral_of_dominated_convergence (fun x => |Real.log (w x)| + |Real.log (C + 1)|) ?_ ?_ ?_ ?_
  · intro n
    exact (Real.measurable_log.comp (hw.add_const _)).aestronglyMeasurable
  · exact hint'.abs.add (integrable_const _)
  · intro n
    filter_upwards [hpos] with x hx
    have hd : 0 < 1 / ((n:ℝ) + 1) := by positivity
    have hd1 : 1 / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    have h1 : Real.log (w x) ≤ Real.log (w x + 1 / ((n:ℝ)+1)) := Real.log_le_log hx (by linarith)
    have h2 : Real.log (w x + 1 / ((n:ℝ)+1)) ≤ Real.log (C + 1) :=
      Real.log_le_log (by linarith) (by linarith [(hwC x).2])
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le (Real.log (w x)), abs_nonneg (Real.log (C+1))]
    · linarith [le_abs_self (Real.log (C+1)), abs_nonneg (Real.log (w x))]
  · filter_upwards [hpos] with x hx
    have h : Tendsto (fun n : ℕ => w x + 1 / ((n:ℝ) + 1)) atTop (𝓝 (w x + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h
    exact (Real.continuousAt_log hx.ne').tendsto.comp h

end GlobalTheory.Mix
