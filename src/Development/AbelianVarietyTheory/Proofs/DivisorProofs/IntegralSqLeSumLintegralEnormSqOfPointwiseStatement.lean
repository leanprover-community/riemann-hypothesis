module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSqLeSumLintegralEnormSqOfPointwise
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

@[expose] public section

open IsDedekindDomain NumberField
open scoped Classical


theorem _root_.GlobalTheory.T.integral_sq_le_sum_lintegral_enorm_sq_of_pointwise : ∀ (E : Type) [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] (μ : MeasureTheory.Measure E)
    (ι : Type) [Fintype ι] (f : E → ℝ) (g : ι → E → ℂ) (C : ℝ), (∀ a, Continuous (g a)) →
    (∀ x, f x ^ 2 ≤ C * ∑ a, ‖g a x‖ ^ 2) →
    ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) ≤ ENNReal.ofReal C * ∑ a, ∫⁻ x, ‖g a x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.sq_le_sum_enorm_sq_lintegral_bound | exact GlobalTheory.sq_le_sum_enorm_sq_lintegral_bound | (intros; apply GlobalTheory.sq_le_sum_enorm_sq_lintegral_bound <;> assumption)
