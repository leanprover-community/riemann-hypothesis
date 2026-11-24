module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFiniteSumTopForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.integral_finite_sum_topForms : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {ι : Type} [Fintype ι] {d : ι → κ → Y → ℝ} {t : ι → ℝ}, (∀ a, IsTopForm e (d a) S) → (∀ a, HasInt e (d a) S (t a)) → HasInt e (fun i y => ∑ a, d a i y) S (∑ a, t a) := by
  first | exact @GlobalTheory.GoodTop.hasInt_sum | exact GlobalTheory.GoodTop.hasInt_sum | (intros; apply GlobalTheory.GoodTop.hasInt_sum <;> assumption)
