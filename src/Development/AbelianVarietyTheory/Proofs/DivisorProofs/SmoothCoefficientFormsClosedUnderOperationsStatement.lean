module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCoefficientFormsClosedUnderOperations
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.smooth_coefficient_forms_closed_under_operations : ∀ (n : ℕ) (v : V n), (∀ γ : Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((fun _ : V n => γ) x) S) v)) ∧ (∀ (J : Type) (s : Finset J) (α : J → V n → Alt n), (∀ j ∈ s, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α j x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (∑ j ∈ s, α j x) S) v)) ∧ (∀ (g : V n → ℂ) (α : V n → Alt n), ContDiffAt ℝ ∞ g v → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (g x • α x) S) v)) ∧ (∀ α β : V n → Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (β x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x * β x) S) v)) := by
  first | exact @GlobalTheory.ChernCalc.smooth_coeff_closure | exact GlobalTheory.ChernCalc.smooth_coeff_closure | (intros; apply GlobalTheory.ChernCalc.smooth_coeff_closure <;> assumption)
