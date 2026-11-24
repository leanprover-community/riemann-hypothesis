module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormPolyEqIntersectionNumber
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

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem _root_.GlobalTheory.T.integral_chernFormPoly_eq_intersectionNumber : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  first | exact @GlobalTheory.ChernLine.integral_evalF_c1W_eq_interPoly | exact GlobalTheory.ChernLine.integral_evalF_c1W_eq_interPoly | (intros; apply GlobalTheory.ChernLine.integral_evalF_c1W_eq_interPoly <;> assumption)
