module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMeasureStereographicIntegral
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
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.sphere_measure_stereographic_integral : let n : ℂ → Fin 3 → ℝ := (fun (a : ℂ) (i : Fin 3) => (![2 * a.re, 2 * a.im, 1 - ‖a‖ ^ 2] : Fin 3 → ℝ) i / (1 + ‖a‖ ^ 2)); (∀ f : (Fin 3 → ℝ) → ℝ, Measurable f → (Integrable (fun a : ℂ => f (n a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) ↔ Integrable (fun m : ReciprocityTheory.ChartRestriction.G.AI.S2 => f fun i => (m : ReciprocityTheory.ChartRestriction.G.AI.E3) i) ReciprocityTheory.ChartRestriction.G.AI.sphereMeasure) ∧ ∫ a : ℂ, f (n a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2) = ∫ m : ReciprocityTheory.ChartRestriction.G.AI.S2, f (fun i => (m : ReciprocityTheory.ChartRestriction.G.AI.E3) i) ∂ ReciprocityTheory.ChartRestriction.G.AI.sphereMeasure) ∧ ∀ a₀ a₁ : ℂ, logSin 1 a₀ a₁ = (1 / 2) * Real.log ((1 - ∑ i, n a₀ i * n a₁ i) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.sphere_measure_stereographic_integral | exact GlobalTheory.CompanionTheory.Relay.sphere_measure_stereographic_integral | (intros; apply GlobalTheory.CompanionTheory.Relay.sphere_measure_stereographic_integral <;> assumption)
