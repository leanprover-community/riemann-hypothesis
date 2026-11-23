module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonReproducesHarmonic
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

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

theorem _root_.GlobalTheory.T.polydisc_poisson_reproduces_harmonic : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℝ) (ρ R M : ℝ), 0 < ρ → ρ < R → ContinuousOn f (punct R) → SepHarm R f → (∀ z ∈ punct R, |f z| ≤ M) → ∀ z ∈ punct ρ, polyPoisson ρ f z = f z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.polyPoisson_eq_self | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.polyPoisson_eq_self | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.polyPoisson_eq_self <;> assumption)
