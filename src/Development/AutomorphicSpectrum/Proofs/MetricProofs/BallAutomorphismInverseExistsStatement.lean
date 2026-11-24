module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsFundSet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallAutomorphismInverseExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.ball_automorphism_inverse_exists : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (Z : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ Z (ballDom q) → Set.BijOn Z (ballDom q) (ballDom q) → DifferentiableOn ℂ G (ballDom q) → (∀ t ∈ ballDom q, ballPot q (Z t) = ballPot q t + (G t).re) → ∃ Y : (Fin n → ℂ) → Fin n → ℂ, DifferentiableOn ℂ Y (ballDom q) ∧ ∀ t ∈ ballDom q, Y t ∈ ballDom q ∧ Z (Y t) = t ∧ Y (Z t) = t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse.exists_inverse | exact GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse.exists_inverse | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse.exists_inverse <;> assumption)
