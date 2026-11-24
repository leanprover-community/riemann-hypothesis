module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnalyticOnNhdOrbitOfDerivSeqNormEq
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
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.analyticOnNhd_orbit_of_derivSeq_norm_eq : ∀ (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] (U₁ : ℝ → H₁ →L[ℂ] H₁) (U₂ : ℝ → H₂ →L[ℂ] H₂), (∀ s t, U₁ (s + t) = U₁ s * U₁ t) → (∀ s t, U₂ (s + t) = U₂ s * U₂ t) → U₁ 0 = 1 → U₂ 0 = 1 → (∀ t x, ‖U₂ t x‖ = ‖x‖) → ∀ (w₁ : ℕ → H₁) (w₂ : ℕ → H₂), (∀ k, HasDerivAt (fun t : ℝ => U₁ t (w₁ k)) (w₁ (k + 1)) 0) → (∀ k, HasDerivAt (fun t : ℝ => U₂ t (w₂ k)) (w₂ (k + 1)) 0) → (∀ k, ‖w₁ k‖ = ‖w₂ k‖) → AnalyticAt ℝ (fun t : ℝ => U₁ t (w₁ 0)) 0 → AnalyticOnNhd ℝ (fun t : ℝ => U₂ t (w₂ 0)) Set.univ := by
  first | exact @GlobalTheory.OrbitAnalytic.analyticOnNhd_orbit_of_norm_eq | exact GlobalTheory.OrbitAnalytic.analyticOnNhd_orbit_of_norm_eq | (intros; apply GlobalTheory.OrbitAnalytic.analyticOnNhd_orbit_of_norm_eq <;> assumption)
