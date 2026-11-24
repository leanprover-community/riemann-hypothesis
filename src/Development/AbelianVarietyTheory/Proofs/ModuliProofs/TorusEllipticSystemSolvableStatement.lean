module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorusEllipticSystemSolvable
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

open Complex Matrix
open scoped ContDiff BigOperators Real

theorem _root_.GlobalTheory.T.exists_periodic_smooth_solution_torus_system : ∀ (n m : ℕ) (p : Fin m → Fin n → ℂ), (∀ ξ : Fin n → ℝ, (∀ a, ∑ k, p a k * (ξ k : ℂ) = 0) → ξ = 0) → ∀ w : Fin m → (Fin n → ℝ) → ℂ, (∀ a, ContDiff ℝ ∞ (w a) ∧ (∀ (ν : Fin n → ℤ) x, w a (x + fun k => (ν k : ℝ)) = w a x)) → (∀ a b x, ∑ k, p a k * fderiv ℝ (w b) x (Pi.single k 1) = ∑ k, p b k * fderiv ℝ (w a) x (Pi.single k 1)) → ∃ (t : Fin m → ℂ) (f : (Fin n → ℝ) → ℂ), ContDiff ℝ ∞ f ∧ (∀ (ν : Fin n → ℤ) x, f (x + fun k => (ν k : ℝ)) = f x) ∧ ∀ a x, ∑ k, p a k * fderiv ℝ f x (Pi.single k 1) = w a x - t a := by
  first | exact @GlobalTheory.torus_elliptic_system_solvable | exact GlobalTheory.torus_elliptic_system_solvable | (intros; apply GlobalTheory.torus_elliptic_system_solvable <;> assumption)
