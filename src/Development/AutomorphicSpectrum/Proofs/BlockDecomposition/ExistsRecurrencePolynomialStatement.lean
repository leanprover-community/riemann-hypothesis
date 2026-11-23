module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRecurrencePolynomial
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.exists_recurrence_polynomial : ∀ (G : Type) [Group G] (a : ℝ → G) (F₀ : G → ℂ) (S : Submodule ℂ (ℝ → ℂ)), (∀ s t, a (s + t) = a s * a t) →
  (∀ g, Continuous fun t => F₀ (a t * g)) → FiniteDimensional ℂ S → (∀ g, (fun t => F₀ (a t * g)) ∈ S) →
  ∃ p : ℂ[X], p.Monic ∧ p.natDegree ≤ Module.finrank ℂ S ∧ (∀ g, ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * F₀ (a j * g) = 0) ∧
    ∀ z, p.IsRoot z → ∃ c : ℂ, z = Complex.exp c ∧
      ∃ F ∈ Submodule.span ℂ (Set.range fun t : ℝ => fun g => F₀ (a t * g)), F ≠ 0 ∧
        ∀ (t : ℝ) g, F (a t * g) = Complex.exp (c * t) * F g := by
  exact @GlobalTheory.CompanionTheory.KillDeg.killPoly_natDegree_le
