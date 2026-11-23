module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotLinearIndependent
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.not_linearIndependent_alt : ∀ (U : Type) [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] (J : U →ₗ[ℝ] U) (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ), (∀ x, J (J x) = -x) → (∀ x y, om x y = -om y x) → (∀ x y, om (J x) (J y) = om x y) → (∀ x, x ≠ 0 → om (J x) x < 0) → ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (p : V →+ U), Function.Injective p → Submodule.span ℝ (Set.range p) = ⊤ → ∀ L : AddSubgroup V, (∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L) → (∀ x : V, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = k) → ∀ c : V → ℂ, (∀ v, ‖c v‖ = 1) → ∀ f : Fin 2 → U → ℂ, (∀ k, Differentiable ℝ (f k)) → (∀ k w z, (fderiv ℝ (f k) w z - Real.pi * Complex.I * (om w z : ℂ) * f k w) + Complex.I * (fderiv ℝ (f k) w (J z) - Real.pi * Complex.I * (om w (J z) : ℂ) * f k w) = 0) → (∀ k, ∀ v ∈ L, ∀ z, f k (z + p v) = c v * Complex.exp (-(Real.pi * Complex.I) * (om z (p v) : ℂ)) * f k z) → ¬ LinearIndependent ℂ f := by
  first | exact @GlobalTheory.VacuumLine.not_linearIndependent | exact GlobalTheory.VacuumLine.not_linearIndependent | (intros; apply GlobalTheory.VacuumLine.not_linearIndependent <;> assumption)
