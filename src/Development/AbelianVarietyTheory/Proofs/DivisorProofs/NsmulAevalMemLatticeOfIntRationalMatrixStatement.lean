module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NsmulAevalMemLatticeOfIntRationalMatrix
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

open Matrix

theorem _root_.GlobalTheory.T.nsmul_aeval_mem_lattice_of_int_rational_matrix : ∀ (g n : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)),
    (∀ x, x ∈ Λ ↔ ∀ k, ∃ m : ℤ, e.repr x k = m) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ),
    Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) →
    ∀ (p : Polynomial ℚ) (D : ℕ), (∀ k l, ∃ m : ℤ, (D : ℚ) * Polynomial.aeval Tq p k l = m) →
    ∀ x ∈ Λ, (D • Polynomial.aeval γ p) x ∈ Λ := by
  first | exact @GlobalTheory.nsmul_aeval_mem_lattice_of_intMatrix | exact GlobalTheory.nsmul_aeval_mem_lattice_of_intMatrix | (intros; apply GlobalTheory.nsmul_aeval_mem_lattice_of_intMatrix <;> assumption)
