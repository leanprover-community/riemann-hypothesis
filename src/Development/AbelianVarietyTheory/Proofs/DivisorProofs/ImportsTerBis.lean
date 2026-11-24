module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
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

namespace GlobalTheory.IntertwiningOperators

open Polynomial

theorem intertwine {K : Type} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K) (h : C * A = B * C)
    (p : K[X]) : aeval B p * C = C * aeval A p := by
  induction p using Polynomial.induction_on with
  | C c =>
    simp only [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial n c ih =>
    rw [pow_succ, ← mul_assoc, map_mul (aeval B) (Polynomial.C c * X ^ n) X,
      map_mul (aeval A) (Polynomial.C c * X ^ n) X, aeval_X, aeval_X, Matrix.mul_assoc, ← h,
      ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

theorem main : ∀ {K : Type} [inst : Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K),
    IsCoprime (Matrix.charpoly A) (Matrix.charpoly B) → C * A = B * C →
      C = (0 : Matrix (Fin b) (Fin a) K) := by
  intro K _ a b A B C hcop h
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : aeval B u * aeval B (Matrix.charpoly A) = 1 := by
    have := congrArg (aeval B) huv
    rw [map_add (f := _), map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, add_zero, map_one] at this
    exact this
  have h2 : aeval B (Matrix.charpoly A) * C = 0 := by
    rw [intertwine A B C h, Matrix.aeval_self_charpoly, Matrix.mul_zero]
  calc C = (aeval B u * aeval B (Matrix.charpoly A)) * C := by rw [h1, Matrix.one_mul]
    _ = 0 := by rw [Matrix.mul_assoc, h2, Matrix.mul_zero]

end GlobalTheory.IntertwiningOperators
