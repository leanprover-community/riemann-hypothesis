module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace GlobalTheory.JSW

def colGL {R : Type} [CommRing R] {a : ℕ} (r : ℕ) (x : Fin a → R) : GL (Fin a) R :=
  ⟨1 + Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0),
   1 - Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0),
   by
    have h : Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) *
        Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) = 0 := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : (k : ℕ) = r
      · simp [hk]
      · simp [hk]
    rw [mul_sub, add_mul, add_mul, one_mul, mul_one, one_mul, h]; abel,
   by
    have h : Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) *
        Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) = 0 := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : (k : ℕ) = r
      · simp [hk]
      · simp [hk]
    rw [sub_mul, mul_add, mul_add, one_mul, mul_one, one_mul, h]; abel⟩

def mirSet (R : Type) [CommRing R] (m : ℕ) : Set (GL (Fin (m + 1)) R) :=
  {g | ∀ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (Fin.last m) j = if j = Fin.last m then 1 else 0}


end GlobalTheory.JSW
