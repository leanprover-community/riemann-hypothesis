module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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

namespace GlobalTheory.DeterminantProductExpansion

theorem det_mul_expand {R : Type} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R) (B : Matrix (Fin N) (Fin i) R) :
    Matrix.det (A * B) = ∑ f : Fin i → Fin N, (∏ a : Fin i, A a (f a)) * Matrix.det (Matrix.submatrix B f id) := by
  let g : Fin i → Fin N → (Fin i → R) := fun a k => A a k • (fun j => B k j)
  have hrow : (A * B : Matrix (Fin i) (Fin i) R) = Matrix.of (fun a => ∑ k : Fin N, g a k) := by
    ext a j
    simp [g, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : Matrix.det (A * B) =
      (Matrix.detRowAlternating : (Fin i → R) [⋀^Fin i]→ₗ[R] R).toMultilinearMap (fun a => ∑ k : Fin N, g a k) := by
    rw [hrow]; rfl

  rw [h1, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  simp only [g]
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

theorem main : ∀ {R : Type} [inst : CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R) (B : Matrix (Fin N) (Fin i) R), Matrix.det (A * B) = ∑ f : Fin i → Fin N, (∏ a : Fin i, A a (f a)) * Matrix.det (Matrix.submatrix B f id) :=
  fun A B => det_mul_expand A B

end GlobalTheory.DeterminantProductExpansion
