module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.SortedSpec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Spectrum
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Finset

noncomputable section

namespace PI.ET

theorem specExists : SpecExists := by
  intro n A hA
  have hH : A.IsHermitian := hA
  set U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUU : U * star U = 1 := (Matrix.mem_unitaryGroup_iff).1 hH.eigenvectorUnitary.2
  have hspec := hH.spectral_theorem
  set l : Fin n → ℝ := hH.eigenvalues with hl

  let σ : Equiv.Perm (Fin n) := Tuple.sort (fun i => OrderDual.toDual (l i))
  have hmono : Monotone ((fun i => OrderDual.toDual (l i)) ∘ σ) := Tuple.monotone_sort _
  refine ⟨l ∘ σ, fun i j hij => hmono hij, U.submatrix id σ, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose, hUU, Matrix.submatrix_id_id]
  · have hD : Matrix.diagonal (fun i => ((l ∘ σ) i : ℂ)) =
        (Matrix.diagonal (fun i => (l i : ℂ))).submatrix σ σ := by
      rw [Matrix.submatrix_diagonal_equiv]
      rfl
    rw [hD, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id]
    conv_lhs => rw [hspec]
    rfl

theorem hsEq : HSEq := by
  intro n A d ⟨_, W, hW, hA⟩
  have hWW : star W * W = 1 := (Matrix.mem_unitaryGroup_iff').1 hW
  rw [Matrix.star_eq_conjTranspose] at hWW
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => (d i : ℂ) with hD
  have hDh : Dᴴ = D := by
    rw [hD, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp [Pi.star_apply, Complex.star_def]
  have hAh : Aᴴ = W * D * Wᴴ := by
    rw [hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hDh,
      Matrix.mul_assoc]
  have key : (A * Aᴴ).trace = ∑ i, ((d i : ℂ)) ^ 2 := by
    rw [hAh, hA]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Wᴴ W, hWW, Matrix.one_mul, Matrix.trace_mul_comm, Matrix.mul_assoc,
      Matrix.mul_assoc, hWW, Matrix.mul_one, hD, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    simp [sq]
  have lhs : (A * Aᴴ).trace = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.mul_conj']
  have := lhs.symm.trans key
  exact_mod_cast this

end PI.ET
