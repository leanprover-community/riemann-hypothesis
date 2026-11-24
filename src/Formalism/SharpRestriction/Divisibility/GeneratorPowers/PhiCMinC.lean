module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open Matrix

theorem whiten_holds : WhitenStatement := by
  intro d L hL
  have hH := hL.isHermitian
  set U : Matrix (Fin d) (Fin d) ℝ := (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) with hU
  set s : Matrix (Fin d) (Fin d) ℝ := Matrix.diagonal (fun i => Real.sqrt (hH.eigenvalues i)) with hs
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  have hstar : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hsq : s * s = Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    rw [hs, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp [Real.mul_self_sqrt (hL.eigenvalues_pos i).le]
  refine ⟨s * Uᵀ, ?_, ?_⟩
  · have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
    have h1 : (star U).det * U.det = 1 := by
      rw [← Matrix.det_mul, hUU, Matrix.det_one]
    have hdU : IsUnit U.det := isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul_eq_one h1)
    rw [Matrix.det_mul, Matrix.det_transpose]
    refine IsUnit.mul ?_ hdU
    rw [hs, Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact (Finset.prod_pos fun i _ => Real.sqrt_pos.mpr (hL.eigenvalues_pos i)).ne'
  · rw [Matrix.transpose_mul, Matrix.transpose_transpose, hs, Matrix.diagonal_transpose, ← hs,
      Matrix.mul_assoc, ← Matrix.mul_assoc s s, hsq, ← Matrix.mul_assoc, ← hstar]
    exact hspec

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
