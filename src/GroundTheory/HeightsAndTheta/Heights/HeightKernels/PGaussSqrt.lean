module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
public import Mathlib.Analysis.Matrix.Spectrum
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PGaussSqrt

theorem eq_eigenvectors_mul_diagonal {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hH : Y.IsHermitian) :
    Y = (hH.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ) * diagonal hH.eigenvalues *
      (hH.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ)ᵀ := by
  conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  rfl

end PGaussSqrt

theorem GaussSqrt.proof : GaussSqrt.Statement := by
  intro g Y hY
  classical
  set hH := hY.isHermitian
  set U : Matrix (Fin g) (Fin g) ℝ := (hH.eigenvectorUnitary : Matrix (Fin g) (Fin g) ℝ) with hUdef
  refine ⟨diagonal (fun i => √(hH.eigenvalues i)) * Uᵀ, ?_⟩
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => (hY.eigenvalues_pos i).le
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose]
  calc U * diagonal (fun i => √(hH.eigenvalues i)) * (diagonal (fun i => √(hH.eigenvalues i)) * Uᵀ)
      = U * (diagonal (fun i => √(hH.eigenvalues i)) * diagonal (fun i => √(hH.eigenvalues i)))
          * Uᵀ := by simp only [Matrix.mul_assoc]
    _ = U * diagonal hH.eigenvalues * Uᵀ := by
      have hsq : (fun i => √(hH.eigenvalues i) * √(hH.eigenvalues i)) = hH.eigenvalues :=
        funext fun i => Real.mul_self_sqrt (hnn i)
      rw [diagonal_mul_diagonal, hsq]
    _ = Y := (PGaussSqrt.eq_eigenvectors_mul_diagonal hH).symm

end GroundTheory.Heights₂.Heights
