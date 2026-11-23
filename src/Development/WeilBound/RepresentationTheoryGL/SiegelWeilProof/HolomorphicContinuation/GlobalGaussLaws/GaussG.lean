module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem conj_half_smul (Z : Matrix (Fin n) (Fin n) ℂ) : ((1 / 2 : ℂ) • (Z + Zᴴ))ᴴ = (1 / 2 : ℂ) • (Z + Zᴴ) := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
  congr 1
  simp [Complex.ext_iff]

theorem exists_sqrt {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y.PosDef) : ∃ S : Matrix (Fin n) (Fin n) ℂ, S * Sᴴ = Y ∧ IsUnit S.det := by
  classical
  have hH := hY.1
  let U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  let d : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => ((Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ))
  have hd : d * dᴴ = diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, Function.comp_apply]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hY.eigenvalues_pos i).le]
    rfl
  have hS : U * d * (U * d)ᴴ = Y := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc d, hd]
    conv_rhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    simp [U, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  refine ⟨U * d, hS, ?_⟩
  have hYu : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp hY.isUnit
  rw [← hS, Matrix.det_mul] at hYu
  exact isUnit_of_mul_isUnit_left hYu

end PositivityTheory.Rg.Sw.Glob.GaussH
