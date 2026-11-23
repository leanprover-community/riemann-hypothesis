module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

theorem hJ_adj {n : ℕ} {ε : Fin n → Bool} (s : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    hJ ε x (uMat s *ᵥ y) = hJ ε (uMat s⁻¹ *ᵥ x) y := by
  have hU : (uMat s)ᴴ * Formalism.REAL.Jm ε * uMat s = Formalism.REAL.Jm ε := s.2
  have hinv : uMat s * uMat s⁻¹ = 1 := by
    simp [Formalism.MainNotions.S.uMat]
  have hJc : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    rw [Pi.star_apply]
    split_ifs <;> simp
  have h1 : (uMat s)ᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat s⁻¹ := by
    calc (uMat s)ᴴ * Formalism.REAL.Jm ε = (uMat s)ᴴ * Formalism.REAL.Jm ε * (uMat s * uMat s⁻¹) := by
          rw [hinv, Matrix.mul_one]
      _ = Formalism.REAL.Jm ε * uMat s⁻¹ := by rw [← Matrix.mul_assoc, hU]
  have key : (uMat s⁻¹)ᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat s := by
    have h2 := congrArg Matrix.conjTranspose h1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJc] at h2
    exact h2.symm
  simp only [Formalism.L2.SG.HidaSetting.hJ, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, key]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
