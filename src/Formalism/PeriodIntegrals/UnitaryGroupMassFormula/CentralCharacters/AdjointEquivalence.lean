module

public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.RealPlaceAnalysis.Complexify
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.DSInfCharCap

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.DSIC

open PI.DSInfCharCap
open scoped InnerProductSpace Matrix

theorem jm_sq {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  rcases eq_or_ne i j with rfl | h
  · cases hε : ε i <;> simp [Matrix.diagonal_apply, hε]
  · simp [Matrix.diagonal_apply, Matrix.one_apply, h]

theorem jm_jm_mul {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := by
  rw [← Matrix.mul_assoc, jm_sq, Matrix.one_mul]

theorem jm_inv {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_left_inv (jm_sq ε)

theorem jm_isUnit {n : ℕ} (ε : Fin n → Bool) : IsUnit (Formalism.REAL.Jm ε) := ⟨⟨Formalism.REAL.Jm ε, Formalism.REAL.Jm ε, jm_sq ε, jm_sq ε⟩, rfl⟩

theorem mem_UJset_iff {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ PI.UpqRep.UJset ε ↔ gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := Iff.rfl

theorem exp_mem_UJ {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ PI.UpqRep.UJset ε := by
  rw [mem_UJset_iff]
  set A : Matrix (Fin n) (Fin n) ℂ := (t : ℂ) • X with hAdef
  have h0 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX
  have hX' : Xᴴ = -(Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) := by
    calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [Matrix.mul_assoc, jm_sq, Matrix.mul_one]
      _ = _ := by rw [h0, Matrix.neg_mul]
  have hA : Aᴴ = Formalism.REAL.Jm ε * (-A) * (Formalism.REAL.Jm ε)⁻¹ := by
    have ht : star (t : ℂ) = t := Complex.conj_ofReal t
    rw [jm_inv, hAdef, Matrix.conjTranspose_smul, hX', ht]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]
  have hcomm : NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
    rw [← Matrix.exp_add_of_commute (-A) A (Commute.neg_left (Commute.refl A)), neg_add_cancel,
      NormedSpace.exp_zero]
  rw [← Matrix.exp_conjTranspose, hA, Matrix.exp_conj _ _ (jm_isUnit ε), jm_inv]
  calc Formalism.REAL.Jm ε * NormedSpace.exp (-A) * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε * NormedSpace.exp A
      = Formalism.REAL.Jm ε * (NormedSpace.exp (-A) * NormedSpace.exp A) := by
        simp only [Matrix.mul_assoc, jm_jm_mul]
    _ = Formalism.REAL.Jm ε := by rw [hcomm, Matrix.mul_one]

end PI.UnitaryGroupMassFormula.DSIC
