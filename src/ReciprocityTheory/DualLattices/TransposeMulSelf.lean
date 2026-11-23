module

public import ReciprocityTheory.DualLattices.NearIdentityColengthStatement
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
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Basic.PEquiv
public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

@[expose] public section

namespace ReciprocityTheory.PGsh

open Matrix

section

variable {K : Type} [Field K] {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

private noncomputable def invPerm (e : G ≃ AddChar G K) : Equiv.Perm G :=
  Function.Involutive.toPerm (fun h => e.symm (e h)⁻¹) (fun h => by simp)

private lemma invPerm_apply (e : G ≃ AddChar G K) (h : G) :
    invPerm e h = e.symm (e h)⁻¹ := rfl

private lemma transpose_mul_self (e : G ≃ AddChar G K) :
    (Matrix.of fun g h : G => e h g)ᵀ * (Matrix.of fun g h : G => e h g) =
      (Fintype.card G : K) • (invPerm e).permMatrix K := by
  ext g h
  have key : ∀ x, e g x * e h x = (e g * e h) x := fun x => (AddChar.mul_apply _ _ _).symm
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.smul_apply,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, smul_eq_mul, key]
  by_cases hgh : e g * e h = 1
  · have h1 : invPerm e g = h := by
      rw [invPerm_apply, inv_eq_of_mul_eq_one_right hgh, Equiv.symm_apply_apply]
    rw [if_pos h1, hgh]
    simp
  · have h1 : ¬ invPerm e g = h := by
      intro h1
      apply hgh
      rw [invPerm_apply] at h1
      rw [← h1, Equiv.apply_symm_apply, mul_inv_cancel]
    rw [if_neg h1, AddChar.sum_eq_zero_of_ne_one hgh, mul_zero]

private lemma det_sq (e : G ≃ AddChar G K) :
    (Matrix.of fun g h : G => e h g).det ^ 2 =
      (Fintype.card G : K) ^ Fintype.card G * (Equiv.Perm.sign (invPerm e) : K) := by
  have h := congrArg Matrix.det (transpose_mul_self e)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_permutation] at h
  rw [sq]
  exact h

end

theorem charTable : CharTableStatement := by
  intro K _ G _ _ _ e
  rw [det_sq e]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (invPerm e)) with h | h <;> rw [h]
  · left; simp
  · right; simp

end ReciprocityTheory.PGsh
