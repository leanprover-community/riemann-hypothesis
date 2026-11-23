module

public import Formalism.HermitianCurvature.StatementWd
public import Mathlib.Basic.Complex.Basic
public import Mathlib.CategoryTheory.Category.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.HermitianCurvature.StatementQ
import Formalism.RealPlaceAnalysis.StatementA

@[expose] public section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

namespace TwistedTransfer

section Alg

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]

theorem io_mul' (x y : A) : (io (x * y) : SlopeTestRemainingChoices S A) = io x * io y := by
  simp only [io, map_mul]

theorem io_add' (x y : A) : (io (x + y) : SlopeTestRemainingChoices S A) = io x + io y := by
  simp only [io, map_add (f := _)]

theorem io_sub' (x y : A) : (io (x - y) : SlopeTestRemainingChoices S A) = io x - io y := by
  simp only [io, map_sub]

theorem io_neg' (x : A) : (io (-x) : SlopeTestRemainingChoices S A) = -io x := by
  simp only [io, map_neg]

theorem io_one' : (io (1 : A) : SlopeTestRemainingChoices S A) = 1 := by
  simp only [io, map_one]

theorem io_zero' : (io (0 : A) : SlopeTestRemainingChoices S A) = 0 := by
  simp only [io, map_zero]

theorem io_algebraMap (t : ℂ) : (io (algebraMap ℂ A t) : SlopeTestRemainingChoices S A) = t • (1 : SlopeTestRemainingChoices S A) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [io, Algebra.algebraMap_eq_smul_one]
  · simp [io, Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h]

theorem commute_io_io {x y : A} (h : Commute x y) : Commute (io x : SlopeTestRemainingChoices S A) (io y) := by
  unfold io
  exact h.map _

theorem commute_smul_one (t : ℂ) (z : SlopeTestRemainingChoices S A) : Commute z (t • (1 : SlopeTestRemainingChoices S A)) :=
  (Commute.one_right z).smul_right t

theorem commute_inv {R : Type*} [Ring R] {a x y : R} (h : Commute a x) (h1 : x * y = 1) (h2 : y * x = 1) :
    Commute a y := by
  show a * y = y * a
  calc a * y = (y * x) * (a * y) := by rw [h2, one_mul]
    _ = y * (x * a) * y := by simp only [mul_assoc]
    _ = y * (a * x) * y := by rw [h.eq]
    _ = y * a * (x * y) := by simp only [mul_assoc]
    _ = y * a := by rw [h1, mul_one]

def cj (f fi : A) (z : SlopeTestRemainingChoices S A) : SlopeTestRemainingChoices S A := io fi * z * io f

variable {f fi : A}

theorem io_f_fi (h : f * fi = 1) : (io f : SlopeTestRemainingChoices S A) * io fi = 1 := by
  rw [← io_mul', h, io_one']

theorem cj_mul (h : f * fi = 1) (z w : SlopeTestRemainingChoices S A) : cj f fi (z * w) = cj f fi z * cj f fi w := by
  have h' : (io f : SlopeTestRemainingChoices S A) * io fi = 1 := io_f_fi h
  simp only [cj, mul_assoc]
  rw [← mul_assoc (io f : SlopeTestRemainingChoices S A) (io fi), h', one_mul]

theorem cj_add (z w : SlopeTestRemainingChoices S A) : cj f fi (z + w) = cj f fi z + cj f fi w := by
  simp only [cj, mul_add, add_mul]

theorem cj_zero : cj f fi (0 : SlopeTestRemainingChoices S A) = 0 := by
  simp only [cj, mul_zero, zero_mul]

theorem cj_of_comm (h : fi * f = 1) {z : SlopeTestRemainingChoices S A} (hz : Commute (io f) z) : cj f fi z = z := by
  have h' : (io fi : SlopeTestRemainingChoices S A) * io f = 1 := io_f_fi h
  unfold cj
  rw [mul_assoc, ← hz.eq, ← mul_assoc, h', one_mul]

theorem cj_io (x : A) : cj f fi (io x : SlopeTestRemainingChoices S A) = io (fi * x * f) := by
  simp only [cj, io_mul']

private theorem io_mul_eU_comm (c : A) (a : S) (i j : Fin 2) :
    (io c : SlopeTestRemainingChoices S A) * eU a i j = eU a i j * io c := by
  ext x y
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, eU, Matrix.of_apply]
  split_ifs <;> simp

theorem cj_ins (a : S) (M : M2 (SlopeTestRemainingChoices S A)) : cj f fi (ins a M) = ins a (M.map (cj f fi)) := by
  simp only [cj, ins, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hc : (io fi : SlopeTestRemainingChoices S A) * eU a i j = eU a i j * io fi := io_mul_eU_comm fi a i j
  calc (io fi : SlopeTestRemainingChoices S A) * (eU a i j * M i j) * io f = ((io fi : SlopeTestRemainingChoices S A) * eU a i j) * M i j * io f := by
        simp only [mul_assoc]
    _ = eU a i j * ((io fi : SlopeTestRemainingChoices S A) * M i j * io f) := by
        rw [hc]
        simp only [mul_assoc]

def Tw (f fi : A) (t : ℂ) (z : SlopeTestRemainingChoices S A) : Prop := cj f fi z = z - t • (1 : SlopeTestRemainingChoices S A)

theorem lift_unipotent_inverse (t : ℂ) : (lift0 (Uinv (A := A) t) : M2 (SlopeTestRemainingChoices S A)) = !![1, 0; t • 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lift0, Uinv, io_one', io_zero', io_algebraMap]

end Alg

end TwistedTransfer

end Formalism.FourierDecayAlt.P5
