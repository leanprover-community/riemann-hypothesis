module

public import Formalism.PolynomialDimension.StatementHar
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option linter.unusedSimpArgs false

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.CountingSumsFrames

section Gen

variable (K : Type) [Field K] (k : ℕ)

def eulX_har (f : PolXY K k) : PolXY K k := ∑ i : Fin k, X (Sum.inl i) * pderiv (Sum.inl i) f

def eulY (f : PolXY K k) : PolXY K k := ∑ i : Fin k, X (Sum.inr i) * pderiv (Sum.inr i) f

variable {K k}

theorem ctrF_apply (f : PolXY K k) :
    ctrF K k f = ∑ i : Fin k, pderiv (Sum.inl i) (pderiv (Sum.inr i) f) := by
  simp [ctrF, LinearMap.sum_apply]

theorem pderiv_inl_h (i : Fin k) : pderiv (Sum.inl i) (hXY K k) = X (Sum.inr i) := by
  classical
  simp [hXY, pderiv_X, Pi.single_apply, Finset.sum_ite_eq']

theorem pderiv_inr_h (i : Fin k) : pderiv (Sum.inr i) (hXY K k) = X (Sum.inl i) := by
  classical
  simp [hXY, pderiv_X, Pi.single_apply, Finset.sum_ite_eq']

theorem ctrF_h_mul (f : PolXY K k) :
    ctrF K k (hXY K k * f) = hXY K k * ctrF K k f + (k : K) • f + eulX_har K k f + eulY K k f := by
  classical
  have key : ∀ i : Fin k, pderiv (Sum.inl i) (pderiv (Sum.inr i) (hXY K k * f)) =
      hXY K k * pderiv (Sum.inl i) (pderiv (Sum.inr i) f) + f +
        X (Sum.inl i) * pderiv (Sum.inl i) f + X (Sum.inr i) * pderiv (Sum.inr i) f := by
    intro i
    rw [pderiv_mul, pderiv_inr_h, map_add (f := _), pderiv_mul, pderiv_mul, pderiv_inl_h, pderiv_X_self]
    ring
  rw [ctrF_apply, ctrF_apply, eulX_har, eulY, Finset.sum_congr rfl (fun i _ => key i)]
  simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul K]

theorem coeff_X_mul_pderiv (v : XY k) (f : PolXY K k) (m : XY k →₀ ℕ) :
    AddMonoidAlgebra.coeff (X v * pderiv v f) m = (m v : K) * AddMonoidAlgebra.coeff f m := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => simp [mul_add, hp, hq]
  | monomial n a =>
    rw [X_mul_pderiv_monomial, MvPolynomial.coeff_smul, coeff_monomial]
    by_cases h : n = m
    · subst h; simp
    · simp [h]

theorem coeff_eulX (f : PolXY K k) (m : XY k →₀ ℕ) :
    AddMonoidAlgebra.coeff (eulX_har K k f) m = (xDeg m : K) * AddMonoidAlgebra.coeff f m := by
  simp [eulX_har, coeff_sum, coeff_X_mul_pderiv, xDeg, Finset.sum_mul]

theorem coeff_eulY (f : PolXY K k) (m : XY k →₀ ℕ) :
    AddMonoidAlgebra.coeff (eulY K k f) m = (yDeg m : K) * AddMonoidAlgebra.coeff f m := by
  simp [eulY, coeff_sum, coeff_X_mul_pderiv, yDeg, Finset.sum_mul]

theorem eulX_of_mem {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    eulX_har K k f = (A : K) • f := by
  ext m
  rw [coeff_eulX, MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases hm : m ∈ f.support
  · rw [(hf m hm).1]
  · rw [notMem_support_iff.1 hm]; simp

theorem eulY_of_mem {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    eulY K k f = (B : K) • f := by
  ext m
  rw [coeff_eulY, MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases hm : m ∈ f.support
  · rw [(hf m hm).2]
  · rw [notMem_support_iff.1 hm]; simp

end Gen

theorem slTwoCommutator_holds : SlTwo := by
  intro K _ _ k A B f hf
  rw [ctrF_h_mul, eulX_of_mem hf, eulY_of_mem hf]
  simp only [Algebra.smul_def, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_zero, map_add (f := _), map_mul,
      map_one, map_zero, map_natCast]
  ring

section Gen2

variable {K : Type} [Field K] {k : ℕ}

end Gen2

section Fis

variable {K : Type} [Field K] {k : ℕ}

end Fis

section Can

variable {K : Type} [Field K] {k : ℕ}

end Can

end Formalism.CountingSumsFrames
