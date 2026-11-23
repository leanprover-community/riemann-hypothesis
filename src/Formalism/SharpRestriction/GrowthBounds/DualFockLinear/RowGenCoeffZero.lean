module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.MemHdIff
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FormCoreSK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.GradedWeylDivisibility
open Formalism.L2.G.Model.TS (fockR)

theorem RE_X (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (v : Fin k × Fin k) :
    RE K k a b (X v) = if v.1 = b then X (a, v.2) else 0 := by
  unfold RE
  simp only [pderiv_X]
  by_cases h : v.1 = b
  · rw [if_pos h, Finset.sum_eq_single v.2]
    · have : ((b, v.2) : Fin k × Fin k) = v := Prod.ext h.symm rfl
      rw [this, Pi.single_eq_same, mul_one]
    · intro t _ ht
      rw [Pi.single_eq_of_ne, mul_zero]
      intro hv
      apply ht
      rw [hv]
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro t _
    rw [Pi.single_eq_of_ne, mul_zero]
    intro hv
    apply h
    rw [hv]

theorem RE_C (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (r : K) : RE K k a b (C r) = 0 := by
  unfold RE
  simp

theorem rowGen_coeff_zero (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k × Fin k) K) :
    (rowGen K a b f).coeff 0 = f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add (f := _), Polynomial.coeff_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, hp]
    congr 1
    simp only [rowGen, aeval_X]
    split_ifs <;> simp

theorem RE_eq_rowDiv (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k × Fin k) K) :
    RE K k a b f = rowDiv K a b 1 f := by
  unfold rowDiv
  induction f using MvPolynomial.induction_on with
  | C r => rw [RE_C]; simp [rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, Polynomial.coeff_C]
  | add p q hp hq => rw [RE_add, map_add (f := _), Polynomial.coeff_add, hp, hq]
  | mul_X p v hp =>
    rw [RE_mul, map_mul, Polynomial.mul_coeff_one, rowGen_coeff_zero, rowGen_coeff_zero, hp, RE_X]
    have : (rowGen K a b (X v)).coeff 1 = if v.1 = b then X (a, v.2) else 0 := by
      simp only [rowGen, aeval_X]
      split_ifs <;> simp [Polynomial.coeff_C]
    rw [this]
    ring

theorem restAdj : RestAdj := by
  intro K _ k a b P Q
  rw [RE_eq_rowDiv, RE_eq_rowDiv]
  exact Formalism.L2.G.Model.TS.Top.fockRRowDivAdj K k k a b 1 P Q

theorem restStab : RestStab := by
  intro K _ _ k ν a b P hP
  rw [RE_eq_rowDiv]
  exact rowDivStable K k k ν a b 1 P hP

end Formalism.MainNotions.TestSideCounting
