module

public import Formalism.CyclotomicNorms.StatementI
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset Polynomial

noncomputable section

namespace Formalism.CyclotomicNorms

namespace Sqf

variable {K : Type} [Field K]

lemma coeff_monicOf_lt {N : ℕ} (a : Fin N → K) (i : Fin N) :
    (monicOf a).coeff (i : ℕ) = a i := by
  unfold monicOf
  rw [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt i.2), zero_add, Polynomial.finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i (fun j _ hj => if_neg (fun h => hj (Fin.ext h).symm)) (by simp)]
  simp

lemma coeff_monicOf_ge {N : ℕ} (a : Fin N → K) (k : ℕ) (hk : N ≤ k) :
    (monicOf a).coeff k = if k = N then 1 else 0 := by
  unfold monicOf
  rw [coeff_add, coeff_X_pow, Polynomial.finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_zero (fun j _ => if_neg (by have := j.2; omega)), add_zero]

lemma natDegree_monicOf {N : ℕ} (a : Fin N → K) : (monicOf a).natDegree = N := by
  unfold monicOf
  rw [natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt a), natDegree_X_pow]

lemma monic_monicOf {N : ℕ} (a : Fin N → K) : (monicOf a).Monic := by
  unfold monicOf
  exact monic_X_pow_add (degree_sum_fin_lt a)

lemma monicOf_coeffs (p : K[X]) (hp : p.Monic) {m : ℕ} (hd : p.natDegree = m) :
    monicOf (fun i : Fin m => p.coeff i) = p := by
  ext n
  rcases lt_or_ge n m with h | h
  · exact coeff_monicOf_lt (fun i : Fin m => p.coeff i) ⟨n, h⟩
  · rw [coeff_monicOf_ge _ n h]
    split_ifs with hn
    · subst hn
      rw [← hd]
      exact hp.coeff_natDegree.symm
    · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

end Sqf

end Formalism.CyclotomicNorms
