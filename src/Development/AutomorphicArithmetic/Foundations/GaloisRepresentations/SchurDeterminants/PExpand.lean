module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset MvPolynomial UpperTheory.Gal.Schur

private lemma one_factor {K R : Type} [CommRing K] [CommRing R] [Algebra K R] (n : ℕ) (x : R)
    (g : Fin n → R) :
    detOne x g = ∑ a : Fin (n + 1), x ^ (a : ℕ) * ((-1) ^ (a : ℕ) * aeval g (esymm (Fin n) K a)) := by
  have key : ∀ a : ℕ, x ^ a * ((-1) ^ a * aeval g (esymm (Fin n) K a)) =
      ∑ t ∈ powersetCard a (univ : Finset (Fin n)), ∏ j ∈ t, (-(x * g j)) := by
    intro a

    simp only [esymm, map_sum, map_prod, aeval_X, mul_sum]
    refine sum_congr rfl fun t ht => ?_
    rw [prod_neg, prod_mul_distrib, prod_const, (mem_powersetCard.1 ht).2]
    ring
  rw [Fin.sum_univ_eq_sum_range (fun a => x ^ a * ((-1) ^ a * aeval g (esymm (Fin n) K a))) (n + 1)]
  simp only [key]
  have hc : n + 1 = #(univ : Finset (Fin n)) + 1 := by simp
  rw [hc, ← sum_powerset, ← prod_one_add]
  unfold detOne
  simp only [sub_eq_add_neg]

theorem UpperTheory.Gal.Schur.expand :
    Expand := by
  intro K R π _ _ _ _ _ n x g
  simp only [one_factor (K := K)]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [prod_mul_distrib]
