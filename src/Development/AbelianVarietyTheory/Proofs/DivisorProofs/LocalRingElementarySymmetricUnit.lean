module

public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZM

namespace GlobalTheory


open Polynomial in
theorem exists_isUnit_esymm_of_eq_one :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [Fintype A] (y : A → R) (a₀ : A),
      y a₀ = 1 → ∃ k : ℕ, 1 ≤ k ∧ k ≤ Fintype.card A ∧
        IsUnit ((Finset.univ.val.map y).esymm k) := by
  intro R _ _ A _ y a₀ h
  by_contra! hne
  set s := Finset.univ.val.map y with hs
  have hcard : Multiset.card s = Fintype.card A := by simp [s, Finset.card_univ]
  have key := congrArg (Polynomial.eval (1 : R)) (Multiset.prod_X_sub_X_eq_sum_esymm s)
  have h0 : ((s.map fun t => X - C t).prod).eval 1 = 0 := by
    rw [Polynomial.eval_multiset_prod]
    apply Multiset.prod_eq_zero
    rw [Multiset.map_map, Multiset.mem_map]
    exact ⟨y a₀, by simp [s], by simp [h]⟩
  rw [h0, Polynomial.eval_finsetSum, Finset.sum_range_succ'] at key
  simp only [eval_mul, eval_pow, eval_neg, eval_one, eval_C, eval_X, one_pow, mul_one,
    pow_zero, one_mul] at key
  have he0 : s.esymm 0 = 1 := by simp [Multiset.esymm, Multiset.powersetCard_zero_left]
  rw [he0] at key
  have hmem : ∑ j ∈ Finset.range (Multiset.card s), (-1 : R) ^ (j + 1) * s.esymm (j + 1)
      ∈ IsLocalRing.maximalIdeal R := by
    apply Ideal.sum_mem
    intro j hj
    apply Ideal.mul_mem_left
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    apply hne (j + 1) (by omega)
    rw [← hcard]; exact Finset.mem_range.mp hj
  have h1 : (1 : R) = -∑ j ∈ Finset.range (Multiset.card s), (-1 : R) ^ (j + 1) * s.esymm (j + 1) := by
    linear_combination -key
  have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [h1]; exact neg_mem hmem
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr this)

end GlobalTheory
