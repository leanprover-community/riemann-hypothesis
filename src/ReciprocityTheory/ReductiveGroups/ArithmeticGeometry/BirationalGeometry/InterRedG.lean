module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M

section Alg

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

open Classical in
theorem blockDeg_single (q : Σ k, ι k) (m : ℕ) (k' : K) :
    ∑ i, (Finsupp.single q m : (Σ k, ι k) →₀ ℕ) ⟨k', i⟩ = if q.1 = k' then m else 0 := by
  obtain ⟨k0, i0⟩ := q
  by_cases h : k0 = k'
  · subst h
    simp [Finsupp.single_apply]
  · simp [h]

def secOf (i : ∀ k, ι k) (b : K → ℕ) : MRing ι := ∏ k, X ⟨k, i k⟩ ^ b k

theorem secOf_eq (i : ∀ k, ι k) (b : K → ℕ) :
    secOf i b = monomial (∑ k, Finsupp.single (⟨k, i k⟩ : Σ k, ι k) (b k)) 1 := by
  rw [secOf, MvPolynomial.monomial_sum_one]
  simp [MvPolynomial.X_pow_eq_monomial]

theorem isMultiHomog_secOf (i : ∀ k, ι k) (b : K → ℕ) : IsMultiHomog (secOf i b) b := by
  classical
  intro m hm k
  rw [secOf_eq, MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hm
  subst hm
  simp only [Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp only [blockDeg_single]
  simp

theorem secOf_not_mem {P : Ideal (MRing ι)} (hP : P.IsPrime) {i : ∀ k, ι k}
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ P) (b : K → ℕ) : secOf i b ∉ P := by
  rw [secOf]
  intro h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hP)).1 h
  exact hi k (hP.mem_of_pow_mem _ hk)

end Alg

end ReciprocityTheory.ChartRestriction.G.Geo
