module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
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

namespace GlobalTheory

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem discr_mul_isIntegral_of_traceDual :
    ∀ (K : Type) [Field K] [NumberField K] (x : K), (∀ y : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (x * y) = n) →
    IsIntegral ℤ ((discr K : K) * x) := by
  intro K _ _ x hx
  classical
  have hmem : ((NumberField.discr K).natAbs : 𝓞 K) ∈ differentIdeal ℤ (𝓞 K) := by
    rw [← NumberField.absNorm_differentIdeal K (𝓞 K)]
    exact Ideal.absNorm_mem _
  have hdual : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K))]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨k, hk⟩ := hx b
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, eq_intCast, ← hk, mul_comm]
  have hprod := FractionalIdeal.mul_mem_mul
    (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ hmem) hdual
  rw [coeIdeal_differentIdeal ℤ ℚ, inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ
    (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K)))] at hprod
  obtain ⟨α, hα⟩ := (FractionalIdeal.mem_one_iff _).mp hprod
  rw [map_natCast] at hα
  have hint : IsIntegral ℤ (((NumberField.discr K).natAbs : K) * x) := by
    rw [← hα]
    exact α.isIntegral_coe
  rcases Int.natAbs_eq (NumberField.discr K) with h | h
  · rw [h]
    simpa using hint
  · rw [h]
    simpa using hint.neg

end GlobalTheory
