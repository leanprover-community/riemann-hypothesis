module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.NablaBasis
public import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

namespace PI.SlopeSteps

open Finset

theorem multinomial_le_pow {N : ℕ} (f : Fin N → ℕ) : Nat.multinomial univ f ≤ N ^ (∑ a, f a) := by
  have h := Finset.sum_pow_eq_sum_piAntidiag (R := ℕ) (univ : Finset (Fin N)) (fun _ => (1 : ℕ)) (∑ a, f a)
  simp only [one_pow, prod_const_one, mul_one, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h
  rw [h]
  exact Finset.single_le_sum (f := fun k => Nat.multinomial univ k) (fun _ _ => Nat.zero_le _)
    (mem_piAntidiag.mpr ⟨rfl, fun i _ => mem_univ i⟩)

theorem col_fact_le {N : ℕ} (f : Fin N → ℕ) :
    (∑ a, f a).factorial ≤ N ^ (∑ a, f a) * ∏ a, (f a).factorial := by
  rw [← Nat.multinomial_spec univ f, mul_comm]
  exact Nat.mul_le_mul_right _ (multinomial_le_pow f)

theorem monomial_factorization_lower : MonoFactLow := by
  intro N ν m hm
  classical
  have h1 : ∏ k ∈ m.support, (m k).factorial = ∏ s : Fin N, ∏ a : Fin N, (m (a, s)).factorial := by
    rw [Finset.prod_subset (Finset.subset_univ _) (fun k _ hk => by
      rw [Finsupp.mem_support_iff, not_not] at hk
      rw [hk, Nat.factorial_zero])]
    rw [Fintype.prod_prod_type, Finset.prod_comm]
  rw [h1, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod' fun s _ => ?_
  have := col_fact_le (fun a => m (a, s))
  rwa [hm s] at this

end PI.SlopeSteps
