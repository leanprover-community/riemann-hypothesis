module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsNormForm
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
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem linearForm_coeff_single {F : Type} [Field F] {n : ℕ} (a : Fin n → F) (i : Fin n) :
    (∑ m, X m * C (a m) : MvPolynomial (Fin n) F).coeff (Finsupp.single i 1) = a i := by
  classical
  rw [coeff_sum, Finset.sum_eq_single i]
  · rw [mul_comm, coeff_C_mul, coeff_X]
    simp
  · intro j _ hji
    rw [mul_comm, coeff_C_mul, coeff_X, if_neg, mul_zero]
    intro h
    exact hji ((Finsupp.single_left_inj one_ne_zero).mp h)
  · simp

theorem LinearFormPrime.proof : LinearFormPrime.Statement := by
  intro F _ n a ha
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  refine Irreducible.prime (irreducible_of_totalDegree_eq_one ?_ ?_)
  · apply le_antisymm
    · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m _ => ?_)
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X, totalDegree_C]
    · have hs : Finsupp.single i 1 ∈ (∑ m, X m * C (a m) : MvPolynomial (Fin n) F).support := by
        rw [mem_support_iff, linearForm_coeff_single]
        exact hi
      simpa using le_totalDegree hs
  · intro x hx
    have h := hx (Finsupp.single i 1)
    rw [linearForm_coeff_single] at h
    refine isUnit_iff_ne_zero.mpr ?_
    rintro rfl
    exact hi (zero_dvd_iff.mp h)

end

end GroundTheory.Heights₂.Heights
