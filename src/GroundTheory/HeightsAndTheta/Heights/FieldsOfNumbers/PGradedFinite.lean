module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
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
import Mathlib.Order.Interval.Finset.Box
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

section

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem finite_monomials_of_multidegree (m : K → ℕ) :
    {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}.Finite := by
  apply (Finsupp.finite_of_degree_eq (∑ k, m k)).subset
  intro d hd
  simp only [Set.mem_ofPred_eq] at hd ⊢
  rw [← hd, Finsupp.weight_eq_sum, Finsupp.degree_eq_sum, Finset.sum_fn, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [blockWeight, Pi.single_apply]

theorem finiteDimensional_multiHomogForms (F : Type*) [Field F] (m : K → ℕ) :
    FiniteDimensional F (weightedHomogeneousSubmodule F (blockWeight ι) m) := by
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]
  have := (finite_monomials_of_multidegree (ι := ι) m).to_subtype
  exact Module.Finite.of_basis
    (basisRestrictSupport F {d | Finsupp.weight (blockWeight ι) d = m})

end

theorem GradedFinite.proof : GradedFinite.Statement := by
  intro F _ K _ _ ι _ I m
  have hfin := finiteDimensional_multiHomogForms (ι := ι) F m
  have hP : FiniteDimensional F (gradedPiece I m) := by
    unfold gradedPiece
    exact Module.Finite.iff_fg.mpr
      ((Module.Finite.iff_fg.mp hfin).map (Ideal.Quotient.mkₐ F I).toLinearMap)
  refine ⟨hP, ?_⟩
  unfold hilbFn
  rw [if_pos fun k => Int.natCast_nonneg (m k)]
  simp only [Int.toNat_natCast]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
