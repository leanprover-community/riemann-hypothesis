module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open scoped nonZeroDivisors

noncomputable section

theorem SliceIdeal.isHomogeneous_linForm {n : ℕ} (u : Fin n → ℂ) : (linForm u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (u j) j

theorem SliceIdeal.exists_homogeneous_sub_mem {n : ℕ} (ℓ : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) :
    ∃ d, ∃ G : MvPolynomial (Fin n) ℂ, G.IsHomogeneous d ∧ G - f ∈ Ideal.span {linForm ℓ - 1} := by
  classical
  refine ⟨f.totalDegree, ∑ i ∈ Finset.range (f.totalDegree + 1),
      linForm ℓ ^ (f.totalDegree - i) * homogeneousComponent i f, ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ fun i hi => ?_
    have hi' : i ≤ f.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h := ((SliceIdeal.isHomogeneous_linForm ℓ).pow (f.totalDegree - i)).mul
      (homogeneousComponent_isHomogeneous i f)
    convert h using 1
    omega
  · have hsum : (∑ i ∈ Finset.range (f.totalDegree + 1),
          linForm ℓ ^ (f.totalDegree - i) * homogeneousComponent i f) - f =
        ∑ i ∈ Finset.range (f.totalDegree + 1),
          (linForm ℓ ^ (f.totalDegree - i) - 1) * homogeneousComponent i f := by
      conv_lhs => arg 2; rw [← sum_homogeneousComponent f]
      rw [← Finset.sum_sub_distrib]
      simp only [sub_one_mul]
    rw [hsum]
    refine Ideal.sum_mem _ fun i _ => ?_
    refine Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.mpr ?_)
    simpa using sub_dvd_pow_sub_pow (linForm ℓ) 1 (f.totalDegree - i)

end

end GroundTheory.Heights₂.Heights
