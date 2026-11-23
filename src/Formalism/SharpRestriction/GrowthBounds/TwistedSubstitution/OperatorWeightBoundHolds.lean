module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FirstWeightLeConductor
public import Formalism.PeriodIntegrals.RowWtSpan
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.MemHdIff
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalC
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FormCoreSK
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdjointTensorOfSingleValid
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OpWords
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.RowLetter
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.RowWtSpan
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OnePos
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.Style
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

noncomputable section

namespace Formalism.MainNotions.TestSideWords

open Formalism.GradedWeylDivisibility

private theorem initMinor_comp_perm_eq_sign_mul {R : Type} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (σ : Equiv.Perm (Fin s)) :
    PI.RW.initMinor R (I ∘ σ) hs =
      ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (Fin r × Fin n) R)) * PI.RW.initMinor R I hs := by
  unfold PI.RW.initMinor
  rw [← Matrix.det_permute σ]
  rfl

private theorem initMinor_eq_zero_of_not_injective {R : Type} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (hI : ¬ Function.Injective I) : PI.RW.initMinor R I hs = 0 := by
  unfold PI.RW.initMinor
  simp only [Function.Injective, not_forall] at hI
  obtain ⟨i, j, hij, hne⟩ := hI
  exact Matrix.det_zero_of_row_eq (Ne.symm (Ne.symm hne)) (by
    funext q
    simp [hij])

private theorem initMinor_eq_sign_sort_mul {R : Type} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (hI : Function.Injective I) :
    PI.RW.initMinor R I hs =
      ((((Equiv.Perm.sign (Tuple.sort I) : ℤˣ) : ℤ) : MvPolynomial (Fin r × Fin n) R)) *
        PI.RW.initMinor R (I ∘ Tuple.sort I) hs := by
  rw [initMinor_comp_perm_eq_sign_mul, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

theorem bideterminant_span_holds : PI.RW.BideterminantSpan := by
  intro R _ _ k n ν
  rw [show PI.RW.dualWeyl R k n ν = Formalism.GradedWeylDivisibility.dualWeyl R k n ν from rfl,
    Formalism.GradedWeylDivisibility.standardMonomialSpanDomain R k n ν]
  refine Submodule.span_le.mpr ?_
  rintro f ⟨K, sz, hsz, I, hν, rfl⟩
  by_cases hinj : ∀ i, Function.Injective (I i)
  · have hb : Formalism.GradedWeylDivisibility.bideterminant R sz hsz I =
        (∏ i, ((((Equiv.Perm.sign (Tuple.sort (I i)) : ℤˣ) : ℤ) : MvPolynomial (Fin k × Fin n) R))) *
          PI.RW.bideterminant R sz hsz (fun i => I i ∘ Tuple.sort (I i)) := by
      show (∏ i, PI.RW.initMinor R (I i) (hsz i)) = _
      unfold PI.RW.bideterminant
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => initMinor_eq_sign_sort_mul (I i) (hsz i) (hinj i))
    rw [hb, ← Int.cast_prod, ← zsmul_eq_mul]
    have hJ : ∀ i, StrictMono (I i ∘ Tuple.sort (I i)) := fun i =>
      (Tuple.monotone_sort (I i)).strictMono_of_injective ((hinj i).comp (Equiv.injective _))
    refine zsmul_mem (Submodule.subset_span ?_) _
    exact ⟨K, sz, hsz, fun i => I i ∘ Tuple.sort (I i), hν, hJ, rfl⟩
  · push_neg at hinj
    obtain ⟨i, hi⟩ := hinj
    have h0 : Formalism.GradedWeylDivisibility.bideterminant R sz hsz I = 0 := by
      show (∏ i, PI.RW.initMinor R (I i) (hsz i)) = 0
      exact Finset.prod_eq_zero (Finset.mem_univ i) (initMinor_eq_zero_of_not_injective (I i) (hsz i) hi)
    rw [h0]
    exact Submodule.zero_mem _

theorem dual_weyl_weights_bounded : Formalism.MainNotions.TestSideCounting.RestWt := rowWtSpan_of bidetMem bideterminant_span_holds

theorem letter_operators_holds : Formalism.MainNotions.TestSideCounting.RestTheta := row_letter_rule

theorem onePos_of_OB (hOB : Formalism.MainNotions.TestSideCounting.OpBound) : Formalism.MainNotions.TestSideCounting.OnePos :=
  Formalism.MainNotions.TestSideCounting.onePos_of_opBound hOB letter_operators_holds dual_weyl_weights_bounded

theorem tensor_operators_of_one_position (h : Formalism.MainNotions.TestSideCounting.OnePos) : Formalism.MainNotions.TestSideCounting.TenOp :=
  adjointTensorOfSingle_valid Formalism.L2.G.Model.TS.Top.fockRBlock h

theorem tenOp_of_OB (hOB : Formalism.MainNotions.TestSideCounting.OpBound) : Formalism.MainNotions.TestSideCounting.TenOp := tensor_operators_of_one_position (onePos_of_OB hOB)

theorem operator_weight_bound_holds : Formalism.MainNotions.TestSideCounting.OpBound := operator_words_bound

theorem tensor_operators_holds : Formalism.MainNotions.TestSideCounting.TenOp := tenOp_of_OB operator_weight_bound_holds

end Formalism.MainNotions.TestSideWords
