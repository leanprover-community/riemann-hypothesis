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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
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

theorem isMultiHomog_prod_pow {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*}
    [CommRing R] (i : ∀ k, ι k) (n : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, i k⟩ : MRing ι R) ^ n k) n := by
  have h := IsWeightedHomogeneous.prod (R := R) Finset.univ
    (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ n k) (fun k => n k • blockWeight ι ⟨k, i k⟩)
    (w := blockWeight ι) (fun k _ => (isWeightedHomogeneous_X R _ _).pow _)
  have hs : (∑ k, n k • blockWeight ι ⟨k, i k⟩) = n := by
    funext j
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [hs] at h
  exact h

theorem prod_pow_not_mem {K : Type} [Fintype K] {ι : K → Type} {R : Type*} [CommRing R]
    (P : Ideal (MRing ι R)) [hP : P.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι R) ∉ P) (n : K → ℕ) :
    (∏ k, (X ⟨k, i k⟩ : MRing ι R) ^ n k) ∉ P := by
  intro h
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact hi k (hP.mem_of_pow_mem _ hk)

theorem ExistsForm.proof : ExistsForm.Statement := by
  intro F _ K _ _ ι _ P hP b
  have := hP.isPrime
  choose i hi using hP.relevant
  refine ⟨fun k => (b k).toNat, fun k => (-b k).toNat,
    ∏ k, (X ⟨k, i k⟩ : MRing ι F) ^ (b k).toNat, ∏ k, (X ⟨k, i k⟩ : MRing ι F) ^ (-b k).toNat,
    isMultiHomog_prod_pow i _, isMultiHomog_prod_pow i _, prod_pow_not_mem P i hi _,
    prod_pow_not_mem P i hi _, ?_⟩
  funext k
  simp only
  omega

end

end GroundTheory.Heights₂.Heights.FieldNumbers
