module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct
open Function

namespace GlobalTheory

theorem exists_isLocalRing_quotient_pairwise_isCoprime_iInf_eq_bot_padicInt :
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] [Module.Finite ℤ_[ℓ] A],
      ∃ (ι : Type) (_ : Fintype ι) (I : ι → Ideal A),
        (∀ i, IsLocalRing (A ⧸ I i)) ∧ Pairwise (IsCoprime on I) ∧ ⨅ i, I i = ⊥ := by
  intro ℓ _ A _ _ _
  classical
  have : HenselianLocalRing ℤ_[ℓ] := henselianLocalRing_of_henselianRing ℤ_[ℓ]
  have := finite_maximalSpectrum_of_finite_of_isLocalRing ℤ_[ℓ] A
  letI := Fintype.ofFinite (MaximalSpectrum A)
  obtain ⟨e, he, H⟩ := exists_completeOrthogonalIdempotents_of_henselian ℤ_[ℓ] A
  refine ⟨MaximalSpectrum A, inferInstance, fun q ↦ Ideal.span {1 - e q}, fun q ↦ ?_, ?_, ?_⟩
  · have := q.isMaximal
    exact isLocalRing_quotient_one_sub (he.idem q) q.asIdeal (H q)
  · intro i j hij
    change IsCoprime (Ideal.span {1 - e i}) (Ideal.span {1 - e j})
    rw [Ideal.isCoprime_span_singleton_iff]
    have h0 : e i * e j = 0 := he.ortho hij
    exact ⟨1, e i, by linear_combination (-1 : A) * h0⟩
  · refine eq_bot_iff.2 fun x hx ↦ ?_
    rw [Submodule.mem_iInf] at hx
    rw [Ideal.mem_bot, ← one_mul x, ← he.complete, Finset.sum_mul]
    refine Finset.sum_eq_zero fun q _ ↦ ?_
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (hx q)
    rw [← hw]
    linear_combination (-w) * (he.idem q).eq

end GlobalTheory
