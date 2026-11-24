module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.hom_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    Q.ideal.IsHomogeneous 𝒜 ∧ (ideal2 Q).IsHomogeneous 𝒜 ∧ ideal2 Q ≤ Q.ideal := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x _ r s r' s' m Q
  refine ⟨?_, ?_, ?_⟩
  · refine Ideal.homogeneous_span 𝒜 _ ?_
    rintro _ ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    exacts [⟨_, Q.hF i⟩, ⟨_, Q.hG i⟩, ⟨_, Q.hE i⟩, ⟨_, Q.hE' i⟩, ⟨_, (Q.hZ i).1⟩]
  · refine Ideal.homogeneous_span 𝒜 _ ?_
    rintro _ ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    exacts [⟨_, sq_mem_neg 𝒜 (Q.hF i)⟩, ⟨_, Q.hG i⟩, ⟨_, sq_mem_pos 𝒜 (Q.hE i)⟩, ⟨_, Q.hE' i⟩, ⟨_, (Q.hZ i).1⟩]
  · refine Ideal.span_le.2 ?_
    rintro _ ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact Ideal.pow_mem_of_mem Q.ideal
        (Ideal.subset_span (Or.inl (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩))))) 2 (by norm_num)
    · exact Ideal.subset_span (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))
    · exact Ideal.pow_mem_of_mem Q.ideal
        (Ideal.subset_span (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))) 2 (by norm_num)
    · exact Ideal.subset_span (Or.inl (Or.inr ⟨i, rfl⟩))
    · exact Ideal.subset_span (Or.inr ⟨i, rfl⟩)
