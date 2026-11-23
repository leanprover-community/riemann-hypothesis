module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.component :
    ∀ (Λ T : Type) [CommRing Λ] [IsDomain Λ] [CommRing T] [Algebra Λ T] [Algebra.IsIntegral Λ T], (∀ a : Λ, a ≠ 0 → algebraMap Λ T a ∈ nonZeroDivisors T) → ∀ P ∈ minimalPrimes T, P.comap (algebraMap Λ T) = ⊥ ∧ (∀ p : Ideal Λ, p.IsPrime → ∃ Q : Ideal T, P ≤ Q ∧ Q.IsPrime ∧ Q.comap (algebraMap Λ T) = p) ∧ ringKrullDim (T ⧸ P) = ringKrullDim Λ := by
  intro Λ T _ _ _ _ _ hreg P hP
  have hP' : P.IsPrime := hP.1.1
  have hbot : P.comap (algebraMap Λ T) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun a ha => ?_
    by_contra hne
    exact Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hP) ha (hreg a hne)
  refine ⟨hbot, fun p hp => ?_, ?_⟩
  · obtain ⟨Q, hQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p P (by
      change P.comap (algebraMap Λ T) ≤ p
      rw [hbot]
      exact bot_le)
    exact ⟨Q, hQ, hQp, hQc⟩
  · haveI : FaithfulSMul Λ (T ⧸ P) := by
      rw [faithfulSMul_iff_algebraMap_injective]
      intro a b hab
      rw [IsScalarTower.algebraMap_apply Λ T (T ⧸ P), IsScalarTower.algebraMap_apply Λ T (T ⧸ P)] at hab
      have hm : Ideal.Quotient.mk P (algebraMap Λ T a) = Ideal.Quotient.mk P (algebraMap Λ T b) := hab
      have h1 : algebraMap Λ T a - algebraMap Λ T b ∈ P := Ideal.Quotient.eq.1 hm
      have h2 : a - b ∈ P.comap (algebraMap Λ T) := by
        rw [Ideal.mem_comap, map_sub]
        exact h1
      rw [hbot, Submodule.mem_bot, sub_eq_zero] at h2
      exact h2
    exact GlobalTheory.ringKrullDim_eq_of_isIntegral Λ (T ⧸ P)
