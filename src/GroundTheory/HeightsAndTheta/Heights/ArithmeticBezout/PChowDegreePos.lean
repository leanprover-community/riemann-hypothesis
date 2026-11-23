module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
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
public import Mathlib.RingTheory.Nullstellensatz
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ChowDegreePos.proof : ChowDegreePos.Statement := by
  intro n k δ W g hk hW hg hδ
  by_contra hlt
  have hδ0 : δ = 0 := by omega
  subst hδ0

  have hnt : NonTorsionWeight (groupWeight k n) := by
    intro m ij h
    have := congrFun h ij.1
    simpa [groupWeight] using this

  have hsupp : ∀ m ∈ g.support, m = 0 := by
    intro m hm
    have h1 : Finsupp.weight (groupWeight k n) m = 0 := hδ (mem_support_iff.1 hm)
    ext ij
    exact (weightedDegree_eq_zero_iff hnt).1 h1 ij
  obtain ⟨c, rfl⟩ : ∃ c, g = C c := by
    refine ⟨AddMonoidAlgebra.coeff g 0, ?_⟩
    ext m
    rw [coeff_C]
    split_ifs with hm
    · rw [hm]
    · by_contra hne
      exact hm (hsupp m (mem_support_iff.2 hne)).symm
  have hc : c ≠ 0 := by
    intro h
    apply hg.1
    rw [h, C_0]
  have hdvd : (C c : MvPolynomial (Fin k × Fin n) ℂ) ∣ 1 :=
    ⟨C c⁻¹, by rw [← C_mul, mul_inv_cancel₀ hc, C_1]⟩
  have hvan := (hg.2 1).2 hdvd

  obtain ⟨x, hx0, hx⟩ : ∃ x : Fin n → AlgebraicClosure ℂ, x ≠ 0 ∧ ∀ p ∈ W, aeval x p = 0 := by
    by_contra hne
    obtain ⟨j, hj⟩ := hW.isRelevant
    apply hj
    have hrad : X j ∈ W.radical := by
      rw [← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure ℂ)]
      rw [mem_vanishingIdeal_iff]
      intro y hy
      by_cases hy0 : y = 0
      · subst hy0
        simp
      · exact absurd ⟨y, hy0, hy⟩ hne
    rwa [hW.isPrime.radical] at hrad
  have hmem : (0 : Fin k × Fin n → AlgebraicClosure ℂ) ∈ incidence W k :=
    ⟨x, hx0, hx, fun i => by simp⟩
  have := hvan 0 hmem
  simp at this

end GroundTheory.Heights₂.Heights
