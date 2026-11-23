module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem GlobalTheory.torsion_parallelogram_vanish : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ (N : ℕ), 0 < N → ∀ M : ℂ → ℝ,
    (∀ t ∈ Λ, M t = 0) → (∀ t ω : ℂ, (N : ℂ) * t ∈ Λ → ω ∈ Λ → M (t + ω) = M t) →
    (∀ P Q : ℂ, (N : ℂ) * P ∈ Λ → (N : ℂ) * Q ∈ Λ → Q ∉ Λ → M (P + Q) + M (P - Q) = 2 * M P + 2 * M Q) →
    ∀ t : ℂ, (N : ℂ) * t ∈ Λ → M t = 0 := by
  intro Λ _ N hN M h0 _ hlaw t ht
  by_cases hQ : t ∈ Λ
  · exact h0 t hQ
  have key : ∀ k : ℕ, M ((k:ℂ) * t) = (k:ℝ)^2 * M t ∧
      M (((k:ℂ)+1) * t) = ((k:ℝ)+1)^2 * M t := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [h0 0 (zero_mem Λ)]
      · simp
    | succ k ih =>
      refine ⟨by push_cast; exact ih.2, ?_⟩
      have hmem : (N:ℂ) * (((k:ℂ)+1) * t) ∈ Λ := by
        have e : (N:ℂ) * (((k:ℂ)+1) * t) = (k+1 : ℕ) • ((N:ℂ) * t) := by
          rw [nsmul_eq_mul]; push_cast; ring
        rw [e]; exact AddSubgroup.nsmul_mem Λ ht _
      have h := hlaw (((k:ℂ)+1) * t) t hmem ht hQ
      have e1 : ((k:ℂ)+1) * t + t = ((k:ℂ)+1+1) * t := by ring
      have e2 : ((k:ℂ)+1) * t - t = (k:ℂ) * t := by ring
      rw [e1, e2, ih.1, ih.2] at h
      push_cast
      linear_combination h
  have h1 := (key N).1
  rw [h0 _ ht] at h1
  have hN' : (N:ℝ)^2 ≠ 0 := by positivity
  exact (mul_eq_zero.mp h1.symm).resolve_left hN'
