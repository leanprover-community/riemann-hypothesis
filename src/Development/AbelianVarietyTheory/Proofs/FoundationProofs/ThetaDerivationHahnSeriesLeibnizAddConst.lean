module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Glue

theorem theta_coeff {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : ℚ) (φ : HahnSeries ℚ Ω) (r : ℚ) :
    (theta s φ).coeff r = algebraMap ℚ Ω (s * r) * φ.coeff r := rfl

theorem theta_leibniz_add_const :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : ℚ) (P Q : HahnSeries ℚ Ω),
      theta s (P * Q) = theta s P * Q + P * theta s Q ∧ theta s (P + Q) = theta s P + theta s Q ∧
        ∀ c : Ω, theta s (HahnSeries.C c) = 0 := by
  intro Ω _ _ s P Q
  refine ⟨?_, ?_, ?_⟩
  · ext r
    have h1 : (theta s P).support ⊆ P.support := fun t ht h => ht (by simp [theta_coeff, h])
    have h2 : (theta s Q).support ⊆ Q.support := fun t ht h => ht (by simp [theta_coeff, h])
    rw [HahnSeries.coeff_add, HahnSeries.coeff_mul_left' P.isPWO_support h1,
      HahnSeries.coeff_mul_right' Q.isPWO_support h2, theta_coeff, HahnSeries.coeff_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    have := (Finset.mem_addAntidiagonal.1 hij).2.2
    rw [← this, theta_coeff, theta_coeff, mul_add, map_add (f := _)]; ring
  · ext r; simp [theta_coeff, mul_add]
  · intro c; ext r
    rw [theta_coeff]
    by_cases h : r = 0
    · simp [h]
    · simp [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne h]

end GlobalTheory.Glue
