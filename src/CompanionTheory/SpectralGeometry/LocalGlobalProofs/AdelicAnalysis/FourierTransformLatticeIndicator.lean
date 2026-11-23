module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core

theorem fou_indicator_coset :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V),
      NADual V χ μ → ∀ L : AddSubgroup V, IsCompact (L : Set V) → IsOpen (L : Set V) → ∀ a y : V,
        fou χ μ (Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ))) y =
          ((μ L).toReal : ℂ) * χ a y * Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y := by
  intro V _ _ _ χ μ h L _ hLo a y
  obtain ⟨hTG, _, _, hSC, hB, hH, _, _, _, _, _, hadd, _⟩ := h
  have hLm : MeasurableSet (L : Set V) := hLo.measurableSet

  have key : ∫ x, Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y ∂μ =
      ((μ L).toReal : ℂ) * Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y := by
    by_cases hy : y ∈ perp χ L
    · have h1 : (fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) =
          fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x := by
        funext x
        by_cases hx : x ∈ (L : Set V)
        · simp [Set.indicator_of_mem hx, hy x hx]
        · simp [Set.indicator_of_notMem hx]
      rw [h1, integral_indicator_const _ hLm, Set.indicator_of_mem hy]
      simp [Measure.real]
    · obtain ⟨l, hl, hne⟩ : ∃ l ∈ (L : Set V), χ l y ≠ 1 := by
        simpa [perp] using hy
      set J := ∫ x, Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y ∂μ with hJ
      have hshift : J = χ l y * J := by
        have h2 := integral_add_right_eq_self (μ := μ)
          (fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) l
        refine h2.symm.trans ?_
        rw [hJ, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        have hmem : x + l ∈ (L : Set V) ↔ x ∈ (L : Set V) := L.add_mem_cancel_right hl
        by_cases hx : x ∈ (L : Set V)
        · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx), hadd]
          ring
        · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]
      have hJ0 : J = 0 := by
        have h3 : (1 - χ l y) * J = 0 := by
          rw [sub_mul, one_mul, ← hshift, sub_self]
        rcases mul_eq_zero.1 h3 with h4 | h4
        · exact absurd (sub_eq_zero.1 h4).symm hne
        · exact h4
      rw [hJ0, Set.indicator_of_notMem hy, mul_zero]

  unfold fou
  have h5 := integral_add_right_eq_self (μ := μ)
    (fun x => Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ)) x * χ x y) a
  rw [← h5]
  have h6 : (fun x => Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ)) (x + a) * χ (x + a) y) =
      fun x => χ a y * (Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) := by
    funext x
    have hmem : x + a ∈ {x | x - a ∈ L} ↔ x ∈ (L : Set V) := by simp
    by_cases hx : x ∈ (L : Set V)
    · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx), hadd]
      ring
    · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]
  rw [h6, integral_const_mul, key]
  ring

end GlobalTheory.CompanionTheory.SW.Core
