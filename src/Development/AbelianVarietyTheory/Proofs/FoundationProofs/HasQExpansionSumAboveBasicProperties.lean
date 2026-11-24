module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNHS

theorem hs_props : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), (∀ (C C' : ℝ) (φ : ℂ → ℂ) (h : HahnSeries ℚ Ω), C ≤ C' → HS ε C φ h → HS ε C' φ h) ∧ (∀ (C : ℝ) (φ ψ : ℂ → ℂ) (h h' : HahnSeries ℚ Ω), HS ε C φ h → HS ε C ψ h' → HS ε C (φ + ψ) (h + h') ∧ HS ε C (φ - ψ) (h - h')) ∧ (∀ (C : ℝ) (r : ℚ) (c : Ω), HS ε C (fun z => ε c * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (HahnSeries.single r c)) ∧ (∀ (C : ℝ) (φ ψ : ℂ → ℂ) (h : HahnSeries ℚ Ω), (∀ z : ℂ, C < z.im → φ z = ψ z) → HS ε C φ h → HS ε C ψ h) := by
  intro Ω _ ε
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C C' φ h hC hs z hz
    exact hs z (lt_of_le_of_lt hC hz)
  · intro C φ ψ h h' hφ hψ
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · have := (hφ z hz).add (hψ z hz)
      simpa [HahnSeries.coeff_add, map_add (f := _), add_mul] using this
    · have := (hφ z hz).sub (hψ z hz)
      simpa [HahnSeries.coeff_sub, map_sub, sub_mul] using this
  · intro C r c z _
    have := hasSum_single (f := fun s : ℚ => ε ((HahnSeries.single r c).coeff s) *
        Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) * z)) r (by
      intro b hb
      simp [HahnSeries.coeff_single_of_ne hb])
    simpa [HahnSeries.coeff_single_same] using this
  · intro C φ ψ h hφψ hs z hz
    rw [← hφψ z hz]
    exact hs z hz

end GlobalTheory.FNHS
