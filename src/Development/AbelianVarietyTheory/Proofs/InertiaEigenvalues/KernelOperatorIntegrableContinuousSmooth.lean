module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLieCoord
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Formalism.DoubleCosetMeasures.StatementZ
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
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

theorem measurable_smooth_comp_infGL {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    {X : Type} [MeasurableSpace X] (γ : X → GL (Fin a) (Cinf E))
    (hγ : Measurable (fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)))) (φ : Sm E a) (g : GA E a) :
    Measurable (fun x => φ.1 (g * infGL E a (γ x))) := by
  classical
  have hc : Measurable (chart φ.1 g) := by
    have e : chart φ.1 g = (invSet E a).piecewise (chart φ.1 g) (fun _ => 0) := by
      funext x
      by_cases h : x ∈ invSet E a
      · simp [Set.piecewise, h]
      · have h' : ¬ IsUnit (Matrix.of x) := h
        simp only [Set.piecewise, h, if_false]
        simp [chart, h']
    rw [e]
    exact ContinuousOn.measurable_piecewise (φ.2 g).continuousOn continuousOn_const isOpen_invSet.measurableSet
  have hγ' : Measurable (fun x => toL (γ x).val) := hγ
  have h2 := hc.comp hγ'
  simpa [Function.comp_def, chart_val] using h2

theorem kerOp_integrable_continuous : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, Continuous φ.1 →
    (∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) →
      (∀ g, Integrable (fun x => k x * φ.1 (g * infGL E a (γ x))) ν) ∧ Continuous (kerOp ν k γ φ.1) := by
  intro E _ _ _ a X _ ν k γ hk φ hφc hb
  obtain ⟨C, hC⟩ := hb
  have hint : Integrable (fun x => ‖k x‖ * C) ν := by
    have h0 := hk.2.2 0
    simp only [pow_zero, mul_one] at h0
    exact h0.mul_const C
  have hm : ∀ g, AEStronglyMeasurable (fun x => k x * φ.1 (g * infGL E a (γ x))) ν := fun g =>
    (hk.1.mul (measurable_smooth_comp_infGL γ hk.2.1 φ g)).aestronglyMeasurable
  have hbd : ∀ g, ∀ᵐ x ∂ν, ‖k x * φ.1 (g * infGL E a (γ x))‖ ≤ ‖k x‖ * C := fun g =>
    Filter.Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  refine ⟨fun g => Integrable.mono' hint (hm g) (hbd g), ?_⟩

  exact continuous_of_dominated hm hbd hint (Filter.Eventually.of_forall fun x =>
    continuous_const.mul (hφc.comp (continuous_id.mul continuous_const)))

end GlobalTheory.JSW
