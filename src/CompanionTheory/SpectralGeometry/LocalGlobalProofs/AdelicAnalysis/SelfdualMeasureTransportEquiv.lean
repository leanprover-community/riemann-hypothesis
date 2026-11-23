module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
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
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem selfDual_map_of_comp {V V' : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V']
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [MeasurableSpace V'] [BorelSpace V']
    (e : V ≃ₜ+ V') (μ : Measure V) (χ : V' → V' → ℂ)
    (h : SelfDual μ (fun x y => χ (e x) (e y))) : SelfDual (μ.map e) χ := by
  obtain ⟨hH, hF⟩ := h
  let eM : V ≃ᵐ V' := e.toHomeomorph.toMeasurableEquiv
  have hcoe : (eM : V → V') = e := rfl
  have hint : ∀ g : V' → ℂ, ∫ y, g y ∂(μ.map e) = ∫ x, g (e x) ∂μ := fun g => by
    rw [← hcoe]; exact integral_map_equiv eM g
  refine ⟨e.isAddHaarMeasure_map μ, fun Φ hc hs hi z => ?_⟩
  have hinner : ∀ y : V, ∫ x, Φ x * χ x (e y) ∂(μ.map e)
      = ∫ x, (Φ ∘ e) x * χ (e x) (e y) ∂μ := fun y => hint _
  have hi' : Integrable (fun y => ∫ x, (Φ ∘ e) x * χ (e x) (e y) ∂μ) μ := by
    have h1 : Integrable ((fun y => ∫ x, Φ x * χ x y ∂(μ.map e)) ∘ eM) μ :=
      (eM.measurableEmbedding.integrable_map_iff).1 (by rw [hcoe]; exact hi)
    refine h1.congr (Filter.Eventually.of_forall fun y => ?_)
    exact hinner y
  have hcs : HasCompactSupport (Φ ∘ e) :=
    hs.comp_homeomorph e.toHomeomorph
  have key := hF (Φ ∘ e) (hc.comp e.continuous) hcs hi' (e.symm z)
  rw [hint]
  simp only [hinner]
  simpa using key

theorem selfDual_transport (V V' : Type) [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V']
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [MeasurableSpace V'] [BorelSpace V']
    (e : V ≃ₜ+ V') (μ : Measure V) (χ : V' → V' → ℂ) :
    SelfDual μ (fun x y => χ (e x) (e y)) ↔ SelfDual (μ.map e) χ := by
  refine ⟨selfDual_map_of_comp e μ χ, fun h => ?_⟩
  have h2 := selfDual_map_of_comp e.symm (μ.map e) (fun x y => χ (e x) (e y)) (by simpa using h)
  have hm : (μ.map e).map e.symm = μ := by
    have m1 : Measurable (e.symm : V' → V) := e.symm.continuous.measurable
    have m2 : Measurable (e : V → V') := e.continuous.measurable
    rw [Measure.map_map m1 m2]
    have : (e.symm : V' → V) ∘ e = id := by ext x; simp
    rw [this, Measure.map_id]
  rwa [hm] at h2

end GlobalTheory.CompanionTheory.SW
