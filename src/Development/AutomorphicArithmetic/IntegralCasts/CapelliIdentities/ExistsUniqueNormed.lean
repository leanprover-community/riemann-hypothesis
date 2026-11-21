import Mathlib

noncomputable def UpperTheory.Reformulated.B.Yzb8.SelfDual :
    {V : Type} →
      [AddCommGroup V] → [TopologicalSpace V] → [inst : MeasurableSpace V] → MeasureTheory.Measure V → (V → V → ℂ) → Prop :=
    fun {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (μ : MeasureTheory.Measure V) (χ : V → V → ℂ) ↦
      μ.IsAddHaarMeasure ∧
        ∀ (Φ : V → ℂ),
          Continuous Φ →
            HasCompactSupport Φ →
              MeasureTheory.Integrable (fun (y : V) ↦ ∫ (x : V), Φ x * χ x y ∂μ) μ →
                ∀ (z : V), ∫ (y : V), (∫ (x : V), Φ x * χ x y ∂μ) * χ y z ∂μ = Φ (-z)

namespace UpperTheory.Reformulated.B.Yzb8

open MeasureTheory FourierTransform
open scoped NNReal ENNReal

section aux

variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private noncomputable def ee (t : ℝ) : ℂ :=
  Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑t : ℂ))








end aux

end UpperTheory.Reformulated.B.Yzb8

open MeasureTheory FourierTransform UpperTheory.Reformulated.B.Yzb8
open scoped NNReal ENNReal
