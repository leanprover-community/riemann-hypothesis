import Mathlib

noncomputable def UpperTheory.Reformulated.B.LiftErrorLocal.ShellInt :
    Prop :=
    ∀ (X : Type) [inst : MeasurableSpace X] (μ : MeasureTheory.Measure X) (N : X → ℝ) (C d A : ℝ),
      Measurable N →
        (∀ᵐ (x : X) ∂μ, (1 : ℝ) ≤ N x) →
          (0 : ℝ) ≤ d →
            (∀ (R : ℝ), (1 : ℝ) ≤ R → (μ : Set X → ENNReal) {x : X | N x ≤ R} ≤ ENNReal.ofReal (C * R ^ d)) →
              d < A → ∫⁻ (x : X), ENNReal.ofReal (N x ^ (-A)) ∂μ < ⊤

