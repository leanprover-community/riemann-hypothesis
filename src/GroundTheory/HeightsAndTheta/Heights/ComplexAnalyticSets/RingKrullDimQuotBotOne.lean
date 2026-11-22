module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ConeBall
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeSlab

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Matrix
open scoped ENNReal

noncomputable section

def PolySublevel.Statement : Prop :=
  ∀ (d : ℕ) (Q : MvPolynomial (Fin d) ℂ), Q ≠ 0 → ∀ R : ℝ, 0 < R →
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ)
          {x : EuclideanSpace ℂ (Fin d) | x ∈ Metric.ball 0 R ∧ ‖eval (fun i => x i) Q‖ ≤ η} ≤
        ENNReal.ofReal (C * η ^ α)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
