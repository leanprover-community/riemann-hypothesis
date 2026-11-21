import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.ResidueChartModel
import GroundTheory.HeightsAndTheta.Heights.ThetaKeyFormula.RigSymFormTauIIsBasisOf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

open RigSymForm

def ResidueFiniteModel.Statement : Prop :=
  ∀ (P : RigSymForm ℂ) (a : ℕ), 3 ≤ a → ∀ (r : ℕ) (x : Fin (r + 1) → P.Fn), P.IsBasisOf a x →
    ∀ b : ℕ, b < a → Nonempty (ResidueChartModel P a b x)



end

end GroundTheory.Heights₂.Heights.KeyFormula
