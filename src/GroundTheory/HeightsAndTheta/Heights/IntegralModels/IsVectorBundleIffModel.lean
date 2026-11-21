import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.IsIsoPullbackObjUnitToUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open CategoryTheory Opposite AlgebraicGeometry Limits

noncomputable section




theorem ClearDenominators.equiv :
    GroundTheory.Heights₂.Heights.Model.ClearDenominators.Statement ↔ ClearDenominators.Statement := by
  constructor
  · intro h X _ _ hf L hL s
    exact h X (toSpecZ X) L hL s
  · intro h X f _ _ _ L hL s
    obtain rfl : f = toSpecZ X := specZ_hom_ext _ _
    exact h X inferInstance L hL s

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
