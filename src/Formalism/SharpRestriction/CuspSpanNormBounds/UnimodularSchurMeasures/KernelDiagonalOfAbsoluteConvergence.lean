import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.KernelDiagonalOfL2UnfoldIdempotent
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkaMeasKabRight
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkbLeOneAddSq
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkpCoefCont

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set TopologicalSpace
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def AbsKernelSquareIntegrable (X : CData) : Prop :=
  ∀ᵐ x ∂X.μ, ∫⁻ y, (∑' γ : X.I.GFset, ‖X.φ (x⁻¹ * (γ : X.I.GA) * y)‖ₑ) ^ 2 ∂X.μ ≠ ∞

def PhiIdem (X : CData) : Prop :=
  Measurable X.φ ∧ (∀ z, X.φ z⁻¹ = star (X.φ z)) ∧ ∀ z, ∫ g, X.φ g * X.φ (g⁻¹ * z) ∂(X.I.muA X.μf) = X.φ z





end Formalism.MainNotions.LeviCoordinates

end
