import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrExistsMeasRep

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

variable {G : Type*} [Group G]

def rrk_K (Γ : Subgroup G) (φ : G → ℂ) (x y : G) : ℂ := ∑' γ : Γ, φ (x⁻¹ * (γ : G) * y)

def rrk_Kab (Γ : Subgroup G) (φ : G → ℂ) (x y : G) : ℝ≥0∞ := ∑' γ : Γ, ‖φ (x⁻¹ * (γ : G) * y)‖ₑ


end Formalism.MainNotions.LeviCoordinates

end
