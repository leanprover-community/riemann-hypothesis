import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.PjFdegAllPos

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

section Q

variable {G : Type} [MeasurableSpace G] (μ : Measure G) {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  (σ : G → (Hs →L[ℂ] Hs)) (d : ℝ)

def pj_Q (x y x' y' : Hs) : Prop :=
  Integrable (fun g => ⟪y, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ) μ ∧
    ∫ g, ⟪y, σ g x⟫_ℂ * star ⟪y', σ g x'⟫_ℂ ∂μ = ⟪x', x⟫_ℂ * ⟪y, y'⟫_ℂ / (d : ℂ)

variable {μ σ d}











end Q



end Formalism.MainNotions.LeviCoordinates

end
