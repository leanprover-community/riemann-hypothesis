import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.UnimodF
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.PjStarProj
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyProjectorSectionLocal

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def SepF (X : CData) : Prop := SecondCountableTopology X.I.Gf

def TensRep (X : CData) : Prop :=
  (∀ g h, X.σs (g * h) = X.σs g ∘L X.σs h) ∧ X.σs 1 = 1 ∧ (∀ g (x : X.Hs), ‖X.σs g x‖ = ‖x‖) ∧
    ∀ x : X.Hs, Continuous fun g => X.σs g x

abbrev muInf (X : CData) : Measure X.I.Ginf := Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)

def SchurS (X : CData) : Prop :=
  ∀ x y : X.Hs, Integrable (fun g => ‖⟪y, X.σs g x⟫_ℂ‖ ^ 2) (muInf X) ∧
    ∫ g, ‖⟪y, X.σs g x⟫_ℂ‖ ^ 2 ∂(muInf X) = ‖x‖ ^ 2 * ‖y‖ ^ 2 / fdegAll X.I X.σ X.w






end Formalism.MainNotions.LeviCoordinates

end
