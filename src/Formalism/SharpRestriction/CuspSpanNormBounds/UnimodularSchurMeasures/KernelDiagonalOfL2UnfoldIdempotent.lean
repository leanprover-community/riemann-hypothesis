import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Mathlib

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace


end Formalism.MainNotions.LeviCoordinates

end
end

section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set TopologicalSpace
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def ker2 (X : CData) (x y : X.I.GA) : ℂ := ∑' γ : X.I.GFset, X.φ (x⁻¹ * (γ : X.I.GA) * y)

def KernelL2RowsColumns (X : CData) : Prop := ∀ᵐ x ∂X.μ, MemLp (fun y => ker2 X x y) 2 X.μ

def KerUnfold (X : CData) : Prop :=
  ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → ∀ f : X.L2, ∀ᵐ x ∂X.μ,
    ((T f : X.L2) : X.I.GA → ℂ) x = ∫ y, ker2 X x y * (f : X.I.GA → ℂ) y ∂X.μ

def KerIdem (X : CData) : Prop :=
  ∀ᵐ x ∂X.μ, Summable (fun γ : X.I.GFset => X.φ (x⁻¹ * (γ : X.I.GA) * x)) ∧
    X.kerD x = ((∫ y, ‖ker2 X x y‖ ^ 2 ∂X.μ : ℝ) : ℂ)


open Classical in

def rrk_kap (X : CData) (x : X.I.GA) : X.L2 :=
  if h : MemLp (fun y => star (ker2 X x y)) 2 ((X.I.muA X.μf).restrict X.fund) then h.toLp _ else 0



end Formalism.MainNotions.LeviCoordinates

end
end
