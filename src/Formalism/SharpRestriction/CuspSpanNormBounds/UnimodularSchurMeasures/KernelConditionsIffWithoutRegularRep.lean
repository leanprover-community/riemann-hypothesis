import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrRightOfFinite

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma




def KernelDiagonalVolumeModulusConditions (n₀ : ℕ) (A C cb c₁ A₂ cε C₁ : ℝ) : Prop :=
  ∀ X : CData, X.HypC n₀ A C cb → X.KernelDiag ∧ X.FinVol ∧
    ∃ Mod : Set X.I.GA, MeasurableSet Mod ∧ X.ProbMod c₁ Mod ∧
      X.NearStep (Formalism.HermitianLatticeCounting.S7.epsN cε X.I.n X.I.f) c₁ A₂ Mod ∧
      X.FarCount (X.Acnt C₁) (2 * (X.I.n : ℝ) ^ 2) Mod ∧ X.DeepInt (A₂ + 1) Mod


end Formalism.MainNotions.LeviCoordinates

end
