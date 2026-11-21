import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.KernelDiagonalOfTriangleInequality
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.TheoremCountStatementOfGeometry
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.ProjectionStatementOfEnd
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.FormalDegreeOfSchurOrth

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def VolumeCountGeometryConditions (n₀ : ℕ) (A C cb cε Cv Cd Cq : ℝ) : Prop :=
  ∀ X : CData, X.HypC n₀ A C cb → X.FinVol ∧ AllCount X (2 * (X.I.n : ℝ) ^ 2) ∧ GeoS X cε Cv Cd Cq



def Rest (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) (n₀ : ℕ) (A C cb cε Cv Cd Cq : ℝ) : Prop :=
  (FPsiEig χ ∧ FConvEig χ ∧ QOrth ∧ QInfChar ∧ QClass χ) ∧ cu_StepsEnd n₀ A 46 ∧ DistTri ∧
    VolumeCountGeometryConditions n₀ A C cb cε Cv Cd Cq

def RestU : Prop :=
  ∃ (χ : ∀ n : ℕ, (Fin n → ℝ) → ℕ → ℂ) (cε Cv Cd Cq : ℝ), 0 < cε ∧ cε ≤ 1 / 90000 ∧ 1 ≤ Cv ∧ 1 ≤ Cd ∧ 0 ≤ Cq ∧
    16 * Cq ≤ Cd ∧ ∀ cb A : ℝ, 0 < cb → 1 ≤ A → ∃ (n₂ : ℕ) (C₄ : ℝ), ∀ (n₀ : ℕ) (C : ℝ), n₂ ≤ n₀ → C₄ ≤ C →
      Rest χ n₀ A C cb cε Cv Cd Cq

end Formalism.MainNotions.LeviCoordinates
