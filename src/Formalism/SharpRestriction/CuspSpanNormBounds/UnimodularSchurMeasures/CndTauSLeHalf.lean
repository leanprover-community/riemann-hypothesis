import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CNDefs

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma







def CSize.PackCount {X : CData} (S : CSize X) : Prop :=
  ∀ x : X.I.GA, ∀ r : InfinitePlace X.I.F → ℝ, (∀ v, 0 ≤ r v) → ∀ T : Finset X.I.GFset,
    (∀ γ ∈ T, X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0 ∧ ∀ v, X.dist x γ v ≤ r v) →
    (T.card : ℝ) ≤
      (1 + 2 * (∏ v, Real.sqrt (X.I.n : ℝ) * Real.exp (r v)) ^ (1 / (Fintype.card (InfinitePlace X.I.F) : ℝ)) /
        S.tau1 x ^ 2) ^ (2 * X.I.n ^ 2 * Fintype.card (InfinitePlace X.I.F))





structure CDeep (X : CData) where
  theta : X.I.GA → ℝ
  rho : X.I.GA → ℝ
  Bs : X.I.GA → ℝ
  volK : ℝ

def CSize.DeepStepsY {X : CData} (S : CSize X) (T : CDeep X) (Cd : ℝ) : Prop :=
  0 < T.volK ∧ X.I.vol X.μf X.fund / T.volK ≤ cn_Y X ^ (Cd * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) ∧
    ∀ᵐ x ∂X.μ, S.tau1 x < 1 / 2 →
      0 ≤ T.theta x ∧ T.theta x ≤ cn_Y X ^ Cd * (2 * S.tau1 x) ^ (1 / (X.qq : ℝ)) ∧
      |(X.kerD x).re| ≤ T.theta x ^ (2 * Formalism.HermitianLatticeCounting.S7.P0 X.I.n X.qq X.I.f) * T.Bs x ∧
      T.Bs x ≤ cn_Y X ^ (Cd * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) * (1 / S.tau1 x) ^ (4 * X.I.n ^ 2 * X.I.f) * X.Dc / T.volK


def CSize.DeepStepsV {X : CData} (S : CSize X) (T : CDeep X) (Cd : ℝ) : Prop :=
  0 < T.volK ∧ X.I.vol X.μf X.fund / T.volK ≤ cn_Y X ^ (Cd * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) ∧
    ∀ᵐ x ∂X.μ, S.tau1 x < 1 / 2 →
      0 ≤ T.rho x ∧
      T.rho x ≤ Cd * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ) * (X.g : ℝ) * X.I.rd * (2 * S.tau1 x) ^ (1 / (X.qq : ℝ)) ∧
      |(X.kerD x).re| ≤ (Cd * T.rho x * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ) * Formalism.HermitianLatticeCounting.S7.b1 X.I.n X.qq X.I.f X.b) ^
          (2 * Formalism.HermitianLatticeCounting.S7.P0 X.I.n X.qq X.I.f) * T.Bs x ∧
      T.Bs x ≤ X.Dc * T.volK⁻¹ * (Cd * (X.I.n : ℝ) ^ 2 * Formalism.HermitianLatticeCounting.S7.b1 X.I.n X.qq X.I.f X.b) ^ (X.I.n ^ 2 * X.I.f) *
          (Cd / S.tau1 x) ^ (4 * X.I.n ^ 2 * X.I.f)



end Formalism.MainNotions.LeviCoordinates

end
