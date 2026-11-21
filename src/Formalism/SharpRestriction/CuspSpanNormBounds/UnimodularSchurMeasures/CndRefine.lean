import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndTauSLeHalf

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma
open Formalism.HermitianLatticeCounting.S7 (P0 b1 Ydat)


def CSize.DeepStepsT {X : CData} (S : CSize X) (volK C : ℝ) : Prop :=
  0 < volK ∧ X.I.vol X.μf X.fund / volK ≤ cn_Y X ^ (C * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) ∧
    ∀ᵐ x ∂X.μ, S.tau1 x < 1 / 2 →
      ∃ (a : ℕ) (τ : ℕ → ℝ), 1 ≤ a ∧ a ≤ X.qq ∧ (∀ i, 0 < τ i) ∧ τ (a + 1) = 1 / 2 ∧ τ 1 = S.tau1 x ∧
        ∀ b' : ℕ, 1 ≤ b' → b' ≤ a → ∃ (ρ : ℝ) (s : ℕ → ℝ) (mult : ℝ), 0 ≤ ρ ∧
          ρ ≤ C * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ) * (X.g : ℝ) * X.I.rd * (τ b' / τ (b' + 1)) ∧ (∀ P, 0 ≤ s P) ∧
          |(X.kerD x).re| ≤ s 0 ^ 2 ∧
          (∀ P < P0 X.I.n X.qq X.I.f, s P ≤ ρ * Real.sqrt ((X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) *
            (C * (X.I.n : ℝ) * (X.b ^ 2 + (P : ℝ) * (X.I.n : ℝ))) * s (P + 1)) ∧
          s (P0 X.I.n X.qq X.I.f) ^ 2 ≤ (4 / (1 / (C * (X.I.n : ℝ) * b1 X.I.n X.qq X.I.f X.b))) ^ (X.I.n ^ 2 * X.I.f) * mult *
            (X.Dc / volK) ∧
          mult ≤ (C * Real.sqrt (X.I.n : ℝ) / S.tau1 x ^ 2) ^ (2 * X.I.n ^ 2 * X.I.f)

end Formalism.MainNotions.LeviCoordinates

end
