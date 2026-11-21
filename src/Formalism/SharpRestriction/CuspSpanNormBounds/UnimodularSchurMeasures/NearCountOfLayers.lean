import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnMeasurablePsi

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def cn_isNear (X : CData) (εN : ℝ) (x : X.I.GA) (γ : X.I.GFset) : Prop :=
  (γ ≠ X.one' ∧ ∀ v, X.dist x γ v ≤ εN) ∧ X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0

def CSize.NearLayers {X : CData} (S : CSize X) (εN δ : ℝ) : Prop :=
  (∀ x ∈ S.I0, ∀ γ : X.I.GFset, γ ≠ X.one' → (∀ v, X.dist x γ v ≤ εN) → X.φ (x⁻¹ * (γ : X.I.GA) * x) = 0) ∧
    ∀ (J : ℕ) (c : Composition J), ∀ x ∈ S.str J c, S.tau J c x ∈ cn_Reg c.length ∧
      ∃ (e : Fin (Fintype.card (cn_Root c.length)) ≃ cn_Root c.length) (β : ℕ → Type) (π : ∀ i, X.I.GFset → β i),
        (∀ γ γ', cn_isNear X εN x γ → cn_isNear X εN x γ' → π 0 γ = π 0 γ') ∧
        (∀ γ γ', cn_isNear X εN x γ → cn_isNear X εN x γ' →
          π (Fintype.card (cn_Root c.length)) γ = π (Fintype.card (cn_Root c.length)) γ' → γ = γ') ∧
        ∀ (i : Fin (Fintype.card (cn_Root c.length))) (T : Finset X.I.GFset), (∀ γ ∈ T, cn_isNear X εN x γ) →
          (∀ y ∈ T, ∀ z ∈ T, π i y = π i z) → (∀ y ∈ T, ∀ z ∈ T, π (i + 1) y = π (i + 1) z → y = z) →
          ∃ laM : ℝ, cn_la (S.tau J c x) (e i) / 2 ≤ laM ∧
            (T.card : ℝ) ≤ (1 + 2 * (∏ _v : InfinitePlace X.I.F, 3 * δ) ^ (1 / (Fintype.card (InfinitePlace X.I.F) : ℝ)) / laM) ^
              (cn_dim c.blocksFun (X.I.n - 2 * J) (e i) * Fintype.card (InfinitePlace X.I.F))


end Formalism.MainNotions.LeviCoordinates

end
