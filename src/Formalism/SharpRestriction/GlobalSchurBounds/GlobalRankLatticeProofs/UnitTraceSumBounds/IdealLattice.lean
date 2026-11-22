module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

@[expose] public section

open Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions NumberField

namespace Formalism.MainNotions.Ext

section Heis

variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]

end Heis

def IdealLattice : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (φ : K →+* ℂ), Module.finrank ℚ K = 2 → IsEmpty (K →+* ℝ) →
    ∀ (cc : Ideal (𝓞 K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 →
      (∃ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 ∧
        AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ (c : K)} = AddSubgroup.closure {w₁, w₂}) ∧
      area (AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ (c : K)}) =
        ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * Real.sqrt |(discr K : ℝ)| / 2

end Formalism.MainNotions.Ext
