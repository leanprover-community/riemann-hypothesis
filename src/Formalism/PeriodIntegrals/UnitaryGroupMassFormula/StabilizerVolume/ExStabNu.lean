import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabSt

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

def ThetaPos : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 _hT =>
  ∀ μ, IsHaarH F E σ M J μ → ∀ 𝓕, IsFDH F E σ M J μ 𝓕 →
    ∃ φ : (Fin a → Fin M → AF F ⊗[F] E) → ℝ, (∀ X, 0 ≤ φ X) ∧ IsAdmS F E (fun X => (φ X : ℂ)) ∧
      meanC μ 𝓕 (thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0}) ≠ 0


end PI.VolStabS
