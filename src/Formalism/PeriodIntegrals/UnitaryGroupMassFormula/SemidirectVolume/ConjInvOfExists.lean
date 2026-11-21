import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.SubgroupLocallyCompactHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.LocallyCompactAdelicUnitary
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.DiscAll

noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def ModOne : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (r : ℕ) (P : Frame E M r) (T : F), 2 * r + 3 ≤ M → P.IsStd σ J T →
    ∀ h ∈ Hsub (AF F) σ J P, ∃ μ : Measure (FrameUnipotentSubgroup (AF F) σ J P), μ.IsHaarMeasure ∧
      ∀ f : HA (AF F) σ J → ENNReal, Measurable f →
        ∫⁻ n, f (h * (n : HA (AF F) σ J) * h⁻¹) ∂μ = ∫⁻ n, f (n : HA (AF F) σ J) ∂μ



end PI.VolSemiDirect.W.Cj
