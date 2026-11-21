import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelDensitiesOfHermitianForm

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_densities_of_hermitian_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → SiegelDensities F E σ M J := by
  first | exact @GlobalTheory.CompanionTheory.SW.TopDens.siegelDensities | exact GlobalTheory.CompanionTheory.SW.TopDens.siegelDensities | (intros; apply GlobalTheory.CompanionTheory.SW.TopDens.siegelDensities <;> assumption)
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem siegelWeilUnitaryConvergent : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent :=
  fun F E _ _ _ _ _ σ hσ M J hJ =>
    ⟨finVol_unitaryGroup F E σ hσ M J hJ, GlobalTheory.T.siegel_densities_of_hermitian_form F E σ hσ M J hJ⟩

end GlobalTheory.CompanionTheory.SW
end
