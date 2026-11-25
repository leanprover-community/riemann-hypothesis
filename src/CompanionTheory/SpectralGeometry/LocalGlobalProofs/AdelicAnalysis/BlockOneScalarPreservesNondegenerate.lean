module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem isHermND_blockOne_algebraMap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → IsHermND σ (blockOne (algebraMap F E t) J) := by
  intro F E _ _ _ _ _ σ M J hJ t ht
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [blockOne]
    · simp [blockOne]
    · simp [blockOne]
    · simpa [blockOne] using hJ.1 i j
  · rw [det_blockOne]
    exact mul_ne_zero ((map_ne_zero _).2 ht) hJ.2

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
