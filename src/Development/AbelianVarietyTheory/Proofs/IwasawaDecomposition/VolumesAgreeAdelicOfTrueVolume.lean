import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCMFamHost
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryAdelicQuotientVolumeIsVolume

section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicQuotientVolume_is_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → VolIs cm τ cd W (trueVol cm τ cd W) := by
  first | exact @GlobalTheory.Mem.Vol.volIs_trueVol | exact GlobalTheory.Mem.Vol.volIs_trueVol | (intros; apply GlobalTheory.Mem.Vol.volIs_trueVol <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem volTieG_of_trueVol : ∀ D : D7, letI := D.host.cmStar;
    (∀ W, D.vol W = trueVol D.sp.cm (Formalism.BasicNotions.TH.tauE D) D.cd W) → Formalism.L2.Theta.VolTieG D := by
  intro D
  letI := D.host.cmStar
  intro h
  rw [volTieG_iff]
  intro W hW
  rw [h W]
  exact GlobalTheory.T.unitaryAdelicQuotientVolume_is_volume _ _ D.sp.cm _ _ D.cd W (isCMFam_host _ D.host _ D.eTau) hW

end GlobalTheory.Mem.Vol
end
