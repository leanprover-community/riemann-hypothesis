import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FundamentalDomainUnitaryAdelicExistsMeasureEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnitaryAdelicVolumeMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSetPosFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotientStatement

section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamentalDomain_unitaryAdelic_exists_measure_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J)), μ.IsHaarMeasure → (∃ 𝓕, IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ) ∧ ∀ 𝓕 𝓕', IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕' μ → μ 𝓕 = μ 𝓕' ∧ μ 𝓕 ≠ 0 := by
  first | exact @GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary | exact GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary | (intros; apply GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isUnitaryAdelicVolumeMeasure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → ∃ μ, IsVolMeasF cm τ cd W (fun ρ => (W.sig (τ ρ)).1) (fun ρ => (W.sig (τ ρ)).2) μ := by
  first | exact @GlobalTheory.Mem.VolExists.exists_isVolMeasF | exact GlobalTheory.Mem.VolExists.exists_isVolMeasF | (intros; apply GlobalTheory.Mem.VolExists.exists_isVolMeasF <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem volIs_trueVol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → VolIs cm τ cd W (trueVol cm τ cd W) := by
  intro F E _ _ _ _ _ _ cm I _ τ cd W hτ hW
  apply trueVol_spec
  obtain ⟨μ, hμ⟩ := GlobalTheory.T.exists_isUnitaryAdelicVolumeMeasure F E cm I τ cd W hτ hW
  obtain ⟨⟨𝓕, h𝓕⟩, hall⟩ := GlobalTheory.T.fundamentalDomain_unitaryAdelic_exists_measure_eq F E cm.sig W.rank W.gram μ hμ.1
  have hcm := cmData_isCMExt_and_gram_isHermND F E cm
  have hfin : μ 𝓕 < ⊤ := GlobalTheory.T.finiteVolume_adelicUnitaryQuotient F E cm.sig hcm.1 W.rank W.gram (hcm.2 W) μ hμ.1 𝓕 h𝓕
  have hne : μ 𝓕 ≠ 0 := (hall 𝓕 𝓕 h𝓕 h𝓕).2
  refine ⟨(μ 𝓕).toReal, ENNReal.toReal_pos hne hfin.ne, ⟨μ, hμ⟩, ?_⟩
  intro μ' hμ'
  have e : μ = μ' := GlobalTheory.Mem.VolUnique.volMeas_unique F E cm I τ cd W hτ hW μ μ' hμ hμ'
  subst e
  refine ⟨⟨𝓕, h𝓕⟩, fun 𝓕' h' => ?_⟩
  rw [ENNReal.ofReal_toReal hfin.ne]
  exact (hall 𝓕' 𝓕 h' h𝓕).1

end GlobalTheory.Mem.Vol
end
