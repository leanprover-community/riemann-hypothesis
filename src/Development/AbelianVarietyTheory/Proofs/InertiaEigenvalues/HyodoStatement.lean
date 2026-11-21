import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrystallineCocycles
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFiltrationDuality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableCocyclesBetweenBlochKatoAndContinuous
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsSemistableStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankBlochKatoGAddELeFAddF
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateTwistDualPerfectPairing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankFiniteLeExponentialCocycles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalContinuousCocyclesGaloisRep

section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.HyodoDef TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem hyodo : Hyodo := by
  intro l _ P AI T K V _ _ _ _ _ ρ hcont hsst c hc hcoc hdR
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  haveI : ContinuousSMul ℚ_[l] V := IsModuleTopology.toContinuousSMul ℚ_[l] V
  obtain ⟨ρ', m, hρ'c, hdual⟩ := GlobalTheory.T.exists_tateTwistDual_perfectPairing l P K V ρ hcont
  have hdrV : IsDR (P.PD K) ρ := GlobalTheory.T.isDeRham_of_isSemistable l P AI T K V ρ hsst
  have hdrV' : IsDR (P.PD K) ρ' := by
    letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
    haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    exact (GlobalTheory.T.de_rham_filtration_duality l P AI T K).1 ℚ_[l] ℤ_[l] GlobalTheory.Published.BlochKato.goodO_padicInt
      { V := V, ρ := ρ, cont := hcont } { V := Fin (finrank ℚ_[l] V) → ℚ_[l], ρ := ρ', cont := hρ'c } m hdrV hdual
  have hfin : Module.Finite ℚ_[l] ↥(continuousCocycles ρ) := GlobalTheory.T.finiteDimensional_continuousCocycles_galoisRep l P K V ρ hcont
  obtain ⟨S, _hfS, hSc, hSst, hSdR, hS⟩ := GlobalTheory.T.semistable_cocycles_between_blochKato_and_continuous l P AI T K V _ ρ ρ' m hcont hdual hsst hfin
  have hgc : geometricCocycles (P.PD K) ρ ≤ continuousCocycles ρ := fun _ h => h.1
  haveI : Module.Finite ℚ_[l] ↥(geometricCocycles (P.PD K) ρ) :=
    Module.Finite.of_injective (Submodule.inclusion hgc) (Submodule.inclusion_injective hgc)
  have hSg : S ≤ geometricCocycles (P.PD K) ρ := fun c hc => ⟨hSc hc, hSdR c hc⟩
  have h1 := GlobalTheory.T.finrank_blochKato_g_add_e_le_f_add_f l P AI T K V ρ _ ρ' m hcont hρ'c hdrV hdrV' hdual
  have h2 := GlobalTheory.T.finrank_finite_le_exponential_cocycles l P AI T K _ ρ' hρ'c hdrV'
  have hEq : S = geometricCocycles (P.PD K) ρ := Submodule.eq_of_le_of_finrank_le hSg (by omega)
  have hcg : c ∈ geometricCocycles (P.PD K) ρ := ⟨⟨hc, hcoc⟩, hdR⟩
  rw [← hEq] at hcg
  exact hSst c hcg

end GlobalTheory.PMon
end
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyodo_statement : Hyodo := by
  atlas_forward_decl GlobalTheory.PMon.hyodo
