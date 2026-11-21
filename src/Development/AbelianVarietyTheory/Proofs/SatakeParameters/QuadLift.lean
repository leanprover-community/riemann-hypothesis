import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticNormHeckeCharRamifiedBelowRamifiedPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTwistRamifiedCharNeSelfStatement

section
open NumberField IsDedekindDomain Formalism.L2.Host UpperTheory.V.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_norm_hecke_char_ramified_below_ramified_prime : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M], Module.finrank K M = 2 → ∀ η : HChar K, IsNormChar M η → ∀ w : HeightOneSpectrum (𝓞 M), ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal → ¬ η.UnrAt (w.under (𝓞 K)) := by
  first | exact @GlobalTheory.QuadNormRam.not_unrAt_of_ramified | exact GlobalTheory.QuadNormRam.not_unrAt_of_ramified | (intros; apply GlobalTheory.QuadNormRam.not_unrAt_of_ramified <;> assumption)
end

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.Published

namespace GlobalTheory.QuadLiftBridge

theorem quadLift : ArthurClozelStrongTC → JacquetShalikaRigidity → GlobalTheory.GalCut.QuadLift := by
  intro hAC hJS K M _ _ _ _ _ _ _ h2 a ha π ⟨w, hw, B, hB⟩
  haveI : Algebra.IsQuadraticExtension K M := ⟨h2⟩
  haveI : IsGalois K M := inferInstance
  refine hAC K M (h2 ▸ Nat.prime_two) a ha π fun η hη hST => ?_
  have hsm : CG.mk π = (CG.mk π).twist η := by
    refine JacquetShalikaRigidity.strong_multiplicity_one hJS ha _ _ (hST.mono fun v ⟨hu, B', h1, h3⟩ => ⟨B', h1, ?_⟩)
    have := h1.twist hu
    rwa [h3] at this
  exact GlobalTheory.T.cuspidal_twist_ramified_char_ne_self K a ha (CG.mk π) η _ B hB (GlobalTheory.T.quadratic_norm_hecke_char_ramified_below_ramified_prime K M h2 η hη w hw) hsm.symm

end GlobalTheory.QuadLiftBridge
end
end
