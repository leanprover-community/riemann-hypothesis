import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoCechNerveChainsOfEtaleLocallySurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSurjectiveEtaleLocallyHasSections

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace GlobalTheory.EtC

theorem chains_cechAug_quasiIso_of_smooth (R : Type) [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X)
    [Smooth f] [Surjective f] : QuasiIso ((chains R).map (cechAug f)) :=
  GlobalTheory.T.quasiIso_cechNerveChains_of_etaleLocallySurjective R (yoneda.map f) (fun U y => GlobalTheory.T.smooth_surjective_etale_locally_has_sections f U y)

end GlobalTheory.EtC
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chains_cechNerve_quasiIso_of_smooth_surjective : ∀ (R : Type) [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X) [Smooth f] [Surjective f], QuasiIso ((chains R).map (cechAug f)) := by
  atlas_forward_decl GlobalTheory.EtC.chains_cechAug_quasiIso_of_smooth
