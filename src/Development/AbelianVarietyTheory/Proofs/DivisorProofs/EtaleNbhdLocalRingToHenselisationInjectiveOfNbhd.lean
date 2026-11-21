import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointedEtaleNbhdTransitionMapDirectedSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointedEtaleNeighbourhoodLocalRingIsDirected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingTransitionMapIsLocalHomInjecti

section
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem Hens.of_injective_of_nbhd (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) :
    Function.Injective (Hens.of i) := by
  have : IsDirected (EtNbhd R) (· ≤ ·) := GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected R
  have : DirectedSystem (fun j : EtNbhd R => j.B) (fun _ _ h => ⇑(EtNbhd.trans h)) :=
    ⟨fun j x => (GlobalTheory.T.pointedEtaleNbhd_transitionMap_directedSystem R).1 j x,
      fun k j l hlj hjk x => (GlobalTheory.T.pointedEtaleNbhd_transitionMap_directedSystem R).2 l j k hlj hjk x⟩
  exact Ring.DirectLimit.of_injective (G := fun j : EtNbhd R => j.B) (fun _ _ h => EtNbhd.trans h)
    (fun _ _ h => (GlobalTheory.T.etaleNbhdLocalRingTransitionMap_isLocalHom_injective R _ _ h).2) i

end GlobalTheory.Henselisation
end

open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleNbhdLocalRingToHenselisation_injective_of_nbhd : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R), Function.Injective (Hens.of i) := by
  atlas_forward_decl GlobalTheory.Henselisation.Hens.of_injective_of_nbhd
