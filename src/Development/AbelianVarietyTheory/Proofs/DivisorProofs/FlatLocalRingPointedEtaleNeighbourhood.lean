import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import BuildAid.ForwardExisting

section
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem EtNbhd.flat_B : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R), Module.Flat R i.B := by
  intro R _ _ i
  haveI : Module.Flat i.A i.B := IsLocalization.flat i.B i.q.primeCompl
  exact Module.Flat.trans R i.A i.B

end GlobalTheory.Henselisation
end

open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_localRing_pointedEtaleNeighbourhood : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R), Module.Flat R i.B := by
  atlas_forward_decl GlobalTheory.Henselisation.EtNbhd.flat_B
