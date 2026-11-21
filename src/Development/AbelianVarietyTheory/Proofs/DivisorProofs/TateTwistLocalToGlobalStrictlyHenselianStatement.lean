import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleEquivalenceSchemeOfStrictlyHenselianStalks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem tateTwist_local_to_global_strictlyHenselian : B3 := by
  intro q Y X S f p _ _ _ _ _ i h
  exact GlobalTheory.T.etaleEquivalence_scheme_of_strictlyHenselian_stalks (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) Y X S f p
    (fun O _ s hs => h O s hs.1)

end GlobalTheory.EtC
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etC_b3 : GlobalTheory.EtC.B3 := by
  first | (exact @GlobalTheory.EtC.tateTwist_local_to_global_strictlyHenselian) | (exact GlobalTheory.EtC.tateTwist_local_to_global_strictlyHenselian) | (intros; apply GlobalTheory.EtC.tateTwist_local_to_global_strictlyHenselian  <;> assumption)
end
