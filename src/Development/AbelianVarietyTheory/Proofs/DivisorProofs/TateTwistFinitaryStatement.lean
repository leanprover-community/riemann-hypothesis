import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorIsFinitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistRingFunctorPreservesFilteredColimits

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem tw_finitary : ∀ (q : ℕ) (i : ℤ), Finitary (tw q i) := fun q i =>
  GlobalTheory.T.etaleSheafOfRingFunctor_isFinitary (ZMod q) (twF q i) (GlobalTheory.EtC.TwistFiltered.twF_preservesFilteredColimits q i)

end GlobalTheory.EtC
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwist_finitary : ∀ (q : ℕ) (i : ℤ), Finitary (tw q i) := by
  first | (exact @GlobalTheory.EtC.tw_finitary) | (exact GlobalTheory.EtC.tw_finitary) | (intros; apply GlobalTheory.EtC.tw_finitary  <;> assumption)
end
