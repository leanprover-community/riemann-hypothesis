import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaSelfAdjointLieOfCountLimitDescentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaUnitaryGroupOddResidueOfLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryLatticeCountRatioTendsto
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearLatticeCountDescentProof
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeFundamentalLemmaCountIdentityOfUnitMatch

section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem unitLemma_lie_and_group (hM : ∀ r : ℕ, GlobalTheory.JR.UnitMatch r) :
    UnitLemmaLie ∧ UnitLemmaGroup :=
  have hL : UnitLemmaLie := GlobalTheory.T.unitLemmaSelfAdjointLie_of_count_limit_descent (GlobalTheory.T.relativeFundamentalLemmaCountIdentity_of_unitMatch hM) GlobalTheory.T.unitary_lattice_count_ratio_tendsto GlobalTheory.T.linearLatticeCountDescent_proof
  ⟨hL, GlobalTheory.T.unitLemma_unitary_group_odd_residue_of_lie hL⟩

end GlobalTheory.UnitLemma
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemma_lieAlgebra_unitaryGroup_of_jacquetRallis : (∀ r : ℕ, GlobalTheory.JR.UnitMatch r) → UnitLemmaLie ∧ UnitLemmaGroup := by
  atlas_forward_decl GlobalTheory.UnitLemma.unitLemma_lie_and_group
