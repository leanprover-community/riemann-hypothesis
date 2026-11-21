import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianLifting
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftingOfDeRhamUnobstructed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSquareZeroLiftsOfDeRhamCohomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamStructureOfCubeDualPoincare

section
theorem GlobalTheory.SqLift.abelianLifting_of_known_theorems :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme →
      GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianUnobstructed →
      GlobalTheory.Published.AbelianLifting :=
  fun a b c d e =>
    GlobalTheory.SqLift.abelianLifting_of_schemeLifts (GlobalTheory.T.abelianSchemeDeRhamStructure_of_cube_dual_poincare a b c d) (GlobalTheory.T.abelianSchemeSquareZeroLifts_of_deRhamCohomology a) e
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeHomLiftingNilDP_of_hodge_cube_duality_unobstructed : GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianUnobstructed → GlobalTheory.Published.AbelianLifting := by
  atlas_forward_decl GlobalTheory.SqLift.abelianLifting_of_known_theorems
