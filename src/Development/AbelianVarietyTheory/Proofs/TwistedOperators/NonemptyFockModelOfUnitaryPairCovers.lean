import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyFockModelUnitaryDualPairStatement

section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory

theorem nonempty_fockData_of_covers :
    ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q)
      (T2 : GrpData r s), Nonempty (FockData T0 T1 T2) :=
  GlobalTheory.T.nonempty_fockModel_unitary_dual_pair

end GlobalTheory
end

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_fockModel_of_unitary_pair_covers : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s), Nonempty (FockData T0 T1 T2) := by
  atlas_forward_decl GlobalTheory.nonempty_fockData_of_covers
