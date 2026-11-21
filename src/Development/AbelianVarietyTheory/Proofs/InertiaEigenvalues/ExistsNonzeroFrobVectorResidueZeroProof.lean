import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNonzeroFrobVectorResidueZero

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exII_holds : ExII := GlobalTheory.T.exists_nonzero_frobVector_residue_zero

end GlobalTheory.PMon
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsNonzeroFrobVectorResidueZero_proof : ExII := by
  atlas_forward_decl GlobalTheory.PMon.exII_holds
