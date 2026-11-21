import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenFiniteOfNoTower
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfMemInertia

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem senFinite : SenFinite := GlobalTheory.PMon.Ram.senFinite_of_noTower GlobalTheory.PMon.Ram.noTower

end GlobalTheory.PMon
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sen_admissible_representation_finite_inertia : SenFinite := by
  atlas_forward_decl GlobalTheory.PMon.senFinite
