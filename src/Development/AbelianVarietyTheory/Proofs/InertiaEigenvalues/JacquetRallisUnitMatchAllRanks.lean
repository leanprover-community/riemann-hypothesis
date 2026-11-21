import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchOfWeilRepQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationQuadraticFieldExists

section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem unitMatch_all : ∀ r, UnitMatch r :=
  GlobalTheory.T.jacquetRallisUnitMatch_of_weilRep_quadratic GlobalTheory.T.weilRepresentation_quadraticField_exists

end GlobalTheory.JR
end

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_all_ranks : ∀ r, UnitMatch r := by
  atlas_forward_decl GlobalTheory.JR.unitMatch_all
