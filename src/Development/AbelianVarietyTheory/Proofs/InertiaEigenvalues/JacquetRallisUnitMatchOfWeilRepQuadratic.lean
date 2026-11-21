import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchingOfWeilField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSucc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchSizeOne

section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem unitMatch_of_weilField : WeilField → ∀ r, UnitMatch r := by
  intro hW r
  induction r with
  | zero => exact GlobalTheory.T.jacquetRallisUnitMatch_sizeOne
  | succ r ih => exact GlobalTheory.T.jacquetRallisUnitMatch_succ (GlobalTheory.T.weilRepresentationEtale_of_quadraticField hW) GlobalTheory.T.weilConstantStandardHermitian_eq_one r (GlobalTheory.T.jacquetRallis_fourier_matching_of_weil_field hW (r + 1)) ih

end GlobalTheory.JR
end

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallisUnitMatch_of_weilRep_quadratic : WeilField → ∀ r, UnitMatch r := by
  atlas_forward_decl GlobalTheory.JR.unitMatch_of_weilField
