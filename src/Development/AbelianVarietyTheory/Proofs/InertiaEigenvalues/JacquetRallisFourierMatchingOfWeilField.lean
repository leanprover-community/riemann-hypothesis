import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchOfWeilRepresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationEtaleOfQuadraticField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleOrbitalFourierRankOneTransfer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilConstantStandardHermitianEqOne

section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem fourierMatch_of_weilField : WeilField → ∀ r, FourierMatch r := fun h =>
  GlobalTheory.T.jacquetRallisFourierMatch_of_weilRepresentation (GlobalTheory.T.weilRepresentationEtale_of_quadraticField h) GlobalTheory.T.etaleOrbitalFourier_rankOne_transfer GlobalTheory.T.weilConstantStandardHermitian_eq_one

end GlobalTheory.JR
end

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquetRallis_fourier_matching_of_weil_field : WeilField → ∀ r, FourierMatch r := by
  atlas_forward_decl GlobalTheory.JR.fourierMatch_of_weilField
