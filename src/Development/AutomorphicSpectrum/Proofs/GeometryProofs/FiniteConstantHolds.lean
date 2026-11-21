import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantAllHolds

section
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem finConst_of_all_hosts : FinConst :=
  FinConstAll.finConst GlobalTheory.T.finite_constant_all_holds

end GlobalTheory.CompanionTheory.Ar.Flat
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_constant_holds : GlobalTheory.CompanionTheory.Ar.Flat.FinConst := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.finConst_of_all_hosts
