import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocLatOverLat

section
namespace GlobalTheory.OverObj

theorem selfDualOverBase : GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.SelfDualOverBase :=
  GlobalTheory.OverCompare.overLattice_iff_selfDualOverBase.mp GlobalTheory.OverLat.overLattice

end GlobalTheory.OverObj
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattice_over_columnBaseLattice : GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.SelfDualOverBase := by
  atlas_forward_decl GlobalTheory.OverObj.selfDualOverBase
