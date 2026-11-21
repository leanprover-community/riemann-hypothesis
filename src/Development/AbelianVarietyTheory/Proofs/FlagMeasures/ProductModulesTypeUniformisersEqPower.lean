import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGHTie
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VENatEqZero
import BuildAid.ForwardExisting

section
namespace GlobalTheory.HTThetaLeaf

theorem main : Formalism.L2.SG.NGHTie.HTTheta := by
  unfold Formalism.L2.SG.NGHTie.HTTheta
  exact GlobalTheory.TypeUnifProd.main

end GlobalTheory.HTThetaLeaf
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_modules_type_uniformisers_eq_power : Formalism.L2.SG.NGHTie.HTTheta := by
  atlas_forward_decl GlobalTheory.HTThetaLeaf.main
