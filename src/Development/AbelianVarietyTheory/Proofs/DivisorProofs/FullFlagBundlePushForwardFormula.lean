import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqOfWeylAntisymmetrizationEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceIntersectionNumberAdjacentSwapNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmChernRootsMulFibrePoint

section
noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.FlagPushProof

theorem flagPushForward : GlobalTheory.Published.FlagPushForward := by
  intro F _ _ X Y ι _ m E E' φ f gr hf hg Q R hR
  have hswap := GlobalTheory.T.flagSpace_intersectionNumber_adjacent_swap_neg F X Y ι m E E' φ f hf gr hg
  refine GlobalTheory.T.linearForm_eq_of_weylAntisymmetrization_eq ι m (Y.interPoly gr) hswap Q (chernRoots m R * fibrePoint m) ?_
  rw [hR, antisymm_chernRoots_mul_fibrePoint]

end GlobalTheory.FlagPushProof
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullFlagBundle_pushForward_formula : GlobalTheory.Published.FlagPushForward := by
  atlas_forward_decl GlobalTheory.FlagPushProof.flagPushForward
