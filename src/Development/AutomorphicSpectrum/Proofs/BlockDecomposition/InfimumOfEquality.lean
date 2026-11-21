import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesOver

section
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem infOfEq_holds : InfOfEq := by
  intro E _ _ _ N t ψ m τ m' hT hI hψ h0 hC
  have hS := hT E N t τ m' hI
  refine GlobalTheory.IsobaricOfPublished.multiset_eq_of_prod_map_add fun u => ?_
  exact smul_left_injective ℂ h0 ((hS.2 u ψ hψ).symm.trans (hC τ u))

end GlobalTheory.CompanionTheory.EGlue
end

open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infimum_of_equality : GlobalTheory.CompanionTheory.EGlue.InfOfEq := by
  atlas_forward_decl GlobalTheory.CompanionTheory.EGlue.infOfEq_holds
