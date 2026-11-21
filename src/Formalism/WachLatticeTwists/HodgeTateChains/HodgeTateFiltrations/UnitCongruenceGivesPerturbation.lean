import Formalism.WachLatticeTwists.HodgeTateChains.AdicPerturbationFixedFreeAndCoboundary
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.TwistKill
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.Complete
import Formalism.WachLatticeTwists.TorsionLengthCounts.SubmoduleLengthBoundStatement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

theorem unit_congruence_gives_perturbation : AdicPerturbationFixedFreeAndCoboundary := by
  intro ℓ _ R _ _ Xm _ _ _ _ ϖ z z' hzz hc hz g B hinj hsur
  obtain ⟨S, hS1, hS2⟩ := inverse_operator_from_injectivity R Xm g z hinj hsur
  obtain ⟨h1, _, h3⟩ := t3 R Xm ϖ z hc hz g S B hS1 hS2
  refine ⟨h1, fun x => ?_⟩
  obtain ⟨y, hy⟩ := h3 (z' • x)
  refine ⟨y, ?_⟩
  rw [← hy, smul_smul, hzz, algebraMap_smul]



end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
