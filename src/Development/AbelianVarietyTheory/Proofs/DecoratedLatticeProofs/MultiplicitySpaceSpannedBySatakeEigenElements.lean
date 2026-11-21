import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceSpanFullSphericalHeckeEigenpartStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainEigenPartHasHeckeParametersStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem eigSpan_of_parts : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → MetEx D → LevFacts D → EigSpan D := by
  intro hC D hF _ hL c hc j hj s hs
  have hspan := GlobalTheory.T.multiplicitySpace_span_fullSphericalHecke_eigenparts hC D hF hL c hc j hj s hs
  have hpar := GlobalTheory.T.thetaChain_eigenPart_has_heckeParameters hC D c hc j hj s hs
  rw [eq_top_iff, ← hspan]
  refine Submodule.span_le.2 ?_
  rintro u ⟨e, he⟩
  by_cases h0 : u = 0
  · rw [h0]; exact Submodule.zero_mem _
  · exact Submodule.subset_span ((hpar u e he).1 h0)

end GlobalTheory.ChainOnto
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_space_spanned_by_satake_eigen_elements : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → MetEx D → LevFacts D → EigSpan D := by
  atlas_forward_decl GlobalTheory.ChainOnto.eigSpan_of_parts
