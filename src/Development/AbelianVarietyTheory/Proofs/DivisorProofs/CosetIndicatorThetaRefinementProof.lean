import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import BuildAid.ForwardExisting

section
namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain Formalism.L2.Ker

theorem coset_refinement : CosetRefinement := by
  intro X A a b S Md _ _ hOdd hLa
  exact indAdd_of A a b S Md hOdd.pos (lattice_classes_finite_refinement X a b S) (indTieD_of_la A a b S Md hOdd.pos hLa)

end GlobalTheory.ColNorms
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetIndicatorThetaRefinement_proof : GlobalTheory.ColNorms.CosetRefinement := by
  atlas_forward_decl GlobalTheory.ColNorms.coset_refinement
