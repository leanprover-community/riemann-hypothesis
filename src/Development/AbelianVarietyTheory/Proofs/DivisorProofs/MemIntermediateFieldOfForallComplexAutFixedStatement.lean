import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntermediateFieldOfForallComplexAutFixed
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import BuildAid.ForwardExisting

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_intermediateField_of_forall_complexAut_fixed : ∀ (F : IntermediateField ℚ ℂ) (x : ℂ), (∀ σ : ℂ ≃+* ℂ, (∀ y ∈ F, σ y = y) → σ x = x) → x ∈ F := by
  atlas_forward_decl GlobalTheory.CMModel.mem_of_forall_ringEquiv_fixed
