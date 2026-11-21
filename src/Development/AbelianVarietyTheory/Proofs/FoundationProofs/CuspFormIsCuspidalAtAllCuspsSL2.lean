import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
import BuildAid.ForwardExisting

section
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem cuspForm_cuspAll : ∀ (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) (f : CuspForm Γ k), CuspAll k f := by
  intro Γ _ k f
  refine ⟨f.holo', fun c hc => ?_⟩
  rw [← Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (Γ : Subgroup (GL (Fin 2) ℝ))] at hc
  exact f.zero_at_cusps' hc

end GlobalTheory.HeckeFamilyMatrices
end

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_isCuspidalAtAllCuspsSL2 : ∀ (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) (f : CuspForm Γ k), CuspAll k f := by
  atlas_forward_decl GlobalTheory.HeckeFamilyMatrices.cuspForm_cuspAll
