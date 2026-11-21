import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorOnCocycleMapsCocycleCoboundaryConj
import BuildAid.ForwardExisting

section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.SlashAction

theorem polySlash_matrix_mul : ∀ (w : ℕ) (A B : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]), p ∈ degreeLT ℂ (w + 1) →
    slP w (A * B) p = slP w B (slP w A p) :=
  fun w A B p hp => (GlobalTheory.HeckeFamilyMatrices.HkC.polySlash_comp w A B p (GlobalTheory.HeckeFamilyMatrices.HkC.mem_degLT_iff.1 hp)).symm

end GlobalTheory.HeckeFamilyMatrices.SlashAction
end

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyDegreeSlashAction_matrix_mul : ∀ (w : ℕ) (A B : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]), p ∈ degreeLT ℂ (w + 1) → slP w (A * B) p = slP w B (slP w A p) := by
  atlas_forward_decl GlobalTheory.HeckeFamilyMatrices.SlashAction.polySlash_matrix_mul
