import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormUnitLeOfEsymm
import BuildAid.ForwardExisting

section
namespace GlobalTheory

open Polynomial in

theorem cauchy_roots_bound : ∀ (n : ℕ) (B : Multiset ℂˣ) (M : ℝ), B.card = n → 1 ≤ M →
    (∀ j, 1 ≤ j → j ≤ n → ‖(B.map fun b : ℂˣ => (b : ℂ)).esymm j‖ ≤ M) →
    ∀ b ∈ B, ‖(b : ℂ)‖ ≤ n * M := by
  first
  | exact @_root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm
  | exact _root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm
  | (apply _root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm <;> assumption)
  | (intros; apply _root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ElementarySymmetricNormBound.norm_unit_le_of_esymm ..)

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_root_le_card_mul_bound_of_esymm_norm_le : ∀ (n : ℕ) (B : Multiset ℂˣ) (M : ℝ), B.card = n → 1 ≤ M → (∀ j, 1 ≤ j → j ≤ n → ‖(B.map fun b : ℂˣ => (b : ℂ)).esymm j‖ ≤ M) → ∀ b ∈ B, ‖(b : ℂ)‖ ≤ n * M := by
  atlas_forward_decl GlobalTheory.cauchy_roots_bound
