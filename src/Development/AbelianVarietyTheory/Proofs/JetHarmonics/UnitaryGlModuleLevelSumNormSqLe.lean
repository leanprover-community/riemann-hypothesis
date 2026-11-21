import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CardFilterFinBounds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleLevelOffDiagNormSqLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightNearDiagonalOperatorsBounds

section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGlModule_level_offDiag_normSq_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → Lev ε E μ j w → (n : ℝ) * ∑ a, ∑ b ∈ univ.erase a, ‖E a b w‖ ^ 2 ≤ (bv / 16) ^ 2 * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.lev_offDiag_normSq_le | exact GlobalTheory.lev_offDiag_normSq_le | (intros; apply GlobalTheory.lev_offDiag_normSq_le <;> assumption)
end

section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightNear_diagonalOperators_bounds : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M), IsUnitary ε E → w ∈ WtNear E Λ t → (∀ m : ℝ, (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → m ≤ ∑ a, ω a ^ 2) → m * ‖w‖ ^ 2 ≤ ∑ a, ‖E a a w‖ ^ 2) ∧ (∀ (a : Fin n) (ζ : ℂ) (d : ℝ), 0 ≤ d → (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → d ≤ ‖ζ + (ω a : ℂ)‖) → d ^ 2 * ‖w‖ ^ 2 ≤ ‖ζ • w + E a a w‖ ^ 2) ∧ ∀ (a : Fin n) (D : ℝ), (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → |ω a| ≤ D) → ‖E a a w‖ ^ 2 ≤ D ^ 2 * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.wtNear_diag_bounds | exact GlobalTheory.wtNear_diag_bounds | (intros; apply GlobalTheory.wtNear_diag_bounds <;> assumption)
end

section
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem lev_gl_size : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv b : ℝ) (w : M),
    IsMod ε E μ → Shape ε kk μ bv → bv ≤ b → j ≤ 4 * n ^ 2 → Lev ε E μ j w →
    ∑ a, ∑ c, ‖E a c w‖ ^ 2 ≤ b ^ 4 * ‖w‖ ^ 2 := by
  intro M _ _ n ε E μ kk j bv b w hM hS hb hj hL
  have hj' : j ≤ 4 * n ^ 2 + 2 := by omega
  obtain ⟨hbv, hpos, -⟩ := GlobalTheory.shape_position n kk j ε μ bv hS hj'
  have hoff := GlobalTheory.T.unitaryGlModule_level_offDiag_normSq_le M n ε E μ kk j bv w hM hS hj' hL
  have hdiag := (GlobalTheory.T.weightNear_diagonalOperators_bounds M n ε E (lowK ε μ) (j : ℝ) w hM.2.1 hL.2).2.2
  have hd : ∀ a, ‖E a a w‖ ^ 2 ≤ (3 * bv) ^ 2 * ‖w‖ ^ 2 := by
    intro a
    refine hdiag a (3 * bv) ?_
    intro ω hω
    obtain ⟨h1, h2⟩ := hpos ω hω a
    rw [abs_le]
    by_cases h : a.val + 1 < kk
    · obtain ⟨h3, h4⟩ := h1 h
      constructor <;> linarith
    · obtain ⟨h3, h4⟩ := h2 (by omega)
      constructor <;> linarith
  have hn : (1 : ℝ) ≤ n := by
    have := hS.1
    have := hS.2.1
    exact_mod_cast (by omega : 1 ≤ n)
  have hbig : 10 ^ 6 * (n : ℝ) ^ 7 ≤ bv := hS.2.2.2.2.2
  have hsplit : ∑ a, ∑ c, ‖E a c w‖ ^ 2
      = ∑ a, ‖E a a w‖ ^ 2 + ∑ a, ∑ c ∈ univ.erase a, ‖E a c w‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact (Finset.add_sum_erase univ (fun c => ‖E a c w‖ ^ 2) (Finset.mem_univ a)).symm
  have hsum : ∑ a, ‖E a a w‖ ^ 2 ≤ n * ((3 * bv) ^ 2 * ‖w‖ ^ 2) := by
    calc ∑ a, ‖E a a w‖ ^ 2 ≤ ∑ _a : Fin n, (3 * bv) ^ 2 * ‖w‖ ^ 2 := Finset.sum_le_sum fun a _ => hd a
      _ = n * ((3 * bv) ^ 2 * ‖w‖ ^ 2) := by simp
  have hO : 0 ≤ ∑ a, ∑ c ∈ univ.erase a, ‖E a c w‖ ^ 2 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun c _ => sq_nonneg _
  have hO' : ∑ a, ∑ c ∈ univ.erase a, ‖E a c w‖ ^ 2 ≤ (bv / 16) ^ 2 * ‖w‖ ^ 2 :=
    le_trans (le_mul_of_one_le_left hO hn) hoff
  have hn7 : (n : ℝ) ≤ (n : ℝ) ^ 7 := le_self_pow₀ hn (by norm_num)
  have hb1 : 10 ^ 6 * (n : ℝ) ≤ bv := by linarith
  have hb2 : 9 * (n : ℝ) + 1 ≤ bv ^ 2 := by nlinarith
  have hb4 : bv ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ hbv.le hb 4
  have hc : (n : ℝ) * (3 * bv) ^ 2 + (bv / 16) ^ 2 ≤ b ^ 4 := by
    have h1 : (9 * (n : ℝ) + 1) * bv ^ 2 ≤ bv ^ 2 * bv ^ 2 := mul_le_mul_of_nonneg_right hb2 (sq_nonneg _)
    nlinarith [sq_nonneg bv]
  have := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖w‖)
  rw [hsplit]
  nlinarith

end GlobalTheory
end

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGlModule_level_sum_norm_sq_le : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv b : ℝ) (w : M), IsMod ε E μ → Shape ε kk μ bv → bv ≤ b → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∑ a, ∑ c, ‖E a c w‖ ^ 2 ≤ b ^ 4 * ‖w‖ ^ 2 := by
  atlas_forward_decl GlobalTheory.lev_gl_size
end
