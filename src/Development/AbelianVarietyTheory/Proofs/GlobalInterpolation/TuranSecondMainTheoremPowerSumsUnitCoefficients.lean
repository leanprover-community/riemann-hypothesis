module

public import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Turan2Main

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory

theorem powerSum_second_main :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N M : ℕ) (z : Fin N → ℂ) (i₀ : Fin N), ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧
      ((N : ℝ) / (C * (M + N))) ^ N * ‖z i₀‖ ^ k ≤ ‖∑ i, z i ^ k‖ := by
  refine ⟨1600, by norm_num, fun N M z i₀ => ?_⟩
  have hN : 0 < N := i₀.pos
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z i‖) ⟨i₀, Finset.mem_univ _⟩
  by_cases h0 : z i₁ = 0
  · refine ⟨M + 1, le_rfl, by omega, ?_⟩
    have : ‖z i₀‖ = 0 := le_antisymm (by simpa [h0] using hi₁ i₀ (Finset.mem_univ _)) (norm_nonneg _)
    rw [this, zero_pow (by omega), mul_zero]
    exact norm_nonneg _
  have hR : 0 < ‖z i₁‖ := norm_pos_iff.2 h0
  obtain ⟨k, hk1, hk2, hk⟩ := Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.turan2Main N M
    (fun i => z i / z i₁) hN (fun i => by rw [norm_div, div_le_one hR]; exact hi₁ i (Finset.mem_univ _))
    ⟨i₁, by simp [h0]⟩
  refine ⟨k, hk1, hk2, ?_⟩
  rw [show ∑ i, (z i / z i₁) ^ k = (∑ i, z i ^ k) / z i₁ ^ k by simp [div_pow, Finset.sum_div],
    norm_div, norm_pow, le_div_iff₀ (by positivity)] at hk
  refine le_trans ?_ hk
  gcongr
  exact hi₁ i₀ (Finset.mem_univ _)

end GlobalTheory
