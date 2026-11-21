import Mathlib
import Formalism.GL3MeanSquares.FourierTransformKernelSurjective

namespace Formalism.HermitianLattices.LocalLatticeBases

open Finset


theorem exponent_loss_per_embedding : ExponentLossPerEmbedding := by
  intro ι Ψ p _ W nu C N t hW ht htN hnu
  have : ∑ τ ∈ Ψ, (2 * W τ + C * N + if p τ then nu τ else 0) ≤ ∑ τ ∈ Ψ, (4 * W τ + (C+1) * N) := by
    apply Finset.sum_le_sum
    intro τ hτ
    split_ifs with h
    · linarith [hnu τ hτ h, hW τ hτ]
    · linarith [hW τ hτ]
  refine this.trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]; ring












theorem length_average_bound : LemmaB'_avg := by
  intro k n S mult hS hm hn j
  have key : ∀ i : Fin k, ∑ w ∈ S, mult w * w i = ∑ w ∈ S, mult w * w j := by
    intro i
    apply Finset.sum_nbij' (fun w => w ∘ Equiv.swap i j) (fun w => w ∘ Equiv.swap i j)
    · intro w hw; exact hS _ w hw
    · intro w hw; exact hS _ w hw
    · intro w _; funext a; simp [Function.comp]
    · intro w _; funext a; simp [Function.comp]
    · intro w _; simp [hm]
  have : ∑ i : Fin k, ∑ w ∈ S, mult w * w i = k * ∑ w ∈ S, mult w * w j := by
    rw [Finset.sum_congr rfl (fun i _ => key i)]; simp
  rw [← this, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [← Finset.mul_sum, hn w hw, mul_comm]









end Formalism.HermitianLattices.LocalLatticeBases
