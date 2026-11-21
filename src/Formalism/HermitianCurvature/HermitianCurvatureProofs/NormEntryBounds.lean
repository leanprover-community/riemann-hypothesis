import Formalism.HermitianCurvature.HermitianCurvatureProofs.EntryMinorBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZhatSectionExists

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

open C2x2 C2x5 HermitianXiVector UnipotentSums EntryMinorBounds

namespace NormEntryBounds

variable {k r : ℕ}

lemma gN_le (g : B.Mat k r) (E : ℝ) (hE : 0 ≤ E) (h : ∀ i j, ‖g i j‖ ≤ E) :
    B.gN g ≤ ((2 * r + k + 1 : ℕ) : ℝ) * E := by
  unfold B.gN
  rw [show ((2 * r + k + 1 : ℕ) : ℝ) * E = Real.sqrt ((((2 * r + k + 1 : ℕ) : ℝ) * E) ^ 2) by
    rw [Real.sqrt_sq (by positivity)]]
  apply Real.sqrt_le_sqrt
  have hs : ∀ i j, Complex.normSq (g i j) ≤ E ^ 2 := by
    intro i j; rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
  calc ∑ i, ∑ j, Complex.normSq (g i j) ≤ ∑ _i : Fin (2 * r + k + 1), ∑ _j : Fin (2 * r + k + 1), E ^ 2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hs i j))
    _ = (((2 * r + k + 1 : ℕ) : ℝ) * E) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring


lemma mul_entry_le (A M : B.Mat k r) (a b : ℝ) (ha : ∀ i j, ‖A i j‖ ≤ a) (hb : ∀ i j, ‖M i j‖ ≤ b)
    (hb0 : 0 ≤ b) (i j : Fin (2 * r + k + 1)) :
    ‖(A * M) i j‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (a * b) := by
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have ht : ∀ p, ‖A i p * M p j‖ ≤ a * b := by
    intro p
    rw [norm_mul]
    exact mul_le_mul (ha i p) (hb p j) (norm_nonneg _) (le_trans (norm_nonneg _) (ha i p))
  calc ∑ p, ‖A i p * M p j‖ ≤ ∑ _p : Fin (2 * r + k + 1), a * b := Finset.sum_le_sum (fun p _ => ht p)
    _ = ((2 * r + k + 1 : ℕ) : ℝ) * (a * b) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end NormEntryBounds

open NormEntryBounds


end Formalism.FourierDecayAlt.P
