import Formalism.PeriodIntegrals.BordSlice
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

section
open Matrix

noncomputable section

namespace PI.HermitianEmbeddingSlice

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic

variable {k r : ℕ}

def emb (k r : ℕ) (y : Fin (k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := fun i =>
  if h : r ≤ i.val ∧ i.val ≤ r + k then y ⟨i.val - r, by omega⟩ else 0

def dd (k : ℕ) (j : Fin (k + 1)) : ℂ := if j = Fin.last k then -1 else 1

lemma Hb_eq : Hb k = diagonal (dd k) := rfl

lemma dd_sq (j : Fin (k + 1)) : dd k j * dd k j = 1 := by
  unfold dd
  split_ifs <;> norm_num

lemma dd_star (j : Fin (k + 1)) : star (dd k j) = dd k j := by
  unfold dd
  split_ifs <;> simp

end PI.HermitianEmbeddingSlice
end
end

section
open Matrix

noncomputable section

namespace PI.HermitianEmbeddingSlice

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic

variable {k r : ℕ}

lemma alg1 (v : Fin (k + 1) → ℂ) (j : Fin (k + 1)) : dd k j * (Hb k *ᵥ v) j = v j := by
  rw [Hb_eq, mulVec_diagonal, ← mul_assoc, dd_sq, one_mul]

lemma alg2 (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (zb : Fin (k + 1) → ℂ) (j : Fin (k + 1)) :
    dd k j * star (star zb ⬝ᵥ (Hb k *ᵥ (μ *ᵥ Pi.single j 1))) = ((Hb k * μᴴ * Hb k) *ᵥ zb) j := by
  have h1 : ∀ v : Fin (k + 1) → ℂ, Hb k *ᵥ v = fun i => dd k i * v i :=
    fun v => funext fun i => by rw [Hb_eq, mulVec_diagonal]
  have h2 : μ *ᵥ Pi.single j 1 = fun i => μ i j :=
    funext fun i => by simp [Matrix.mulVec, dotProduct_single]
  rw [← mulVec_mulVec, ← mulVec_mulVec, h2]
  simp only [h1]
  simp only [dotProduct, Matrix.mulVec, conjTranspose_apply, star_sum, Pi.star_apply, star_mul', star_star]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [dd_star]
  ring

end PI.HermitianEmbeddingSlice
end
end
