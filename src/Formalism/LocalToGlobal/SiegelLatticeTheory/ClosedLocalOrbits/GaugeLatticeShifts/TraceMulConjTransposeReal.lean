import Formalism.LocalRingCardinality.DataCD

open Matrix

noncomputable section

namespace Formalism.MainNotions.S.Gauge.Cd

variable {P Q : ℕ}

local notation "ι" => Fin P ⊕ Fin Q

theorem jpq_sq : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  unfold Formalism.UG.Jpq
  rw [Matrix.fromBlocks_multiply]
  simp

theorem jpq_conjTranspose : (Formalism.UG.Jpq P Q)ᴴ = Formalism.UG.Jpq P Q := by
  unfold Formalism.UG.Jpq
  rw [Matrix.fromBlocks_conjTranspose]
  simp


def hs2 (Z : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (Z i j)



end Formalism.MainNotions.S.Gauge.Cd
