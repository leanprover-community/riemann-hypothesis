module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplExtMem

lemma omega_zero_left {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (w : l ⊕ l → R) : symplOmega (0 : l ⊕ l → R) w = 0 := by
  simp [symplOmega]

lemma omega_zero_right {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (w : l ⊕ l → R) : symplOmega w (0 : l ⊕ l → R) = 0 := by
  simp [symplOmega]

variable {R : Type*} [Zero R] {n : ℕ} (α β γ δ : R) (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)

end PSymplExtMem

open PSymplExtMem in
theorem SymplExtMem.proof (h1 : SymplOmegaMem.Statement) (h2 : SymplCons.Statement) :
    SymplExtMem.Statement := by
  intro R _ n α β γ δ Q hdet hQ
  rw [h1 R (Fin (n + 1))]
  have hQ' := (h1 R (Fin n) Q).1 hQ
  have hc := (h2 R n).2
  rintro (x | x) (y | y) <;> cases x using Fin.cases <;> cases y using Fin.cases <;>
    simp only [row_e, row_f, row_inl, row_inr, hc, hQ', omega_zero_left, omega_zero_right] <;>
    simp [Matrix.J, Matrix.one_apply, Fin.succ_ne_zero, Fin.succ_inj] <;>
    first
      | ring1
      | linear_combination hdet
      | linear_combination (-1 : R) * hdet
      | exact fun h => absurd (Eq.symm h) (Fin.succ_ne_zero _)

end GroundTheory.Heights₂.Heights
