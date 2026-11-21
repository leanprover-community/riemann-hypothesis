import Mathlib
import Formalism.HermitianCurvature.StatementQ
import Formalism.FormalDegreeBessel.FinalG

open Matrix
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace PI.UnitaryGroupMassFormula.QnFFZero

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem glev_zero (k r : ℕ) (g : Mx k r) : g ∈ Glev k r 0 ↔ g ∈ UH (Hpk k r) := by
  simp only [Glev, Set.mem_ofPred_eq]
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, fun a ha => absurd ha (by simp)⟩

theorem nset_uh (k r : ℕ) (n : Mx k r) (h : n ∈ Nset k r) : n ∈ UH (Hpk k r) := by
  simp only [Nset, Set.mem_ofPred_eq] at h
  exact h.1


theorem ell_one (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) : ell k r z 1 = 0 := by
  unfold ell
  apply Finset.sum_eq_zero
  intro a _
  split_ifs with h
  · apply Matrix.one_apply_ne
    intro he
    simp [eI, Fin.ext_iff] at he
  · rw [Matrix.one_mulVec]
    exact hz _ (Or.inl (by simp [eI]))

theorem psi_one (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (hz : inWb k r z) : psi k r z c 1 = 1 := by
  simp [psi, ell_one k r z hz]


end PI.UnitaryGroupMassFormula.QnFFZero
