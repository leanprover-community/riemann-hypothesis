module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

@[expose] public section

noncomputable section

open Matrix
open scoped NNReal Kronecker

namespace GlobalTheory.WeilM

variable {R : Type} [CommRing R]

theorem schr_schr [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ] (w w' : (κ → R) × (κ → R))
    (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x w.1 w'.1]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * (mul_invOf_self (2 : R))

variable {α β κ : Type}

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

end GlobalTheory.WeilM

end
