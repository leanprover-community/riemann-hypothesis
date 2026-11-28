module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Lib.Speed

/-!
# Dirichlet characters and the primitive characters that induce them

`New.exists_isPrimitive_changeLevel_eq`: every Dirichlet character is induced by a primitive one.
-/

@[expose] public section

open Complex DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- Every complex Dirichlet character χ mod N, with N ≥ 1, is induced by a primitive character ψ
mod M for some divisor M ≥ 1 of N. -/
lemma New.exists_isPrimitive_changeLevel_eq :
    ∃ (M : ℕ) (hM : M ∣ N) (ψ : DirichletCharacter ℂ M),
      NeZero M ∧ IsPrimitive ψ ∧ changeLevel hM ψ = χ :=
  ⟨χ.conductor, χ.conductor_dvd_level, χ.primitiveCharacter, ⟨χ.conductor_ne_zero⟩,
    χ.primitiveCharacter_isPrimitive, χ.changeLevel_primitiveCharacter⟩
