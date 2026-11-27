module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
public import Lib.Speed

/-!
# Dirichlet characters and the primitive characters that induce them

Two facts for passing between a Dirichlet character `χ` and the primitive character that induces it.
`New.prod_euler_factor_ne_zero`: off the line `re s = 0`, the inverse Euler factors
`1 - χ(p) p ^ (-s)` at the primes dividing a given number do not vanish.
`New.exists_isPrimitive_changeLevel_eq`: every Dirichlet character is induced by a primitive one.
-/

@[expose] public section

open Complex DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

omit [NeZero N] in
/-- For a Dirichlet character `χ` and `re s ≠ 0`, the product of the inverse Euler factors
`1 - χ(p) p ^ (-s)` over the primes `p` dividing `M` does not vanish. -/
lemma New.prod_euler_factor_ne_zero {M : ℕ} {s : ℂ} (h_re : s.re ≠ 0) :
    ∏ p ∈ M.primeFactors, (1 - χ p * (p : ℂ) ^ (-s)) ≠ 0 :=
  prod_one_sub_mul_prime_cpow_ne_zero χ h_re

/-- Every complex Dirichlet character χ mod N, with N ≥ 1, is induced by a primitive character ψ
mod M for some divisor M ≥ 1 of N. -/
lemma New.exists_isPrimitive_changeLevel_eq :
    ∃ (M : ℕ) (hM : M ∣ N) (ψ : DirichletCharacter ℂ M),
      NeZero M ∧ IsPrimitive ψ ∧ changeLevel hM ψ = χ :=
  ⟨χ.conductor, χ.conductor_dvd_level, χ.primitiveCharacter, ⟨χ.conductor_ne_zero⟩,
    χ.primitiveCharacter_isPrimitive, χ.changeLevel_primitiveCharacter⟩
