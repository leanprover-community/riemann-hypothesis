module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.TrivialZeros
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.ZeroReflection
public import Lib.Speed

/-!
# Zeros of L(s, χ) and of L(1 − s, χ⁻¹)

`New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero` shows that a zero `s` of L(·, χ) with
`s.re ≠ 0` and `s ≠ 1` is either a pole of `χ.gammaFactor` or gives the zero `1 - s` of L(·, χ⁻¹),
extending the symmetry given by the functional equation from primitive to all Dirichlet characters.
It is assembled from Tau Ceti's trivial zeros of imprimitive L-functions
(`DirichletCharacter.LFunction_eq_zero_iff_of_re_neg`) and its reflection of zeros in the critical
strip (`DirichletCharacter.LFunction_one_sub_eq_zero_iff`).

## Relation to the literature

Known result: the symmetry of the zeros, a consequence of the functional equation for Dirichlet
L-functions. Source: Montgomery and Vaughan, Multiplicative Number Theory I, 2007, Corollaries 10.3
and 10.8.
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

/-- Symmetry of the zeros: if L(s, χ) = 0, re s ≠ 0 and s ≠ 1, then either s is a pole of the gamma
factor of χ (where Mathlib gives it the value 0), or L(1 − s, χ⁻¹) = 0. The character need not be
primitive, and multiplicities are not compared. -/
lemma New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero (s : ℂ) (h_re : s.re ≠ 0)
    (h_ne_one : s ≠ 1) (hs : χ.LFunction s = 0) :
    χ.gammaFactor s = 0 ∨ LFunction χ⁻¹ (1 - s) = 0 := by
  -- Left of the critical strip only the trivial zeros remain, inside it the zeros reflect, and
  -- right of it there are none.
  rcases h_re.lt_or_gt with h_neg | h_pos
  · exact .inl ((χ.LFunction_eq_zero_iff_of_re_neg h_neg).1 hs)
  rcases lt_or_ge s.re 1 with h_lt | h_ge
  · exact .inr ((χ⁻¹.LFunction_one_sub_eq_zero_iff h_pos h_lt).2 (by rwa [inv_inv]))
  · exact absurd hs (χ.LFunction_ne_zero_of_one_le_re (.inr h_ne_one) h_ge)
