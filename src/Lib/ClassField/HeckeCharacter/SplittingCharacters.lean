module

public import Lib.Weil.DualPair.Defs
import Lib.ClassField.HeckeCharacter.SplitTameCharacters

/-!
# Splitting characters

Here a pair of spaces is indexed by two characters `ν_S`, `ν_T` of `[U(1)]` instead of by
splitting characters `χ_S`, `χ_T`. The splitting character of rank `k` attached to `ν` is the Hecke
character `ν.spaceChar k`, `y ↦ ν(y / ȳ) υ(y)⁻ᵏ`, with `υ` the splitting character from `WeilData`.
The file gives its rules for products and hyperbolic planes, and its value at `rankTwist ν n`.

## Relation to the literature

Known result: splitting characters of a CM extension.
Source: Harris–Kudla–Sweet (1996), §1.
-/

@[expose] public section

noncomputable section

namespace New

open WeilData Fintype

variable {E : Type} [Field E] [CMType E] [WeilData E]

namespace AutChar

variable {ν ν' : AutChar E} {k l : ℕ}

/-- The splitting character of `ν * ν'` at rank `k + l` is the product of those of `ν` at rank `k`
and of `ν'` at rank `l`, as for an orthogonal sum of spaces. -/
lemma spaceChar_mul : (ν * ν').spaceChar (k + l) = ν.spaceChar k * ν'.spaceChar l := by
  rw [spaceChar, map_mul, pow_add, mul_mul_mul_comm, spaceChar, spaceChar]

/-- Adding `l` hyperbolic planes, that is, raising the rank by `2 * l`, keeps the splitting
character if `ν` is multiplied by `upsilonU1 ^ l`. Here `ν.spaceChar k` is the Hecke character
`x ↦ ν (x / x̄) * υ x ^ (-k)` of `E`, where `υ` is the splitting character of the Weil data.
`upsilonU1` is the restriction of `υ` to the norm-one ideles. -/
lemma spaceChar_add_two_mul : (ν * upsilonU1 ^ l).spaceChar (k + 2 * l) = ν.spaceChar k := by
  simp only [spaceChar, map_mul, map_pow, baseChange_upsilonU1]
  group

/-- Let `E` be a CM field with Weil data, whose splitting character is `υ`. For a character `ν` of
`[U(1)]` and a finite type `n`, let `rankTwist ν n = ν · υ^⌊card n / 2⌋` (with `υ` restricted to
norm-one ideles). Its space character at rank `card n`, the Hecke character
`x ↦ (rankTwist ν n)(x / x̄) · υ(x)^(-card n)`, equals `ν.baseChange` if `card n` is even and
`ν.baseChange * υ⁻¹` if `card n` is odd. -/
theorem spaceChar_rankTwist_eq_ite (ν : AutChar E) (n : Type*) [Fintype n] :
    (rankTwist ν n).spaceChar (card n) =
      if Even (card n) then ν.baseChange else ν.baseChange * υ⁻¹ := by
  -- `rankTwist` adds `card n / 2` hyperbolic planes to a space of rank `card n % 2`.
  have h_mod_two : (rankTwist ν n).spaceChar (card n) = ν.spaceChar (card n % 2) := by
    rw [rankTwist, ← spaceChar_add_two_mul (ν := ν), Nat.mod_add_div]
  split_ifs with hn
  · rw [h_mod_two, Nat.even_iff.mp hn, spaceChar, pow_zero, mul_one]
  · rw [h_mod_two, Nat.not_even_iff.mp hn, spaceChar, pow_one]

end AutChar

end New

end
