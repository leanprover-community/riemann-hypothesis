module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.BernoulliSignedNumerator
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.LemmaX

/-! # A signed residue formula for the first Bernoulli number of the product character -/

@[expose] public section

namespace UpperTheory.V.X

open Finset

/-- For an odd product character with primitive dyadic factor, its first generalized
Bernoulli number is one quarter of the signed residue sum. This expression is integral
away from two even when the residue characteristic divides the odd conductor. -/
theorem genB_prodX_eq_quarter_signed_sum {K : Type} [Field K] [CharZero K]
    {f n : ℕ} (hf : Odd f) (hn : 2 ≤ n) (φ : DirichletCharacter K f)
    (ξ : DirichletCharacter K (2 ^ n)) (hξ : ξ.IsPrimitive) (hodd : φ (-1) * ξ (-1) = -1) :
    Bern.genB 1 (prodX φ ξ : ZMod (f * 2 ^ n) → K) =
      (∑ r : Fin (2 ^ n), bernoulliSignedCoeff φ (2 ^ n) r * ξ r) / 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hF : ((f * 2 ^ (k + 2) : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.mul_pos hf.pos (by positivity)).ne'
  have hmean (N m : ℕ) (hN : N = 2 * m) (hm : 0 < m) (he : Even m)
      (ψ : DirichletCharacter K N) (hψ : ψ (1 + m) = -1) :
      (∑ x ∈ range (f * N), φ x * ψ x * (x : K)) / (f * N : ℕ) =
        (∑ r : Fin N, bernoulliSignedCoeff φ N r * ψ r) / 4 := by
    subst N
    exact bernoulliWeightedMean_eq_quarter_signed_sum hf hm he φ ψ hψ
  have hhalf := UpperTheory.primitive_two_pow_character_one_add_half_eq_neg_one K (k + 2)
    (by omega) ξ hξ
  calc
    _ = (∑ x ∈ range (f * 2 ^ (k + 2)), φ x * ξ x * (x : K)) / (f * 2 ^ (k + 2) : ℕ) := by
      apply (eq_div_iff hF).mpr
      rw [mul_comm]
      exact genB_prodX hf.pos φ ξ hodd
    _ = _ := hmean _ (2 ^ (k + 1)) (pow_succ' _ _) (by positivity)
      (by rw [pow_succ']; exact even_two.mul_right _) ξ (by simpa using hhalf)

end UpperTheory.V.X
