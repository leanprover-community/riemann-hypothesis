module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.BernoulliProductSignedSum
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-! # Detecting Bernoulli units by signed character sums in the residue field -/

@[expose] public section

namespace UpperTheory.V.X

open Finset

/-- The signed residue sum at the two factors of a character. -/
def signedCharacterSum {R : Type*} [CommRing R] {f N : ℕ}
    (φ : DirichletCharacter R f) (ξ : DirichletCharacter R N) : R :=
  ∑ r : Fin N, bernoulliSignedCoeff φ N r * ξ r

/-- Reduction commutes with the signed residue sum, also when the residue
characteristic divides the odd conductor. -/
theorem map_signedCharacterSum {R S : Type*} [CommRing R] [CommRing S] (ρ : R →+* S)
    {f N : ℕ} (φ : DirichletCharacter R f) (ξ : DirichletCharacter R N) :
    ρ (signedCharacterSum φ ξ) = signedCharacterSum (φ.ringHomComp ρ) (ξ.ringHomComp ρ) := by
  simp [signedCharacterSum, bernoulliSignedCoeff, apply_ite ρ, MulChar.ringHomComp_apply]

private def integralCharacter {ℓ N : ℕ} [Fact ℓ.Prime] {A : Subring (PadicAlgCl ℓ)}
    (hA : ∀ x : PadicAlgCl ℓ, x ∈ A ↔ ‖x‖ ≤ 1) (χ : DirichletCharacter (PadicAlgCl ℓ) N) :
    DirichletCharacter A N where
  toFun a := ⟨χ a, (hA _).mpr (χ.norm_le_one a)⟩
  map_one' := Subtype.ext (map_one χ)
  map_mul' a b := Subtype.ext (map_mul χ a b)
  map_nonunit' _ ha := Subtype.ext (χ.map_nonunit ha)

/-- A residue-field nonvanishing criterion for the first generalized Bernoulli number.
The odd character takes Frobenius-fixed values, while the dyadic character retains its
half-turn and the parity of the product. -/
theorem norm_genB_prodX_of_residue {ℓ d f n : ℕ} [Fact ℓ.Prime] (hl : ℓ ≠ 2)
    (hd : 0 < d) (hf : Odd f) (hn : 2 ≤ n)
    (φ : DirichletCharacter (PadicAlgCl ℓ) f) (ξ : DirichletCharacter (PadicAlgCl ℓ) (2 ^ n))
    (hord : orderOf φ ∣ ℓ ^ d - 1) (hprim : ξ.IsPrimitive) (hodd : φ (-1) * ξ (-1) = -1)
    (hres : ∀ (k : Type) [Field k] [CharP k ℓ] (ψ : DirichletCharacter k f)
      (χ : DirichletCharacter k (2 ^ n)), (2 : k) ≠ 0 → (∀ u, ψ u ^ (ℓ ^ d) = ψ u) →
      ψ (-1) * χ (-1) = -1 → χ (1 + 2 ^ (n - 1)) = -1 → signedCharacterSum ψ χ ≠ 0) :
    ‖Bern.genB 1 (prodX φ ξ : ZMod (f * 2 ^ n) → PadicAlgCl ℓ)‖ = 1 := by
  obtain ⟨k, _, _, A, red, hA, hred⟩ := UpperTheory.exists_residue_map_padicAlgCl_integers ℓ
  let φA := integralCharacter hA φ
  let ξA := integralCharacter hA ξ
  have h2 : (2 : k) ≠ 0 := fun hz ↦ hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
    ((CharP.cast_eq_zero_iff k ℓ 2).mp hz))
  have hQ := Nat.one_lt_pow hd.ne' (Fact.out : Nat.Prime ℓ).one_lt
  have hfix (a : ZMod f) : φ a ^ (ℓ ^ d) = φ a := by
    by_cases ha : IsUnit a
    · have hp : φ a ^ (ℓ ^ d - 1) = 1 := by
        rw [← MulChar.pow_apply' φ (by omega : ℓ ^ d - 1 ≠ 0) a, orderOf_dvd_iff_pow_eq_one.mp hord,
          MulChar.one_apply ha]
      calc
        _ = φ a ^ (ℓ ^ d - 1 + 1) := by rw [Nat.sub_add_cancel hQ.le]
        _ = _ := by rw [pow_succ, hp, one_mul]
    · rw [φ.map_nonunit ha, zero_pow (by omega : ℓ ^ d ≠ 0)]
  have hoddA : φA (-1) * ξA (-1) = -1 := Subtype.ext hodd
  have hturnA : ξA (1 + 2 ^ (n - 1)) = -1 := Subtype.ext
    (UpperTheory.primitive_two_pow_character_one_add_half_eq_neg_one _ n hn ξ hprim)
  have hS : red (signedCharacterSum φA ξA) ≠ 0 := by
    rw [map_signedCharacterSum]
    apply hres k _ _ h2
    · intro a
      change (red (φA a)) ^ (ℓ ^ d) = red (φA a)
      rw [← map_pow]
      exact congrArg red (Subtype.ext (hfix a))
    · simpa only [MulChar.ringHomComp_apply, map_mul, map_neg, map_one] using congrArg red hoddA
    · simpa only [MulChar.ringHomComp_apply, map_neg, map_one] using congrArg red hturnA
  have hunit (x : A) (hx : red x ≠ 0) : ‖(x : PadicAlgCl ℓ)‖ = 1 :=
    le_antisymm ((hA _).mp x.property) (not_lt.mp (mt (hred _).mpr hx))
  have hfour : ‖(4 : PadicAlgCl ℓ)‖ = 1 := hunit 4 (by
    rw [map_ofNat, show (4 : k) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2)
  have hφ : φA.ringHomComp A.subtype = φ := rfl
  have hξ : ξA.ringHomComp A.subtype = ξ := rfl
  rw [genB_prodX_eq_quarter_signed_sum hf hn φ ξ hprim hodd]
  change ‖signedCharacterSum φ ξ / 4‖ = 1
  rw [← hφ, ← hξ, ← map_signedCharacterSum, norm_div, hfour, div_one]
  exact hunit _ hS

end UpperTheory.V.X
