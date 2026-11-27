module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.BernoulliFourierRows
public import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Ring

/-!
# The Bernoulli numerator in signed residue classes

Translation by half the conductor reverses the dyadic character. Pairing these
two halves cancels the integer weights and expresses the numerator divided by
the conductor in terms of integral signed coefficients, including when the
residue characteristic divides the odd conductor.
-/

@[expose] public section

namespace UpperTheory.V.X

open Finset

variable {R : Type*} [CommRing R]

private theorem weighted_half_sum (H : ℕ) (w : ℕ → R)
    (hanti : ∀ x, w (H + x) = -w x) :
    4 * (∑ x ∈ range (2 * H), (x : R) * w x) =
      (2 * H : ℕ) * ∑ x ∈ range (2 * H), (if x < H then -w x else w x) := by
  rw [two_mul, sum_range_add, sum_range_add]
  have hw : (∑ x ∈ range H, (x : R) * w x) +
      (∑ x ∈ range H, ((H + x : ℕ) : R) * w (H + x)) =
      -(H : R) * ∑ x ∈ range H, w x := by
    rw [← sum_add_distrib, mul_sum]
    exact sum_congr rfl fun x _ ↦ by rw [hanti, Nat.cast_add]; ring
  have hlo : (∑ x ∈ range H, (if x < H then -w x else w x)) = -∑ x ∈ range H, w x := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun x hx ↦ by simp [mem_range.mp hx]
  have hhi : (∑ x ∈ range H, (if H + x < H then -w (H + x) else w (H + x))) =
      -∑ x ∈ range H, w x := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun x _ ↦ by simp [hanti]
  rw [hw, hlo, hhi]
  push_cast
  ring

private theorem sum_signed_residues {f N : ℕ} (φ : ZMod f → R) (ξ : ZMod N → R) :
    (∑ x ∈ range (f * N), (if x < f * N / 2 then -(φ x * ξ x) else φ x * ξ x)) =
      ∑ r : Fin N, bernoulliSignedCoeff φ N r * ξ r := by
  let F (x : ℕ) := if x < f * N / 2 then -(φ x * ξ x) else φ x * ξ x
  change (∑ x ∈ range (f * N), F x) = _
  rw [← Fin.sum_univ_eq_sum_range F (f * N)]
  rw [← finProdFinEquiv.sum_comp (fun x : Fin (f * N) ↦ F x), Fintype.sum_prod_type, sum_comm]
  apply sum_congr rfl
  intro r _
  rw [bernoulliSignedCoeff, sum_mul]
  apply sum_congr rfl
  intro j _
  change F (r.val + N * j.val) = _
  simp only [F, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
  split <;> simp_all

/-- Four times the numerator of the first generalized Bernoulli number is the conductor
times the signed residue sum. Here the dyadic character reverses sign on translating by
half its modulus. The identity holds before division in any commutative coefficient ring. -/
theorem bernoulliNumerator_eq_signed_sum {f m : ℕ} (hf : Odd f)
    (φ : ZMod f → R) (ξ : ZMod (2 * m) → R) (hξ : ∀ r, ξ (r + m) = -ξ r) :
    4 * (∑ x ∈ range (f * (2 * m)), (x : R) * (φ x * ξ x)) =
      (f * (2 * m) : ℕ) * ∑ r : Fin (2 * m), bernoulliSignedCoeff φ (2 * m) r * ξ r := by
  have heq : f * (2 * m) = 2 * (f * m) := by ring
  have hshift : ((f * m : ℕ) : ZMod (2 * m)) = m := by
    obtain ⟨k, hk⟩ := hf
    rw [hk, show (2 * k + 1) * m = (2 * m) * k + m by ring]
    simp
  have hanti (x : ℕ) : φ ((f * m + x : ℕ) : ZMod f) * ξ ((f * m + x : ℕ) : ZMod (2 * m)) =
      -(φ x * ξ x) := by
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add,
      Nat.cast_add, hshift, add_comm, hξ, mul_neg]
  rw [← sum_signed_residues, heq, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  exact weighted_half_sum (f * m) (fun x ↦ φ x * ξ x) hanti

private theorem character_add_half {m : ℕ} (hm : 0 < m) (he : Even m)
    (ξ : DirichletCharacter R (2 * m)) (hξ : ξ (1 + m) = -1) (r : ZMod (2 * m)) :
    ξ (r + m) = -ξ r := by
  have : NeZero (2 * m) := ⟨by omega⟩
  obtain ⟨x, rfl⟩ : ∃ x : ℕ, (x : ZMod (2 * m)) = r := ⟨r.val, ZMod.natCast_zmod_val r⟩
  rcases Nat.even_or_odd x with hx | ⟨k, hk⟩
  · have hz (y : ℕ) (hy : Even y) : ξ (y : ZMod (2 * m)) = 0 := by
      apply MulChar.map_nonunit
      intro hu
      exact Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) hy.two_dvd (dvd_mul_right 2 m)
        ((ZMod.isUnit_iff_coprime _ _).mp hu)
    rw [← Nat.cast_add, hz _ (hx.add he), hz _ hx, neg_zero]
  · have hmod : ((x * m : ℕ) : ZMod (2 * m)) = m := by
      rw [hk, show (2 * k + 1) * m = (2 * m) * k + m by ring]
      simp
    have hmul : (x : ZMod (2 * m)) * (1 + m) = x + m := by
      rw [mul_add, mul_one, ← Nat.cast_mul, hmod]
    rw [← hmul, map_mul, hξ, mul_neg_one]

/-- The weighted mean defining the odd-character Bernoulli number equals one quarter
of the signed residue sum. Only the dyadic character value at one plus half the
modulus is needed; in particular the right side has no odd-conductor denominator. -/
theorem bernoulliWeightedMean_eq_quarter_signed_sum {K : Type*} [Field K] [CharZero K]
    {f m : ℕ} (hf : Odd f) (hm : 0 < m) (he : Even m) (φ : ZMod f → K)
    (ξ : DirichletCharacter K (2 * m)) (hξ : ξ (1 + m) = -1) :
    (∑ x ∈ range (f * (2 * m)), φ x * ξ x * (x : K)) / (f * (2 * m) : ℕ) =
      (∑ r : Fin (2 * m), bernoulliSignedCoeff φ (2 * m) r * ξ r) / 4 := by
  have hF : ((f * (2 * m) : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.mul_pos hf.pos (Nat.mul_pos (by decide) hm)).ne'
  have h := bernoulliNumerator_eq_signed_sum hf φ ξ (character_add_half hm he ξ hξ)
  apply (div_eq_div_iff hF (by norm_num)).mpr
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

end UpperTheory.V.X
