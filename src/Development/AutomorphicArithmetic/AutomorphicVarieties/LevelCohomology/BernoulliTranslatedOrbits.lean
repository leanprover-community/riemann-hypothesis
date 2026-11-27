module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.BernoulliDyadicOrbits
import Mathlib.Data.Fin.Rev
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic.Ring

/-!
# Translated dyadic orbits with an odd conductor

The signed coefficient over a residue modulo `N` sums the lifts to modulus `f * N`.
Negation reverses the lifts. Translation by `f * N / 2` permutes them over the
opposite residue modulo `N` and fixes their labels modulo `f`. These two symmetries
allow the character sum to be read on the powers of five starting at any unit.
-/

@[expose] public section

namespace UpperTheory.V.X

open Finset

variable {R : Type*} [CommRing R] {f : ℕ}

private def signedLift (φ : ZMod f → R) (M x : ℕ) : R :=
  if x < M then -φ x else φ x

private lemma coeff_eq_sum (φ : ZMod f → R) (H r : ℕ) :
    bernoulliSignedCoeff φ (2 * H) r =
      ∑ j : Fin f, signedLift φ (f * H) (r + 2 * H * j) := by
  have he : f * (2 * H) / 2 = f * H := by
    rw [show f * (2 * H) = f * H * 2 by ring, Nat.mul_div_cancel _ (by decide)]
  simp only [bernoulliSignedCoeff, he, signedLift]

private lemma lift_lt {N r : ℕ} (hr : r < N) (j : Fin f) : r + N * j < f * N := by
  have hle := Nat.mul_le_mul_left N (Nat.succ_le_of_lt j.isLt)
  rw [Nat.mul_succ, mul_comm N f] at hle
  omega

/-- Reflection pairs the lift at index `j` with the lift at `f-1-j`. An odd
representative misses the midpoint when `H` is even. -/
theorem bernoulliSignedCoeff_reflect (φ : DirichletCharacter R f) {H r : ℕ}
    (hH : Even H) (hr : r < 2 * H) (ho : Odd r) :
    bernoulliSignedCoeff φ (2 * H) (2 * H - r) =
      -φ (-1) * bernoulliSignedCoeff φ (2 * H) r := by
  rw [coeff_eq_sum, coeff_eq_sum, ← Equiv.sum_comp Fin.revPerm
    (fun j : Fin f ↦ signedLift φ (f * H) (2 * H - r + 2 * H * j)), mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  let x := r + 2 * H * (j : ℕ)
  let y := 2 * H - r + 2 * H * (j.rev : ℕ)
  have hxy : y + x = 2 * (f * H) := by
    have hj : (j.rev : ℕ) + (j : ℕ) + 1 = f := by
      rw [Fin.val_rev]
      have := j.isLt
      omega
    dsimp only [y, x]
    calc _ = (2 * H - r + r) + 2 * H * ((j.rev : ℕ) + j) := by ring
         _ = 2 * H * ((j.rev : ℕ) + j + 1) := by rw [Nat.sub_add_cancel hr.le]; ring
         _ = _ := by rw [hj]; ring
  have hxne : x ≠ f * H := by
    have hx : Odd x := ho.add_even ((even_two.mul_right H).mul_right _)
    exact fun he ↦ (Nat.not_even_iff_odd.mpr hx) (he ▸ hH.mul_left f)
  have hcast : (y : ZMod f) = -(x : ZMod f) := by
    have h := congrArg (fun t : ℕ ↦ (t : ZMod f)) hxy
    exact eq_neg_of_add_eq_zero_left (by simpa using h : (y : ZMod f) + x = 0)
  have hφ : φ (y : ZMod f) = φ (-1) * φ (x : ZMod f) := by
    rw [hcast, ← neg_one_mul (x : ZMod f), map_mul]
  change signedLift φ (f * H) y = -φ (-1) * signedLift φ (f * H) x
  unfold signedLift
  rw [hφ]
  split_ifs <;> first | omega | ring

/-- Adding the full-level midpoint preserves the value of `φ` modulo `f` and swaps signs. -/
private lemma signedLift_half (φ : ZMod f → R) {M x : ℕ} (hd : f ∣ M) (hx : x < 2 * M) :
    signedLift φ M ((x + M) % (2 * M)) = -signedLift φ M x := by
  have hM : (M : ZMod f) = 0 := (ZMod.natCast_eq_zero_iff ..).mpr hd
  unfold signedLift
  by_cases hl : x < M
  · rw [Nat.mod_eq_of_lt (by omega), ite_eq_right (by omega), ite_eq_left hl, neg_neg]
    simp [hM]
  · have hrem : (x + M) % (2 * M) = x - M := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    rw [hrem, ite_eq_left (by omega), ite_eq_right hl, Nat.cast_sub (by omega), hM, sub_zero]

private lemma coeff_half_lower (φ : ZMod f → R) (hf : Odd f) {r H : ℕ} (hr : r < H) :
    bernoulliSignedCoeff φ (2 * H) (r + H) = -bernoulliSignedCoeff φ (2 * H) r := by
  obtain ⟨k, rfl⟩ := hf
  -- Adding the midpoint changes the lower residue by H and the lift index by k.
  let b : Fin (2 * k + 1) := ⟨k, by omega⟩
  rw [coeff_eq_sum, coeff_eq_sum, ← Equiv.sum_comp (Equiv.addRight b)
    (fun j : Fin (2 * k + 1) ↦ signedLift φ ((2 * k + 1) * H) (r + H + 2 * H * j)),
    ← sum_neg_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  let M := (2 * k + 1) * H
  let x := r + 2 * H * j.val
  let y := r + H + 2 * H * (j + b).val
  have htotal : (2 * k + 1) * (2 * H) = 2 * M := by dsimp [M]; ring
  have hx : x < 2 * M := htotal ▸ lift_lt (by omega : r < 2 * H) j
  have hy : y < 2 * M := htotal ▸ lift_lt (by omega : r + H < 2 * H) (j + b)
  have hindex : j.val + k ≡ (j + b).val [MOD 2 * k + 1] := (Nat.mod_modEq _ _).symm
  have hmod : x + M ≡ y [MOD 2 * M] := by
    rw [show 2 * M = 2 * H * (2 * k + 1) by dsimp [M]; ring,
      show x + M = r + H + 2 * H * (j.val + k) by dsimp [x, M]; ring]
    exact (hindex.mul_left' (2 * H)).add_left (r + H)
  change signedLift φ M y = -signedLift φ M x
  rw [← Nat.mod_eq_of_modEq hmod hy]
  exact signedLift_half φ (dvd_mul_right _ _) hx

/-- The half-turn permutes lifts modulo `f * (2 * H)` when `f` is odd. This uses
only the periodicity of the coefficient function modulo `f`. -/
theorem bernoulliSignedCoeff_add_half (φ : ZMod f → R) (hf : Odd f) {r H : ℕ}
    (hr : r < 2 * H) :
    bernoulliSignedCoeff φ (2 * H) ((r + H) % (2 * H)) = -bernoulliSignedCoeff φ (2 * H) r := by
  by_cases hl : r < H
  · rw [Nat.mod_eq_of_lt (by omega)]
    exact coeff_half_lower φ hf hl
  · have hrem : (r + H) % (2 * H) = r - H := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    have h := coeff_half_lower φ hf (by omega : r - H < H)
    rw [Nat.sub_add_cancel (by omega)] at h
    rw [hrem, h, neg_neg]

private lemma odd_unit_val {N H : ℕ} [NeZero N] (hN : N = 2 * H) (x : ZMod N) (hx : IsUnit x) :
    Odd x.val := by
  have hu : IsUnit (x.val : ZMod N) := by rwa [ZMod.natCast_zmod_val]
  exact (((ZMod.isUnit_iff_coprime _ _).mp hu).of_dvd_right
    (hN ▸ dvd_mul_right 2 H)).odd_of_right

private lemma mul_one_add_half {N H : ℕ} [NeZero N] (hN : N = 2 * H) (x : ZMod N) (hx : Odd x.val) :
    x * (1 + (H : ZMod N)) = x + H := by
  obtain ⟨k, hk⟩ := hx
  have hmod : ((x.val * H : ℕ) : ZMod N) = H := by
    rw [hk, show (2 * k + 1) * H = N * k + H by rw [hN]; ring]
    simp
  rw [mul_add, mul_one]
  congr 1
  simpa only [Nat.cast_mul, ZMod.natCast_zmod_val] using hmod

/-- Translating the powers of five by a unit `a` extracts the factor `4 * χ a`
from the all-residue sum. The truncated orbit has length `2^n = N/8`. -/
theorem translated_signed_sum_eq_four_mul (hf : Odd f) (n : ℕ) (φ : DirichletCharacter R f)
    (χ : DirichletCharacter R (2 ^ (n + 3))) (hodd : φ (-1) * χ (-1) = -1)
    (hhalf : χ (1 + 2 ^ (n + 2)) = -1) (a : (ZMod (2 ^ (n + 3)))ˣ) :
    let N := 2 ^ (n + 3)
    ∑ r : Fin N, bernoulliSignedCoeff φ N r * χ r =
      (4 * χ (a : ZMod N)) * ∑ j ∈ range (2 ^ n),
        bernoulliSignedCoeff φ N ((a : ZMod N) * 5 ^ j).val * χ 5 ^ j := by
  intro N
  let H := 2 ^ (n + 2)
  have hN : N = 2 * H := pow_succ' _ _
  have hH : 0 < H := Nat.two_pow_pos _
  have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.mpr (by omega)
  let C := bernoulliSignedCoeff φ N
  let G (x : ZMod N) := C x.val * χ x
  let F (x : ZMod N) := G (a * x)
  have hunit (j : ℕ) : IsUnit ((a : ZMod N) * 5 ^ j) := by
    apply a.isUnit.mul
    simpa using (ZMod.unitFive : (ZMod (2 ^ (n + 3)))ˣ).isUnit.pow j
  have hzero (x : ZMod N) (hx : ¬IsUnit x) : F x = 0 := by
    simp [F, G, map_mul, χ.map_nonunit hx]
  have hneg (j : ℕ) : F (-(5 ^ j)) = F (5 ^ j) := by
    let x : ZMod N := a * 5 ^ j
    have : NeZero x := ⟨(hunit j).ne_zero⟩
    have hr : x.val < 2 * H := hN ▸ x.val_lt
    have hC := bernoulliSignedCoeff_reflect φ (Even.pow_of_ne_zero even_two (by omega : n + 2 ≠ 0))
      hr (odd_unit_val hN x (hunit j))
    change bernoulliSignedCoeff φ (2 * H) (2 * H - x.val) = _ at hC
    rw [← hN] at hC
    change G ((a : ZMod N) * -(5 ^ j)) = G x
    rw [mul_neg]
    change C (-x).val * χ (-x) = C x.val * χ x
    rw [ZMod.val_neg_of_ne_zero, show C (N - x.val) = -φ (-1) * C x.val from hC,
      show χ (-x) = χ (-1) * χ x by rw [← neg_one_mul x, map_mul]]
    calc _ = -(φ (-1) * χ (-1)) * (C x.val * χ x) := by ring
         _ = _ := by rw [hodd, neg_neg, one_mul]
  have hperiod (j : ℕ) : F (5 ^ (2 ^ n + j)) = F (5 ^ j) := by
    let x : ZMod N := a * 5 ^ j
    have h5 : (5 : ZMod N) ^ (2 ^ n) = 1 + (H : ZMod N) := by
      have h := map_five_pow_half_turn n (MonoidHom.id (ZMod N))
      change (5 : ZMod N) ^ (2 ^ n) = 1 + 2 ^ (n + 2) at h
      simpa [H] using h
    have hc := bernoulliSignedCoeff_add_half (φ : ZMod f → R) hf (hN ▸ x.val_lt : x.val < 2 * H)
    rw [← hN] at hc
    have hv : C (x * (1 + (H : ZMod N))).val = -C x.val := by
      rw [mul_one_add_half hN x (odd_unit_val hN x (hunit j)), ZMod.val_add,
        ZMod.val_natCast_of_lt (by omega : H < N)]
      exact hc
    have ht : χ (1 + (H : ZMod N)) = -1 := by simpa [H] using hhalf
    have hmul : (a : ZMod N) * 5 ^ (2 ^ n + j) = x * (1 + (H : ZMod N)) := by
      rw [pow_add (5 : ZMod N), h5]; dsimp only [x]; ring
    change G ((a : ZMod N) * 5 ^ (2 ^ n + j)) = G x
    rw [hmul]
    simp only [G, hv, map_mul, ht, mul_neg_one, neg_mul_neg]
  have hpow (j : ℕ) : F (5 ^ j) =
      χ (a : ZMod N) * (C ((a : ZMod N) * 5 ^ j).val * χ 5 ^ j) := by
    simp only [F, G, map_mul, map_pow]
    ring
  calc
    _ = ∑ x : ZMod N, G x := by
      rw [← (ZMod.finEquiv N).sum_comp G]
      refine sum_congr rfl fun r _ ↦ ?_
      change C r.val * χ r.val = C (ZMod.finEquiv N r).val * χ (ZMod.finEquiv N r)
      have hv (L : ℕ) [NeZero L] (b : Fin L) : (ZMod.finEquiv L b).val = b.val := by
        cases L with
        | zero => exact Fin.elim0 b
        | succ _ => rfl
      rw [← hv N r, ZMod.natCast_zmod_val]
    _ = ∑ x : ZMod N, F x := (Equiv.sum_comp (Units.mulLeft a) G).symm
    _ = ∑ j ∈ range (2 ^ (n + 1)), (F (5 ^ j) + F (-(5 ^ j))) :=
      sum_dyadic_units_eq_sum_powers n F hzero
    _ = _ := by
      simp_rw [hneg, ← two_mul]
      rw [← mul_sum, pow_succ, mul_two, sum_range_add]
      simp_rw [hperiod, hpow, ← mul_sum]
      ring

/-- Vanishing of the all-residue sum forces vanishing on every translated truncated orbit. -/
theorem translated_signed_sum_eq_zero {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (hf : Odd f)
    (n : ℕ) (φ : DirichletCharacter K f) (χ : DirichletCharacter K (2 ^ (n + 3)))
    (hodd : φ (-1) * χ (-1) = -1) (hhalf : χ (1 + 2 ^ (n + 2)) = -1)
    (hsum : ∑ r : Fin (2 ^ (n + 3)), bernoulliSignedCoeff φ (2 ^ (n + 3)) r * χ r = 0)
    (a : (ZMod (2 ^ (n + 3)))ˣ) :
    ∑ j ∈ range (2 ^ n), bernoulliSignedCoeff φ (2 ^ (n + 3))
      ((a : ZMod (2 ^ (n + 3))) * 5 ^ j).val * χ 5 ^ j = 0 := by
  rw [translated_signed_sum_eq_four_mul hf n φ χ hodd hhalf a] at hsum
  have h4 : (4 : K) ≠ 0 := by rw [show (4 : K) = 2 * 2 by ring]; exact mul_ne_zero h2 h2
  exact (mul_eq_zero.mp hsum).resolve_left (mul_ne_zero h4 (a.isUnit.map χ).ne_zero)

/-- Natural representatives give the `a * 5^j % N` coefficients directly, with the
orbit length expressed as `N / 8`. -/
theorem translated_signed_sum_eq_zero_of_odd {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (hf : Odd f) (n : ℕ) (φ : DirichletCharacter K f) (χ : DirichletCharacter K (2 ^ (n + 3)))
    (hodd : φ (-1) * χ (-1) = -1) (hhalf : χ (1 + 2 ^ (n + 2)) = -1) (a : ℕ) (ha : Odd a) :
    let N := 2 ^ (n + 3)
    (∑ r : Fin N, bernoulliSignedCoeff φ N r * χ r) = 0 →
      ∑ j ∈ range (N / 8), bernoulliSignedCoeff φ N (a * 5 ^ j % N) * χ 5 ^ j = 0 := by
  intro N hs
  have hu : IsUnit (a : ZMod N) := (ZMod.isUnit_iff_coprime _ _).mpr
    (ha.coprime_two_right.pow_right (n + 3))
  have h := translated_signed_sum_eq_zero h2 hf n φ χ hodd hhalf hs hu.unit
  have hlen : N / 8 = 2 ^ n := by
    dsimp [N]; rw [pow_add]; exact Nat.mul_div_cancel _ (by decide)
  have hv (j : ℕ) : a * 5 ^ j % N = ((hu.unit : ZMod N) * 5 ^ j).val := by
    rw [hu.unit_spec, ← ZMod.val_natCast, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  simpa only [hlen, hv] using h

end UpperTheory.V.X
