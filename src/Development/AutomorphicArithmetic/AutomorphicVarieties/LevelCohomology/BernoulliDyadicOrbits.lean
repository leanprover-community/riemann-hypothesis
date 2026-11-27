module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.BernoulliBoundary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.BernoulliSignedNumerator
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic.Ring

/-!
# Pure dyadic Bernoulli sums on the orbits of 5

For `N = 2^(n+3)`, the units are the residues `±5^j` with `j < N/4`.
Negation and translation by `N/2` each reverse the sign of the pure Bernoulli
coefficient. For an odd primitive character the character value also changes
sign under both operations. Each representative with `j < N/8` therefore
contributes four equal terms to the all-residue signed sum.
-/

@[expose] public section

namespace UpperTheory.V.X

open Finset

/-- Sum a function supported on units by enumerating the two cosets of the powers of 5. -/
theorem sum_dyadic_units_eq_sum_powers {A : Type*} [AddCommMonoid A] (n : ℕ)
    (F : ZMod (2 ^ (n + 3)) → A) (hF : ∀ x, ¬IsUnit x → F x = 0) :
    ∑ x : ZMod (2 ^ (n + 3)), F x =
      ∑ j ∈ range (2 ^ (n + 1)), (F (5 ^ j) + F (-(5 ^ j))) := by
  classical
  let N := 2 ^ (n + 3)
  have hlarge : 2 < N := by dsimp [N]; rw [pow_add]; have := Nat.two_pow_pos n; omega
  have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.mpr (by omega)
  let u : (ZMod N)ˣ := ZMod.unitFive
  let v : (ZMod N)ˣ := -1
  have hu : orderOf u = 2 ^ (n + 1) := ZMod.orderOf_unitFive _
  have hv : orderOf v = 2 := by
    rw [Units.orderOf_neg_one, ZMod.ringChar_zmod_n, ite_eq_right]
    omega
  let E (g : (ZMod N)ˣ) {m : ℕ} (hg : orderOf g = m) : Fin m ≃ Subgroup.zpowers g :=
    (finCongr hg.symm).trans (finEquivZPowers (isOfFinOrder_of_finite g))
  let prodEquiv : Subgroup.zpowers u × Subgroup.zpowers v ≃ (ZMod N)ˣ :=
    Equiv.ofBijective _ (ZMod.isComplement'_zpowers_unitFive_neg_one (n + 3))
  let e := ((E u hu).prodCongr (E v hv)).trans prodEquiv
  let inc : (ZMod N)ˣ ↪ ZMod N := ⟨Units.val, Units.val_injective⟩
  calc
    _ = ∑ x ∈ univ.map inc, F x := by
      symm
      refine sum_subset (subset_univ _) fun x _ hx ↦ hF x ?_
      rintro ⟨w, rfl⟩
      exact hx (mem_map.mpr ⟨w, mem_univ _, rfl⟩)
    _ = ∑ w : (ZMod N)ˣ, F w := sum_map _ _ _
    _ = ∑ j : Fin (2 ^ (n + 1)), ∑ k : Fin 2, F (5 ^ (j : ℕ) * (-1) ^ (k : ℕ)) := by
      rw [← e.sum_comp (fun w : (ZMod N)ˣ ↦ F w), Fintype.sum_prod_type]
      refine sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ ?_
      change F (↑(u ^ (j : ℕ) * v ^ (k : ℕ)) : ZMod N) = _
      simp [u, v, Units.val_pow_eq_pow_val]
    _ = _ := by
      simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one,
        mul_neg_one]
      exact Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ F (5 ^ j) + F (-(5 ^ j))) _

/-- The upper and lower half signs are reversed at opposite unit residues. -/
private lemma pureCoeff_neg {R : Type*} [CommRing R] (m : ℕ) (hm : Even m) (hm' : 0 < m)
    (x : ZMod (2 * m)) (hx : IsUnit x) :
    bernoulliSignedCoeff (fun _ : ZMod 1 ↦ (1 : R)) (2 * m) (-x).val =
      -bernoulliSignedCoeff (fun _ : ZMod 1 ↦ (1 : R)) (2 * m) x.val := by
  have : NeZero (2 * m) := ⟨by omega⟩
  have : Nontrivial (ZMod (2 * m)) := ZMod.nontrivial_iff.mpr (by omega)
  have : NeZero x := ⟨hx.ne_zero⟩
  have hne : x.val ≠ m := by
    intro he
    have hu : IsUnit (x.val : ZMod (2 * m)) := by rwa [ZMod.natCast_zmod_val]
    rw [he] at hu
    exact Nat.not_coprime_of_dvd_of_dvd (by decide : 1 < 2) hm.two_dvd (dvd_mul_right 2 m)
      ((ZMod.isUnit_iff_coprime _ _).mp hu)
  have hlt := x.val_lt
  simp only [bernoulliSignedCoeff, Fin.sum_univ_one, Fin.val_zero, Nat.mul_zero, Nat.add_zero,
    one_mul, Nat.mul_div_cancel_left _ (by decide : 0 < 2), ZMod.val_neg_of_ne_zero]
  split_ifs <;> first | omega | simp_all

/-- Multiplying an odd residue by the half-turn adds half the modulus. -/
private lemma five_pow_half_shift (n j : ℕ) :
    let H := 2 ^ (n + 2)
    let N := 2 ^ (n + 3)
    (5 ^ (2 ^ n + j) : ℕ) % N = (5 ^ j % N + H) % N := by
  intro H N
  obtain ⟨c, hc, hv⟩ := five_pow_stride n
  obtain ⟨t, ht⟩ := (hc.mul ((by decide : Odd 5).pow (n := j))).exists_bit1
  have hx : 5 ^ (2 ^ n + j) = 5 ^ j + H + t * N := by
    rw [pow_add, hv]
    dsimp [H, N]
    calc (1 + 4 * 2 ^ n * c) * 5 ^ j = 5 ^ j + 4 * 2 ^ n * (c * 5 ^ j) := by ring
         _ = _ := by rw [ht]; ring
  rw [hx, mul_comm t N, Nat.add_mul_mod_self_left, Nat.mod_add_mod]

/-- For a pure odd dyadic character, the all-residue sum is four times the signed
polynomial at `χ 5`. The half-turn hypothesis also works after reducing the character. -/
theorem pureDyadic_signed_sum_eq_four_mul_of_half_turn {R : Type*} [CommRing R] (n : ℕ)
    (χ : DirichletCharacter R (2 ^ (n + 3))) (hodd : χ (-1) = -1)
    (hhalf : χ (1 + 2 ^ (n + 2)) = -1) :
    let N := 2 ^ (n + 3)
    ∑ r : Fin N, bernoulliSignedCoeff (fun _ : ZMod 1 ↦ (1 : R)) N r * χ r =
      4 * ∑ j ∈ range (2 ^ n), bernoulliSignedCoeff (fun _ : ZMod 1 ↦ (1 : R)) N (5 ^ j % N) *
        χ 5 ^ j := by
  intro N
  let H := 2 ^ (n + 2)
  have hN : N = 2 * H := by dsimp [N, H]; rw [pow_succ']
  let C := bernoulliSignedCoeff (fun _ : ZMod 1 ↦ (1 : R)) N
  let F (x : ZMod N) := C x.val * χ x
  have hzero (x : ZMod N) (hx : ¬IsUnit x) : F x = 0 := by simp [F, χ.map_nonunit hx]
  have hneg (j : ℕ) : F (-(5 ^ j)) = F (5 ^ j) := by
    have hx : IsUnit (5 ^ j : ZMod N) := by
      simpa using (ZMod.unitFive : (ZMod (2 ^ (n + 3)))ˣ).isUnit.pow j
    have hC : C (-(5 ^ j : ZMod N)).val = -C (5 ^ j : ZMod N).val := by
      change bernoulliSignedCoeff _ N _ = -bernoulliSignedCoeff _ N _
      generalize (5 ^ j : ZMod N) = x at hx ⊢
      revert x
      rw [hN]
      exact pureCoeff_neg H (Even.pow_of_ne_zero even_two (by omega)) (Nat.two_pow_pos _)
    have hχ (x : ZMod N) : χ (-x) = -χ x := by rw [← neg_one_mul x, map_mul, hodd, neg_one_mul]
    simp only [F, hC, hχ, neg_mul_neg]
  have hpow (j : ℕ) : F (5 ^ j) = C (5 ^ j % N) * χ 5 ^ j := by
    simp only [F, map_pow, ← ZMod.val_natCast, Nat.cast_pow, Nat.cast_ofNat]
  have hβ : χ 5 ^ (2 ^ n) = -1 := (map_five_pow_half_turn n χ.toMonoidHom).trans hhalf
  have hperiod (j : ℕ) : F (5 ^ (2 ^ n + j)) = F (5 ^ j) := by
    rw [hpow, hpow, pow_add (χ 5), hβ, neg_one_mul, five_pow_half_shift]
    have hC (r : ℕ) (hr : r < N) : C ((r + H) % N) = -C r := by
      simp only [C, bernoulliSignedCoeff, Fin.sum_univ_one, Fin.val_zero, Nat.mul_zero, Nat.add_zero,
        one_mul, show N / 2 = H by omega]
      by_cases hl : r < H
      · rw [Nat.mod_eq_of_lt (by omega), ite_eq_right (by omega), ite_eq_left hl, neg_neg]
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), ite_eq_left (by omega),
          ite_eq_right hl]
    rw [show 2 ^ (n + 2) = H from rfl, hC _ (Nat.mod_lt _ (Nat.two_pow_pos _)), neg_mul_neg]
  calc
    _ = ∑ x : ZMod N, F x := by
      rw [← (ZMod.finEquiv N).sum_comp F]
      exact sum_congr rfl fun r _ ↦ by
        change C r.val * χ r.val = C (ZMod.finEquiv N r).val * χ (ZMod.finEquiv N r)
        have hv (L : ℕ) [NeZero L] (a : Fin L) : (ZMod.finEquiv L a).val = a.val := by
          cases L with
          | zero => exact Fin.elim0 a
          | succ l => rfl
        rw [← hv N r, ZMod.natCast_zmod_val]
    _ = ∑ j ∈ range (2 ^ (n + 1)), (F (5 ^ j) + F (-(5 ^ j))) :=
      sum_dyadic_units_eq_sum_powers n F hzero
    _ = _ := by
      simp_rw [hneg, ← two_mul]
      rw [← mul_sum, pow_succ, mul_two, sum_range_add]
      simp_rw [hperiod, hpow]
      ring

/-- At twice an even modulus, the only possible nontrivial unit in the kernel of
reduction is `1 + m`. Thus triviality on this element suffices for descent. -/
private lemma factorsThrough_half {R : Type*} [CommRing R] {m : ℕ} (hm : 1 < m)
    (χ : DirichletCharacter R (2 * m)) (hχ : χ (1 + m) = 1) : χ.FactorsThrough m := by
  have : NeZero m := ⟨by omega⟩
  have : NeZero (2 * m) := ⟨by omega⟩
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (dvd_mul_left m 2)]
  intro x hx
  rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, ← ZMod.natCast_val, Units.val_one] at hx
  let r := (x : ZMod (2 * m)).val
  have hmod : r ≡ 1 [MOD m] := (ZMod.natCast_eq_natCast_iff r 1 m).mp (by rw [Nat.cast_one]; exact hx)
  have hr := Nat.mod_eq_of_modEq hmod hm
  have hbound : r < 2 * m := ZMod.val_lt _
  rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one,
    ← ZMod.natCast_zmod_val (x : ZMod (2 * m))]
  change χ (r : ZMod (2 * m)) = 1
  by_cases hlt : r < m
  · rw [Nat.mod_eq_of_lt hlt] at hr
    simp [hr]
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hr
    rw [show r = 1 + m by omega]
    simpa using hχ

/-- A primitive character cannot descend to the half modulus. Squaring the half-turn
then forces its character value to be `-1` over a field. -/
private lemma primitive_half_turn {K : Type*} [Field K] (n : ℕ)
    (χ : DirichletCharacter K (2 ^ (n + 3))) (hprim : χ.IsPrimitive) :
    χ (1 + 2 ^ (n + 2)) = -1 := by
  let m := 2 ^ (n + 2)
  have hm : 1 < m := Nat.one_lt_pow (by omega) (by decide)
  have hN : 2 ^ (n + 3) = 2 * m := pow_succ' _ _
  have hne : χ (1 + 2 ^ (n + 2)) ≠ 1 := by
    intro h
    have hcast : (m : ZMod (2 ^ (n + 3))) = 2 ^ (n + 2) := by simp [m]
    rw [← hcast] at h
    have hft : χ.FactorsThrough m := by
      revert χ
      rw [hN]
      exact fun χ _ h ↦ factorsThrough_half hm χ h
    have hle := Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr hft)
    change χ.conductor ≤ m at hle
    rw [show χ.conductor = 2 ^ (n + 3) from hprim] at hle
    omega
  have hs : χ (1 + 2 ^ (n + 2)) ^ 2 = 1 := by
    have h5 := map_five_pow_half_turn n χ.toMonoidHom
    change χ 5 ^ (2 ^ n) = χ (1 + 2 ^ (n + 2)) at h5
    rw [← h5, ← pow_mul, ← pow_succ, ← map_pow,
      ← ZMod.orderOf_five (n + 1), pow_orderOf_eq_one, map_one]
  exact (sq_eq_one_iff.mp hs).resolve_left hne

/-- The all-residue signed sum for an odd primitive dyadic character equals four times
the sum on the powers of 5 below the half-turn. -/
theorem pureDyadic_signed_sum_eq_four_mul {K : Type*} [Field K] (n : ℕ)
    (χ : DirichletCharacter K (2 ^ (n + 3))) (hodd : χ (-1) = -1) (hprim : χ.IsPrimitive) :
    let N := 2 ^ (n + 3)
    ∑ r : Fin N, bernoulliSignedCoeff (fun _ : ZMod 1 ↦ (1 : K)) N r * χ r =
      4 * ∑ j ∈ range (2 ^ n), bernoulliSignedCoeff (fun _ : ZMod 1 ↦ (1 : K)) N (5 ^ j % N) *
        χ 5 ^ j :=
  pureDyadic_signed_sum_eq_four_mul_of_half_turn n χ hodd (primitive_half_turn n χ hprim)

/-- For a pure character the factor of four cancels the quarter in the weighted mean. -/
theorem pureDyadic_weightedMean_eq_sum_powers {K : Type*} [Field K] [CharZero K] (n : ℕ)
    (χ : DirichletCharacter K (2 ^ (n + 3))) (hodd : χ (-1) = -1) (hprim : χ.IsPrimitive) :
    let N := 2 ^ (n + 3)
    (∑ x ∈ range N, χ x * (x : K)) / (N : K) =
      ∑ j ∈ range (2 ^ n), bernoulliSignedCoeff (fun _ : ZMod 1 ↦ (1 : K)) N (5 ^ j % N) *
        χ 5 ^ j := by
  intro N
  let m := 2 ^ (n + 2)
  have hN : N = 2 * m := pow_succ' _ _
  have hhalf : χ (1 + (m : ZMod N)) = -1 := by simpa [m, N] using primitive_half_turn n χ hprim
  have hquarter (L : ℕ) (hL : L = 2 * m) (ξ : DirichletCharacter K L)
      (hξ : ξ (1 + (m : ZMod L)) = -1) :
      (∑ x ∈ range L, ξ x * (x : K)) / (L : K) =
        (∑ r : Fin L, bernoulliSignedCoeff (fun _ : ZMod 1 ↦ (1 : K)) L r * ξ r) / 4 := by
    subst L
    simpa [m] using bernoulliWeightedMean_eq_quarter_signed_sum (f := 1) odd_one (Nat.two_pow_pos _)
      (Even.pow_of_ne_zero even_two (by omega : n + 2 ≠ 0)) (fun _ ↦ (1 : K)) ξ hξ
  rw [hquarter N hN χ hhalf, pureDyadic_signed_sum_eq_four_mul n χ hodd hprim,
    mul_div_cancel_left₀ _ (by norm_num)]

/-- At the equality conductor, the all-residue signed sum of an odd primitive character
is nonzero in the residue field. -/
theorem pureDyadic_signed_sum_boundary_ne_zero {K : Type*} [Field K] {ℓ : ℕ}
    [Fact ℓ.Prime] [CharP K ℓ] (d e c : ℕ) (he : 2 ≤ e) (hc : Odd c)
    (hQ : ℓ ^ d = 1 + 2 ^ e * c) (h2 : (2 : K) ≠ 0) :
    let N := 2 ^ (2 * e - 1)
    ∀ χ : DirichletCharacter K N, χ (-1) = -1 → χ.IsPrimitive →
      ∑ r : Fin N, bernoulliSignedCoeff (fun _ : ZMod 1 ↦ (1 : K)) N r * χ r ≠ 0 := by
  dsimp only
  obtain ⟨n, hn⟩ : ∃ n, 2 * e - 1 = n + 3 := ⟨2 * e - 4, by omega⟩
  rw [hn]
  intro χ hodd hprim
  have hhalf := primitive_half_turn n χ hprim
  rw [pureDyadic_signed_sum_eq_four_mul_of_half_turn n χ hodd hhalf]
  refine mul_ne_zero (by rw [show (4 : K) = 2 * 2 by ring]; exact mul_ne_zero h2 h2) ?_
  have h := bernoulliSignedSum_boundary_ne_zero d e c he hc hQ h2 (χ 5)
  dsimp only at h
  rw [hn, show 2 ^ (n + 3) / 8 = 2 ^ n by rw [pow_add]; exact Nat.mul_div_cancel _ (by decide)] at h
  exact h ((map_five_pow_half_turn n χ.toMonoidHom).trans hhalf)

end UpperTheory.V.X
