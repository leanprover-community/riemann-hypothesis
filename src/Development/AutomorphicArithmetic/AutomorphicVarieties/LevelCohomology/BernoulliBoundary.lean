module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.BernoulliRowSpecialization
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The equality layer for the pure dyadic Bernoulli sum

At `f = 1`, `N = 2*h^2`, and `h = 2^(e-1)`, the square of the row step
is half the modulus. Split the powers of five into even and odd exponents.
Their common squared stride has step `2*h`, whose square vanishes modulo `N`.
The two resulting signed progressions fold to the same geometric sum, up to a
phase. The original frequency has higher two-power order than this phase.

The signs and the choice of row are from the
[dyadic conductor derivation](https://github.com/leanprover-community/riemann-hypothesis/issues/5647).
-/

@[expose] public section

namespace UpperTheory.V.X

open Finset

variable {K : Type*} [Field K]

private lemma pureCoeff (N r : ℕ) :
    bernoulliSignedCoeff (fun _ : ZMod 1 ↦ (1 : K)) N r = if r < N / 2 then - 1 else 1 := by
  simp [bernoulliSignedCoeff]

/-- A translated half-row with linear stride. Folding the indices modulo `m` changes
both the sign of the coefficient and that of the phase in the upper half. -/
private lemma translated_half {m H r s w d : ℕ} (hm : 0 < m) (hr : r < H)
    (hr1 : r ≡ 1 [MOD 2 * m]) (hH : 2 * m ∣ H) (hw : w ≡ 1 + H * d [MOD H * (2 * m)])
    (hd : m.Coprime d) {γ : K} (hγ : γ ^ m = -1) :
    γ ^ s * bernoulliFourierRow (fun _ : ZMod 1 ↦ (1 : K)) (H * (2 * m)) (r + H * s) w m (γ ^ d) =
      -∑ t : Fin m, γ ^ (t : ℕ) := by
  let perm : Fin m → Fin m := fun j ↦ ⟨(s + d * j) % m, Nat.mod_lt _ hm⟩
  have hinj : Function.Injective perm := by
    intro i j hij
    have hij' : s + d * i ≡ s + d * j [MOD m] := congrArg Fin.val hij
    exact Fin.ext (((hij'.add_left_cancel' s).cancel_left_of_coprime hd).eq_of_lt_of_lt i.isLt j.isLt)
  let e := Equiv.ofBijective perm ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, rfl⟩)
  rw [← e.sum_comp (fun t : Fin m ↦ γ ^ (t : ℕ)), ← sum_neg_distrib, bernoulliFourierRow, mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  let t := s + d * (j : ℕ)
  let u := t % (2 * m)
  have hu : u < 2 * m := Nat.mod_lt _ (by omega)
  have hstart : r + H * s ≡ 1 [MOD 2 * m] :=
    (Nat.add_modEq_left_iff.mpr (dvd_mul_of_dvd_left hH s)).trans hr1
  have hx : (r + H * s) * w ^ (j : ℕ) % (H * (2 * m)) = r + H * u := by
    apply Nat.mod_eq_of_modEq (((pow_modEq_one_add_of_dvd hH hw j).mul_left (r + H * s)).trans ?_)
    · have hle := Nat.mul_le_mul_left H (Nat.succ_le_of_lt hu)
      rw [Nat.mul_succ] at hle
      omega
    · rw [show (r + H * s) * (1 + H * (d * j)) = r + H * (s + (r + H * s) * (d * j)) by ring]
      have hstep : s + (r + H * s) * (d * j) ≡ t [MOD 2 * m] := by
        simpa [t] using ((hstart.mul_right (d * j)).add_left s)
      exact ((hstep.trans (Nat.mod_modEq _ _).symm).mul_left' H).add_left r
  have hcut : r + H * u < H * (2 * m) / 2 ↔ u < m := by
    rw [show H * (2 * m) = (H * m) * 2 by ring, Nat.mul_div_cancel _ (by decide)]
    constructor
    · intro hlt
      by_contra! hge
      exact hlt.not_ge ((Nat.mul_le_mul_left H hge).trans (Nat.le_add_left _ _))
    · intro hlt
      have hle := Nat.mul_le_mul_left H (Nat.succ_le_of_lt hlt)
      rw [Nat.mul_succ] at hle
      omega
  have hfull : γ ^ (2 * m) = 1 := by rw [two_mul, pow_add, hγ]; simp
  have hphase : γ ^ s * (γ ^ d) ^ (j : ℕ) = γ ^ u := by
    rw [← pow_mul, ← pow_add]
    exact pow_eq_pow_mod _ hfull
  have hindex : (e j : ℕ) = u % m := (Nat.mod_mod_of_dvd t (dvd_mul_left m 2)).symm
  rw [hx, pureCoeff, if_congr hcut rfl rfl, mul_left_comm, hphase, hindex]
  by_cases h : u < m
  · simp [h, Nat.mod_eq_of_lt h]
  · have hu' : u % m + m = u := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    simp only [ite_eq_right h, one_mul]
    calc γ ^ u = γ ^ (u % m + m) := congrArg (γ ^ ·) hu'.symm
         _ = _ := by rw [pow_add, hγ, mul_neg_one]

private lemma sum_range_even_odd (F : ℕ → K) (m : ℕ) :
    ∑ i ∈ range (2 * m), F i =
      (∑ j ∈ range m, F (2 * j)) + ∑ j ∈ range m, F (2 * j + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, sum_range_succ, sum_range_succ, ih, sum_range_succ, sum_range_succ]
    ac_rfl

/-- The even and odd powers give rows of half the length with the squared stride and frequency. -/
private lemma split_row (N v m : ℕ) (β : K) :
    bernoulliFourierRow (fun _ : ZMod 1 ↦ (1 : K)) N 1 v (2 * m) β =
      bernoulliFourierRow (fun _ : ZMod 1 ↦ (1 : K)) N 1 (v ^ 2) m (β ^ 2) +
        β * bernoulliFourierRow (fun _ : ZMod 1 ↦ (1 : K)) N v (v ^ 2) m (β ^ 2) := by
  let C := bernoulliSignedCoeff (fun _ : ZMod 1 ↦ (1 : K)) N
  unfold bernoulliFourierRow
  simp only [one_mul]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ C (v ^ j % N) * β ^ j), sum_range_even_odd,
    Fin.sum_univ_eq_sum_range (fun j ↦ C ((v ^ 2) ^ j % N) * (β ^ 2) ^ j),
    Fin.sum_univ_eq_sum_range (fun j ↦ C (v * (v ^ 2) ^ j % N) * (β ^ 2) ^ j), mul_sum]
  simp only [pow_succ, pow_mul, mul_comm _ v, mul_left_comm β, mul_comm _ β]

/-- At the boundary `e = k + 3`, the row starting at 1 is nonzero for every allowed
frequency in a field of odd characteristic. Here `h = 2^(e-1)`, `N = 2*h²` and the
stride is `5^(h/4)`. -/
theorem bernoulliFourierRow_boundary_ne_zero (k : ℕ) (β : K) (h2 : (2 : K) ≠ 0) :
    let h := 4 * 2 ^ k
    β ^ h = -1 →
      bernoulliFourierRow (fun _ : ZMod 1 ↦ (1 : K)) (2 * h ^ 2) 1 (5 ^ (2 ^ k)) h β ≠ 0 := by
  intro h hβ
  let m := 2 * 2 ^ k
  have hm : 0 < m := Nat.mul_pos (by decide) (Nat.two_pow_pos _)
  have hh : h = 2 * m := by dsimp [h, m]; ring
  let H := 2 * h
  let v := 5 ^ (2 ^ k)
  have hN : 2 * h ^ 2 = H * (2 * m) := by dsimp [H]; rw [hh]; ring
  obtain ⟨c, ⟨s, hs⟩, hv⟩ := five_pow_stride k
  have hv' : v = (1 + h) + H * s := by dsimp [v, H]; rw [hv, hs]; dsimp [h]; ring
  obtain ⟨d, hd, hvsq⟩ := five_pow_stride (k + 1)
  have hw : v ^ 2 ≡ 1 + H * d [MOD H * (2 * m)] := by
    rw [pow_succ 2 k, pow_mul, show 4 * (2 ^ k * 2) = H by dsimp [H, h]; ring] at hvsq
    rw [show v ^ 2 = 1 + H * d from hvsq]
  have hd' : (2 * m).Coprime d := by
    rw [← hh, show h = 2 ^ (k + 2) by dsimp [h]; ring]
    exact hd.coprime_two_left.pow_left _
  obtain ⟨γ, hγ, hγd⟩ := exists_row_phase hm hd'.symm
    (show (β ^ 2) ^ m = -1 by rw [← pow_mul, ← hh, hβ])
  have hH : 2 * m ∣ H := by dsimp [H]; rw [hh]; exact dvd_mul_left _ _
  have hlarge : 1 < h := by omega
  have hEven := translated_half (s := 0) (r := 1) hm (by dsimp [H]; omega)
    (Nat.ModEq.refl _) hH hw (hd'.of_dvd_left (dvd_mul_left m 2)) hγ
  have hOdd := translated_half (s := s) (r := 1 + h) hm (by dsimp [H]; omega)
    (Nat.add_modEq_left_iff.mpr (hh ▸ dvd_rfl)) hH hw (hd'.of_dvd_left (dvd_mul_left m 2)) hγ
  rw [hγd, pow_zero, one_mul, Nat.mul_zero, Nat.add_zero] at hEven
  rw [hγd, ← hv'] at hOdd
  have hG : (∑ j : Fin m, γ ^ (j : ℕ)) ≠ 0 := by
    rw [Fin.sum_univ_eq_sum_range (γ ^ ·)]
    intro hz
    have he := geom_sum_mul γ m
    rw [hz, zero_mul, hγ] at he
    exact h2 (by linear_combination he)
  have hphase : γ ^ s + β ≠ 0 := by
    intro he
    have hb : β = -(γ ^ s) := by linear_combination he
    have hfull : γ ^ h = 1 := by rw [hh, two_mul, pow_add, hγ]; simp
    have heven : Even h := ⟨m, by omega⟩
    rw [hb, heven.neg_pow, ← pow_mul, mul_comm s h, pow_mul, hfull, one_pow] at hβ
    exact h2 (by linear_combination hβ)
  rw [hN, show 5 ^ (2 ^ k) = v from rfl, hh, split_row]
  intro hz
  apply (mul_ne_zero hphase hG)
  linear_combination γ ^ s * hEven + β * hOdd - γ ^ s * hz

/-- A character's half-turn at `1 + N/2` supplies the frequency hypothesis
at `5`, for any dyadic level `N ≥ 8`. -/
theorem map_five_pow_half_turn {R : Type*} [Monoid R] (n : ℕ)
    (χ : ZMod (2 ^ (n + 3)) →* R) : χ 5 ^ (2 ^ n) = χ (1 + 2 ^ (n + 2)) := by
  obtain ⟨c, ⟨s, hs⟩, hv⟩ := five_pow_stride n
  have h : 5 ^ (2 ^ n) = 1 + 2 ^ (n + 2) + 2 ^ (n + 3) * s := by rw [hv, hs]; ring
  rw [← map_pow]
  congr 1
  calc
    (5 : ZMod (2 ^ (n + 3))) ^ (2 ^ n) = ((5 ^ (2 ^ n) : ℕ) : ZMod (2 ^ (n + 3))) := by push_cast; rfl
    _ = _ := by rw [h, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]; push_cast; rfl

/-- The signed sum for the pure character at the sharp equality layer is nonzero.
Here `e ≥ 2`, `ℓ^d - 1 = 2^e*c` with `c` odd, and `z` is the reduced value at 5
of the dyadic character. Its half-order relation is `z^(N/8) = -1`. -/
theorem bernoulliSignedSum_boundary_ne_zero {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (d e c : ℕ) (he : 2 ≤ e) (hc : Odd c) (hQ : ℓ ^ d = 1 + 2 ^ e * c)
    (h2 : (2 : K) ≠ 0) (z : K) :
    let N := 2 ^ (2 * e - 1)
    z ^ (N / 8) = -1 →
      ∑ i ∈ range (N / 8), bernoulliSignedCoeff (fun _ : ZMod 1 ↦ (1 : K)) N (5 ^ i % N) * z ^ i ≠ 0 := by
  intro N hz
  by_cases he2 : e = 2
  · have hN8 : N = 8 := by dsimp [N]; rw [he2]; decide
    rw [hN8]
    change ∑ i ∈ range 1, bernoulliSignedCoeff (fun _ : ZMod 1 ↦ (1 : K)) 8 (5 ^ i % 8) * z ^ i ≠ 0
    simp [pureCoeff]
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 3 := ⟨e - 3, by omega⟩
  let h := 4 * 2 ^ k
  have hT : 2 ^ (k + 1 + 1) = h := by dsimp [h]; ring
  have hN : N = 2 * h ^ 2 := by
    dsimp [N, h]
    rw [show 2 * (k + 3) - 1 = k + k + 5 by lia, pow_add, pow_add]
    ring
  have hlen : N / 8 = 2 ^ k * h := by
    rw [hN, show 2 * h ^ 2 = (2 ^ k * h) * 8 by dsimp [h]; ring, Nat.mul_div_cancel _ (by decide)]
  intro hs
  apply bernoulliFourierRow_boundary_ne_zero k (z ^ (2 ^ k)) h2 (by
    change (z ^ (2 ^ k)) ^ h = -1
    rwa [← pow_mul, ← hlen])
  have row := bernoulliFourierRow_eq_zero_of_sum_eq_zero d (k + 1) k c 1
    (fun _ : ZMod 1 ↦ (1 : K)) z hc h2 (by simp)
  dsimp only at row
  rw [hT, show 4 * 2 ^ k = h from rfl, show h * (2 * h) = N by rw [hN]; ring] at row
  change bernoulliFourierRow _ (2 * h ^ 2) 1 _ h _ = 0
  rw [← hN]
  exact row (by rw [hQ]; dsimp [h]; ring) hz (by simpa only [one_mul] using hs)

end UpperTheory.V.X
