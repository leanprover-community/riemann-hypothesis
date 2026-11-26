module

public import Lib.Weil.Periods.PointLattice

/-!
# The string of a graded space as the powers `𝔢 ^ i`

The orthogonal complement of `X` in a graded space with a string of `s` vectors behaves like
`E[𝔢] / (𝔢 ^ s)`: the vector called `𝔢 ^ i` is `New.Grading.stringPower`, a multiple of the string
vector with number `i`. That vector has grade `s - 1 - 2 * i`.

* `New.Grading.stringMap_mulVec_stringPower`: the map `New.Grading.stringMap` between neighbouring
  spaces is the projection `E[𝔢] / (𝔢 ^ s) → E[𝔢] / (𝔢 ^ (s - 1))`.
* `New.Grading.exists_stringSum_eq`, `New.Grading.stringMapFin_stringSum`: over the finite adeles
  the `𝔢 ^ i` span the complement of `X` (the vectors fixed by the projection
  `New.Grading.stringProj` to the span of the string vectors), and `New.Grading.stringMapFin`
  keeps the coordinates in `𝔢 ^ i` for `i < s - 1`.

Notions from other files:
* `New.Space E ι ε`: a hermitian matrix `V.J` over `E`, indexed by `ι`, with an adelic point;
* `New.Grading V N X s`: an identification `X ⊕ Fin s ≃ ι` under which string vector `i` pairs only
  with string vector `s - 1 - i`, to `1` (to `-N` in the middle), a constant `c = star c ≠ 0`, and
  the fact `N = star N ≠ 0`;
* `New.Grading.stringMap`, `New.Grading.stringMapFin`: the map that kills `X` and the string vector
  `s - 1` and keeps the number of any other string vector, up to a factor, and its part at the
  finite adeles;
-/

@[expose] public section

open Matrix

noncomputable section

namespace New.Grading

variable {E X X' ι ι' : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι'] [DecidableEq X] [DecidableEq X']
  {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {s : ℕ} {N : E} {V : Space E ι ε} {V' : Space E ι' ε'}
  (Y : Grading V N X s)

/-- The coefficient of `𝔢 ^ i` at the string vector `i`: a power of the constant `c` of the grading,
times `-N` if that vector has negative grade, that is if `s ≤ 2 * i`. -/
def powerCoeff (i : ℕ) : E :=
  if 2 * i < s then Y.genericConst.val ^ (i - s / 2 : ℤ) else -N * Y.genericConst.val ^
    (i - (s - 1) / 2 : ℤ)

/-- The vector `𝔢 ^ i` of the complement `E[𝔢] / (𝔢 ^ s)` of `X`: the multiple `Y.powerCoeff i` of
the string vector `i`, and `0` for `s ≤ i`. -/
def stringPower (i : ℕ) (k : ι) : E :=
  (Y.indexEquiv.symm k).elim 0 fun b : Fin s ↦ if b.val = i then Y.powerCoeff i else 0

/-- For a grading `Y` whose string has length `s`, the vector `𝔢 ^ i` is `Y.powerCoeff i` times the
`i`-th string vector. If that vector has nonnegative grade `s − 1 − 2i` (`2 * i < s`), this
coefficient is `c ^ n` for `n = i - s / 2`, where `c` is the constant `Y.genericConst`. -/
lemma powerCoeff_of_lt {i : ℕ} {n : ℤ} (hi : 2 * i < s) (hn : n = i - s / 2) :
    Y.powerCoeff i = Y.genericConst.val ^ n := by
  rw [powerCoeff, ite_eq_left hi, hn]

/-- In negative grade (`s ≤ 2 * i`) the coefficient of `𝔢 ^ i` is `-N * c ^ n` for
`n = i - (s - 1) / 2`. -/
lemma powerCoeff_of_le {i : ℕ} {n : ℤ} (hi : s ≤ 2 * i) (hn : n = i - (s - 1) / 2) :
    Y.powerCoeff i = -N * Y.genericConst.val ^ n := by
  rw [powerCoeff, ite_eq_right hi.not_gt, hn]

/-- The coefficient `Y.powerCoeff i` of `𝔢 ^ i` is nonzero, as `c` and `N` are. -/
lemma powerCoeff_ne_zero (i : ℕ) : Y.powerCoeff i ≠ 0 := by
  simp [powerCoeff, ite_eq_iff, zpow_ne_zero _ Y.genericConst.property.left,
    Y.N_ne_zero_and_star_eq.left]

/-- For `i < s` the vector `𝔢 ^ i` is supported at the string index `i`. -/
lemma stringPower_eq_single (i : Fin s) :
    Y.stringPower i = Pi.single (Y.indexEquiv (.inr i)) (Y.powerCoeff i) := by
  funext k
  obtain ⟨a | b, rfl⟩ := Y.indexEquiv.surjective k <;>
    simp [stringPower, Pi.single_apply, Fin.ext_iff]

lemma stringPower_eq_zero {i : ℕ} (hi : s ≤ i) : Y.stringPower i = 0 := by
  funext k
  obtain ⟨a | b, rfl⟩ := Y.indexEquiv.surjective k
  · simp [stringPower]
  · simp [stringPower, show b.val ≠ i by omega]

/-- For gradings `Y` and `Y'` of string lengths `s` and `s - 1` with the same constant `c`, the
factor of `Y.stringMap Y'` at the string vector `i` (the two `if`s below) times the coefficient of
`𝔢 ^ i` in `Y` is its coefficient in `Y'`. -/
lemma stringMap_factor_mul_powerCoeff (Y' : Grading V' N X' (s - 1))
    (hc : Y'.genericConst = Y.genericConst) (i : ℕ) :
    (if Odd s ↔ 2 * i + 1 < s then 1 else Y.genericConst.val) * (if 2 * i + 1 = s then -N else 1) *
      Y.powerCoeff i = Y'.powerCoeff i := by
  have hc_ne : Y.genericConst.val ≠ 0 := Y.genericConst.property.left
  -- The exponent of `c` in the factor.
  set e : ℤ := if s % 2 = 1 ↔ 2 * i + 1 < s then 0 else 1
  have h_factor : (if Odd s ↔ 2 * i + 1 < s then 1 else Y.genericConst.val) = Y.genericConst.val ^
    e := by
    simp [e, Nat.odd_iff]
  rw [h_factor]
  have h_nonneg (hi : 2 * i < s) : Y.powerCoeff i = Y.genericConst.val ^ (i - s / 2 : ℤ) :=
    Y.powerCoeff_of_lt hi rfl
  -- The grade of `𝔢 ^ i` is positive, `0` or negative.
  obtain h | h | h := lt_trichotomy (2 * i + 1) s
  · have h_right : Y'.powerCoeff i = Y'.genericConst.val ^ (e + (i - s / 2) : ℤ) :=
      Y'.powerCoeff_of_lt (by omega) (by omega)
    rw [ite_eq_right h.ne, mul_one, h_nonneg (by omega), h_right, hc, zpow_add₀ hc_ne]
  · have h_right : Y'.powerCoeff i = -N * Y'.genericConst.val ^ (e + (i - s / 2) : ℤ) :=
      Y'.powerCoeff_of_le (by omega) (by omega)
    rw [ite_eq_left h, h_nonneg (by omega), h_right, hc, zpow_add₀ hc_ne]
    ring
  · have h_left : Y.powerCoeff i = -N * Y.genericConst.val ^ (i - (s - 1) / 2 : ℤ) :=
      Y.powerCoeff_of_le (by omega) rfl
    have h_right : Y'.powerCoeff i = -N * Y'.genericConst.val ^ (e + (i - (s - 1) / 2) : ℤ) :=
      Y'.powerCoeff_of_le (by omega) (by omega)
    rw [ite_eq_right h.ne', h_left, h_right, hc, zpow_add₀ hc_ne]
    ring

/-- Let `Y'` be a grading of a second space `V'` with the same `N` and string length `s - 1`. Assume
`Y'` carries the same constant `c` as `Y`, where `c = c̄ ≠ 0` is the element of `E` that each
grading carries for the generic character. Then for `i < s` the matrix `Y.stringMap Y'` sends
`Y.stringPower i` (the vector `𝔢 ^ i` of `V`, seen over the adeles by the diagonal embedding
`toAdele`) to `Y'.stringPower i` (the vector `𝔢 ^ i` of `V'`), which is `0` for `i = s - 1`. -/
lemma stringMap_mulVec_stringPower (Y' : Grading V' N X' (s - 1))
    (hc : Y'.genericConst = Y.genericConst) (i : Fin s) :
    Y.stringMap Y' *ᵥ toAdele ∘ Y.stringPower i = toAdele ∘ Y'.stringPower i := by
  funext k
  rw [stringMap, ← RingHom.map_mulVec, stringPower_eq_single, mulVec_single]
  obtain ⟨a | b, rfl⟩ := Y'.indexEquiv.surjective k
  · simp [stringPower]
  · -- At the string index `b` both sides are `Y'.powerCoeff i` if `b = i`, else `0`.
    by_cases hb : b.val = i <;>
      simp [stringPower, hb, ← Y.stringMap_factor_mul_powerCoeff Y' hc i]

/-- The vector `∑ i < s, t i • 𝔢 ^ i` over the finite adeles, with coefficients `t`. -/
def stringSum (t : ℕ → 𝔸f E) : ι → 𝔸f E :=
  ∑ i ∈ Finset.range s, t i • algebraMap E (𝔸f E) ∘ Y.stringPower i

variable {Y}

lemma stringProj_stringSum (t : ℕ → 𝔸f E) :
    Y.stringProj (Y.stringSum t) = Y.stringSum t :=
  stringProj_eq_self_iff.2 (by simp [stringSum, stringPower])

/-- At the string index `b` the sum `∑ t i • 𝔢 ^ i` has the entry `Y.powerCoeff b * t b`. -/
lemma stringSum_apply_inr (t : ℕ → 𝔸f E) (b : Fin s) :
    Y.stringSum t (Y.indexEquiv (.inr b)) = algebraMap E (𝔸f E) (Y.powerCoeff b) * t b := by
  simp [stringSum, stringPower, apply_ite (algebraMap E (𝔸f E)), mul_comm]

/-- The vectors `𝔢 ^ i` span the complement of `X` over the finite adeles: a vector `y` fixed by
the projection `Y.stringProj` to the span of the string is a sum `∑ t i • 𝔢 ^ i`. -/
lemma exists_stringSum_eq {y : ι → 𝔸f E} (hy : Y.stringProj y = y) :
    ∃ t : ℕ → 𝔸f E, Y.stringSum t = y := by
  -- The coefficient of `𝔢 ^ i` is the entry of `y` at the string index `i` over `Y.powerCoeff i`.
  let t (i : ℕ) : 𝔸f E := if hi : i < s then
    algebraMap E (𝔸f E) (Y.powerCoeff i)⁻¹ * y (Y.indexEquiv (.inr ⟨i, hi⟩)) else 0
  refine ⟨t, funext fun k ↦ ?_⟩
  obtain ⟨a | b, rfl⟩ := Y.indexEquiv.surjective k
  · -- Both vectors are fixed by the projection, so both vanish at the indices in `X`.
    rw [stringProj_eq_self_iff.1 (stringProj_stringSum t) a, stringProj_eq_self_iff.1 hy a]
  · simp [stringSum_apply_inr, t, ← mul_assoc, ← map_mul, Y.powerCoeff_ne_zero b]

/-- For gradings with the same constant `c`, the map `Y.stringMapFin Y'`, the finite part of
`Y.stringMap Y'`, sends `𝔢 ^ i` to `𝔢 ^ i`. -/
lemma stringMapFin_stringPower {Y' : Grading V' N X' (s - 1)}
    (hc : Y'.genericConst = Y.genericConst) (i : Fin s) :
    Y.stringMapFin Y' (algebraMap E (𝔸f E) ∘ Y.stringPower i) =
      algebraMap E (𝔸f E) ∘ Y'.stringPower i := by
  funext k
  have h_adele : (Y.stringMap Y' *ᵥ toAdele ∘ Y.stringPower i) k = toAdele (Y'.stringPower i k) :=
    congrFun (Y.stringMap_mulVec_stringPower Y' hc i) k
  -- Take the finite component.
  simpa [stringMapFin, mulVec, dotProduct, Prod.snd_sum, toAdele] using congrArg Prod.snd h_adele

/-- For gradings `Y` and `Y'` of string lengths `s` and `s - 1` with the same constant `c`, the map
`Y.stringMapFin Y'`, the finite part of `Y.stringMap Y'`, acts on the sums `∑ t i • 𝔢 ^ i` as the
projection `E[𝔢] / (𝔢 ^ s) → E[𝔢] / (𝔢 ^ (s - 1))`: it keeps `t i` for `i < s - 1`. -/
lemma stringMapFin_stringSum {Y' : Grading V' N X' (s - 1)} (hc : Y'.genericConst = Y.genericConst)
    (t : ℕ → 𝔸f E) :
    Y.stringMapFin Y' (Y.stringSum t) = Y'.stringSum t := by
  calc Y.stringMapFin Y' (Y.stringSum t)
    _ = ∑ i ∈ Finset.range s, t i • algebraMap E (𝔸f E) ∘ Y'.stringPower i := by
      rw [stringSum, map_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [map_smul, stringMapFin_stringPower hc ⟨i, Finset.mem_range.1 hi⟩]
    _ = Y'.stringSum t := by
      -- The term for `i = s - 1` vanishes in `Y'`.
      refine (Finset.sum_subset (by simp) fun i _ hi ↦ ?_).symm
      simp [Y'.stringPower_eq_zero (show s - 1 ≤ i by simpa using hi)]

end New.Grading

end
