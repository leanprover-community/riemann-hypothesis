module

import TauCeti.NumberTheory.NumberField.FrequencySum
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.DedekindZeta.ExpBound
public import Aesop.BuiltinRules
public import Lib.General.NumberTheory.EmbeddingsAndDifferent

/-!
# Sums over frequencies

The frequencies are the elements `ν` of a totally complex number field `E`. If `E` has `f` infinite
places, the sum of `∏_v [ν]_v ^ (-3)` over any finite subset of `E` is at most `C ^ f` with
`C = 64 * 38 * e ^ 4`. At an infinite place `[ν]_v` is `(max 1 |ν|_v) ^ 2`, with `|ν|_v` the usual
absolute value, and the finite places together give the norm of the denominator of `ν`. The numbers
with a given denominator `𝔟` lie in `N 𝔟` cosets of the ring of integers, each coset is counted by
small squares, and the sum over `𝔟` is at most the value at `2` of the Dedekind zeta function.

Notions from other files:
* `Φ v`: the chosen complex embedding of `E` that induces the infinite place `v`
  (`PlaceEmbedding E`).
-/

@[expose] public section

open NumberField Finset

noncomputable section

namespace New

variable {E : Type} [Field E] [NumberField E]

/-- The denominator of `ν`: the ideal of the integers `a` such that `a ν` is integral. -/
def denominator (ν : E) : Ideal (𝓞 E) where
  carrier := {a : 𝓞 E | IsIntegral ℤ (algebraMap (𝓞 E) E a * ν)}
  zero_mem' := by simpa using isIntegral_zero
  add_mem' ha hb := by simpa [add_mul] using IsIntegral.add ha hb
  smul_mem' c a ha := by simpa [mul_assoc] using IsIntegral.mul c.isIntegral_coe ha

omit [NumberField E] in
lemma mem_denominator {ν : E} {a : 𝓞 E} :
    a ∈ denominator ν ↔ IsIntegral ℤ (algebraMap (𝓞 E) E a * ν) :=
  Iff.rfl

omit [NumberField E] in
private lemma denominator_eq_denIdeal (ν : E) : denominator ν = Algebra.denIdeal E ν := by
  ext a
  rw [mem_denominator, Algebra.mem_denIdeal_iff]
  exact ⟨fun h ↦ ⟨⟨_, h⟩, rfl⟩, fun ⟨a, ha⟩ ↦ ha.symm ▸ a.isIntegral_coe⟩

lemma denominator_ne_bot (ν : E) : denominator ν ≠ ⊥ := by
  simpa only [denominator_eq_denIdeal] using
    Algebra.denIdeal_ne_bot E (nonZeroDivisors (𝓞 E)) ν

/-- For a nonzero ideal `𝔟`, the numbers `ν` whose denominator (the ideal of the integers `a`
with `a ν` integral) contains `𝔟` can be given `N 𝔟` labels so that two numbers with the same
label differ by an algebraic integer. -/
lemma exists_coset_label {𝔟 : Ideal (𝓞 E)} (h𝔟 : 𝔟 ≠ ⊥) :
    ∃ label : E → Fin (Ideal.absNorm 𝔟), ∀ ν ν' : E,
      𝔟 ≤ denominator ν → 𝔟 ≤ denominator ν' → label ν = label ν' → IsIntegral ℤ (ν - ν') := by
  simp_rw [denominator_eq_denIdeal]
  obtain ⟨label, h_label⟩ := NumberField.exists_label_fin_absNorm_of_ne_bot h𝔟
  refine ⟨label, fun ν ν' hν hν' h_eq ↦ ?_⟩
  obtain ⟨t, ht⟩ := h_label ν ν' hν hν' h_eq
  exact ht ▸ t.isIntegral_coe

/-- The sum of `Ideal.absNorm 𝔟 ^ (-2)` over a finite set `s` of ideals of the ring of integers of
`E` is at most `exp (2 [E : ℚ])`, where `[E : ℚ] = Module.finrank ℚ E`: it is at most the value at
`2` of the Euler product with all coefficients equal to `1`, that is `ζ_E(2)`. -/
lemma sum_absNorm_inv_sq_le (s : Finset (Ideal (𝓞 E))) :
    ∑ 𝔟 ∈ s, (Ideal.absNorm 𝔟 : ℝ)⁻¹ ^ 2 ≤ Real.exp (2 * Module.finrank ℚ E) := by
  simpa [Real.rpow_neg_ofNat] using
    TauCeti.sum_absNorm_rpow_neg_le_exp_two_mul_finrank (K := E) le_rfl s

variable [PlaceEmbedding E]

/-- Let `X` be a finite subset of a totally complex field `E` any two elements of which differ by
an algebraic integer. Then the sum over `ν ∈ X` of the archimedean weights
`∏_v (max 1 ‖Φ v ν‖)⁻¹ ^ 6` is at most `(64 * 38) ^ f`, where `Φ v` is the chosen embedding at `v`
and `f` is the number of infinite places. -/
lemma sum_coset_weight_le [IsTotallyComplex E] {X : Finset E}
    (hX : ∀ ν ∈ X, ∀ ν' ∈ X, IsIntegral ℤ (ν - ν')) :
    ∑ ν ∈ X, ∏ v : InfinitePlace E, (max 1 ‖Φ v ν‖)⁻¹ ^ 6 ≤ (64 * 38) ^ Core.numInfPlaces E := by
  simpa only [← InfinitePlace.apply, mk_Φ] using
    (NumberField.sum_prod_inv_max_one_pow_six_le_of_sub_mem (X := X)
      fun ν hν ν' hν' ↦ ⟨⟨ν - ν', hX ν hν ν' hν'⟩, rfl⟩)

/-- Let `X` be a finite subset of a totally complex field `E`. The archimedean weights
`∏_v (max 1 ‖Φ v ν‖)⁻¹ ^ 6` of those `ν ∈ X` with a given nonzero denominator `𝔟` add up to at most
`Ideal.absNorm 𝔟 * (64 * 38) ^ Core.numInfPlaces E`, as these `ν` lie in at most `Ideal.absNorm 𝔟`
cosets of the integers. -/
lemma sum_weight_filter_denominator_eq_le [IsTotallyComplex E] [DecidableEq (Ideal (𝓞 E))]
    (X : Finset E) {𝔟 : Ideal (𝓞 E)} (h𝔟 : 𝔟 ≠ ⊥) :
    ∑ ν ∈ X with denominator ν = 𝔟, ∏ v : InfinitePlace E, (max 1 ‖Φ v ν‖)⁻¹ ^ 6 ≤
      Ideal.absNorm 𝔟 * (64 * 38) ^ Core.numInfPlaces E := by
  simp_rw [← InfinitePlace.apply, mk_Φ, denominator_eq_denIdeal]
  convert NumberField.sum_filter_denIdeal_eq_prod_inv_max_one_pow_six_le X h𝔟 using 2
  congr 1

/-- Let `E` be a totally complex number field with `f = Core.numInfPlaces E` infinite places. For a
finite set `X ⊂ E`, the sum of `∏_v [ν]_v ^ (-3)` over `ν ∈ X` is at most
`(64 * 38 * e ^ 4) ^ f`. -/
theorem sum_height_inv_cube_le [IsTotallyComplex E] (X : Finset E) :
    ∑ ν ∈ X, (∏ v : InfinitePlace E, (max 1 ‖Φ v ν‖)⁻¹ ^ 6) *
      (Ideal.absNorm (denominator ν) : ℝ)⁻¹ ^ 3 ≤
      (64 * 38 * Real.exp 4) ^ Core.numInfPlaces E := by
  simpa only [← InfinitePlace.apply, mk_Φ, denominator_eq_denIdeal] using
    NumberField.sum_prod_inv_max_one_pow_six_mul_inv_absNorm_denIdeal_pow_three_le X

end New

end
