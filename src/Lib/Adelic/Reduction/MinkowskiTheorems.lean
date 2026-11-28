module

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Int.Log
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Algebra.Module.ZLattice.Basic
import TauCeti.LinearAlgebra.LinearIndependent.Extraction.Estimates
import TauCeti.NumberTheory.GeometryOfNumbers.MinkowskiSecond
public import Lib.Adelic.Adeles.IdeleModulus
public import Lib.Adelic.Unitary.Defs
import Lib.Adelic.Adeles.StrongApproximation
import Lib.General.NumberTheory.FrobeniusOrbits

/-!
# Adelic Minkowski theorems and counts of rational points in boxes

This file proves Minkowski's first theorem and the upper bound in his second theorem over the
adeles, for the lattice attached to `y : GL n (𝔸 E)`. This lattice consists of the rational vectors
`ξ` with `y⁻¹ ξ` integral at the finite places, measured by `y⁻¹ ξ` at the infinite places. Here
`New.𝔸 E` is `ℂ ^ f × 𝔸f E` with `f = New.Core.numInfPlaces E`; here `[CMType E]` makes `E` a number
field whose infinite places are all complex, each place `w` with a chosen embedding `Φ w : E → ℂ`.
`New.toAdele` is the diagonal embedding, `New.ideleAbs` the adelic absolute value and `New.Ô` the
ring of integral finite adeles, and the unit box is `ball 0 1 ×ˢ Ô E` (sup norm) in each coordinate.

## Main definitions and results

* `New.minkowski_first`: a lower bound for the number of rational `ξ` with `y⁻¹ ξ` in the unit box.
* `New.Core.twoAtInfinity`, `New.Core.dyadicDiag`, `New.Core.profileBases`: the idele that is `2` at
  infinity, the diagonal matrices `D` of its powers, and the rational bases `Y` with `y⁻¹ Y D⁻¹` in
  a given set.
* `New.Core.frameLattice`, `New.Core.frameLength`: the lattice of `y` and the Euclidean length of
  `y⁻¹ ξ` at infinity.
* `New.Core.minkowski_second_theorem`: the second theorem. The lattice contains a basis of `E ^ n`
  for which `|det y|` times the product of the `2 f`-th powers of the lengths is bounded in terms of
  `f`, `n` and the discriminant. The proof embeds `frameLattice y` as a `ℤ`-lattice in
  `n → InfinitePlace E → ℂ`, bounds its covolume by unfolding over `𝔸 ^ n / E ^ n`, and extracts an
  `E`-basis from Tau Ceti's real successive minima.
* `New.exists_basis_frameLength_le_two_zpow`: a bound of the same kind, with a larger constant, for
  the lengths rounded up to powers `2 ^ x j`.
* `New.Core.encard_le_of_dyadic_box`: at most `C * 4 ^ (f * ∑ i, (x i)⁺)` rational vectors `ξ` have
  the vector of the `twoAtInfinity E ^ (-x i) * ξ i` in a given compact set.
* `New.Core.exists_eq_zero_of_zpow_mul_mem`: for a compact set `B` of adeles and all large `m`, no
  nonzero `a` in `E` has `twoAtInfinity E ^ m * a` in `B`.

Notions from other files:
* `New.ratVectors`: the image of `E ^ n` in `𝔸 E ^ n` under the diagonal embedding, as an additive
  subgroup.

## Relation to the literature

Part of a known result: Reduction theory, here the adelic Minkowski theorems. For Mahler-Godement
compactness and finite covolume see `Lib.Adelic.Reduction.FiniteVolume`.
-/

@[expose] public section

noncomputable section

/-! ## Minkowski's first theorem with multiplicity -/

section MinkowskiFirst

open Set ENNReal Fintype Matrix MeasureTheory Metric NumberField Measure

namespace New

variable {E : Type*} [Field E] [CMType E] {n : Type*} [Fintype n] [DecidableEq n] (y : GL n (𝔸 E))

/-- Unfolding: the number of rational `ξ` with `y⁻¹ (ξ + x) ∈ S`, integrated over the quotient of
`𝔸 ^ n` by the subgroup `E ^ n = ratVectors E n`, is `|det y| * volume S`. The integral over the
quotient is taken against `quotMeasure`, the measure on `𝔸 ^ n` given by `volume` weighted by a
cutoff for this subgroup; its total mass is the covolume `1`. -/
lemma lintegral_encard_rat_points {S : Set (n → 𝔸 E)} (hS : MeasurableSet S) :
    ENNReal.ofReal (ideleAbs y.det) * volume S =
      ∫⁻ x : n → 𝔸 E, {ξ : n → E |
        y⁻¹.val *ᵥ (toAdele ∘ ξ + x) ∈ S}.encard ∂(ratVectors E n).quotMeasure := by
  -- Unfolding: `(x, ξ) ↦ y⁻¹ (ξ + x)` carries `quotMeasure ⊗ count` to `|det y| • volume`. The
  -- measure of the preimage of `S` is the left side, and by Fubini it is also the right side.
  have h_scale : MeasurePreserving (y⁻¹.1 *ᵥ ·) volume (ENNReal.ofReal (ideleAbs y.det) • volume) :=
    ⟨by fun_prop, (volume_map_mulVec_adele y⁻¹).trans (by simp)⟩
  have h_unfold : MeasurePreserving (fun p : (n → 𝔸 E) × ratVectors E n ↦ y⁻¹.val *ᵥ (p.2 +ᵥ p.1))
      ((ratVectors E n).quotMeasure.prod count) (ENNReal.ofReal (ideleAbs y.det) • volume) :=
    h_scale.comp measurePreserving_addOrbitMeasure
  rw [← smul_eq_mul, ← smul_apply, ← h_unfold.measure_preimage hS.nullMeasurableSet,
    Measure.prod_apply (h_unfold.measurable hS)]
  refine lintegral_congr fun x ↦ ?_
  -- the fibre over `x` is counted in `ratVectors E n`, the image of `n → E` under `toAdele ∘ ·`
  rw [count_apply .of_discrete]
  let e : (n → E) ≃ ratVectors E n := .ofInjective _ (toAdele (E := E)).injective.comp_left
  exact_mod_cast encard_congr e.subtypeEquivOfSubtype.symm

omit [DecidableEq n] in
/-- The box of radius `r`, the adelic vectors with all entries of absolute value below `r` at the
`f = numInfPlaces E` infinite places and integral at the finite places, has volume
`((r ^ 2 * π * (2 / rd)) ^ f) ^ card n`, where `rd = rootDiscr E` is the root discriminant. -/
lemma volume_pi_ball_prod_integral {r : ℝ} (hr : 0 < r) :
    volume (univ.pi fun _ : n ↦ (ball 0 r ×ˢ Ô E : Set (𝔸 E))) = ENNReal.ofReal
      (((r ^ 2 * Real.pi * (2 / rootDiscr E)) ^ Core.numInfPlaces E) ^ card n) := by
  have h_inf : volume (ball (0 : InfinitePlace E → ℂ) r) =
      ENNReal.ofReal (r ^ 2 * Real.pi) ^ Core.numInfPlaces E := by
    simp [volume_pi, ball_pi _ hr, ofReal_mul (sq_nonneg r), ofReal_pow hr.le, ← NNReal.coe_real_pi]
  have h_entry : volume (ball 0 r ×ˢ Ô E : Set (𝔸 E)) =
      ENNReal.ofReal ((r ^ 2 * Real.pi * (2 / rootDiscr E)) ^ Core.numInfPlaces E) := by
    rw [volume_eq_prod, prod_prod, h_inf, volume_Ô, mul_pow (r ^ 2 * Real.pi), ← inv_div, inv_pow,
      ← volÔ_eq, ← ofReal_pow (by positivity), ofReal_mul (by positivity), ofReal_coe_nnreal]
  rw [volume_pi, pi_pi, h_entry, Finset.prod_const, Finset.card_univ,
    ← ofReal_pow (by positivity [rootDiscr_pos E])]

open Pointwise in
/-- Minkowski's first theorem with multiplicity: for `y` in `GL n (𝔸 E)`, the adelic absolute value
`|det y|` is at most `(2 rd) ^ (f n)` times the number of `ξ` in `E ^ n` with `y⁻¹ ξ` integral at
the finite places and all its entries of absolute value below `1` at the infinite places. Here
`rd = rootDiscr E` is the root discriminant, `f` the number of infinite places and `n` stands for
`card n`. -/
lemma minkowski_first :
    ENNReal.ofReal (ideleAbs y.det) ≤
      ENNReal.ofReal (((2 * rootDiscr E) ^ Core.numInfPlaces E) ^ card n) *
        {ξ : n → E | ∀ i : n, (y⁻¹.val *ᵥ toAdele ∘ ξ) i ∈ ball 0 1 ×ˢ Ô E}.encard := by
  -- Blichfeldt's argument for the box `S` of radius `1 / 2`: two rational points of a translate of
  -- `y S` differ by a point of `y` times the box of radius `1`.
  let box : Set (𝔸 E) := ball 0 2⁻¹ ×ˢ Ô E
  let S : Set (n → 𝔸 E) := univ.pi fun _ ↦ box
  set N : ℕ∞ := {ξ : n → E | ∀ i : n, (y⁻¹.val *ᵥ toAdele ∘ ξ) i ∈ ball 0 1 ×ˢ Ô E}.encard
  have h_count (x : n → 𝔸 E) : {ξ : n → E | y⁻¹.val *ᵥ (toAdele ∘ ξ + x) ∈ S}.encard ≤ N := by
    obtain h_empty | ⟨ξ₀, hξ₀⟩ := {ξ | y⁻¹.val *ᵥ (toAdele ∘ ξ + x) ∈ S}.eq_empty_or_nonempty
    · simp only [h_empty, encard_empty, zero_le]
    refine encard_le_encard_of_injOn (f := (· - ξ₀)) (fun ξ hξ i ↦ ?_) sub_left_injective.injOn
    simpa [box, mulVec_add, mulVec_sub, ← two_mul] using
      sub_mem_sub (hξ i (mem_univ i)) (hξ₀ i (mem_univ i))
  -- Averaging the count over the translates gives `|det y| vol S`.
  have h_mean : .ofReal (ideleAbs y.det) * volume S ≤ (N : ℝ≥0∞) := by
    rw [lintegral_encard_rat_points y (.univ_pi fun _ ↦ (isOpen_ball.prod isOpen_Ô).measurableSet)]
    exact lintegral_le_const (.of_forall fun x ↦ mod_cast h_count x)
  -- It remains to see `1 ≤ ((2 rd) ^ f) ^ n * vol S`, and the right side is `π ^ (f n)`.
  set c : ℝ := ((2 * rootDiscr E) ^ Core.numInfPlaces E) ^ card n with hc
  have h_base : 2 * rootDiscr E * (2⁻¹ ^ 2 * Real.pi * (2 / rootDiscr E)) = Real.pi := by
    field [(rootDiscr_pos E).ne']
  have h_vol : 1 ≤ ENNReal.ofReal c * volume S := by
    rw [volume_pi_ball_prod_integral (by positivity),
      ← ofReal_mul (by positivity [rootDiscr_pos E]), hc, ← mul_pow, ← mul_pow, h_base,
      one_le_ofReal]
    exact one_le_pow₀ (one_le_pow₀ (by linarith [Real.two_le_pi]))
  calc _ ≤ ENNReal.ofReal c * volume S * ENNReal.ofReal (ideleAbs y.det) :=
        le_mul_of_one_le_left' h_vol
    _ ≤ ENNReal.ofReal c * N := by grw [mul_assoc, mul_comm (volume S), h_mean]

/-- Minkowski's first theorem: if `|det y| > (2 * rootDiscr E) ^ (f * n)`, with `f` the number of
infinite places, some nonzero rational `ξ` has `y⁻¹ ξ` integral at the finite places and all
its entries of absolute value `< 1` at the infinite places. -/
lemma exists_ne_zero_inv_mulVec_mem
    (h_det : ((2 * rootDiscr E) ^ Core.numInfPlaces E) ^ card n < ideleAbs y.det) :
    ∃ ξ : n → E, (∀ i : n, (y⁻¹.val *ᵥ toAdele ∘ ξ) i ∈ ball 0 1 ×ˢ Ô E) ∧ ξ ≠ 0 := by
  -- more than one rational `ξ` has `y⁻¹ ξ` in the box, so one of them is not zero
  have h_count : 1 < {ξ : n → E | ∀ i : n, (y⁻¹.val *ᵥ toAdele ∘ ξ) i ∈ ball 0 1 ×ˢ Ô E}.encard :=
    mod_cast one_lt_of_lt_mul_right (α := ℝ≥0∞)
      (((ofReal_lt_ofReal_iff ideleAbs_pos).2 h_det).trans_le (minkowski_first y))
  exact exists_ne_of_one_lt_encard h_count 0

end New

end MinkowskiFirst

/-! ## Minkowski's second theorem and counts of rational points in boxes -/

section MinkowskiSecond

open NumberField Finset Fintype Prod Complex Int Matrix Real Function Metric

namespace New.Core

variable (E : Type _) [Field E] [CMType E] {n : Type _} [Fintype n] [DecidableEq n]

/-! ### Isometries, determinants and powers of two at infinity -/

/-- The idele of `E` that is `2` at all infinite places and `1` at the finite places. -/
def twoAtInfinity (E : Type _) [Field E] [NumberField E] : (𝔸 E)ˣ :=
  Units.map ⟨⟨fun z : ℂ ↦ (fun _ ↦ z, 1), rfl⟩, by aesop⟩ (Units.mk0 2 (by simp))

variable {E}

/-- A matrix `Q` with orthonormal columns, that is `Qᴴ * Q = 1`, preserves the sum of the squared
absolute values of the entries of a vector. -/
lemma sum_norm_sq_mulVec_of_isometry {m : Type*} [Fintype m] {Q : Matrix m n ℂ} (hQ : Qᴴ * Q = 1)
    (v : n → ℂ) : ∑ i : m, ‖(Q *ᵥ v) i‖ ^ 2 = ∑ i : n, ‖v i‖ ^ 2 := by
  have h_inner : star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = star v ⬝ᵥ v := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hQ, one_mulVec]
  simpa [dotProduct, ← ofReal_inj, ← conj_mul'] using h_inner

/-- The adelic absolute value of the determinant of the adelic matrix with components `a w` at the
infinite places `w` and finite part `b` (`mkAdelicGL`) is the product of the `‖det (a w)‖ ^ 2` and
of the absolute value `finIdeleAbs` of the finite idele `det b`. -/
lemma ideleAbs_det_mkAdelicGL (a : InfinitePlace E → GL n ℂ) (b : GL n (𝔸f E)) :
    ideleAbs (mkAdelicGL (a, b)).det =
      (∏ w : InfinitePlace E, ‖(a w).val.det‖ ^ 2) * finIdeleAbs b.det := by
  simp [finIdeleAbs, ideleAbs, det_apply, fst_sum, fst_prod, snd_sum, snd_prod]

/-- For an integer vector `x`, the diagonal adelic matrix whose `i`-th entry is `2 ^ x i` at the
infinite places and `1` at the finite places. -/
def dyadicDiag {E : Type _} [Field E] [NumberField E]
    (x : n → ℤ) : GL n (𝔸 E) := diagGL fun i : n ↦ twoAtInfinity E ^ x i

/-- The set of `Y` in `GL n E` with `y⁻¹ Y D⁻¹` in `M`, where `D = dyadicDiag x` is diagonal with
entries `2 ^ x i` at infinity and `1` at the finite places. -/
def profileBases (M : Set (GL n (𝔸 E))) (x : n → ℤ) (y : GL n (𝔸 E)) : Set (GL n E) :=
  {Y : GL n E | y⁻¹ * Y.map toAdele * (dyadicDiag x)⁻¹ ∈ M}

/-- The adeles with components of absolute value at most `r` (by default `1`) at the infinite places
and integral at the finite places form a compact set. -/
lemma isCompact_closedBall_prod_integral (r : ℝ := 1) :
    IsCompact (closedBall 0 r ×ˢ Ô E : Set (𝔸 E)) :=
  (isCompact_closedBall 0 r).prod isCompact_Ô

/-- The matrix `dyadicDiag x`, with diagonal entries `2 ^ x i` at the infinite places and `1` at
the finite ones, has determinant of adelic absolute value `(2 ^ (2 f)) ^ ∑ i, x i`, with `f` the
number of infinite places. -/
lemma ideleAbs_det_dyadicDiag (x : n → ℤ) :
    ideleAbs (dyadicDiag x : GL n (𝔸 E)).det = (2 ^ (2 * numInfPlaces E)) ^ ∑ i : n, x i := by
  have h_two : ideleAbs (twoAtInfinity E) = 2 ^ (2 * numInfPlaces E) := by
    simp [ideleAbs, twoAtInfinity, pow_mul]
  have h_det : (dyadicDiag x : GL n (𝔸 E)).det = ∏ i : n, twoAtInfinity E ^ x i :=
    Units.ext (by simp [dyadicDiag, diagGL])
  simp [h_det, h_two, DiscreteSeries.zpow_sum_of_ne_zero]

/-- The matrix `dyadicDiag x` for natural exponents `x i` has determinant of adelic absolute value
`((2 ^ f) ^ ∑ i, x i) ^ 2`, with `f` the number of infinite places. -/
lemma ideleAbs_det_dyadicDiag_natCast (x : n → ℕ) :
    ideleAbs (dyadicDiag fun i : n ↦ (x i : ℤ) : GL n (𝔸 E)).det =
      ((2 ^ numInfPlaces E) ^ ∑ i : n, x i) ^ 2 := by
  rw [ideleAbs_det_dyadicDiag, ← Nat.cast_sum, zpow_natCast]
  ring

/-- For natural exponents `x i`, all entries of the inverse of `dyadicDiag x` (the diagonal matrix
with entries `2 ^ x i` at the infinite places and `1` at the finite ones) have absolute value at
most `1` at the infinite places and lie in the ring `Ô E` of integral finite adeles. -/
lemma dyadicDiag_inv_mem (x : n → ℕ) :
    (dyadicDiag fun i : n ↦ (x i : ℤ) : GL n (𝔸 E))⁻¹.val ∈
      Set.matrix (closedBall (0 : InfinitePlace E → ℂ) 1 ×ˢ Ô E) := by
  simpa [dyadicDiag, diagonal_mem_matrix_iff, Pi.pow_def, twoAtInfinity, ← map_inv] using
    fun i ↦ inv_le_one_of_one_le₀ (one_le_pow₀ (n := x i) (one_le_two (α := ℝ)))

/-- The inverse of `dyadicDiag x` multiplies the `i`-th entry of an adelic vector by
`twoAtInfinity E ^ (-x i)`. -/
lemma dyadicDiag_inv_mulVec_apply (x : n → ℤ) (v : n → 𝔸 E) (i : n) :
    ((dyadicDiag x)⁻¹.val *ᵥ v) i = (twoAtInfinity E ^ (-x i)).val * v i := by
  simp [dyadicDiag, diagGL, mulVec_diagonal, ← map_inv, -map_zpow]

/-- An invertible matrix with entries in `E` has, over the adeles, a determinant of absolute value
`1`: this is the product formula for `det Y`. -/
@[simp↓]
lemma ideleAbs_det_map_toAdele (Y : GL n E) : ideleAbs (Y.map toAdele).det = 1 := by
  rw [Y.map_det toAdele, ideleAbs_toAdele]

/-! ### Successive minima -/

/-- A real function `len` attains its minimum on a nonempty set `S` that has only finitely many
points below each bound. -/
lemma exists_min_of_finite_le {V : Type*} {S : Set V} (len : V → ℝ)
    (h_finite : ∀ r : ℝ, {v ∈ S | len v ≤ r}.Finite) (hS : S.Nonempty) :
    ∃ v ∈ S, ∀ u ∈ S, len v ≤ len u := by
  obtain ⟨v₀, hv₀⟩ := hS
  obtain ⟨v, hv, hv_least⟩ :=
    Set.exists_min_image {u ∈ S | len u ≤ len v₀} len (h_finite _) ⟨v₀, hv₀, le_rfl⟩
  exact ⟨v, hv.1, by grind⟩

/-- The lattice `E ^ n ∩ z_f Ô ^ n` of an adelic frame `z`: the rational vectors `ξ` such that
`z⁻¹ ξ` is integral at the finite places. -/
def frameLattice (z : GL n (𝔸 E)) : Set (n → E) :=
  {ξ : n → E | ∀ i : n, ((z⁻¹.val *ᵥ toAdele ∘ ξ) i).2 ∈ Ô E}

/-- The length of a rational vector `ξ` at an adelic frame `z`: the Euclidean norm of the
coordinates of `z⁻¹ ξ` at all infinite places together. -/
def frameLength (z : GL n (𝔸 E)) (ξ : n → E) : ℝ :=
  ‖WithLp.toLp 2 fun p : InfinitePlace E × n ↦ ((z⁻¹.val *ᵥ toAdele ∘ ξ) p.2).1 p.1‖

/-- Each coordinate of `z⁻¹ ξ` at an infinite place `w` has absolute value at most the length
`frameLength z ξ`, the Euclidean norm of all these coordinates together. -/
lemma norm_apply_le_frameLength (z : GL n (𝔸 E)) (ξ : n → E) (w : InfinitePlace E) (i : n) :
    ‖((z⁻¹.val *ᵥ toAdele ∘ ξ) i).1 w‖ ≤ frameLength z ξ :=
  PiLp.norm_apply_le
    (WithLp.toLp 2 fun p : InfinitePlace E × n ↦ ((z⁻¹.val *ᵥ toAdele ∘ ξ) p.2).1 p.1) (w, i)

/-- A nonzero rational vector `ξ` has positive length `frameLength z ξ`, the Euclidean norm of
`z⁻¹ ξ` at all infinite places together. -/
lemma frameLength_pos (z : GL n (𝔸 E)) {ξ : n → E} (hξ : ξ ≠ 0) : 0 < frameLength z ξ := by
  -- If the length vanishes, so does `ξ = z (z⁻¹ ξ)` at the infinite places.
  refine lt_of_not_ge fun h_le ↦ hξ (funext fun i ↦ ?_)
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have h_coord (j : n) : ((z⁻¹.val *ᵥ toAdele ∘ ξ) j).1 w = 0 :=
    norm_le_zero_iff.1 ((norm_apply_le_frameLength z ξ w j).trans h_le)
  have h_frame : ((z.val *ᵥ z⁻¹.val *ᵥ toAdele ∘ ξ) i).1 w = 0 := by
    rw [mulVec, dotProduct, fst_sum, Finset.sum_apply]
    exact Finset.sum_eq_zero fun j _ ↦ by simp [-coe_units_inv, h_coord j]
  simpa using h_frame

/-- The archimedean space `(E ⊗_ℚ ℝ) ^ n ≅ n → InfinitePlace E → ℂ`. -/
private abbrev ArchSpace (E n : Type*) [Field E] [CMType E] := n → InfinitePlace E → ℂ

/-- Action of the infinite component of `z⁻¹` on `ArchSpace E n`. -/
private def archEquiv (z : GL n (𝔸 E)) : ArchSpace E n ≃ₗ[InfinitePlace E → ℂ] ArchSpace E n :=
  (GeneralLinearGroup.toLin (z.map (RingHom.fst _ (𝔸f E)))⁻¹).toLinearEquiv

/-- Archimedean coordinates `ξ ↦ (z⁻¹ ξ)_∞`, viewed as a `ℚ`-linear map into `ℂ ^ (f × n)`. -/
private def archMap (z : GL n (𝔸 E)) : (n → E) →ₗ[ℚ] ArchSpace E n :=
  (archEquiv z).toLinearMap.restrictScalars ℚ ∘ₗ
    (RingHom.pi Φ).toAddMonoidHom.toRatLinearMap.compLeft n

private lemma archMap_apply (z : GL n (𝔸 E)) (ξ : n → E) (i : n) :
    archMap z ξ i = ((z⁻¹.val *ᵥ toAdele ∘ ξ) i).1 :=
  funext fun w ↦ by
    simp [archMap, archEquiv, GeneralLinearGroup.toLin, mulVec, dotProduct, fst_sum, ← map_inv,
      -Units.val_inv_eq_inv_val]

private lemma archMap_injective (z : GL n (𝔸 E)) : Injective (archMap z) :=
  (archEquiv z).injective.comp fun _ _ h ↦ funext fun i ↦ (RingHom.pi Φ).injective (congrFun h i)

/-- The additive map `ξ ↦ z⁻¹ ξ` from `n → E` to `n → 𝔸 E`. -/
private def frameMap (z : GL n (𝔸 E)) : (n → E) →+ (n → 𝔸 E) :=
  z⁻¹.val.mulVecLin.toAddMonoidHom.comp (toAdele.toAddMonoidHom.compLeft n)

/-- The lattice `frameLattice z` viewed as a `ℤ`-submodule of `n → E`. -/
private def frameLatticeSubmodule (z : GL n (𝔸 E)) : Submodule ℤ (n → E) :=
  ((AddSubgroup.pi Set.univ fun _ : n ↦
    (Ô E).toAddSubgroup.comap (AddMonoidHom.snd _ _)).comap (frameMap z)).toIntSubmodule

/-- The archimedean image of `frameLattice z` as a `ℤ`-submodule of `ArchSpace E n`. -/
private abbrev archLattice (z : GL n (𝔸 E)) : Submodule ℤ (ArchSpace E n) :=
  (frameLatticeSubmodule z).map ((archMap z).restrictScalars ℤ)

private instance (z : GL n (𝔸 E)) : DiscreteTopology (archLattice z) := by
  refine continuous_subtypeVal.discrete_of_tendsto_cofinite_cocompact
    (tendsto_cofinite_cocompact_iff.mpr fun C hC ↦ ?_)
  let K : Set (n → 𝔸 E) :=
    (fun p : ArchSpace E n × (n → 𝔸f E) ↦ z.val *ᵥ fun i ↦ (p.1 i, p.2 i)) ''
      (C ×ˢ Set.univ.pi fun _ : n ↦ (Ô E : Set (𝔸f E)))
  have hK : IsCompact K := (hC.prod (isCompact_univ_pi fun _ ↦ isCompact_Ô)).image (by fun_prop)
  have h_fin : (Subtype.val ⁻¹' (archMap z '' {ξ : n → E | toAdele ∘ ξ ∈ K}) :
      Set (archLattice z)).Finite :=
    ((isCovolOneLattice_ratVectors.finite_preimage hK).image (archMap z)).preimage
      Subtype.val_injective.injOn
  refine h_fin.subset ?_
  rintro ⟨_, ξ, hξ, rfl⟩ hCξ
  exact ⟨ξ, ⟨(archMap z ξ, fun i ↦ (frameMap z ξ i).2), ⟨hCξ, fun i _ ↦ hξ i trivial⟩,
    by simp [frameMap, AddMonoidHom.compLeft, archMap_apply]⟩, rfl⟩

private instance (z : GL n (𝔸 E)) : IsZLattice ℝ (archLattice z) := by
  have h_dense : DenseRange (archMap z) :=
    (archEquiv z).surjective.denseRange.comp (.piMap fun _ ↦ denseRange_Φ)
      ((archEquiv z).toLinearMap.restrictScalars ℝ).continuous_of_finiteDimensional
  refine ⟨Submodule.eq_top_iff'.mpr (isClosed_property h_dense
    (Submodule.isClosed_of_finiteDimensional _) fun ξ ↦ ?_)⟩
  obtain ⟨N, hN, h_int⟩ := exists_forall_mul_mem_Ô fun i : n ↦ (frameMap z ξ i).2
  have h_lat : N • ξ ∈ frameLatticeSubmodule z := fun i _ ↦ by
    change (frameMap z (N • ξ) i).2 ∈ Ô E
    rw [map_nsmul]
    simpa [← Nat.cast_smul_eq_nsmul (𝔸f E)] using h_int i
  have h_mem : (N : ℝ) • archMap z ξ ∈ archLattice z :=
    ⟨N • ξ, h_lat, by rw [LinearMap.restrictScalars_apply, map_nsmul, Nat.cast_smul_eq_nsmul]⟩
  exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 hN)).1 (Submodule.subset_span h_mem)

open MeasureTheory MeasurableEquiv in
/-- The covolume of `archLattice z` satisfies `|det z| * covolume (archLattice z) ≤
(rd / 2) ^ (f n)`, obtained by unfolding `F × Ô ^ n` over `𝔸 ^ n / E ^ n` for a fundamental domain
`F` of `archLattice z`. -/
private lemma ideleAbs_det_mul_covolume_le (z : GL n (𝔸 E)) :
    ideleAbs z.det * ZLattice.covolume (archLattice z) ≤
      ((rootDiscr E / 2) ^ numInfPlaces E) ^ card n := by
  -- A fundamental domain `F` of `archLattice z` times `Ô ^ n` contains `z⁻¹ (ξ + x)` for at most
  -- one rational `ξ`, so `lintegral_encard_rat_points` bounds `|det z| * covolume * volÔ ^ n ≤ 1`.
  let b := Module.finBasis ℤ (archLattice z)
  let β := b.ofZLatticeBasis ℝ (archLattice z)
  let F : Set (ArchSpace E n) := ZSpan.fundamentalDomain β
  let S : Set (n → 𝔸 E) :=
    arrowProdEquivProdArrow _ _ n ⁻¹' (F ×ˢ Set.univ.pi fun _ : n ↦ (Ô E : Set (𝔸f E)))
  have hS : MeasurableSet S := (arrowProdEquivProdArrow ..).measurable
    ((ZSpan.fundamentalDomain_measurableSet _).prod (.univ_pi fun _ ↦ isOpen_Ô.measurableSet))
  have h_sub (x : n → 𝔸 E) : {ξ : n → E | z⁻¹.val *ᵥ (toAdele ∘ ξ + x) ∈ S}.Subsingleton := by
    intro ξ₁ h₁ ξ₂ h₂
    let y (ξ : n → E) : n → 𝔸 E := z⁻¹.val *ᵥ (toAdele ∘ ξ + x)
    have h_diff : y ξ₁ - y ξ₂ = frameMap z (ξ₁ - ξ₂) := by
      simp [y, frameMap, map_sub, AddMonoidHom.compLeft, mulVec_add]
    have h_fin : ξ₁ - ξ₂ ∈ frameLatticeSubmodule z := fun i _ ↦ by
      change (frameMap z (ξ₁ - ξ₂) i).2 ∈ Ô E
      rw [← h_diff]
      exact (Ô E).sub_mem (h₁.2 i trivial) (h₂.2 i trivial)
    have h_lat : archMap z (ξ₁ - ξ₂) ∈ Submodule.span ℤ (Set.range β) := by
      rw [b.ofZLatticeBasis_span ℝ]
      exact ⟨ξ₁ - ξ₂, h_fin, rfl⟩
    have h_mem₁ : (fun i ↦ (y ξ₁ i).1) - 0 ∈ F := by
      rw [sub_zero]
      exact h₁.1
    have h_mem₂ : (fun i ↦ (y ξ₁ i).1) - archMap z (ξ₁ - ξ₂) ∈ F := by
      have h_eq : (fun i ↦ (y ξ₁ i).1) - archMap z (ξ₁ - ξ₂) = fun i ↦ (y ξ₂ i).1 := by
        funext i
        rw [Pi.sub_apply, archMap_apply]
        change (y ξ₁ i).1 - (frameMap z (ξ₁ - ξ₂) i).1 = (y ξ₂ i).1
        rw [← h_diff]
        simp
      rw [h_eq]
      exact h₂.1
    have h_zero : 0 = archMap z (ξ₁ - ξ₂) :=
      ZSpan.eq_of_sub_mem_fundamentalDomain β (zero_mem _) h_lat h_mem₁ h_mem₂
    exact sub_eq_zero.1 ((map_eq_zero_iff (archMap z) (archMap_injective z)).1 h_zero.symm)
  have h_vol : (ENNReal.ofReal (ideleAbs z.det) * volume S).toReal ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top <|
      (lintegral_encard_rat_points z hS).trans_le <| lintegral_le_const <|
        .of_forall fun x ↦ mod_cast Set.encard_le_one_iff_subsingleton.2 (h_sub x)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ideleAbs_pos.le,
    (volume_measurePreserving_arrowProdEquivProdArrow ..).measure_preimage_equiv] at h_vol
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume (ZLattice.isAddFundamentalDomain b _)]
  simp [F, β, volume_pi_pi, Measure.volume_eq_prod, volÔ_eq, inv_pow, ← mul_assoc] at h_vol
  simpa [Measure.real] using (mul_inv_le_iff₀ (by positivity [rootDiscr_pos E])).1 h_vol

open MeasureTheory in
/-- Minkowski's second theorem over `E`. For `z` in `GL n (𝔸 E)` the lattice `frameLattice z`, of
the rational `ξ` with `z⁻¹ ξ` integral at the finite places, contains a basis `y 0, …, y (n - 1)`
of `E ^ n`, ordered by length, with `|det z| * ∏ j, ‖y j‖ ^ (2 f) ≤ (2 f n rd) ^ (f n)`. Here
`‖ξ‖ = frameLength z ξ` is the Euclidean norm of `z⁻¹ ξ` at all infinite places together, `f` is
the number of infinite places, `n` stands for `card n`, `rd` is the root discriminant and
`|det z|` the adelic absolute value. Only the upper bound of the theorem is proved. -/
theorem minkowski_second_theorem (z : GL n (𝔸 E)) :
    ∃ y : Fin (Fintype.card n) → n → E,
      LinearIndependent E y ∧
      (∀ j : Fin (Fintype.card n), y j ∈ frameLattice z) ∧
      (Monotone fun j : Fin (Fintype.card n) ↦ frameLength z (y j)) ∧
      ideleAbs z.det * ∏ j : Fin (Fintype.card n), frameLength z (y j) ^ (2 * numInfPlaces E) ≤
        (2 * (numInfPlaces E * Fintype.card n) * rootDiscr E) ^
          (numInfPlaces E * Fintype.card n) := by
  -- Take a real basis of `archLattice z` attaining the successive minima of the sup-norm unit ball.
  let K : ConvexBody (ArchSpace E n) := .closedUnitBall _
  have hK0 : (0 : ArchSpace E n) ∈ interior (K : Set (ArchSpace E n)) :=
    ConvexBody.zero_mem_interior_of_coe_eq_closedBall ConvexBody.coe_closedUnitBall
  have h_dim : Module.finrank ℝ (ArchSpace E n) = Module.finrank ℚ E * card n := by
    simp [ArchSpace, Module.finrank_pi_fintype, Complex.finrank_real_complex,
      finrank_eq_two_mul_card_infinitePlace, numInfPlaces, mul_comm]
  let e_dim := Fin.castOrderIso h_dim.symm
  obtain ⟨w, hwL, -, hwK, -⟩ := ZLattice.exists_basis_gauge_eq_successiveMin (archLattice z) hK0
  choose u hu_mem hu_eq using fun r ↦ Submodule.mem_map.1 (hwL (e_dim r))
  simp only [LinearMap.restrictScalars_apply] at hu_eq
  -- Extract `card n` vectors independent over `E` with sup-norm product controlled by the minima.
  have h_indep : LinearIndependent ℝ (archMap z ∘ u) := by
    simpa [Function.comp_def, hu_eq] using w.linearIndependent.comp e_dim e_dim.injective
  have h_norm (r : Fin (Module.finrank ℚ E * card n)) :
      ‖archMap z (u r)‖ ≤ ZLattice.successiveMin (archLattice z) K (e_dim r) := by
    rw [hu_eq r]
    exact (ConvexBody.mem_smul_iff_norm_le_of_coe_eq_closedBall ConvexBody.coe_closedUnitBall
      (ZLattice.successiveMin_nonneg _ _ _)).1 (hwK (e_dim r))
  obtain ⟨s, hs_indep, -, hs_prod⟩ :=
    TauCeti.exists_linearIndependent_comp_finrank_mul_prod_pow_le (F := ℚ) (K := E) (E := ℝ)
      (f := archMap z) (u := u) h_indep (fun _ ↦ norm_nonneg _) h_norm
      ((ZLattice.monotone_successiveMin (archLattice z) hK0).comp e_dim.monotone)
  let σ := Tuple.sort fun j ↦ frameLength z (u (s j))
  refine ⟨u ∘ s ∘ σ, hs_indep.comp σ σ.injective, fun j i ↦ hu_mem (s (σ j)) i trivial,
    Tuple.monotone_sort fun k ↦ frameLength z (u (s k)), ?_⟩
  -- Compare `frameLength` with the sup norm and apply Minkowski's 2nd theorem to `archLattice z`.
  set f := numInfPlaces E with hf
  have h_l2 (ξ : n → E) : frameLength z ξ ^ 2 ≤ (f * card n : ℝ) * ‖archMap z ξ‖ ^ 2 := by
    rw [frameLength, PiLp.norm_sq_eq_of_L2]
    exact (Finset.sum_le_sum fun p _ ↦ pow_le_pow_left₀ (norm_nonneg _)
      (by simpa [archMap_apply] using
        (norm_le_pi_norm _ p.1).trans (norm_le_pi_norm (archMap z ξ) p.2))
      2).trans_eq (by simp [f, mul_assoc])
  have h_volK : 1 ≤ volume.real (K : Set (ArchSpace E n)) := by
    simp [K, Measure.real, ArchSpace, volume_pi, closedBall_pi _ zero_le_one, NNReal.coe_real_pi]
    exact one_le_pow₀ (one_le_pow₀ (by linarith [Real.two_le_pi]))
  have h_two_pow : (2 : ℝ) ^ Module.finrank ℝ (ArchSpace E n) = 4 ^ (f * card n) := by
    rw [h_dim, finrank_eq_two_mul_card_infinitePlace, ← hf, mul_assoc 2, pow_mul]
    norm_num
  have h_symm : ∀ x ∈ K, -x ∈ K := fun x hx ↦ by
    simpa [← SetLike.mem_coe, K] using hx
  have h_min : ∏ i, ZLattice.successiveMin (archLattice z) K i ≤
      4 ^ (f * card n) * ZLattice.covolume (archLattice z) :=
    (le_mul_of_one_le_right (Finset.prod_nonneg fun i _ ↦ ZLattice.successiveMin_nonneg _ _ i)
      h_volK).trans ((ZLattice.prod_successiveMin_mul_measureReal_le_two_pow_mul_covolume
      (archLattice z) volume h_symm).trans_eq (by rw [h_two_pow]))
  dsimp only [Function.comp_apply]
  rw [Equiv.prod_comp σ fun j ↦ frameLength z (u (s j)) ^ (2 * f)]
  have h_det_nonneg : 0 ≤ ideleAbs z.det := ideleAbs_pos.le
  calc ideleAbs z.det * ∏ j, frameLength z (u (s j)) ^ (2 * f)
      ≤ ideleAbs z.det * ∏ j, ((f * card n : ℝ) * ‖archMap z (u (s j))‖ ^ 2) ^ f :=
        mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀
          (fun _ _ ↦ pow_nonneg (norm_nonneg _) _) fun j _ ↦ by
            rw [pow_mul]
            exact pow_le_pow_left₀ (sq_nonneg _) (h_l2 _) f) h_det_nonneg
    _ = (f * card n : ℝ) ^ (f * card n) *
          (ideleAbs z.det * (∏ j, ‖archMap z (u (s j))‖) ^ (2 * f)) := by
        simp [mul_pow, prod_mul_distrib, ← pow_mul, mul_comm f, prod_pow]
        ring
    _ ≤ (f * card n : ℝ) ^ (f * card n) *
          (4 ^ (f * card n) * (ideleAbs z.det * ZLattice.covolume (archLattice z))) := by
        rw [hf, ← finrank_eq_two_mul_card_infinitePlace]
        grw [hs_prod]
        have h_reindex : (∏ l, ZLattice.successiveMin (archLattice z) K (e_dim l)) =
            ∏ i, ZLattice.successiveMin (archLattice z) K i := e_dim.toEquiv.prod_comp _
        rw [h_reindex]
        grw [h_min]
        exact le_of_eq (by ring)
    _ ≤ (2 * (f * card n) * rootDiscr E) ^ (f * card n) := by
        grw [ideleAbs_det_mul_covolume_le]
        rw [← hf, ← pow_mul, ← mul_pow, ← mul_pow]
        exact le_of_eq (by ring)

/-- Minkowski's second theorem with dyadic bounds. For `y` in `GL n (𝔸 E)` there are an invertible
matrix `Y` over `E` and integers `x j` such that each row `Y j` lies in `frameLattice y` (the
vectors `ξ ∈ Eⁿ` with `y⁻¹ ξ` integral at all finite places) and has `frameLength` at most
`2 ^ x j`, and `|det y| * (2 ^ (2 f)) ^ ∑ j, x j ≤ (8 f n rd) ^ (f n)`. Here `frameLength y ξ` is
the Euclidean norm of the coordinates of `y⁻¹ ξ` at all infinite places together, `f` is the number
of infinite places, `n` stands for `card n`, `rd` is the root discriminant and `|det y|` is the
adelic absolute value. -/
theorem _root_.New.exists_basis_frameLength_le_two_zpow (y : GL n (𝔸 E)) :
    ∃ (Y : Matrix n n E) (x : n → ℤ),
      Y.det ≠ 0 ∧
      (∀ j : n, Y j ∈ frameLattice y) ∧
      (∀ j : n, frameLength y (Y j) ≤ 2 ^ x j) ∧
      ideleAbs y.det * (2 ^ (2 * numInfPlaces E)) ^ ∑ j : n, x j ≤
        (8 * (numInfPlaces E * Fintype.card n) * rootDiscr E) ^
          (numInfPlaces E * Fintype.card n) := by
  -- Round the lengths of the basis of `minkowski_second_theorem` up to powers of `2`; this
  -- at most doubles each of them.
  obtain ⟨v, h_indep, h_mem, -, h_prod⟩ := minkowski_second_theorem y
  let e : n ≃ Fin (card n) := equivFin n
  let len (j : n) : ℝ := frameLength y (v (e j))
  have len_pos (j : n) : 0 < len j := frameLength_pos y (h_indep.ne_zero (e j))
  have pow_le (j : n) : (2 : ℝ) ^ clog 2 (len j) ≤ 2 * len j := by
    have h_lt : (2 : ℝ) ^ (clog 2 (len j) - 1) < len j :=
      mod_cast zpow_pred_clog_lt_self one_lt_two (len_pos j)
    rw [zpow_sub_one₀ two_ne_zero] at h_lt
    linarith
  have h_det : det (of fun j ↦ v (e j)) ≠ 0 := ((isUnit_iff_isUnit_det _).1
    (linearIndependent_row_iff_isUnit.1 (h_indep.comp e e.injective))).ne_zero
  refine ⟨of fun j ↦ v (e j), fun j ↦ clog 2 (len j), h_det, fun j ↦ h_mem (e j),
    fun j ↦ mod_cast self_le_zpow_clog one_lt_two (len j), ?_⟩
  set f : ℕ := numInfPlaces E
  calc ideleAbs y.det * (2 ^ (2 * f)) ^ ∑ j : n, clog 2 (len j)
      = ideleAbs y.det * ∏ j : n, ((2 : ℝ) ^ clog 2 (len j)) ^ (2 * f) := by
        rw [prod_pow, ← DiscreteSeries.zpow_sum_of_ne_zero two_ne_zero, ← zpow_natCast,
          ← zpow_natCast, zpow_comm]
    _ ≤ ideleAbs y.det * ∏ j : n, (2 * len j) ^ (2 * f) := by
        gcongr with j
        exacts [ideleAbs_pos.le, pow_le j]
    _ = 4 ^ (f * card n) * (ideleAbs y.det * ∏ j, frameLength y (v j) ^ (2 * f)) := by
        simp only [mul_pow, prod_mul_distrib, prod_const, card_univ, len, ← e.prod_comp]
        rw [pow_mul 2, ← pow_mul]
        ring
    _ ≤ 4 ^ (f * card n) * (2 * (f * card n) * rootDiscr E) ^ (f * card n) := by gcongr
    _ = (8 * (f * card n) * rootDiscr E) ^ (f * card n) := by rw [← mul_pow]; ring

open MeasureTheory ENNReal Set

/-! ### Counting rational points -/

/-- The sum over all tuples `x : n → α` of the product of the `f (x i)` is at most the product over
`n` of the sums of `f`. -/
lemma tsum_prod_le_prod_tsum {α : Type*} (f : α → ℝ≥0∞) :
    ∑' x : n → α, ∏ i : n, f (x i) ≤ ∏ _ : n, tsum f := by
  classical
  refine tsum_le_of_sum_le' bot_le fun s ↦ ?_
  -- a finite set of tuples lies in the product of its projections, over which the sum factors
  have h_sub : s ⊆ piFinset (fun i ↦ s.image (eval i)) := fun x hx ↦
    mem_piFinset.2 fun i ↦ mem_image_of_mem (eval i) hx
  grw [h_sub, ← prod_univ_sum, sum_le_tsum]

open Pointwise in
/-- Let `box` be the set of adelic vectors with entries of size at most `1` at infinity and
integral at the finite places, and let `t = twoAtInfinity E` be the idele that is `2` at infinity
and `1` at the finite places. If the vector of the `t ^ (-x i) * u i` lies in `B` and `v` lies in
`F`, then `u + v` multiplied by the inverse of the diagonal matrix of the `t ^ max (x i) 0` lies in
`box * B + box * F`. -/
lemma dyadicDiag_toNat_inv_mulVec_add_mem {B F : Set (n → 𝔸 E)} (x : n → ℤ) {u v : n → 𝔸 E}
    (hu : (fun i : n ↦ (twoAtInfinity E ^ (-x i)).val * u i) ∈ B) (hv : v ∈ F) :
    (dyadicDiag fun i : n ↦ ((x i).toNat : ℤ))⁻¹.val *ᵥ (u + v) ∈
      (univ.pi fun _ : n ↦ (closedBall 0 1 ×ˢ Ô E : Set (𝔸 E))) * B +
        (univ.pi fun _ : n ↦ (closedBall 0 1 ×ˢ Ô E : Set (𝔸 E))) * F := by
  -- nonpositive powers of `twoAtInfinity E` lie in the box, and `-x⁺ = (-x⁺ + x) - x`
  set box : Set (n → 𝔸 E) := univ.pi fun _ ↦ closedBall 0 1 ×ˢ Ô E
  have pow_mem (m : n → ℤ) (hm : m ≤ 0) : (fun i ↦ (twoAtInfinity E ^ m i).val) ∈ box := by
    simpa [box, field, twoAtInfinity, ← map_zpow, Pi.le_def] using hm
  have h_eq : (dyadicDiag fun i ↦ ((x i).toNat : ℤ))⁻¹.val *ᵥ (u + v) =
      (fun i ↦ (twoAtInfinity E ^ (-x⁺ + x) i).val) *
          (fun i ↦ (twoAtInfinity E ^ (-x i)).val * u i) +
        (fun i ↦ (twoAtInfinity E ^ (-x⁺) i).val) * v := by
    ext1 i
    simp only [dyadicDiag_inv_mulVec_apply, show ((x i).toNat : ℤ) = x⁺ i by simp [posPart],
      Pi.add_apply, Pi.mul_apply, Pi.neg_apply, ← mul_assoc, ← Units.val_mul, ← _root_.zpow_add,
      add_neg_cancel_right, mul_add]
  rw [h_eq]
  exact Set.add_mem_add (Set.mul_mem_mul (pow_mem _ (neg_add_nonpos_iff.2 (le_posPart x))) hu)
    (Set.mul_mem_mul (pow_mem _ (neg_nonpos.2 (posPart_nonneg x))) hv)

open Pointwise in
/-- Counting rational points in a box. For a compact set `B` of adelic vectors there is a finite `C`
with the following property. For every `x : n → ℤ`, let `f a` (`a ∈ S`) be a family of distinct
rational vectors such that the vector with entries `twoAtInfinity E ^ (-x i) * f a i` lies in `B`
for every `a`, where `twoAtInfinity E` is the idele that is `2` at infinity and `1` at the finite
places. Then the family has at most `C * ((2 ^ r) ^ ∑ i, max (x i) 0) ^ 2` members, with
`r = numInfPlaces E` the number of infinite places. -/
lemma encard_le_of_dyadic_box {α : Type*} {B : Set (n → 𝔸 E)} (hB : IsCompact B) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (x : n → ℤ) {S : Set α} (f : α → n → E),
        (h_inj : InjOn f S) →
        (h_mem : ∀ a ∈ S, (fun i : n ↦ (twoAtInfinity E ^ (-x i)).val * toAdele (f a i)) ∈ B) →
        S.encard ≤ C * ENNReal.ofReal (((2 ^ numInfPlaces E) ^ ∑ i : n, (x i).toNat) ^ 2) := by
  -- Let `F` be a compact set into which every `v` is moved by a rational vector. Translate the
  -- points `f a` so that all land in `D K`, with `K = box * B + box * F` and `D = dyadicDiag x⁺`,
  -- and count the rational points there on average (`lintegral_encard_rat_points`).
  obtain ⟨F, hF, h_move⟩ := IsCovolOneLattice.exists_compact_cover (ratVectors E n)
  let box : Set (n → 𝔸 E) := univ.pi fun _ ↦ closedBall 0 1 ×ˢ Ô E
  let K : Set (n → 𝔸 E) := box * B + box * F
  have hK : IsCompact K :=
    have h_box := isCompact_univ_pi fun _ ↦ isCompact_closedBall_prod_integral
    (h_box.mul hB).add (h_box.mul hF)
  refine ⟨volume K, hK.measure_ne_top, fun x S f h_inj h_mem ↦ ?_⟩
  let D : GL n (𝔸 E) := dyadicDiag fun i ↦ ((x i).toNat : ℤ)
  -- for each shift `v`, add to the points `f a` the rational vector `ξ` that moves `v` into `F`
  have h_count (v : n → 𝔸 E) :
      S.encard ≤ {η : n → E | D⁻¹.val *ᵥ (toAdele ∘ η + v) ∈ K}.encard := by
    obtain ⟨r, ⟨ξ, rfl⟩, hξ : toAdele ∘ ξ + v ∈ F⟩ := h_move v
    refine encard_le_encard_of_injOn (f := fun a ↦ f a + ξ) (fun a ha ↦ ?_)
      ((add_left_injective ξ).comp_injOn h_inj)
    have h_add : toAdele ∘ (f a + ξ) + v = toAdele ∘ f a + (toAdele ∘ ξ + v) := by
      simp [add_assoc]
    rw [mem_ofPred_eq, h_add]
    exact dyadicDiag_toNat_inv_mulVec_add_mem x (h_mem a ha) hξ
  -- the mean of these counts over `v` is `|det D| * volume K`
  rw [mul_comm (volume K), ← ideleAbs_det_dyadicDiag_natCast,
    lintegral_encard_rat_points D hK.measurableSet]
  exact (le_iInf fun v ↦ mod_cast h_count v).trans (iInf_le_lintegral _)

end New.Core

end MinkowskiSecond

/-! ## Rational elements scaled into a compact set of adeles -/

open Pointwise in
/-- For a compact set `B` of adeles there is an integer `c` such that, for every integer `e < c`, an
element `a` of `E` (embedded diagonally by `toAdele`) that lies in `B` after multiplication by
`2 ^ (-e)` at the infinite places, that is by `twoAtInfinity E ^ (-e)`, is zero. -/
lemma New.Core.exists_eq_zero_of_zpow_mul_mem {E : Type*} [Field E] [CMType E] {B : Set (𝔸 E)}
    (hB : IsCompact B) :
    ∃ c : ℤ, ∀ e : ℤ, e < c → ∀ {a : E},
      (twoAtInfinity E ^ (-e)).val * toAdele a ∈ B → a = 0 := by
  -- The set `F` of rational points of `box * B` is finite, so some `N : ℕ` is not a quotient of two
  -- of its elements. But for `e < -N` both `N * a` and `a` lie in `F`, which forces `a = 0`.
  let box : Set (𝔸 E) := Metric.closedBall 0 1 ×ˢ Ô E
  let F : Set E := {x | toAdele x ∈ box * B}
  have F_finite : F.Finite :=
    finite_setOf_toAdele_mem (isCompact_closedBall_prod_integral.mul hB)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : E) ∉ F / F :=
    ((F_finite.div F_finite).preimage_embedding Nat.castEmbedding).exists_notMem
  refine ⟨-N, fun e he a ha ↦ by_contra fun ha_ne ↦ ?_⟩
  have h_multiple (k : ℕ) (hk : k * (2 : ℝ) ^ e ≤ 1) : k * a ∈ F := by
    have h_box : k * (twoAtInfinity E ^ e).val ∈ box := by
      simpa [box, twoAtInfinity, ← map_zpow, Pi.mul_def] using hk
    -- `toAdele (k * a) = (k * 2 ^ e) * (2 ^ (-e) * a)`
    simpa [F, mul_assoc] using Set.mul_mem_mul h_box ha
  have h_scale : (N : ℝ) * 2 ^ e ≤ 2 ^ N * 2 ^ (-N : ℤ) := by
    gcongr
    exacts [mod_cast N.lt_two_pow_self.le, one_le_two]
  have h_one : (2 : ℝ) ^ e ≤ 1 := zpow_le_one_of_nonpos₀ one_le_two (by lia)
  have ha_mem : a ∈ F := by simpa using h_multiple 1 (by simpa using h_one)
  exact hN ⟨N * a, h_multiple N (by simpa using h_scale), a, ha_mem,
    mul_div_cancel_right₀ (N : E) ha_ne⟩

end
