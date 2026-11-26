module

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.SimpleRing.Principal
public import Lib.General.LinearAlgebra.MatricesNearIdentity
import Lib.DiscreteSeries.FlenstedJensen.CasimirEigenfunction
import Lib.DiscreteSeries.Holomorphic.HighestVectorExtension
import Lib.DiscreteSeries.Holomorphic.MaximalCompactMinors

/-!
# One minor near the identity

For a unitary matrix `k` and a diagonal projection `P`, the principal minor of `k` on the range of
`P` has squared modulus at most `exp (-‖[P, k]‖² / 2)` (`norm_principalMinor_sq_le_exp`).

For `g` in `USign ε` near `1` and `X = g - 1`, the coefficient `l.dsCoeff g` is
`l.flenstedJensen 1 y` for a matrix `y = (1 - u) g (1 - v)` with `u`, `v` strictly triangular, and
each principal minor of `kᴴ y k` on a set of lowest entries of `l` is
`exp (tr (P logOneAdd X) + ‖[P, X]‖² / 4 + r)` with an explicit bound for `r`
(`exists_principalMinor_eq_exp`). This rests on an exact formula for `det (1 + P X)` through
`logOneAdd` (`exists_det_compress_eq_exp_logOneAdd`). The norm of a matrix is the entrywise `ℓ²`
norm (`Norms.Frobenius`).
-/

@[expose] public section

noncomputable section

section SizeOfOneMinor

open Matrix Finset Norms.Frobenius Complex

namespace New.DiscreteSeries

variable {n : Type} [Fintype n] [DecidableEq n] {P k : Matrix n n ℂ} {p : n → Prop}
  [DecidablePred p]

/-! ### The size of one minor -/

/-- The square of `|det Y|` is at most `exp (tr (Yᴴ Y - 1))`; this trace is real. -/
lemma norm_det_sq_le_exp (Y : Matrix n n ℂ) :
    ‖Y.det‖ ^ 2 ≤ Real.exp (Yᴴ * Y - 1).trace.re := by
  -- Use `x ≤ exp (x - 1)` on the eigenvalues `x ≥ 0` of `Yᴴ Y`.
  have hY : (Yᴴ * Y).IsHermitian := isHermitian_conjTranspose_mul_self Y
  have nonneg : ∀ i, 0 ≤ hY.eigenvalues i := eigenvalues_conjTranspose_mul_self_nonneg Y
  have trace_eq : (Yᴴ * Y - 1).trace.re = ∑ i, (hY.eigenvalues i - 1) := by
    rw [trace_sub, hY.trace_eq_sum_eigenvalues]
    simp
  calc ‖Y.det‖ ^ 2 = ‖(Yᴴ * Y).det‖ := by
        rw [det_mul, det_conjTranspose, norm_mul, norm_star, sq]
    _ = ∏ i, hY.eigenvalues i := by
        simp [hY.det_eq_prod_eigenvalues, abs_of_nonneg (nonneg _)]
    _ ≤ ∏ i, Real.exp (hY.eigenvalues i - 1) :=
        prod_le_prod₀ (fun i _ ↦ nonneg i) fun i _ ↦ by
          linarith only [Real.add_one_le_exp (hY.eigenvalues i - 1)]
    _ = Real.exp (Yᴴ * Y - 1).trace.re := by rw [trace_eq, Real.exp_sum]

/-- The principal minor of `X` on the indices satisfying `p` is `det (1 + P (X - 1))`, where `P` is
the diagonal projection to these indices. -/
lemma principalMinor_eq_det_coordProj (X : Matrix n n ℂ) (p : n → Prop) [DecidablePred p] :
    principalMinor X p = (1 + coordProj p * (X - 1)).det := by
  rw [principalMinor_eq_det, coordProj, sub_eq_add_neg, ← mul_neg, neg_sub]

/-- For a unitary matrix `k` and an orthogonal projection `P`, the crossing block
`M = (1 - P) k P` satisfies `Mᴴ M = P - P kᴴ P k P`. -/
lemma conjTranspose_mul_self_one_sub_mul_mul (hP : IsStarProjection P) (hk : kᴴ * k = 1) :
    ((1 - P) * k * P)ᴴ * ((1 - P) * k * P) = P - P * kᴴ * P * k * P := by
  have hPP : P * P = P := hP.isIdempotentElem
  have hP_adj : Pᴴ = P := hP.isSelfAdjoint
  simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hP_adj]
  linear_combination (norm := noncomm_ring) P * kᴴ * hPP * k * P + P * hk * P + hPP

/-- For a unitary matrix `k` and an orthogonal projection `P`, the Frobenius norms of the
commutator and of the block `(1 - P) k P` satisfy `‖[P, k]‖² = 2 ‖(1 - P) k P‖²`. -/
lemma norm_lie_sq_of_unitary (hP : IsStarProjection P) (hk : kᴴ * k = 1) :
    ‖⁅P, k⁆‖ ^ 2 = 2 * ‖(1 - P) * k * P‖ ^ 2 := by
  have hk' : k * kᴴ = 1 := mul_eq_one_symm hk
  have hPP : P * P = P := hP.isIdempotentElem
  have hP_adj : Pᴴ = P := hP.isSelfAdjoint
  -- Both sides are `2 (tr P - tr (P kᴴ P k))`.
  have lie_eq : ⁅P, k⁆ᴴ * ⁅P, k⁆ = kᴴ * (P * k) - kᴴ * (P * k * P) - P * kᴴ * P * k + P := by
    rw [Ring.lie_def, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hP_adj]
    linear_combination (norm := noncomm_ring) kᴴ * hPP * k + P * hk * P + hPP
  have trace_conj : (kᴴ * (P * k)).trace = P.trace := by
    rw [trace_mul_comm, mul_assoc, hk', mul_one]
  have trace_left : (kᴴ * (P * k * P)).trace = (P * kᴴ * P * k).trace := by
    simp only [← mul_assoc, trace_mul_comm _ P]
  have trace_right : (P * kᴴ * P * k * P).trace = (P * kᴴ * P * k).trace := by
    simp only [trace_mul_comm _ P, ← mul_assoc, hPP]
  have block_eq : ((1 - P) * k * P)ᴴ * ((1 - P) * k * P) = P - P * kᴴ * P * k * P :=
    conjTranspose_mul_self_one_sub_mul_mul hP hk
  rw [← ofReal_inj, ofReal_mul, ← trace_star_mul_self_eq_norm_sq,
    ← trace_star_mul_self_eq_norm_sq, lie_eq, block_eq]
  simp only [trace_add, trace_sub, trace_conj, trace_left, trace_right, ofReal_ofNat]
  ring

/-- Size of one minor: let `k` be a unitary matrix, `S` the set of indices satisfying `p`, and
`P = coordProj p` the diagonal projection to `S`. Then the principal minor of `k` on `S` satisfies
`|det_S k|² ≤ exp (-‖[P, k]‖² / 2)`. -/
theorem norm_principalMinor_sq_le_exp (p : n → Prop) [DecidablePred p] (hk : kᴴ * k = 1) :
    ‖principalMinor k p‖ ^ 2 ≤ Real.exp (-(‖⁅coordProj p, k⁆‖ ^ 2 / 2)) := by
  -- With `M = (1 - P) k P` and `Y = (1 - P) + P k P` we have `det_S k = det Y` and
  -- `Yᴴ Y = (1 - P) + P kᴴ P k P = 1 - Mᴴ M`, while `‖[P, k]‖² = 2 ‖M‖²`.
  have hP : IsStarProjection (coordProj p) := isStarProjection_coordProj p
  set P : Matrix n n ℂ := coordProj p
  have hPP : P * P = P := hP.isIdempotentElem
  let M : Matrix n n ℂ := (1 - P) * k * P
  let Y : Matrix n n ℂ := 1 - P + P * k * P
  have minor_eq : principalMinor k p = Y.det := by
    have Y_eq : Y = 1 + P * (k - 1) * P := by
      simp [Y, mul_sub, sub_mul, hPP, sub_add_eq_add_sub, add_sub_assoc]
    rw [principalMinor_eq_det_coordProj, Y_eq, det_one_add_mul_comm (P * (k - 1)), ← mul_assoc, hPP]
  have Y_sq : Yᴴ * Y = 1 - P + P * kᴴ * P * k * P := by
    simp [Y, hP.isSelfAdjoint.star_eq, ← star_eq_conjTranspose, add_mul, mul_add, mul_sub, sub_mul,
      ← mul_assoc, mul_assoc _ P P, hPP]
  have gram_eq : Yᴴ * Y - 1 = -(Mᴴ * M) := by
    rw [Y_sq, conjTranspose_mul_self_one_sub_mul_mul hP hk]
    abel
  calc ‖principalMinor k p‖ ^ 2 ≤ Real.exp (Yᴴ * Y - 1).trace.re := by
        rw [minor_eq]
        exact norm_det_sq_le_exp Y
    _ = Real.exp (-‖M‖ ^ 2) := by
        rw [gram_eq, trace_neg, trace_star_mul_self_eq_norm_sq, neg_re, ofReal_re]
    _ = Real.exp (-(‖⁅P, k⁆‖ ^ 2 / 2)) := by
        rw [norm_lie_sq_of_unitary hP hk, mul_div_cancel_left₀ _ two_ne_zero]

/-- The entry `(i, j)` of the commutator of `X` with the diagonal projection to the indices
satisfying `p` has the norm of `X i j` if exactly one of `p i`, `p j` holds, else it is `0`. -/
lemma norm_lie_coordProj_apply (X : Matrix n n ℂ) (i j : n) :
    ‖⁅coordProj p, X⁆ i j‖ = if p i ↔ p j then 0 else ‖X i j‖ := by
  by_cases hi : p i <;> by_cases hj : p j <;> simp [coordProj, Ring.lie_def, hi, hj]

end New.DiscreteSeries

end SizeOfOneMinor

section DeterminantOfCompression

open Ring Matrix Norms.Frobenius Complex intervalIntegral

namespace New.DiscreteSeries

variable {n : Type*} [Fintype n] [DecidableEq n] {P Q X Y : Matrix n n ℂ} {δ c : ℝ}

attribute [local simp] mul_add add_mul mul_assoc lie_def IsIdempotentElem.eq
  IsIdempotentElem.mul_self_mul IsStarProjection.isIdempotentElem

/-- Let `P` and `Q` be orthogonal projections, and let `‖X‖ ≤ δ ≤ 1 / 2`, `tr ([P, Q] Y) = 0`,
`‖[P, X] - Y‖ ≤ δ c`, `‖Y‖ ≤ c` and `‖Q - P‖ ≤ c`. Then
`det (1 + P X) = exp (tr (Q logOneAdd X) - tr (Y ^ 2) / 4 + r)` with `|r| ≤ 100 δ c ^ 2`. -/
lemma exists_det_compress_eq_exp_logOneAdd (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hδ : δ ≤ 2⁻¹) (hX : ‖X‖ ≤ δ) (h_comm : (⁅P, Q⁆ * Y).trace = 0)
    (h_near : ‖⁅P, X⁆ - Y‖ ≤ δ * c) (hY : ‖Y‖ ≤ c) (hPQ : ‖Q - P‖ ≤ c) :
    ∃ r : ℂ, (1 + P * X).det = cexp ((Q * logOneAdd X).trace - 4⁻¹ * (Y * Y).trace + r) ∧
      ‖r‖ ≤ 100 * δ * c ^ 2 := by
  have hδ_nonneg : 0 ≤ δ := (norm_nonneg X).trans hX
  have hc_nonneg : 0 ≤ c := (norm_nonneg Y).trans hY
  have hPX : ‖P * X‖ ≤ δ := norm_proj_mul_le hP hX
  have h_lie : ‖⁅P, X⁆‖ ≤ c + 2⁻¹ * c := (norm_le_insert' _ Y).trans (by grw [hY, h_near, hδ])
  -- `log det (1 + P X)` is the integral over `[0, 1]` of `tr ((1 + s P X)⁻¹ P X)`, by
  -- `det_one_add_eq_exp_trace_logOneAdd`, and `tr (Q logOneAdd X)` is that of
  -- `tr (Q (1 + s X)⁻¹ X)`. So the remainder `r` is the integral of the difference, corrected by
  -- `s tr (Y ^ 2) / 2`.
  have h_int_P := intervalIntegrable_trace_mul_inv_one_add_smul_mul (hPX.trans hδ) 1
  have h_int_Q := intervalIntegrable_trace_mul_inv_one_add_smul_mul (hX.trans hδ) Q
  have h_int_Y : IntervalIntegrable (fun s : ℝ ↦ (s : ℂ) * (2⁻¹ * (Y * Y).trace))
      MeasureTheory.volume 0 1 :=
    (continuous_ofReal.intervalIntegrable ..).mul_const _
  have h_integral : ∫ s : ℝ in 0..1, ((1 * ((1 + s • (P * X))⁻¹ * (P * X))).trace -
        (Q * ((1 + s • X)⁻¹ * X)).trace + s * (2⁻¹ * (Y * Y).trace)) =
      (logOneAdd (P * X)).trace - (Q * logOneAdd X).trace + 4⁻¹ * (Y * Y).trace := by
    rw [integral_add (h_int_P.sub h_int_Q) h_int_Y, integral_sub h_int_P h_int_Q,
      integral_trace_mul_inv_one_add_smul_mul (hPX.trans hδ) 1,
      integral_trace_mul_inv_one_add_smul_mul (hX.trans hδ) Q, integral_mul_const,
      integral_ofReal, integral_id]
    norm_num
    ring
  refine ⟨(logOneAdd (P * X)).trace - (Q * logOneAdd X).trace + 4⁻¹ * (Y * Y).trace, ?_, ?_⟩
  · rw [det_one_add_eq_exp_trace_logOneAdd (hPX.trans hδ)]
    congr 1
    ring
  -- It remains to bound the integrand at each `s ∈ (0, 1]`.
  rw [← h_integral]
  refine (norm_integral_le_of_norm_le_const (C := 100 * δ * c ^ 2) fun s hs ↦ ?_).trans_eq
    (by simp)
  have hs_mem : s ∈ Set.Icc (0 : ℝ) 1 := by grind
  have hs_half : s / 2 ∈ Set.Icc (0 : ℝ) 1 := by grind
  -- The resolvents `W = (1 + s X)⁻¹` and `V = (1 + s P X)⁻¹` are within `2 δ` of `1`.
  have hsX : ‖s • X‖ ≤ δ := norm_smul_le_of_le_one s hX hs_mem
  have hsPX : ‖s • (P * X)‖ ≤ δ := norm_smul_le_of_le_one s hPX hs_mem
  have hW_mul : (1 + s • X) * (1 + s • X)⁻¹ = 1 :=
    one_add_mul_inv_one_add (hsX.trans_lt (by linarith))
  have hW_mul' : (1 + s • X)⁻¹ * (1 + s • X) = 1 :=
    inv_one_add_mul_one_add (hsX.trans_lt (by linarith))
  have hW : ‖(1 + s • X)⁻¹ - 1‖ ≤ 2 * δ :=
    (norm_inv_one_add_sub_one_le (hsX.trans hδ)).trans (by linarith)
  have hV_mul : (1 + s • (P * X)) * (1 + s • (P * X))⁻¹ = 1 :=
    one_add_mul_inv_one_add (hsPX.trans_lt (by linarith))
  have hV_mul' : (1 + s • (P * X))⁻¹ * (1 + s • (P * X)) = 1 :=
    inv_one_add_mul_one_add (hsPX.trans_lt (by linarith))
  have hV : ‖(1 + s • (P * X))⁻¹ - 1‖ ≤ 2 * δ :=
    (norm_inv_one_add_sub_one_le (hsPX.trans hδ)).trans (by linarith)
  set W : Matrix n n ℂ := (1 + s • X)⁻¹
  set V : Matrix n n ℂ := (1 + s • (P * X))⁻¹
  set A : Matrix n n ℂ := ⁅P, X⁆
  set D : Matrix n n ℂ := Q - P
  let Z : Matrix n n ℂ := W - 1
  let N : Matrix n n ℂ := Z * (A * Z + A) + A * Z
  -- Rewrite the integrand as four traces, each of a product with one factor of size `δ` and two
  -- of size `c`. The identity uses `W (1 + s X) = 1`, `V (1 + s P X) = 1`, `P ^ 2 = P`,
  -- `Q ^ 2 = Q`, `tr ([P, Q] Y) = 0` and `tr (M M') = tr (M' M)`.
  have h_split : (1 * (V * (P * X))).trace - (Q * (W * X)).trace + s * (2⁻¹ * (Y * Y).trace) =
      trace ((P * D + Q * D - D) * (A - Y + Z * A - s • (N + A) * X)) -
        trace (s • (P * A) * ((N + A) * (V - 1) + N)) -
        trace ((D - P * D - P * D) * D * (X + Z * X)) -
        trace ((s / 2) • (A - Y) * (A + Y)) := by
    linear_combination (norm := (
      simp +zetaDelta only [hP, hQ, trace_mul_comm P, trace_mul_comm V, trace_mul_comm Y (_ * _),
        trace_mul_comm X (P * X), mul_sub, sub_mul, mul_add, add_mul, mul_assoc, one_mul, mul_one,
        lie_def, IsStarProjection.isIdempotentElem, IsIdempotentElem.eq,
        IsIdempotentElem.mul_self_mul, trace_sub, trace_add, trace_smul, smul_add,
        Algebra.smul_mul_assoc, Algebra.mul_smul_comm, real_smul, ofReal_div, ofReal_ofNat]
      ring_nf))
      h_comm + congr(($hV_mul' * P * W * X * P +
        V * P * (A * ($hW_mul' * P * (1 - W) + W * P * $hW_mul) - $hW_mul * X * P) +
        (1 - P) * $hV_mul * P * X - ⁅P, D⁆ * ($hW_mul' * P * W - W * P * $hW_mul) * X).trace)
  rw [h_split]
  apply le_trans
  · apply_rules (transparency := .reducible) (maxDepth := 99)
      [norm_smul_le_of_le_one s (hρ := hs_mem), norm_smul_le_of_le_one (s / 2) (hρ := hs_half),
      norm_proj_mul_le hP, norm_proj_mul_le hQ, @norm_trace_mul_le, norm_sub_le_of_le,
      norm_add_le_of_le, norm_mul_le_of_le]
  · have hδc := mul_nonneg hδ_nonneg (sq_nonneg c)
    linarith [mul_le_mul_of_nonneg_right hδ hδc,
      mul_le_mul_of_nonneg_right hδ (mul_nonneg hδ_nonneg hδc)]

end New.DiscreteSeries

end DeterminantOfCompression

section MinorExpansion

open Ring Matrix Norms.Frobenius Complex ComplexConjugate

namespace New.DiscreteSeries

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} {h : ℕ} {l : HCParam ε}
  {X : Matrix n n ℂ}

attribute [local simp] mul_add add_mul mul_assoc lie_def principalMinor_eq_det coordProj

/-- The determinant of a matrix that is triangular for an injective order `o` is the product of
its diagonal entries. -/
lemma det_eq_prod_diag_of_blockTriangular {b : Matrix n n ℂ} {o : n → ℤ} (ho : o.Injective) :
    b.BlockTriangular o → b.det = ∏ i, b i i :=
  let := LinearOrder.lift' o ho
  det_of_isUpperTriangular

/-- The value of `l.flenstedJensen 1` at `zᴴ` is the conjugate of its value at `z`. -/
lemma conj_flenstedJensen_one (z : Matrix n n ℂ) :
    conj (l.flenstedJensen 1 z) = l.flenstedJensen 1 zᴴ := by
  simp [flenstedJensen, conj_weightMinors, ← integral_conj, mul_comm, mul_assoc]

/-- Let `u` be block diagonal and strictly triangular: `u i j = 0` unless `l i < l j` and
`ε i = ε j`. If `X` and `(1 - u) * X` are accretive, then `l.flenstedJensen 1` at
`((1 - u) * X)ᴴ` is the conjugate of its value at `X`. -/
lemma flenstedJensen_shift_eq_conj (hl : l.HasGap h) {u : Matrix n n ℂ}
    (hu : ∀ i j, ¬(l i < l j ∧ ε i = ε j) → u i j = 0) (hX : X.IsAccretive)
    (huX : ((1 - u) * X).IsAccretive) :
    l.flenstedJensen 1 ((1 - u) * X)ᴴ = conj (l.flenstedJensen 1 X) := by
  have h_det : (1 - u).det ≠ 0 ∧ X.det ≠ 0 := by simpa [det_mul] using huX.det_ne_zero
  -- `1 - u` is block diagonal and triangular, with diagonal entries `1`.
  have hu_mem : 1 - u ∈ blockDiagAlg ε := mem_blockDiagAlg.2 fun i j hij ↦ by
    simp [one_apply_ne (show i ≠ j by rintro rfl; exact hij rfl), hu i j (by tauto)]
  have hu_borel : IsBorelMatrix (-(-l)) (1 - u) := ⟨fun i j hij ↦ by
    have h_lt : l j < l i := by simpa using hij
    simp [one_apply_ne (show i ≠ j by rintro rfl; exact lt_irrefl _ h_lt),
      hu i j fun h' ↦ lt_asymm h_lt h'.1], h_det.1⟩
  -- Move the factor `1 - u` from the second argument to the first, where it acts by a character
  -- with value `1`.
  have h_move : l.flenstedJensen (1 - u) X = l.flenstedJensen 1 ((1 - u) * X) := by
    have := flenstedJensen_eq_of_accretive hl (one_mem _) (by simpa using huX) hu_mem
      (g := (1 - u) * X) (by simp_all)
    simp_all
  have h_char : l.flenstedJensen (1 - u) X = l.flenstedJensen 1 X := by
    have h_minors (k : maxCompactU ε) :
        weightMinors l.lowestKType ((1 - u) * (k : Matrix n n ℂ)) =
          weightMinors l.lowestKType (k : Matrix n n ℂ) := by
      rw [hl.isKDominant_lowestKType.weightMinors_oppBorel_mul hl.neg.injective
        ((Matrix.isUnit_iff_isUnit_det _).1 k.1.1.isUnit).ne_zero hu_mem hu_borel]
      simp [diagChar, show ∀ i, u i i = 0 from fun i ↦ hu i i (by simp)]
    simp [flenstedJensen, h_minors]
  rw [← conj_flenstedJensen_one, ← h_move, h_char]

/-- Let `l` have gap `h` and let `X = g - 1` have norm less than `1 / 1000`. There is a matrix `y`
with `l.dsCoeff g = l.flenstedJensen 1 y` such that, for `k ∈ K = maxCompactU ε` and the diagonal
projection `P = coordProj p` to a set `p` of lowest entries of `l`, the principal minor of
`kᴴ y k` on `p` is `exp (tr (P logOneAdd X) + ‖[P, X]‖² / 4 + r)` with
`|r| ≤ 2 · 10⁵ ‖X‖ (‖[P, X]‖² + ‖[P, k]‖²)`. -/
lemma exists_principalMinor_eq_exp (hl : l.HasGap h) (g : USign ε)
    (hg : ‖(g : Matrix n n ℂ) - 1‖ < 1000⁻¹) :
    ∃ y : Matrix n n ℂ, l.dsCoeff g = l.flenstedJensen 1 y ∧
      ∀ (p : n → Prop) [DecidablePred p], (∀ i j, p i → ¬p j → l i < l j) →
        ∀ k : maxCompactU ε, ∃ r : ℂ,
          principalMinor ((k : Matrix n n ℂ)ᴴ * y * (k : Matrix n n ℂ)) p =
            cexp ((coordProj p * logOneAdd ((g : Matrix n n ℂ) - 1)).trace +
              ‖⁅coordProj p, (g : Matrix n n ℂ) - 1⁆‖ ^ 2 / 4 + r) ∧
          ‖r‖ ≤ 200000 * ‖(g : Matrix n n ℂ) - 1‖ *
            (‖⁅coordProj p, (g : Matrix n n ℂ) - 1⁆‖ ^ 2 +
              ‖⁅coordProj p, (k : Matrix n n ℂ)⁆‖ ^ 2) := by
  set X : Matrix n n ℂ := (g : Matrix n n ℂ) - 1
  have hX_nonneg : 0 ≤ ‖X‖ := norm_nonneg X
  have hX_half : ‖X‖ ≤ 2⁻¹ := by linarith
  have hX_four : 4 * ‖X‖ ≤ 2⁻¹ := by linarith
  -- `r c` is the part of `X` strictly below the diagonal for the order `c`, inside the blocks of
  -- `ε`. Multiply `g` by the unipotent factors `1 - u` and `1 - r c`.
  let r (c : n → ℤ) : Matrix n n ℂ := lowerMask ε c X
  let u : Matrix n n ℂ := r (-l)
  let y (c : n → ℤ) : Matrix n n ℂ := (1 - u) * g * (1 - r c)
  let m : Matrix n n ℂ := X - u - u * X
  have hu : ‖u‖ ≤ ‖X‖ := norm_entryMask_le
  have hr (c : n → ℤ) : ‖r c‖ ≤ ‖X‖ := norm_entryMask_le
  have hm : ‖m‖ ≤ ‖X‖ + ‖X‖ + ‖X‖ * ‖X‖ :=
    norm_sub_le_of_le (norm_sub_le_of_le (le_refl ‖X‖) hu) (norm_mul_le_of_le hu le_rfl)
  have hm' : ‖m‖ ≤ 3 * ‖X‖ := by nlinarith [mul_le_mul_of_nonneg_right hX_half hX_nonneg]
  have hy_near (c : n → ℤ) : ‖y c - 1‖ ≤ 4 * ‖X‖ := by
    have h_eq : y c - 1 = m - r c - m * r c := by
      have hgX : (g : Matrix n n ℂ) = 1 + X := by simp [X]
      simp only [y, m, hgX]
      noncomm_ring
    rw [h_eq]
    have := norm_sub_le_of_le (norm_sub_le_of_le hm (hr c)) (norm_mul_le_of_le hm (hr c))
    nlinarith [mul_le_mul_of_nonneg_right hg.le hX_nonneg,
      mul_le_mul_of_nonneg_right hg.le (mul_nonneg hX_nonneg hX_nonneg)]
  -- Step 1: the coefficient is `l.flenstedJensen 1 (y l)`. Removing either factor conjugates the
  -- value.
  have hy_acc (c : n → ℤ) : (y c).IsAccretive :=
    isAccretive_of_norm_sub_one_lt ((hy_near c).trans_lt (by linarith))
  have hg_acc : (g : Matrix n n ℂ).IsAccretive :=
    isAccretive_of_norm_sub_one_lt (hg.trans (by norm_num))
  have hug_acc : ((1 - u) * (g : Matrix n n ℂ)).IsAccretive := by
    simpa [y, show r 0 = 0 from rfl] using hy_acc 0
  have h_coeff : l.dsCoeff g = l.flenstedJensen 1 (y l) := by
    have h_left := flenstedJensen_shift_eq_conj hl (u := u) (by simp [u, r]; grind) hg_acc hug_acc
    have h_right := flenstedJensen_shift_eq_conj hl (u := (r l)ᴴ)
      (X := ((1 - u) * (g : Matrix n n ℂ))ᴴ) (by simp [r]; grind)
      (by simpa [IsAccretive, add_comm] using hug_acc)
      (by simpa [y, IsAccretive, add_comm] using hy_acc l)
    rw [dsCoeff_eq_flenstedJensen hl (one_mem _) (by simpa using hg_acc)]
    simpa [y] using (h_right.trans (congrArg _ h_left)).symm
  -- Step 2: on a set of highest entries of `l` the triangular factors do not change the minor.
  have h_minor (p : n → Prop) [DecidablePred p] (hp : ∀ i j, p i → ¬p j → l j < l i) :
      principalMinor (y l) p = principalMinor (g : Matrix n n ℂ) p := by
    clear * - hp hl
    rw [principalMinor_mul, principalMinor_mul, principalMinor_eq_det,
      det_eq_prod_diag_of_blockTriangular hl.injective, mul_comm, principalMinor_eq_det,
      det_eq_prod_diag_of_blockTriangular hl.neg.injective] <;>
      simp [u, r, BlockTriangular, Matrix.one_apply] <;> grind
  refine ⟨y l, h_coeff, fun p _ hp κ ↦ ?_⟩
  -- Step 3: one minor. Notation: `P` projects to `p`, `Q = k P kᴴ`, and `A`, `B`, `C` are the
  -- commutators of `P` with `X`, `u`, `r l`.
  set k : Matrix n n ℂ := (κ : Matrix n n ℂ)
  let s : Matrix n n ℂ := signMatrix ε
  have hk : kᴴ * k = 1 := (U_one_mem_unitaryGroup ⟨_, κ.property⟩).1
  have hk' : k * kᴴ = 1 := mul_eq_one_symm hk
  have hk_mem : k ∈ blockDiagAlg ε := mem_maxCompactU.1 κ.property
  have hP : IsStarProjection (coordProj p) := isStarProjection_coordProj p
  have hsP : Commute s (coordProj p) := commute_diagonal ..
  set P : Matrix n n ℂ := coordProj p
  set A : Matrix n n ℂ := ⁅P, X⁆
  set B : Matrix n n ℂ := ⁅P, u⁆
  set C : Matrix n n ℂ := ⁅P, r l⁆
  set G : Matrix n n ℂ := B * X + u * A
  let Q : Matrix n n ℂ := k * P * kᴴ
  let V : Matrix n n ℂ := (1 + X)⁻¹ - 1
  let H : Matrix n n ℂ := G + m * C - (G + B - A) * r l
  have ⟨h_mask, hB⟩ : (∀ c, ⁅P, r c⁆ = lowerMask ε c A) ∧ B = blockDiagPart ε A - C := by
    simp +zetaDelta [← ext_iff, blockDiagPart]
    grind
  have h_det_compl (x : Matrix n n ℂ) :
      (1 + (1 - P) * (x - 1)).det = principalMinor x (¬p ·) := by
    simp [P, det_apply, sub_mul]
    grind
  have hP_compl : IsStarProjection (1 - P) := hP.one_sub
  have hA_nonneg : 0 ≤ ‖A‖ := norm_nonneg A
  have hPk_nonneg : 0 ≤ ‖⁅P, k⁆‖ := norm_nonneg _
  have hP_star : Pᴴ = P := hP.2
  have hV : ‖V‖ ≤ 2 * ‖X‖ := norm_inv_one_add_sub_one_le hX_half
  have hB_le : ‖B‖ ≤ ‖A‖ := by
    rw [show B = lowerMask ε (-l) A from h_mask (-l)]
    exact norm_entryMask_le
  have hC_le : ‖C‖ ≤ ‖A‖ := by
    rw [show C = lowerMask ε l A from h_mask l]
    exact norm_entryMask_le
  have hg_inv : (g : Matrix n n ℂ)⁻¹ = signMatrix ε * (g : Matrix n n ℂ)ᴴ * signMatrix ε := by
    simp [← U.coe_inv (signMatrix_mul_self ε)]
  have hg_star : (g : Matrix n n ℂ)ᴴ = s * (g : Matrix n n ℂ)⁻¹ * s := by
    grind [signMatrix_mul_self]
  have hkPk : k * ⁅P, k⁆ᴴ = P - Q := by simp [Q, mul_sub, ← mul_assoc, hk', hP_star]
  have hPQ : ‖P - Q‖ ≤ ‖⁅P, k⁆‖ :=
    (hkPk ▸ frobenius_norm_mul_of_unitary hk _).trans_le (norm_star _).le
  -- `[P, y l - 1]` is `A - B - C` up to the second order term `H`.
  have hH : ‖H‖ ≤ 8 * ‖X‖ * ‖A‖ := by
    have hG : ‖G‖ ≤ ‖A‖ * ‖X‖ + ‖X‖ * ‖A‖ :=
      norm_add_le_of_le (norm_mul_le_of_le hB_le le_rfl) (norm_mul_le_of_le hu le_rfl)
    have := norm_sub_le_of_le (norm_add_le_of_le hG (norm_mul_le_of_le hm' hC_le))
      (norm_mul_le_of_le (norm_sub_le_of_le (norm_add_le_of_le hG hB_le) (le_refl ‖A‖)) (hr l))
    linarith [mul_nonneg hX_nonneg hA_nonneg,
      mul_le_mul_of_nonneg_right hX_half (mul_nonneg hX_nonneg hA_nonneg)]
  -- The complementary minor of `g`.
  have ⟨x, hx_eq, hx⟩ := exists_det_compress_eq_exp_logOneAdd (Y := -A) hP_compl hP_compl hX_half
    (le_refl ‖X‖) (by simp) (by simp [A, mul_sub, sub_mul, mul_nonneg]) (norm_neg A).le (by simp)
  -- The complementary minor of `y l`, which is that of `g`.
  have h_near_compl : ‖⁅1 - P, y l - 1⁆ - (B + C - A)‖ ≤ 4 * ‖X‖ * (4 * ‖A‖) := by
    rw [show ⁅1 - P, y l - 1⁆ - (B + C - A) = H by simp +zetaDelta only [lie_def]; noncomm_ring]
    linarith [mul_nonneg hX_nonneg hA_nonneg]
  have ⟨z, hz_eq, hz⟩ := exists_det_compress_eq_exp_logOneAdd (Y := B + C - A) hP_compl hP_compl
    hX_four (hy_near l) (by simp) h_near_compl
    (by linarith [norm_sub_le_of_le (norm_add_le_of_le hB_le hC_le) (le_refl ‖A‖)]) (by simp)
  -- The minor of `kᴴ (y l) k` on `p`, as `det (1 + Q (y l - 1))`.
  have h_comm : (⁅Q, P⁆ * (A - B - C)).trace = 0 := by
    simp [Q, s, hB, blockDiagPart_eq, hsP.eq, trace_mul_comm P,
      (mem_blockDiagAlg_iff_commute.1 hk_mem).left_comm,
      A, X, inv_eq_left_inv hk ▸ blockDiagAlg.inv_mem hk_mem _ rfl, trace_mul_comm k,
      trace_mul_comm kᴴ, trace_mul_comm s, signMatrix_mul_self, mul_sub, sub_mul]
    ring_nf
  have h_near : ‖⁅Q, y l - 1⁆ - (A - B - C)‖ ≤ 4 * ‖X‖ * (4 * (‖A‖ + ‖⁅P, k⁆‖)) := by
    rw [show ⁅Q, y l - 1⁆ - (A - B - C) = (y l - 1) * (P - Q) - (P - Q) * (y l - 1) - H by
      simp +zetaDelta only [lie_def]; noncomm_ring]
    have := norm_sub_le_of_le (norm_sub_le_of_le (norm_mul_le_of_le (hy_near l) hPQ)
      (norm_mul_le_of_le hPQ (hy_near l))) hH
    linarith [mul_nonneg hX_nonneg hA_nonneg, mul_nonneg hX_nonneg hPk_nonneg]
  have ⟨t, ht_eq, ht⟩ := exists_det_compress_eq_exp_logOneAdd (P := Q) (Y := A - B - C)
    (hP.map (Unitary.conjStarAlgAut ℂ _ ⟨k, hk, hk'⟩)) hP hX_four (hy_near l) h_comm h_near
    (by linarith [norm_sub_le_of_le (norm_sub_le_of_le (le_refl ‖A‖) hB_le) hC_le])
    (by linarith)
  rw [h_det_compl, h_minor _ (by tauto), ← h_det_compl, hx_eq] at hz_eq
  have h_conj : principalMinor (kᴴ * y l * k) p = (1 + Q * (y l - 1)).det := by
    simp only [mul_assoc, principalMinor_eq_det, coordProj, det_one_add_mul_comm k, Q, P]
    noncomm_ring [hk]
  have h_det_y : (1 + (y l - 1)).det = (1 + X).det := by
    simpa [principalMinor_of_forall, X] using h_minor ⊤
  have h_det : cexp (logOneAdd (y l - 1)).trace = cexp (logOneAdd X).trace := by
    rw [← det_one_add_eq_exp_trace_logOneAdd ((hy_near l).trans hX_four), h_det_y,
      det_one_add_eq_exp_trace_logOneAdd hX_half]
  -- The remainder: those of the three determinants, and the difference between `‖A‖ ^ 2` and
  -- `-tr (A ^ 2)`, which comes from `Xᴴ = s ((1 + X)⁻¹ - 1) s`.
  have h_corr : ‖((4⁻¹ : ℝ) • (V * (A * V + A) + A * V) * (A - B - C - B - C)).trace‖ ≤
      (2 * ‖X‖ * (‖A‖ * (2 * ‖X‖) + ‖A‖) + ‖A‖ * (2 * ‖X‖)) *
        (‖A‖ + ‖A‖ + ‖A‖ + ‖A‖ + ‖A‖) :=
    norm_trace_mul_le (norm_smul_le_of_le_one 4⁻¹ (norm_add_le_of_le (norm_mul_le_of_le hV
      (norm_add_le_of_le (norm_mul_le_of_le le_rfl hV) le_rfl)) (norm_mul_le_of_le le_rfl hV))
      ⟨by norm_num, by norm_num⟩) (norm_sub_le_of_le (norm_sub_le_of_le (norm_sub_le_of_le
      (norm_sub_le_of_le le_rfl hB_le) hC_le) hB_le) hC_le)
  refine ⟨t + z - x + ((4⁻¹ : ℝ) • (V * (A * V + A) + A * V) * (A - B - C - B - C)).trace,
    ?_, ?_⟩
  · -- Multiply by the complementary minor and by `det (y l) = det g`, and compare exponents.
    refine h_conj.trans (ht_eq.trans (mul_right_cancel₀ (by simp)
      (congr(_ * ($hz_eq * $h_det)).trans ?_)))
    simp [V, s, hg_star, hP_star, hB, blockDiagPart_eq, hsP.eq, trace_mul_comm P,
      ← ofReal_pow, A, X, trace_mul_comm s, signMatrix_mul_self, ← mul_assoc s s, ← exp_add,
      mul_sub, sub_mul, ← trace_star_mul_self_eq_norm_sq]
    ring_nf
  · have := norm_add_le_of_le (norm_sub_le_of_le (norm_add_le_of_le ht hz) hx) h_corr
    linarith [mul_nonneg hX_nonneg (sq_nonneg ‖A‖), mul_nonneg hX_nonneg (sq_nonneg ‖⁅P, k⁆‖),
      mul_nonneg hX_nonneg (sq_nonneg (‖A‖ - ‖⁅P, k⁆‖)),
      mul_le_mul_of_nonneg_right hX_half (mul_nonneg hX_nonneg (sq_nonneg ‖A‖))]

end New.DiscreteSeries

end MinorExpansion
