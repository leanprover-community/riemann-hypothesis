module

public import Lib.DiscreteSeries.FlenstedJensen.SquareIntegrability
public import New.Appendix.DiscreteSeries.MinorExpansion

/-!
# The Gaussian shape of the coefficient

Near `1` the coefficient `l.dsCoeff g` of a discrete series with a large gap is nearly the phase
`exp (tr μ log g)` times a number in `[0, 1]`, where `μ` is the weight `l.lowestKType`
(`exists_norm_dsCoeff_div_cexp_sub_le`). The coefficient is a mean over `K` of a quotient of
products of minors, and the estimates for one minor are multiplied over the sets `{i | t ≤ w i}` of
a weight `w`. In the comments, `λ^ρ` is `paramAddRho l` and `Q_w` is `gapWeightedNormSq w`.
The Gaussian is `exp (-q)` with `q = Q_{-λ^ρ} (g - 1) / 4`; note `Q_{-w} = Q_w`.
Except in the first section, the norm of a matrix is the Frobenius norm.

* `USign ε` is the unitary group of the form `diag ε`; `K = maxCompactU ε` is its subgroup of
  unitary matrices, with the Haar measure `haarK ε` of mass one.
* `l : HCParam ε` is a doubled Harish-Chandra parameter `2λ`; `paramAddRho l` is `λ + ρ` and
  `l.lowestKType` is `λ + ρ - 2ρ_c`.
* `weightMinors w g` is the product over `t : ℤ` of the principal minors of `g` on the sets
  `{i | t ≤ w i}`, those with `t ≤ 0` divided by `det g`; `w.kTypeNormSq` is the mean of its
  squared modulus over `K`.
* `l.flenstedJensen g z` is the mean over `k ∈ K` of
  `weightMinors μ (g k) * conj (weightMinors μ k) / weightMinors (-paramAddRho l) (kᴴ z k)`,
  divided by `μ.kTypeNormSq` (Flensted-Jensen's integral); the matrix coefficient `l.dsCoeff` is
  defined through it.

## Relation to the literature

See `New.Appendix.DiscreteSeries.Periods` for related work.
-/

@[expose] public section

open Matrix MeasureTheory Finset Fintype Ring Complex ComplexConjugate

namespace New.DiscreteSeries

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} {l : HCParam ε} {δ T q : ℝ}
  {h L A : ℕ} {a b : ℤ} {w : n → ℤ}

section Dimension

open Norms.L2Operator

/-- Let the parameter `l = 2λ` have gap `500 n ^ 3 + A` (the entries of `λ` are distinct, and those
with different signs `ε` are this far apart) and `|l i| ≤ L`. Then the mean `μ.kTypeNormSq` over
`K = maxCompactU ε` of the squared modulus of the highest weight coefficient `weightMinors μ`, for
`μ = l.lowestKType`, is at least `1 / (4 (2000 (n + L + 1) ^ 6) ^ (2 n ^ 2))`. -/
lemma one_le_pow_mul_kTypeNormSq [Nonempty n] (hl : l.HasLargeGap A) (hL : ∀ i : n, |l i| ≤ L) :
    1 ≤ (2000 * (card n + L + 1) ^ 6) ^ (2 * card n ^ 2) * (4 * l.lowestKType.kTypeNormSq) := by
  -- Compare volume and integral on `K`, which has mass one: all of `K` lies in the unit ball for
  -- the operator norm (opened in this section), and `l.dsCoeff k = weightMinors μ k` there.
  have h_univ : {k : maxCompactU ε | ‖(k : Matrix n n ℂ)‖ ≤ 1} = Set.univ :=
    Set.eq_univ_of_forall fun k ↦
      (CStarRing.norm_of_mem_unitary (U_one_mem_unitaryGroup ⟨_, k.property⟩)).le
  have h_ball : haarK ε {k : maxCompactU ε | ‖(k : Matrix n n ℂ)‖ ≤ 1} ≤
      ENNReal.ofReal ((2000 * (card n + L + 1) ^ 6 * 1 ^ 2) ^ (2 * card n ^ 2)) *
        ENNReal.ofReal (∫ k : maxCompactU ε, 4 * ‖l.dsCoeff k‖ ^ 2 ∂haarK ε) :=
    measure_ball_le_integral_dsCoeff (hg := hl) hL (haarK ε) (maxCompactU ε).subtype
      integrable_of_compactSpace 1 le_rfl
  rw [← ENNReal.one_le_ofReal, ENNReal.ofReal_mul (by positivity)]
  simpa [h_univ, dsCoeff_of_mem_maxCompactU, integral_const_mul] using h_ball

/-- Let the parameter `l = 2λ` have gap `500 n ^ 3 + A` and `|l i| ≤ L`, and let `T` be at least
`1`, `n ^ 2` and `n ^ 2 log (n + L + 1)`. Then the mean `μ.kTypeNormSq` over `K = maxCompactU ε` of
the squared modulus of the highest weight coefficient `weightMinors μ`, for `μ = l.lowestKType`, is
at least `exp (-5000 T)`. The inverse of `μ.kTypeNormSq` plays the part of the dimension of the
lowest `K`-type, so this takes the place of the bound from Weyl's dimension formula. -/
lemma exp_neg_le_kTypeNormSq [Nonempty n] (hl : l.HasLargeGap A) (hL : ∀ i : n, |l i| ≤ L)
    (hT : 1 ≤ T) (hT_card : card n ^ 2 ≤ T)
    (hT_log : card n ^ 2 * Real.log (card n + L + 1) ≤ T) :
    Real.exp (-(5000 * T)) ≤ l.lowestKType.kTypeNormSq := by
  have h_pos : 0 < l.lowestKType.kTypeNormSq := kTypeNormSq_pos l.lowestKType
  -- Take logarithms in the lower bound.
  have h_log : 0 ≤ 2 * card n ^ 2 * (Real.log 2000 + 6 * Real.log (card n + L + 1)) +
      (Real.log 4 + Real.log l.lowestKType.kTypeNormSq) := by
    simpa (disch := positivity) [Real.log_mul, Real.log_pow] using
      Real.log_nonneg (one_le_pow_mul_kTypeNormSq hl hL)
  -- Here `log 2000 ≤ 2000` and `log 4 ≤ 4` suffice.
  have h_mul : (card n : ℝ) ^ 2 * Real.log 2000 ≤ card n ^ 2 * 2000 := by
    grw [Real.log_le_self (by norm_num)]
  exact (Real.le_log_iff_exp_le h_pos).1
    (by linarith [Real.log_le_self (zero_le_four : (0 : ℝ) ≤ 4)])

end Dimension

open Norms.Frobenius

/-- The quadratic form `Q_w (X) = ∑_{i, j} |w i - w j| |X i j| ^ 2`. -/
noncomputable abbrev gapWeightedNormSq (w : n → ℤ) (X : Matrix n n ℂ) : ℝ :=
  ∑ i : n, ∑ j : n, |w i - w j| * ‖X i j‖ ^ 2

omit [DecidableEq n] in
lemma gapWeightedNormSq_nonneg (w : n → ℤ) (X : Matrix n n ℂ) : 0 ≤ gapWeightedNormSq w X := by
  positivity

/-- Let the entries of `w` lie in `[a, b]`, and let `P_t = coordProj (t ≤ w ·)` be the projection
to the coordinates `{i | t ≤ w i}`. The squared Frobenius norms of the commutators `[P_t, X]`,
`a < t ≤ b`, add up to `Q_w (X) = ∑_{i, j} |w i - w j| |X i j| ^ 2`, because exactly
`|w i - w j|` of these sets separate `i` from `j`. -/
lemma sum_norm_lie_coordProj_sq (hw : ∀ i : n, a ≤ w i ∧ w i ≤ b) (X : Matrix n n ℂ) :
    ∑ t ∈ Ioc a b, ‖⁅coordProj (t ≤ w ·), X⁆‖ ^ 2 = gapWeightedNormSq w X := by
  have h_card (i j : n) : (#{t ∈ Ioc a b | ¬(t ≤ w i ↔ t ≤ w j)} : ℤ) = |w i - w j| := by
    rw [show {t ∈ Ioc a b | ¬(t ≤ w i ↔ t ≤ w j)} = Ioc (w i ⊓ w j) (w i ⊔ w j) by grind,
      Int.card_Ioc, max_sub_min_eq_abs', Int.toNat_of_nonneg (abs_nonneg _)]
  have h_entry (t : ℤ) (i j : n) :
      ‖⁅coordProj (t ≤ w ·), X⁆ i j‖ ^ 2 = if t ≤ w i ↔ t ≤ w j then 0 else ‖X i j‖ ^ 2 := by
    simp [norm_lie_coordProj_apply, ite_pow]
  simp only [frobenius_norm_sq_eq_sum, h_entry, (Ioc a b).sum_comm]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by simp [sum_ite, ← h_card]

/-- If the entries of `w` lie in `[a, b]`, the projections `coordProj (t ≤ w ·)` to the coordinates
`{i | t ≤ w i}`, `a < t ≤ b`, add up to `diag w - a`; this is the resulting identity for their
traces against `X`. -/
lemma sum_trace_coordProj_mul (hw : ∀ i : n, a ≤ w i ∧ w i ≤ b) (X : Matrix n n ℂ) :
    ∑ t ∈ Ioc a b, (coordProj (t ≤ w ·) * X).trace = (intDiagonal w * X).trace - a * X.trace := by
  have h_card (i : n) : (#{t ∈ Ioc a b | t ≤ w i} : ℤ) = w i - a := by
    rw [show {t ∈ Ioc a b | t ≤ w i} = Ioc a (w i) by grind, Int.card_Ioc,
      Int.toNat_of_nonneg (sub_nonneg.2 (hw i).1)]
  simp only [trace, diag_apply, coordProj, diagonal_mul, (Ioc a b).sum_comm, mul_sum,
    ← sum_sub_distrib, ← sub_mul]
  exact sum_congr rfl fun i _ ↦ by simp [sum_ite, ← Int.cast_sub, ← h_card]

/-- An element of `K = maxCompactU ε` is a unitary matrix. -/
lemma maxCompactU_conjTranspose_mul_self (k : maxCompactU ε) :
    (k : Matrix n n ℂ)ᴴ * (k : Matrix n n ℂ) = 1 :=
  Matrix.mem_unitaryGroup_iff'.1 (U_one_mem_unitaryGroup ⟨_, k.property⟩)

/-- On `K = maxCompactU ε`, the product of principal minors `weightMinors w` decays like a Gaussian:
its squared modulus at `k` is at most `exp (-Q_w (k) / 2)`. -/
lemma norm_weightMinors_sq_le_exp (w : n → ℤ) (k : maxCompactU ε) :
    ‖weightMinors w k‖ ^ 2 ≤ Real.exp (-(gapWeightedNormSq w k / 2)) := by
  -- Multiply the bounds for one minor, and use that `det k` has modulus one.
  let M : ℤ := ∑ j : n, |w j|
  have hw : ∀ i : n, -M ≤ w i ∧ w i ≤ M := neg_sum_abs_le_and_le_sum_abs w
  calc ‖weightMinors w k‖ ^ 2
      = ∏ t ∈ Ioc (-M) M, ‖principalMinor (k : Matrix n n ℂ) (t ≤ w ·)‖ ^ 2 := by
        rw [weightMinors_eq_det_zpow_mul_prod (GeneralLinearGroup.det_ne_zero _) _ _ hw, norm_mul,
          norm_zpow, U.norm_det, _root_.one_zpow, one_mul, norm_prod, prod_pow]
    _ ≤ ∏ t ∈ Ioc (-M) M, Real.exp (-(‖⁅coordProj (t ≤ w ·), (k : Matrix n n ℂ)⁆‖ ^ 2 / 2)) :=
        prod_le_prod₀ (fun t _ ↦ sq_nonneg _) fun t _ ↦
          norm_principalMinor_sq_le_exp _ (maxCompactU_conjTranspose_mul_self k)
    _ = Real.exp (-(gapWeightedNormSq w k / 2)) := by
        rw [← Real.exp_sum, sum_neg_distrib, ← sum_div, sum_norm_lie_coordProj_sq hw]

/-- The entries of `paramAddRho l - l.lowestKType = 2 ρ_c` (written `twoRho l (ε · = ε ·)`) are at
most `n` in modulus, so the traces of `Z` against the diagonal matrices of the two weights differ
by at most `n ^ 2 ‖Z‖` (Frobenius norm). -/
lemma norm_trace_paramAddRho_sub_trace_lowestKType_le (l : HCParam ε) (Z : Matrix n n ℂ) :
    ‖(intDiagonal (paramAddRho l) * Z).trace - (intDiagonal l.lowestKType * Z).trace‖ ≤
      card n ^ 2 * ‖Z‖ := by
  have h_rho (i : n) : ‖(twoRho l (ε · = ε ·) i : ℂ)‖ ≤ card n :=
    (norm_intCast _).trans_le (mod_cast abs_twoRho_le (ε · = ε ·) i l)
  calc _ = ‖∑ i : n, twoRho l (ε · = ε ·) i * Z i i‖ := by simp [trace, lowestKType, sub_mul]
    _ ≤ ∑ _i : n, card n * ‖Z‖ :=
        norm_sum_le_of_le _ fun i _ ↦ norm_mul_le_of_le (h_rho i) (norm_apply_le_frobenius_norm ..)
    _ = card n ^ 2 * ‖Z‖ := by simp [sq, mul_assoc]

/-- For `k ∈ K = maxCompactU ε` we have `Q_{-λ^ρ} (k) ≤ Q_μ (k) + 2 n ^ 2`. This holds because
`λ^ρ - μ = 2ρ_c` has entries at most `n` in modulus and `‖k‖ ^ 2 = n` (Frobenius norm). Here `2ρ_c`
is the sum of the compact roots (`ε i = ε j`) positive for `l`. -/
lemma gapWeightedNormSq_neg_paramAddRho_le (l : HCParam ε) (k : maxCompactU ε) :
    gapWeightedNormSq (-paramAddRho l) k ≤ gapWeightedNormSq l.lowestKType k + 2 * card n ^ 2 := by
  have h_norm : ‖(k : Matrix n n ℂ)‖ ^ 2 = card n := by
    rw [← ofReal_inj, ← trace_star_mul_self_eq_norm_sq, maxCompactU_conjTranspose_mul_self,
      trace_one, ofReal_natCast]
  have h_diff (i j : n) : |(-paramAddRho l) i - (-paramAddRho l) j| ≤
      |l.lowestKType i - l.lowestKType j| + 2 * card n := by
    simp only [Pi.neg_apply, lowestKType]
    grind [abs_eq_max_neg, abs_twoRho_le (ε · = ε ·) i l, abs_twoRho_le (ε · = ε ·) j l]
  calc gapWeightedNormSq (-paramAddRho l) k
      ≤ ∑ i : n, ∑ j : n, (|l.lowestKType i - l.lowestKType j| + 2 * card n : ℤ) *
          ‖(k : Matrix n n ℂ) i j‖ ^ 2 :=
        sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦
          mul_le_mul_of_nonneg_right (mod_cast h_diff i j) (sq_nonneg _)
    _ = gapWeightedNormSq l.lowestKType k + 2 * card n * ‖(k : Matrix n n ℂ)‖ ^ 2 := by
        simp [gapWeightedNormSq, frobenius_norm_sq_eq_sum, add_mul, mul_sum, sum_add_distrib]
    _ = gapWeightedNormSq l.lowestKType k + 2 * card n ^ 2 := by rw [h_norm, mul_assoc, ← sq]

/-- Let `l = 2λ` be a parameter of gap `h` and let `g` in `USign ε` satisfy
`‖g - 1‖ ≤ δ ≤ 10 ^ (-12)` (Frobenius norm). Put `λ^ρ = paramAddRho l`, `μ = l.lowestKType`,
`Q_w (X) = ∑_{i, j} |w i - w j| |X i j| ^ 2` and `q = Q_{-λ^ρ} (g - 1) / 4`. Then
`l.dsCoeff g = l.flenstedJensen 1 y` for an invertible matrix `y` such that, for all
`k ∈ K = maxCompactU ε`, the product of principal minors `weightMinors (-λ^ρ) (kᴴ y k)` is
`exp (q - tr (μ logOneAdd (g - 1)) - r)` with `|r| ≤ 10 ^ 6 δ (q + Q_μ (k) + n ^ 2)`. -/
lemma exists_weightMinors_neg_paramAddRho_eq_cexp (hl : l.HasGap h) (g : USign ε)
    (hg : ‖(g : Matrix n n ℂ) - 1‖ ≤ δ) (hδ : δ ≤ 1e-12) :
    ∃ y : Matrix n n ℂ, l.dsCoeff g = l.flenstedJensen 1 y ∧ y.det ≠ 0 ∧
      ∀ k : maxCompactU ε, ∃ r : ℂ,
        weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * y * k) =
          cexp ((gapWeightedNormSq (-paramAddRho l) ((g : Matrix n n ℂ) - 1) / 4 : ℝ) -
            (intDiagonal l.lowestKType * logOneAdd ((g : Matrix n n ℂ) - 1)).trace - r) ∧
        ‖r‖ ≤ 10 ^ 6 * δ * (gapWeightedNormSq (-paramAddRho l) ((g : Matrix n n ℂ) - 1) / 4 +
          gapWeightedNormSq l.lowestKType k + card n ^ 2) := by
  have hδ_nonneg : 0 ≤ δ := (norm_nonneg _).trans hg
  have hg_half : ‖(g : Matrix n n ℂ) - 1‖ ≤ 2⁻¹ := by linarith
  obtain ⟨y, h_coeff, h_minor⟩ := exists_principalMinor_eq_exp hl g (by linarith)
  set X : Matrix n n ℂ := (g : Matrix n n ℂ) - 1
  set Z : Matrix n n ℂ := logOneAdd X
  set w : n → ℤ := -paramAddRho l
  have hZ_le : ‖Z‖ ≤ 2 * δ := (norm_logOneAdd_le hg_half).trans (by linarith)
  -- The sets `{i | t ≤ w i}` consist of lowest entries of `l`.
  have h_order (t : ℤ) (i j : n) (hi : t ≤ w i) (hj : ¬t ≤ w j) : l i < l j :=
    hl.paramAddRho_lt_iff.1 (neg_lt_neg_iff.1 ((not_le.1 hj).trans_le hi))
  -- For the set of all indices the formula for one minor gives the determinant.
  have h_det (k : maxCompactU ε) :
      ((k : Matrix n n ℂ)ᴴ * y * (k : Matrix n n ℂ)).det = cexp Z.trace := by
    simpa [principalMinor_of_forall, coordProj, lie_def, -det_mul] using (h_minor ⊤ · k)
  have hy : y.det ≠ 0 := fun h_zero ↦
    (h_det 1).trans_ne (exp_ne_zero _) (by simp [h_zero])
  refine ⟨y, h_coeff, hy, fun k ↦ ?_⟩
  -- Multiply the formulas for one minor over the sets `{i | t ≤ w i}`.
  choose r hr_eq hr_le using fun t : ℤ ↦ h_minor (t ≤ w ·) (h_order t) k
  let M : ℤ := ∑ j : n, |w j|
  have h_range : ∀ i : n, -M ≤ w i ∧ w i ≤ M := neg_sum_abs_le_and_le_sum_abs w
  refine ⟨(intDiagonal (paramAddRho l) * Z).trace - (intDiagonal l.lowestKType * Z).trace -
    ∑ t ∈ Ioc (-M) M, r t, ?_, ?_⟩
  · have h_sq : (∑ t ∈ Ioc (-M) M, (‖⁅coordProj (t ≤ w ·), X⁆‖ : ℂ) ^ 2 / 4 : ℂ) =
        ((gapWeightedNormSq w X / 4 : ℝ) : ℂ) := by
      rw [← sum_norm_lie_coordProj_sq h_range X]
      push_cast
      rw [sum_div]
    have h_prod : ∏ t ∈ Ioc (-M) M,
        principalMinor ((k : Matrix n n ℂ)ᴴ * y * (k : Matrix n n ℂ)) (t ≤ w ·) =
          cexp ((intDiagonal w * Z).trace + M * Z.trace + (gapWeightedNormSq w X / 4 : ℝ) +
            ∑ t ∈ Ioc (-M) M, r t) := by
      rw [prod_congr rfl fun t _ ↦ hr_eq t, ← exp_sum, sum_add_distrib, sum_add_distrib, h_sq,
        sum_trace_coordProj_mul h_range, Int.cast_neg, neg_mul, sub_neg_eq_add]
    have h_neg : (intDiagonal w * Z).trace = -(intDiagonal (paramAddRho l) * Z).trace := by
      simp [w, trace]
    rw [weightMinors_eq_det_zpow_mul_prod ((h_det k).trans_ne (exp_ne_zero _)) _ _ h_range, h_det,
      h_prod, ← exp_intCast_mul, ← exp_add, Int.cast_neg, h_neg]
    exact congrArg cexp (by ring)
  · have h_sum : ‖∑ t ∈ Ioc (-M) M, r t‖ ≤
        200000 * ‖X‖ * (gapWeightedNormSq w X + gapWeightedNormSq w k) := by
      refine (norm_sum_le_of_le _ fun t _ ↦ hr_le t).trans_eq ?_
      simp only [← mul_sum, sum_add_distrib, sum_norm_lie_coordProj_sq h_range]
    have h_k : gapWeightedNormSq w k ≤ gapWeightedNormSq l.lowestKType k + 2 * card n ^ 2 :=
      gapWeightedNormSq_neg_paramAddRho_le l k
    calc ‖(intDiagonal (paramAddRho l) * Z).trace - (intDiagonal l.lowestKType * Z).trace -
          ∑ t ∈ Ioc (-M) M, r t‖
        ≤ ‖(intDiagonal (paramAddRho l) * Z).trace - (intDiagonal l.lowestKType * Z).trace‖ +
            ‖∑ t ∈ Ioc (-M) M, r t‖ := norm_sub_le _ _
      _ ≤ card n ^ 2 * (2 * δ) + 200000 * δ *
            (gapWeightedNormSq w X + (gapWeightedNormSq l.lowestKType k + 2 * card n ^ 2)) := by
          grw [norm_trace_paramAddRho_sub_trace_lowestKType_le, hZ_le, h_sum, hg, h_k]
      _ ≤ 10 ^ 6 * δ *
            (gapWeightedNormSq w X / 4 + gapWeightedNormSq l.lowestKType k + card n ^ 2) := by
          nlinarith [gapWeightedNormSq_nonneg l.lowestKType k, sq_nonneg (card n : ℝ),
            gapWeightedNormSq_nonneg w X]

/-- Let `y` be invertible. Flensted-Jensen's integral `l.flenstedJensen g y` at the identity matrix
`g = 1` is the mean over `k ∈ K = maxCompactU ε` of `|weightMinors μ k| ^ 2 / weightMinors
(-paramAddRho l) (kᴴ y k)`, divided by the mean `μ.kTypeNormSq` of `|weightMinors μ k| ^ 2`. Suppose
that the denominator of the integrand is `exp (q - θ - r k)` for all `k ∈ K`, with `q` real and `θ`,
`r k` complex. Then `l.flenstedJensen 1 y / exp θ` differs from `exp (-q)` by the mean over `K` of
`|weightMinors μ k| ^ 2 exp (-q) (exp (r k) - 1)`, divided by `μ.kTypeNormSq`. -/
lemma flenstedJensen_div_exp_sub {y : Matrix n n ℂ} {θ : ℂ} {r : maxCompactU ε → ℂ} (hy : y.det ≠ 0)
    (h_denom : ∀ k : maxCompactU ε,
      weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * y * k) = cexp (q - θ - r k)) :
    l.flenstedJensen 1 y / cexp θ - Real.exp (-q) =
      (∫ k : maxCompactU ε,
          (‖weightMinors l.lowestKType k‖ ^ 2 * Real.exp (-q) : ℝ) * (cexp (r k) - 1) ∂haarK ε) /
        l.lowestKType.kTypeNormSq := by
  let F (k : maxCompactU ε) : ℂ :=
    weightMinors l.lowestKType (1 * k) * conj (weightMinors l.lowestKType k) /
      weightMinors (-paramAddRho l) ((k : Matrix n n ℂ)ᴴ * y * k)
  have h_def : l.flenstedJensen 1 y =
      (∫ k : maxCompactU ε, F k ∂haarK ε) / l.lowestKType.kTypeNormSq := rfl
  have hF : Integrable F (haarK ε) := integrable_of_compactSpace <| by
    fun_prop (disch := simp [h_denom, hy, GeneralLinearGroup.det_ne_zero])
  have h_point (k : maxCompactU ε) :
      (‖weightMinors l.lowestKType k‖ ^ 2 * Real.exp (-q) : ℝ) * (cexp (r k) - 1) =
        F k / cexp θ - (‖weightMinors l.lowestKType k‖ ^ 2 : ℝ) * Real.exp (-q) := by
    simp only [F, h_denom, one_mul, mul_conj', exp_sub, ofReal_mul, ofReal_pow, ofReal_exp,
      ofReal_neg, Complex.exp_neg]
    field_simp
  have h_sq : Integrable (fun k : maxCompactU ε ↦
      ((‖weightMinors l.lowestKType k‖ ^ 2 : ℝ) * Real.exp (-q) : ℂ)) (haarK ε) :=
    integrable_of_compactSpace (by fun_prop (disch := simp [GeneralLinearGroup.det_ne_zero]))
  have h_int : ∫ k : maxCompactU ε,
      (‖weightMinors l.lowestKType k‖ ^ 2 * Real.exp (-q) : ℝ) * (cexp (r k) - 1) ∂haarK ε =
        (∫ k : maxCompactU ε, F k ∂haarK ε) / cexp θ -
          l.lowestKType.kTypeNormSq * Real.exp (-q) := by
    simp only [h_point]
    rw [integral_sub (hF.div_const _) h_sq, integral_div, integral_mul_const,
      integral_complex_ofReal]
  rw [h_int, h_def, sub_div,
    mul_div_cancel_left₀ _ (ofReal_ne_zero.2 (kTypeNormSq_pos l.lowestKType).ne'), div_right_comm]

/-- Let `δ T ≤ 10 ^ (-12)`, `T ≥ 1`, `0 ≤ N ≤ T`, `0 ≤ m ≤ exp (-Q / 2)` and
`|r| ≤ 10 ^ 6 δ (q + Q + N)`, with `δ`, `q`, `Q` nonnegative. Then `m exp (-q) |exp r - 1|` is at
most `exp (-q) m / 10 + exp (-5100 T)`: either `r` is small, or `m exp (-q)` is. -/
lemma mul_norm_exp_sub_one_le {m Q N : ℝ} {r : ℂ} (hT : 1 ≤ T) (hδ_nonneg : 0 ≤ δ)
    (hδT : δ * T ≤ 1e-12) (hq : 0 ≤ q) (hQ : 0 ≤ Q) (hN_nonneg : 0 ≤ N) (hN : N ≤ T)
    (hm_nonneg : 0 ≤ m) (hm : m ≤ Real.exp (-(Q / 2))) (hr : ‖r‖ ≤ 10 ^ 6 * δ * (q + Q + N)) :
    m * Real.exp (-q) * ‖cexp r - 1‖ ≤ Real.exp (-q) / 10 * m + Real.exp (-(5100 * T)) := by
  set s : ℝ := q + Q + N with hs
  rcases le_total s (50000 * T) with h_small | h_large
  · have hr_small : ‖r‖ ≤ 1 / 20 := by linarith [mul_le_mul_of_nonneg_left h_small hδ_nonneg]
    calc m * Real.exp (-q) * ‖cexp r - 1‖ ≤ m * Real.exp (-q) * (2 * (1 / 20)) := by
          grw [Complex.norm_exp_sub_one_le (hr_small.trans (by norm_num)), hr_small]
      _ ≤ _ := by linarith [Real.exp_nonneg (-(5100 * T))]
  · have hδ_le : δ ≤ 1e-12 := (le_mul_of_one_le_right hδ_nonneg hT).trans hδT
    have hr_quarter : ‖r‖ ≤ s / 4 := by
      linarith [mul_le_mul_of_nonneg_right hδ_le (show 0 ≤ s by positivity)]
    have h_exp : ‖cexp r - 1‖ ≤ Real.exp ‖r‖ - 1 := by
      simpa using r.norm_exp_sub_sum_le_exp_norm_sub_sum 1
    calc m * Real.exp (-q) * ‖cexp r - 1‖
        ≤ Real.exp (-(Q / 2)) * Real.exp (-q) * Real.exp (s / 4) := by
          grw [hm, h_exp, hr_quarter, sub_one_lt]
      _ ≤ Real.exp (-(5100 * T)) := by
          rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
          linarith
      _ ≤ Real.exp (-q) / 10 * m + Real.exp (-(5100 * T)) := le_add_of_nonneg_left (by positivity)

/-- **Gaussian shape.** Let the parameter `l = 2λ` have gap `500 n ^ 3 + A` and `|l i| ≤ L`, let `T`
be at least `1`, `n ^ 2` and `n ^ 2 log (n + L + 1)`, and let `δ T ≤ 10 ^ (-12)`. For `g` in the
unitary group `USign ε` of the form `diag ε` with `‖g - 1‖ ≤ δ` (Frobenius norm), the discrete
series coefficient `l.dsCoeff g`, divided by the phase `exp (tr μ log g)`, is within
`ϱ / 10 + exp (-100 T)` of a number `ϱ ∈ [0, 1]`; the proof takes a Gaussian in `g - 1` for `ϱ`. -/
lemma exists_norm_dsCoeff_div_cexp_sub_le [Nonempty n] (hl : l.HasLargeGap A)
    (hL : ∀ i : n, |l i| ≤ L)
    {g : USign ε} (hg : ‖(g : Matrix n n ℂ) - 1‖ ≤ δ) (hT : 1 ≤ T) (hT_card : card n ^ 2 ≤ T)
    (hT_log : card n ^ 2 * Real.log (card n + L + 1) ≤ T) (hδT : δ * T ≤ 1e-12) :
    ∃ ϱ ∈ Set.Icc (0 : ℝ) 1,
      ‖l.dsCoeff g / cexp (intDiagonal l.lowestKType * logOneAdd ((g : Matrix n n ℂ) - 1)).trace -
          ϱ‖ ≤ ϱ / 10 + Real.exp (-100 * T) := by
  -- Take `ϱ = exp (-q)` with `q = gapWeightedNormSq (-λ^ρ) (g - 1) / 4`, where
  -- `λ^ρ = paramAddRho l`.
  have hδ_nonneg : 0 ≤ δ := (norm_nonneg _).trans hg
  have hδ_le : δ ≤ 1e-12 := (le_mul_of_one_le_right hδ_nonneg hT).trans hδT
  set Z : Matrix n n ℂ := logOneAdd ((g : Matrix n n ℂ) - 1)
  set q : ℝ := gapWeightedNormSq (-paramAddRho l) ((g : Matrix n n ℂ) - 1) / 4 with hq
  have hq_nonneg : 0 ≤ q := by positivity
  refine ⟨Real.exp (-q), ⟨Real.exp_nonneg _, Real.exp_le_one_iff.2 (by linarith)⟩, ?_⟩
  -- Step 1: a mean over `K`, at a matrix `y` whose products of minors are known.
  obtain ⟨y, h_dsCoeff_eq, hy, h_denom⟩ := exists_weightMinors_neg_paramAddRho_eq_cexp hl g hg hδ_le
  choose r hr_eq hr_le using h_denom
  have h_mean : l.dsCoeff g / cexp (intDiagonal l.lowestKType * Z).trace - Real.exp (-q) =
      (∫ k : maxCompactU ε,
          (‖weightMinors l.lowestKType k‖ ^ 2 * Real.exp (-q) : ℝ) * (cexp (r k) - 1) ∂haarK ε) /
        l.lowestKType.kTypeNormSq := by
    rw [h_dsCoeff_eq, flenstedJensen_div_exp_sub hy hr_eq]
  -- Step 2: the integrand is small where `r k` is not.
  have h_point (k : maxCompactU ε) :
      ‖(‖weightMinors l.lowestKType k‖ ^ 2 * Real.exp (-q) : ℝ) * (cexp (r k) - 1)‖ ≤
        Real.exp (-q) / 10 * ‖weightMinors l.lowestKType k‖ ^ 2 + Real.exp (-(5100 * T)) := by
    rw [norm_mul, Complex.norm_of_nonneg (by positivity)]
    exact mul_norm_exp_sub_one_le hT hδ_nonneg hδT hq_nonneg (gapWeightedNormSq_nonneg _ _)
      (sq_nonneg _) hT_card (sq_nonneg _) (norm_weightMinors_sq_le_exp l.lowestKType k)
      (hr_le k)
  -- Integrate this bound, and use the lower bound for `l.lowestKType.kTypeNormSq`.
  have h_sq : Integrable (fun k : maxCompactU ε ↦
      Real.exp (-q) / 10 * ‖weightMinors l.lowestKType k‖ ^ 2) (haarK ε) :=
    integrable_of_compactSpace (by fun_prop (disch := simp [GeneralLinearGroup.det_ne_zero]))
  have h_pos : 0 < l.lowestKType.kTypeNormSq := kTypeNormSq_pos l.lowestKType
  rw [h_mean, norm_div, Complex.norm_of_nonneg h_pos.le, div_le_iff₀ h_pos]
  calc _ ≤ ∫ k : maxCompactU ε, Real.exp (-q) / 10 * ‖weightMinors l.lowestKType k‖ ^ 2 +
          Real.exp (-(5100 * T)) ∂haarK ε :=
        norm_integral_le_of_norm_le (h_sq.fun_add (integrable_const _)) (.of_forall h_point)
    _ = Real.exp (-q) / 10 * l.lowestKType.kTypeNormSq +
          Real.exp (-100 * T) * Real.exp (-(5000 * T)) := by
        rw [← Real.exp_add, show -100 * T + -(5000 * T) = -(5100 * T) by ring]
        simp [integral_add h_sq (integrable_const _), integral_const_mul]
    _ ≤ (Real.exp (-q) / 10 + Real.exp (-100 * T)) * l.lowestKType.kTypeNormSq := by
        grw [exp_neg_le_kTypeNormSq hl hL hT hT_card hT_log, add_mul]

end New.DiscreteSeries
