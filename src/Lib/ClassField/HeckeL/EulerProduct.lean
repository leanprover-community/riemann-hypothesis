module

import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Finset.Functor
import Mathlib.RingTheory.Ideal.Int
import TauCeti.NumberTheory.RamificationInertia.Tower
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.BoundedCoefficients
import TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.PrimeDensity
public import Lib.ClassField.Places.Ideles
import Lib.Adelic.Adeles.StrongApproximation

/-!
# Euler products over primes of a number field

This file treats Hecke characters of a number field `K`, given by their finite part `ψ`, a
character of the finite ideles `(𝔸f K)ˣ`, and Euler products with coefficients `a v`, `‖a v‖ ≤ 1`,
over the primes `v` of `K`, as functions of a real variable `s > 1`.

* `New.IsHeckeOfType`: `ψ` has open kernel and `ψ x * ∏ w, (Φ w x / ‖Φ w x‖) ^ n w = 1` on `Kˣ`;
  `New.heckeCoeff ψ S` is the value of `ψ` at the local idele of the chosen uniformiser for `v ∉ S`,
  and `0` for `v ∈ S`.
* `New.eulerProd`: the product `∏ (1 - a v * q ^ (-s))⁻¹`, defined as `exp` of a sum of logarithms;
  `New.hasProd_eulerProd` says that it is the limit of the partial products, and
  `New.primeEulerProduct_eq_eulerProd` that for `s > 1` it is Tau Ceti's
  `TauCeti.primeEulerProduct`.
* `New.hasSum_eulerProd`: for a completely multiplicative function on ideals, of modulus at most
  `1`, the product equals the Dirichlet series.
* `New.frequently_prime_q`: infinitely many primes have degree one.

Densities at the primes of degree one are Tau Ceti's `TauCeti.HasPrimeDensity`. Here
`New.FinPlace K` is the type of nonzero primes of `𝓞 K`, `q = v.q` is the absolute norm of `v`, and
degree one means that `q` is prime.

Notions from other files:
* `New.locIdele v`: sends `x ∈ K_vˣ` to the finite idele with component `x` at `v` and `1`
  elsewhere; `New.uniformizer v` is a chosen uniformiser of the completion `K_v`.
* `Φ w` (class `New.PlaceEmbedding`): a chosen complex embedding of `K` inducing the infinite
  place `w`.

## Relation to the literature

Known; see `Lib.ClassField.HeckeL.ContinuationAtOne` for sources.
-/

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain.HeightOneSpectrum Filter Topology Complex Finset Ideal Module
  ContinuousAt Set

namespace New

variable {K : Type*} [Field K] [NumberField K]
  (ψ : (𝔸f K)ˣ →* ℂˣ) (n : InfinitePlace K → ℤ) (a : FinPlace K → ℂ) {s : ℝ}

/-- The character `ψ` of the finite ideles is the finite part of a Hecke character of type `n`,
where `n` gives an integer exponent `n w` to each infinite place `w`: the kernel of `ψ` is open,
and `ψ x * ∏ w, (Φ w x / ‖Φ w x‖) ^ n w = 1` for `x ∈ Kˣ`, with `Φ w` the chosen complex embedding
inducing `w` and `x` read as a finite idele by the diagonal embedding. -/
def IsHeckeOfType [PlaceEmbedding K] : Prop :=
  ψ.ker.IsOpen ∧
  ∀ x : Kˣ, ψ (principalIdele x) * ∏ w : InfinitePlace K, (Φ w x.val / ‖Φ w x‖) ^ n w = 1

/-- `ψ` is unramified at the finite place `v`: it is `1` on the units of the completion `K_v` of
valuation `1`, read as finite ideles by `New.locIdele v`. -/
def CharUnramifiedAt (v : FinPlace K) : Prop :=
  ∀ u : (LocField v)ˣ, Valued.v u.val = 1 → ψ (locIdele v u) = 1

/-- The function on finite places sending `v ∉ S` to the value of `ψ` at the local idele of the
chosen uniformiser `uniformizer v` of `K_v`, and `v ∈ S` to `0`. -/
def heckeCoeff (S : Set (FinPlace K)) : FinPlace K → ℂ :=
  indicator Sᶜ fun v : FinPlace K ↦ (ψ (locIdele v (uniformizer v))).val

/-- The Euler product `∏ (1 - a v * q ^ (-s))⁻¹` over the primes `v` of `K`, with `q = v.q` the norm
of `v`, as a function of real `s`. It is written `exp (-∑' v, log (1 + -(a v * q ^ (-s))))`, in the
form `log (1 + w)` of Mathlib's bounds for the logarithm. The value at `s` is the limit of this
expression at `s` within `(1, ∞)`: for `‖a v‖ ≤ 1` and `s > 1` it is the expression itself
(`New.eulerProd_eq_exp`, `New.hasProd_eulerProd`), at `s = 1` it is the limit from the right if that
exists, and for `s < 1` it has no meaning. With `a = heckeCoeff ψ S` and `ψ` unramified at every
`v ∉ S` it is the Euler product of the Hecke `L`-function of `ψ` without the factors at `S`. -/
def eulerProd : ℝ → ℂ :=
  extendFrom (Set.Ioi 1) fun s : ℝ ↦
    exp (-∑' v : FinPlace K, Complex.log (1 + -(a v * v.q ^ (-s : ℂ))))

/-- For a finite set `u` of primes of `K`, the sum over `v ∈ u` of `1 / p ^ 2`, with `p` the least
prime factor of the norm `v.q`, is at most the degree `[K : ℚ]`. -/
lemma sum_inv_minFac_sq_le_finrank (u : Finset (FinPlace K)) :
    ∑ v ∈ u, (v.q.minFac ^ 2 : ℝ)⁻¹ ≤ finrank ℚ K := by
  -- Group the primes by the least factor `p` of their norm. The primes of one group lie over the
  -- same rational prime, so there are at most `[K : ℚ]` of them, and `∑ 1 / p ^ 2 ≤ 1`.
  have h_minFac (v : FinPlace K) : v.q.minFac = absNorm (v.asIdeal.under ℤ) := by
    -- The norm of `v` is a positive power of the rational prime below `v`.
    simp [← (v.asIdeal.under ℤ).absNorm_pow_inertiaDeg v.asIdeal,
      (Nat.absNorm_under_prime _).pow_minFac (inertiaDeg_pos ..).ne']
  have h_group (v : FinPlace K) : #{w ∈ u | w.q.minFac = v.q.minFac} ≤ finrank ℚ K := by
    grw [← RingOfIntegers.rank,
      ← TauCeti.RamificationInertia.ncard_primesOver_le_finrank (v.asIdeal.under ℤ),
      ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn _ (fun w hw ↦ ⟨w.isPrime, ⟨ext ?_⟩⟩) asIdeal_injective.injOn
      (IsDedekindDomain.primesOver_finite ..)
    -- `w` lies over the prime below `v`: two ideals of `ℤ` with the same norm are equal.
    simp_all [Int.cast_mem_ideal_iff]
  -- The least prime factors lie in `(1, N)` for `N` one more than their maximum.
  set N : ℕ := u.sup fun v : FinPlace K ↦ v.q.minFac + 1
  have h_range : u.image (fun v : FinPlace K ↦ v.q.minFac) ⊆ Ioo 1 N :=
    image_subset_iff.mpr fun v hv ↦ mem_Ioo.mpr ⟨(Nat.minFac_prime v.one_lt_q.ne').one_lt,
      le_sup (f := fun w : FinPlace K ↦ w.q.minFac + 1) hv⟩
  calc
    _ = ∑ p ∈ u.image (fun v : FinPlace K ↦ v.q.minFac),
          #{w ∈ u | w.q.minFac = p} • (p ^ 2 : ℝ)⁻¹ :=
      sum_comp (fun p : ℕ ↦ (p ^ 2 : ℝ)⁻¹) _
    _ ≤ ∑ p ∈ u.image (fun v : FinPlace K ↦ v.q.minFac), finrank ℚ K • (p ^ 2 : ℝ)⁻¹ :=
      sum_le_sum (forall_mem_image.mpr fun v _ ↦ nsmul_le_nsmul_left (by positivity) (h_group v))
    _ ≤ finrank ℚ K • (2 / ((1 : ℕ) + 1) : ℝ) := by
      -- `∑ 1 / p ^ 2 ≤ 2 / (1 + 1)` over `1 < p < N`.
      grw [← smul_sum, h_range, sum_Ioo_inv_sq_le]
    _ = finrank ℚ K := by norm_num

variable {a}

/-- For real `s > 1` the series of `N(I) ^ (-s)` over all ideals `I` of `𝓞 K` converges, with
`N(I) = absNorm I` (the zero ideal has norm `0` and term `0`). -/
lemma summable_absNorm_rpow (hs : 1 < s) :
    Summable fun I : Ideal (𝓞 K) ↦ (absNorm I : ℝ) ^ (-s) := by
  refine (summable_subtype_and_compl (s := (nonZeroDivisors (Ideal (𝓞 K)) : Set _))).1
    ⟨(TauCeti.summable_absNorm_rpow_ideal_iff (K := K)).mpr hs, ?_⟩
  have h_fin : ((nonZeroDivisors (Ideal (𝓞 K)) : Set (Ideal (𝓞 K)))ᶜ).Finite :=
    (Set.finite_singleton (⊥ : Ideal (𝓞 K))).subset fun I hI ↦
      by_contra fun hne ↦ hI (mem_nonZeroDivisors_of_ne_zero hne)
  exact h_fin.summable (fun I ↦ (absNorm I : ℝ) ^ (-s))

/-- For `‖a v‖ ≤ 1` and real `t ≤ s`, the term `-(a v * q ^ (-s))` of the Euler factor has norm at
most `q ^ (-t)`, with `q = v.q` the norm of the prime `v`. -/
private lemma norm_neg_mul_cpow_le_rpow_of_norm_le_one (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1) {t : ℝ}
    (ht : t ≤ s) (v : FinPlace K) : ‖-(a v * v.q ^ (-s : ℂ))‖ ≤ (v.q : ℝ) ^ (-t) := by
  grw [norm_neg, norm_mul_le, ha, one_mul, norm_cpow_le, ht]
  · -- `‖q ^ (-s)‖ = q ^ (-s)` for the positive real `q`.
    simp
  · exact mod_cast v.one_lt_q.le

/-- For `‖a v‖ ≤ 1` and real `s ≥ 1`, the term `-(a v * q ^ (-s))` has norm at most `1 / q`. -/
private lemma norm_neg_mul_cpow_le_inv_of_norm_le_one (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1)
    (hs : 1 ≤ s) (v : FinPlace K) : ‖-(a v * v.q ^ (-s : ℂ))‖ ≤ (v.q : ℝ)⁻¹ := by
  simpa [Real.rpow_neg] using norm_neg_mul_cpow_le_rpow_of_norm_le_one ha hs v

/-- For `‖a v‖ ≤ 1` and real `1 ≤ σ ≤ s`, the logarithm of the Euler factor `1 - a v * q ^ (-s)` has
norm at most `2 * q ^ (-σ)`. -/
lemma norm_log_one_add_neg_mul_cpow_le_of_norm_le_one (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1)
    {σ : ℝ} (hσ : 1 ≤ σ) (hσs : σ ≤ s) (v : FinPlace K) :
    ‖Complex.log (1 + -(a v * v.q ^ (-s : ℂ)))‖ ≤ 2 * v.q ^ (-σ) := by
  set w : ℂ := -(a v * v.q ^ (-s : ℂ))
  have h_inv : ‖w‖ ≤ (v.q : ℝ)⁻¹ := norm_neg_mul_cpow_le_inv_of_norm_le_one ha (hσ.trans hσs) v
  have h_half : ‖w‖ ≤ 1 / 2 := by
    rw [one_div]
    exact h_inv.trans (inv_anti₀ two_pos (mod_cast v.one_lt_q))
  exact (norm_log_one_add_half_le_self h_half).trans
    (mul_le_mul (by norm_num) (norm_neg_mul_cpow_le_rpow_of_norm_le_one ha hσs v)
      (norm_nonneg w) zero_le_two)

/-- For `‖a v‖ ≤ 1` and real `s ≥ 1`, the Euler factor `1 - a v * q ^ (-s)` lies in the slit plane,
where the logarithm is continuous. -/
lemma one_add_neg_mul_cpow_mem_slitPlane_of_norm_le_one (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1)
    (hs : 1 ≤ s) (v : FinPlace K) : 1 + -(a v * v.q ^ (-s : ℂ)) ∈ slitPlane :=
  mem_slitPlane_of_norm_lt_one ((norm_neg_mul_cpow_le_inv_of_norm_le_one ha hs v).trans_lt
    (inv_lt_one_of_one_lt₀ (mod_cast v.one_lt_q)))

/-- If `‖a v‖ ≤ 1` and `s > 1`, the series `∑ v, log (1 - a v * q ^ (-s))` converges, its sum is
continuous at `s`, and `New.eulerProd a s` is the exponential of minus this sum. -/
@[local simp]
lemma eulerProd_eq_exp (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1) (hs : 1 < s) :
    let logFactor (s : ℝ) (v : FinPlace K) : ℂ := Complex.log (1 + -(a v * v.q ^ (-s : ℂ)))
    eulerProd a s = exp (-∑' v : FinPlace K, logFactor s v) ∧
    Summable (logFactor s) ∧
    ContinuousAt (fun t : ℝ ↦ -∑' v : FinPlace K, logFactor t v) s := by
  -- Fix `σ` between `1` and `s`. For `t ≥ σ` the logarithms are dominated by the convergent series
  -- `∑ 2 * q ^ (-σ)`, which gives summability and, by dominated convergence, continuity.
  intro logFactor
  obtain ⟨σ, hσ, hσs⟩ : ∃ σ : ℝ, 1 < σ ∧ σ < s := exists_between hs
  have h_sum : Summable fun v : FinPlace K ↦ 2 * (v.q : ℝ) ^ (-σ) :=
    ((summable_absNorm_rpow hσ).comp_injective asIdeal_injective).mul_left _
  have h_bound (t : ℝ) (ht : σ ≤ t) (v : FinPlace K) : ‖logFactor t v‖ ≤ 2 * (v.q : ℝ) ^ (-σ) :=
    norm_log_one_add_neg_mul_cpow_le_of_norm_le_one ha hσ.le ht v
  have h_term (v : FinPlace K) : ContinuousAt (fun t : ℝ ↦ logFactor t v) s :=
    ContinuousAt.clog (by fun_prop (disch := simp [IsDedekindDomain.HeightOneSpectrum.ne_bot]))
      (one_add_neg_mul_cpow_mem_slitPlane_of_norm_le_one ha hs.le v)
  have h_cont : ContinuousAt (fun t : ℝ ↦ -∑' v : FinPlace K, logFactor t v) s :=
    (tendsto_tsum_of_dominated_convergence h_sum h_term (.mono (Ici_mem_nhds hσs) h_bound)).neg
  -- The extension by continuity keeps the value at a point of continuity.
  exact ⟨extendFrom_eq (subset_closure hs) h_cont.cexp.continuousWithinAt.tendsto,
    h_sum.of_norm_bounded (h_bound s hσs.le), h_cont⟩

/-- For `‖a v‖ ≤ 1` and real `s > 1`, `New.eulerProd a s` is the exponential of minus the sum of
the logarithms of the Euler factors `1 - a v * q ^ (-s)`. -/
lemma eulerProd_eq_exp_neg_tsum_log_of_norm_le_one (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1) (hs : 1 < s) :
    eulerProd a s = exp (-∑' v : FinPlace K, Complex.log (1 + -(a v * v.q ^ (-s : ℂ)))) := by
  obtain ⟨h_eq, -, -⟩ := eulerProd_eq_exp ha hs
  exact h_eq

/-- For `‖a v‖ ≤ 1` and real `s > 1`, the logarithms of the Euler factors `1 - a v * q ^ (-s)` are
summable over the primes `v`. -/
lemma summable_log_one_add_neg_mul_cpow_of_norm_le_one (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1)
    (hs : 1 < s) : Summable fun v : FinPlace K ↦ Complex.log (1 + -(a v * v.q ^ (-s : ℂ))) := by
  obtain ⟨-, h_sum, -⟩ := eulerProd_eq_exp ha hs
  exact h_sum

/-- If `‖a v‖ ≤ 1` for all primes `v` of `K` and `s > 1` is real, the Euler product
`∏ v, (1 - a v * q ^ (-s))⁻¹` converges unconditionally to `New.eulerProd a s`. -/
lemma hasProd_eulerProd (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1) (hs : 1 < s) :
    HasProd (fun v : FinPlace K ↦ (1 - a v * v.q ^ (-s : ℂ))⁻¹) (eulerProd a s) := by
  have h_sum := (summable_log_one_add_neg_mul_cpow_of_norm_le_one ha hs).hasSum
  rw [eulerProd_eq_exp_neg_tsum_log_of_norm_le_one ha hs, exp_neg]
  -- The factor `1 - x` is written `1 + -x`, the form whose logarithms are summed.
  simp only [sub_eq_add_neg]
  exact (hasProd_of_hasSum_log (fun v ↦ slitPlane_ne_zero
    (one_add_neg_mul_cpow_mem_slitPlane_of_norm_le_one ha hs.le v)) h_sum).inv₀ (exp_ne_zero _)

/-- For `‖a v‖ ≤ 1` and real `s > 1`, Tau Ceti's Euler product `TauCeti.primeEulerProduct a s`
is `New.eulerProd a s`. -/
lemma primeEulerProduct_eq_eulerProd (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1) (hs : 1 < s) :
    TauCeti.primeEulerProduct a s = eulerProd a s := by
  rw [TauCeti.primeEulerProduct_def, ← (hasProd_eulerProd ha hs).tprod_eq]
  simp [div_eq_mul_inv, cpow_neg]

/-- For `‖a v‖ ≤ 1`, a finite set `Q` of primes and `P s = ∏ w ∈ Q, (1 - a w * q_w ^ (-s))`: `P` is
analytic at the real point `1`, `P 1 ≠ 0`, and for real `s > 1` setting the coefficients at `Q` to
zero multiplies the Euler product by `P s`. -/
lemma eulerProd_erase (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1) (Q : Finset (FinPlace K)) :
    let P (s : ℂ) : ℂ := ∏ w ∈ Q, (1 - a w * w.q ^ (-s))
    AnalyticAt ℝ (P ∘ ofReal) 1 ∧
    P 1 ≠ 0 ∧
    ∀ s > (1 : ℝ), eulerProd (indicator Qᶜ a) s = eulerProd a s * P s := by
  intro P
  have h_factor_ne {t : ℝ} (ht : 1 ≤ t) (w : FinPlace K) : 1 - a w * w.q ^ (-t : ℂ) ≠ 0 := by
    simpa [sub_eq_add_neg] using
      slitPlane_ne_zero (one_add_neg_mul_cpow_mem_slitPlane_of_norm_le_one ha ht w)
  have hP_analytic : AnalyticAt ℂ P 1 := by
    fun_prop (disch := simp [IsDedekindDomain.HeightOneSpectrum.ne_bot])
  have hP_one : P 1 ≠ 0 := prod_ne_zero_iff.mpr fun w _ ↦ by simpa using h_factor_ne le_rfl w
  refine ⟨(hP_analytic.restrictScalars (𝕜' := ℂ)).comp_of_eq (ofRealCLM.analyticAt 1) (by simp),
    hP_one, fun s hs ↦ ?_⟩
  -- The two convergent products have the same factors outside `Q`, so their values differ by
  -- the quotient of the finite products over `Q`.
  let g (v : FinPlace K) : ℂ := (1 - Set.indicator Qᶜ a v * v.q ^ (-s : ℂ))⁻¹
  have h_erased : HasProd g (eulerProd (Set.indicator Qᶜ a) s) :=
    hasProd_eulerProd (fun v ↦ (norm_indicator_le_norm_self a v).trans (ha v)) hs
  have h_congr : HasProd g (eulerProd a s *
      ((∏ w ∈ Q, g w) / ∏ w ∈ Q, (1 - a w * w.q ^ (-s : ℂ))⁻¹)) :=
    (hasProd_eulerProd ha hs).congr_cofinite₀ (fun w _ ↦ inv_ne_zero (h_factor_ne hs.le w))
      fun w hw ↦ by simp [g, hw]
  -- At `Q` the new factors are `1` and the old ones have product `(P s)⁻¹`.
  have h_g_one : ∀ w ∈ Q, g w = 1 := fun w hw ↦ by simp [g, hw]
  rw [h_erased.unique h_congr, prod_eq_one h_g_one, prod_inv_distrib, one_div, inv_inv]

open Real

/-- If `‖a v‖ ≤ 1` for all `v` and `s ≥ σ ≥ 2` are real, the Euler product with coefficients `a` is
nonzero at `s`, and the logarithm of its modulus has absolute value at most
`2 * [K : ℚ] * 2 ^ (2 - σ)`. -/
lemma eulerProd_ne_zero_and_abs_log_norm_le (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1) {σ : ℝ} (hσ : 2 ≤ σ)
    (hs : σ ≤ s) :
    eulerProd a s ≠ 0 ∧ |Real.log ‖eulerProd a s‖| ≤ 2 * finrank ℚ K * 2 ^ (2 - σ) := by
  have hs_one : 1 < s := by linarith
  have h_summable := summable_log_one_add_neg_mul_cpow_of_norm_le_one ha hs_one
  -- Each logarithm is at most `2 * q ^ (-σ) ≤ 2 * 2 ^ (2 - σ) / p ^ 2`, as `q ≥ 2` and `p ≤ q` for
  -- the least prime factor `p` of `q`.
  have h_term (v : FinPlace K) :
      ‖log (1 + -(a v * v.q ^ (-s : ℂ)))‖ ≤ 2 * 2 ^ (2 - σ) * (v.q.minFac ^ 2 : ℝ)⁻¹ := by
    have hq : (2 : ℝ) ≤ v.q := mod_cast v.one_lt_q
    have hp : 0 < v.q.minFac := v.q.minFac_pos
    calc _ ≤ 2 * (v.q : ℝ) ^ (-σ) :=
          norm_log_one_add_neg_mul_cpow_le_of_norm_le_one ha (by linarith) hs v
      _ = 2 * v.q ^ (2 - σ) * (v.q ^ 2 : ℝ)⁻¹ := by simp [rpow_sub, v.q_bounds, field, rpow_neg]
      _ ≤ _ := by
        grw [rpow_le_rpow_of_nonpos two_pos hq (sub_nonpos.mpr hσ), Nat.minFac_le v.one_lt_q.le]
  -- Sum over the primes, using `∑ p⁻² ≤ [K : ℚ]`.
  have h_sum : ‖∑' v, log (1 + -(a v * v.q ^ (-s : ℂ)))‖ ≤ 2 * finrank ℚ K * 2 ^ (2 - σ) := by
    refine le_of_tendsto' h_summable.hasSum.norm fun u ↦ ?_
    grw [norm_sum_le, h_term, ← Finset.mul_sum, sum_inv_minFac_sq_le_finrank u, mul_right_comm]
  -- The product is `exp (-z)` for the sum `z` of the logarithms: it is nonzero, and
  -- `|log ‖exp (-z)‖| = |re z| ≤ ‖z‖`.
  rw [eulerProd_eq_exp_neg_tsum_log_of_norm_le_one ha hs_one]
  refine ⟨exp_ne_zero _, ?_⟩
  set z : ℂ := ∑' v : FinPlace K, Complex.log (1 + -(a v * v.q ^ (-s : ℂ)))
  calc |Real.log ‖exp (-z)‖| = |z.re| := by rw [norm_exp, Real.log_exp, neg_re, abs_neg]
    _ ≤ ‖z‖ := abs_re_le_norm z
    _ ≤ 2 * finrank ℚ K * 2 ^ (2 - σ) := h_sum

/-- Euler product: for `χ` multiplicative on the ideals of `𝓞 K` with `‖χ I‖ ≤ 1` and real `s > 1`,
the series `∑ I, χ I * N(I) ^ (-s)` converges to the Euler product with coefficients `χ v`. -/
lemma hasSum_eulerProd (χ : Ideal (𝓞 K) →* ℂ) (hχ : ∀ I : Ideal (𝓞 K), ‖χ I‖ ≤ 1) (hs : 1 < s) :
    HasSum (fun I : Ideal (𝓞 K) ↦ χ I * I.absNorm ^ (-s : ℂ))
      (eulerProd (fun v : FinPlace K ↦ χ v.asIdeal) s) := by
  classical
  -- Sieve: multiplying the series by the factors `1 - χ v * N v ^ (-s)`, `v ∈ T`, removes the
  -- ideals divisible by a prime of `T`. As `T` grows only the term `1` of the unit ideal survives,
  -- so the sum of the series times the inverse of the Euler product is `1`.
  let t (I : Ideal (𝓞 K)) : ℂ := χ I * I.absNorm ^ (-s : ℂ)
  let sieved (T : Finset (FinPlace K)) (I : Ideal (𝓞 K)) : ℂ :=
    if ∀ v ∈ T, ¬v.asIdeal ∣ I then t I else 0
  have h_norm_le (I : Ideal (𝓞 K)) : ‖t I‖ ≤ (absNorm I : ℝ) ^ (-s) := by
    grw [norm_mul_le, hχ, norm_cpow_le]
    simp
  have h_summable : Summable t := (summable_absNorm_rpow hs).of_norm_bounded h_norm_le
  have h_sieve (T : Finset (FinPlace K)) :
      HasSum (sieved T) ((∑' I, t I) * ∏ v ∈ T, (1 - t v.asIdeal)) := by
    induction T using Finset.cons_induction with
    | empty => simpa [sieved] using h_summable.hasSum
    | cons v T hv ih =>
      -- The terms removed at `v` are those of the ideals `v * I`: they are `t v` times the old
      -- terms at `I`.
      let removed (I : Ideal (𝓞 K)) : ℂ := sieved T I - sieved (cons v T hv) I
      have h_mul (I : Ideal (𝓞 K)) : removed (v.asIdeal * I) = t v.asIdeal * sieved T I := by
        -- `t` is multiplicative; `v ∣ v * I`, and a prime `w ∈ T` (so `w ≠ v`) divides `v * I`
        -- if and only if it divides `I`.
        have h_t_mul : t (v.asIdeal * I) = t v.asIdeal * t I := by
          simp only [t, map_mul, Nat.cast_mul, natCast_mul_cpow]
          ring
        have h_cons_zero : sieved (cons v T hv) (v.asIdeal * I) = 0 :=
          ite_eq_right fun h ↦ h v (mem_cons_self v T) (dvd_mul_right v.asIdeal I)
        have h_iff : (∀ w ∈ T, ¬w.asIdeal ∣ v.asIdeal * I) ↔ ∀ w ∈ T, ¬w.asIdeal ∣ I := by
          refine forall₂_congr fun w hw ↦ ?_
          simp [(prime w).dvd_mul, prime_dvd_prime_iff_eq (prime w) (prime v),
            asIdeal_injective.ne (ne_of_mem_of_not_mem hw hv)]
        simp only [removed, h_cons_zero, sub_zero]
        simp only [sieved, h_iff, h_t_mul, mul_ite, mul_zero]
      have h_off : ∀ I ∉ Set.range fun J : Ideal (𝓞 K) ↦ v.asIdeal * J, removed I = 0 := by
        grind [dvd_def]
      have h_removed :
          HasSum removed (t v.asIdeal * ((∑' I, t I) * ∏ w ∈ T, (1 - t w.asIdeal))) :=
        ((mul_right_injective₀ v.ne_bot).hasSum_iff h_off).mp
          ((ih.mul_left (t v.asIdeal)).congr_fun h_mul)
      rw [prod_cons, mul_left_comm, one_sub_mul]
      exact (ih.sub h_removed).congr_fun fun I ↦ (sub_sub_self _ _).symm
  -- Termwise limit: a proper ideal lies in some prime, and is removed once `T` contains it.
  have h_term (I : Ideal (𝓞 K)) :
      Tendsto (fun T ↦ sieved T I) atTop (𝓝 (if I = ⊤ then 1 else 0)) := by
    split_ifs with hI
    · simp [sieved, t, hI, ← one_eq_top, (prime _).not_dvd_one]
    · obtain ⟨v, hI_le⟩ : ∃ v : FinPlace K, I ≤ v.asIdeal :=
        (ideal_ne_top_iff_exists (RingOfIntegers.not_isField K) I).mp hI
      have h_zero : ∀ T ≥ ({v} : Finset (FinPlace K)), sieved T I = 0 := by grind [dvd_iff_le]
      exact tendsto_atTop_of_eventually_const h_zero
  -- Dominated convergence: each sieved term is `t I` or `0`.
  have h_bound (T : Finset (FinPlace K)) (I : Ideal (𝓞 K)) : ‖sieved T I‖ ≤ ‖t I‖ := by
    grind [norm_zero]
  have h_lim_one : Tendsto (fun T : Finset (FinPlace K) ↦ (∑' I, t I) * ∏ v ∈ T, (1 - t v.asIdeal))
      atTop (𝓝 1) := by
    have h_dom := tendsto_tsum_of_dominated_convergence h_summable.norm h_term (.of_forall h_bound)
    rw [tsum_ite_eq] at h_dom
    exact h_dom.congr fun T ↦ (h_sieve T).tsum_eq
  -- The partial products of the factors `1 - t v` tend to the inverse of the Euler product.
  have h_lim_prod : HasProd (fun v : FinPlace K ↦ 1 - t v.asIdeal)
      (eulerProd (fun v : FinPlace K ↦ χ v.asIdeal) s)⁻¹ := by
    have h_ne : eulerProd (fun v : FinPlace K ↦ χ v.asIdeal) s ≠ 0 := by
      simp [eulerProd_eq_exp_neg_tsum_log_of_norm_le_one (fun v ↦ hχ v.asIdeal) hs]
    simpa only [inv_inv] using (hasProd_eulerProd (fun v ↦ hχ v.asIdeal) hs).inv₀ h_ne
  exact h_summable.hasSum_iff.mpr
    (eq_of_mul_inv_eq_one (tendsto_nhds_unique (h_lim_prod.const_mul _) h_lim_one))

/-- A number field `K` has infinitely many primes of degree one, that is, finite places `w` whose
absolute norm `w.q` is a prime number. -/
lemma frequently_prime_q : ∃ᶠ w : FinPlace K in cofinite, w.q.Prime :=
  frequently_cofinite_iff_infinite.2 TauCeti.infinite_setOf_prime_absNorm

end New

end
