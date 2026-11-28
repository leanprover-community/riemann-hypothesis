module

import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.TendstoOfTendstoExp
import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
import TauCeti.NumberTheory.ArithmeticDirichletSeries.DirichletDensity.PrimeDensity
import TauCeti.NumberTheory.ArithmeticDirichletSeries.ResidueDegree
public import Lib.ClassField.Places.Ideles

/-!
# Euler products over primes of a number field and densities at primes of degree one

This file treats Hecke characters of a number field `K`, given by their finite part `ψ`, a
character of the finite ideles `(𝔸f K)ˣ`, and Euler products with coefficients `a v`, `‖a v‖ ≤ 1`,
over the primes `v` of `K`, as functions of a real variable `s > 1`.

* `New.IsHeckeOfType`: `ψ` has open kernel and `ψ x * ∏ w, (Φ w x / ‖Φ w x‖) ^ n w = 1` on `Kˣ`;
  `New.heckeCoeff ψ S` is the value of `ψ` at the local idele of the chosen uniformiser for `v ∉ S`,
  and `0` for `v ∈ S`.
* `New.eulerProd`: the product `∏ (1 - a v * q ^ (-s))⁻¹`, defined as `exp` of a sum of logarithms;
  `New.hasProd_eulerProd` says that it is the limit of the partial products.
* `New.hasSum_eulerProd`: for a completely multiplicative function on ideals, of modulus at most
  `1`, the product equals the Dirichlet series.
* `New.HasPrimeDensity`: the Dirichlet mean of `a` over the primes of degree one. Densities are
  linear and monotone (`New.HasPrimeDensity.sum`, `New.HasPrimeDensity.re_le_re`).
* `New.hasPrimeDensity_of_tendsto`: the density is read off from the order of the pole or zero of
  the product at `1`.

Up to a bounded error, the logarithm of the product is the sum of `a v * q ^ (-s)` over the primes
of degree one (`New.norm_log_one_add_neg_mul_cpow_sub_ite_le_of_norm_le_one`,
`New.sum_inv_minFac_sq_le_finrank`). Here `New.FinPlace K` is the type of nonzero primes of `𝓞 K`,
`q = v.q` is the absolute norm of `v`, and degree one means that `q` is prime.

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
  (ψ : (𝔸f K)ˣ →* ℂˣ) (n : InfinitePlace K → ℤ) (a b : FinPlace K → ℂ) {s : ℝ}

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

/-- The Dirichlet mean of `a` over the primes of degree one (those of prime norm `q`) is `l`, with
a bounded error: for `s > 1` near `1` the series `∑ a v * q ^ (-s)` over these primes converges,
and its sum is `l * log (1 / (s - 1)) + x s` with `x` bounded as `s → 1⁺`. -/
def HasPrimeDensity (l : ℂ) : Prop :=
  ∃ x : ℝ → ℂ,
    -- `∑ a v * q ^ (-s) = -l * log (s - 1) + O(1)` as `s → 1⁺`, over the `v` whose norm `q` is
    -- prime
    x =O[𝓝[>] 1] (1 : ℝ → ℝ) ∧
    ∀ᶠ s : ℝ in 𝓝[>] 1,
      HasSum (fun v : FinPlace K ↦ ite v.q.Prime (a v) 0 * v.q ^ (-s : ℂ))
        (x s - l * Real.log (s - 1))

private lemma mul_q_cpow_neg (x : ℂ) (v : FinPlace K) (s : ℝ) :
    x * (v.q : ℂ) ^ (-s : ℂ) = x / (Ideal.absNorm v.asIdeal : ℂ) ^ (s : ℂ) := by
  rw [cpow_neg, div_eq_mul_inv]

private lemma log_factor_eq (a : FinPlace K → ℂ) (s : ℝ) (v : FinPlace K) :
    Complex.log (1 + -(a v * v.q ^ (-s : ℂ))) =
      -(-Complex.log (1 - a v / (Ideal.absNorm v.asIdeal : ℂ) ^ (s : ℂ))) := by
  rw [neg_neg, ← sub_eq_add_neg, mul_q_cpow_neg]

private lemma degreeOneTerm_eq (a : FinPlace K → ℂ) (s : ℝ) (v : FinPlace K) :
    ite v.q.Prime (a v) 0 * v.q ^ (-s : ℂ) =
      (TauCeti.higherDegreePrimes K)ᶜ.indicator a v / (Ideal.absNorm v.asIdeal : ℂ) ^ (s : ℂ) := by
  simp only [← mul_q_cpow_neg, Set.indicator, Set.mem_compl_iff,
    TauCeti.notMem_higherDegreePrimes_iff_prime_absNorm]

/-- For a finite set `u` of primes of `K`, the sum over `v ∈ u` of `1 / p ^ 2`, with `p` the least
prime factor of the norm `v.q`, is at most the degree `[K : ℚ]`. -/
lemma sum_inv_minFac_sq_le_finrank (u : Finset (FinPlace K)) :
    ∑ v ∈ u, (v.q.minFac ^ 2 : ℝ)⁻¹ ≤ finrank ℚ K := by
  have h_minFac (v : FinPlace K) : v.q.minFac = TauCeti.rationalPrimeBelow v := by
    rw [show v.q = Ideal.absNorm v.asIdeal from rfl, TauCeti.absNorm_eq_rationalPrimeBelow_pow,
      (TauCeti.prime_rationalPrimeBelow v).pow_minFac (inertiaDeg_pos ..).ne']
  set N : ℕ := u.sup fun v : FinPlace K ↦ TauCeti.rationalPrimeBelow v + 1
  calc ∑ v ∈ u, (v.q.minFac ^ 2 : ℝ)⁻¹
      = ∑ v ∈ u, ((TauCeti.rationalPrimeBelow v : ℝ) ^ 2)⁻¹ := by simp only [h_minFac]
    _ ≤ finrank ℚ K * ∑ m ∈ Ioo 1 N, (m ^ 2 : ℝ)⁻¹ :=
        TauCeti.sum_comp_rationalPrimeBelow_le (g := fun m : ℕ ↦ ((m : ℝ) ^ 2)⁻¹)
          (fun _ _ ↦ by positivity) fun v hv ↦
            mem_Ioo.mpr ⟨(TauCeti.prime_rationalPrimeBelow v).one_lt,
              le_sup (f := fun w : FinPlace K ↦ TauCeti.rationalPrimeBelow w + 1) hv⟩
    _ ≤ finrank ℚ K * (2 / ((1 : ℕ) + 1) : ℝ) := by grw [sum_Ioo_inv_sq_le]
    _ = finrank ℚ K := by norm_num

variable {a b} {l l' : ℂ}

private lemma hasPrimeDensity_iff_tauCeti :
    HasPrimeDensity a l ↔ TauCeti.HasPrimeDensity a l := by
  simp_rw [HasPrimeDensity, TauCeti.hasPrimeDensity_iff, degreeOneTerm_eq]
  constructor
  · rintro ⟨x, hx, hsum⟩
    refine ⟨hsum.mono fun s hs ↦ hs.summable, hx.congr' ?_ .rfl⟩
    filter_upwards [hsum] with s hs
    rw [TauCeti.degreeOnePrimeSum_def, hs.tsum_eq, one_div, Real.log_inv]
    push_cast
    ring
  · rintro ⟨hsum, hO⟩
    refine ⟨fun s ↦ TauCeti.degreeOnePrimeSum a s - l * Real.log (1 / (s - 1)), hO, ?_⟩
    filter_upwards [hsum] with s hs
    convert hs.hasSum using 1
    rw [TauCeti.degreeOnePrimeSum_def, one_div, Real.log_inv]
    push_cast
    ring

/-- For real `s > 1` the series of `N(I) ^ (-s)` over all ideals `I` of `𝓞 K` converges, with
`N(I) = absNorm I` (the zero ideal has norm `0` and term `0`). -/
lemma summable_absNorm_rpow (hs : 1 < s) :
    Summable fun I : Ideal (𝓞 K) ↦ (absNorm I : ℝ) ^ (-s) := by
  refine (summable_subtype_and_compl (s := (nonZeroDivisors (Ideal (𝓞 K)) : Set _))).1
    ⟨(TauCeti.summable_absNorm_rpow_ideal_iff (K := K)).mpr hs, ?_⟩
  have h_fin : ((nonZeroDivisors (Ideal (𝓞 K)) : Set (Ideal (𝓞 K)))ᶜ).Finite :=
    (Set.finite_singleton (⊥ : Ideal (𝓞 K))).subset fun I hI ↦
      by_contra fun hne ↦ hI (mem_nonZeroDivisors_of_ne_zero hne)
  exact h_fin.summable fun I ↦ (absNorm I : ℝ) ^ (-s)

/-- For `‖a v‖ ≤ 1` and real `1 ≤ σ ≤ s`, the logarithm of the Euler factor `1 - a v * q ^ (-s)` has
norm at most `2 * q ^ (-σ)`. -/
lemma norm_log_one_add_neg_mul_cpow_le_of_norm_le_one (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1)
    {σ : ℝ} (hσ : 1 ≤ σ) (hσs : σ ≤ s) (v : FinPlace K) :
    ‖Complex.log (1 + -(a v * v.q ^ (-s : ℂ)))‖ ≤ 2 * v.q ^ (-σ) := by
  rw [log_factor_eq, norm_neg]
  exact (TauCeti.norm_neg_log_one_sub_div_absNorm_cpow_le (ha v)
    (by simpa using hσ.trans hσs) (by simpa using hσs)).trans (by gcongr; norm_num)

/-- For `‖a v‖ ≤ 1` and real `s ≥ 1`, the logarithm of the Euler factor `1 - a v * q ^ (-s)`
differs from `-(a v * q ^ (-s))` (if `q` is prime) or from `0` (if not) by at most `2 / p ^ 2`, with
`p` the least prime factor of `q`. -/
lemma norm_log_one_add_neg_mul_cpow_sub_ite_le_of_norm_le_one (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1)
    (hs : 1 ≤ s) (v : FinPlace K) :
    ‖Complex.log (1 + -(a v * v.q ^ (-s : ℂ))) -
        (if v.q.Prime then -(a v * v.q ^ (-s : ℂ)) else 0)‖ ≤ 2 / v.q.minFac ^ 2 := by
  split_ifs with hq
  · have h_half : ‖a v / (Ideal.absNorm v.asIdeal : ℂ) ^ (s : ℂ)‖ ≤ 1 / 2 :=
      TauCeti.norm_div_absNorm_cpow_le_half (ha v) (by simpa)
    have h_inv : ‖a v / (Ideal.absNorm v.asIdeal : ℂ) ^ (s : ℂ)‖ ≤ (v.q : ℝ)⁻¹ :=
      (TauCeti.norm_div_absNorm_cpow_le_rpow_neg (ha v)).trans <| by
        simpa [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le
          (show (1 : ℝ) ≤ v.q from mod_cast v.one_lt_q.le) (neg_le_neg hs)
    rw [show Complex.log (1 + -(a v * v.q ^ (-s : ℂ))) - -(a v * v.q ^ (-s : ℂ)) =
        -(-Complex.log (1 - a v / (Ideal.absNorm v.asIdeal : ℂ) ^ (s : ℂ)) -
          a v / (Ideal.absNorm v.asIdeal : ℂ) ^ (s : ℂ)) by
        rw [← sub_eq_add_neg, mul_q_cpow_neg]; ring, norm_neg]
    calc _ ≤ ‖a v / (Ideal.absNorm v.asIdeal : ℂ) ^ (s : ℂ)‖ ^ 2 :=
          Complex.norm_neg_log_one_sub_sub_le h_half
      _ ≤ (v.q : ℝ)⁻¹ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h_inv 2
      _ ≤ 2 / v.q.minFac ^ 2 := by
          rw [hq.minFac_eq, inv_pow, div_eq_mul_inv]
          linarith [inv_nonneg.mpr (sq_nonneg (v.q : ℝ))]
  · have h_sq : ((v.q.minFac : ℝ) ^ 2) ≤ v.q :=
      mod_cast Nat.minFac_sq_le_self (zero_lt_one.trans v.one_lt_q) hq
    rw [sub_zero]
    calc ‖Complex.log (1 + -(a v * v.q ^ (-s : ℂ)))‖ ≤ 2 / v.q := by
          simpa only [Real.rpow_neg_one, div_eq_mul_inv] using
            norm_log_one_add_neg_mul_cpow_le_of_norm_le_one ha le_rfl hs v
      _ ≤ 2 / v.q.minFac ^ 2 :=
          div_le_div_of_nonneg_left zero_le_two (pow_pos (mod_cast v.q.minFac_pos) 2) h_sq

/-- For `‖a v‖ ≤ 1` and real `s ≥ 1`, the Euler factor `1 - a v * q ^ (-s)` lies in the slit plane,
where the logarithm is continuous. -/
lemma one_add_neg_mul_cpow_mem_slitPlane_of_norm_le_one (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1)
    (hs : 1 ≤ s) (v : FinPlace K) : 1 + -(a v * v.q ^ (-s : ℂ)) ∈ slitPlane := by
  rw [← sub_eq_add_neg, mul_q_cpow_neg]
  exact TauCeti.one_sub_div_absNorm_cpow_mem_slitPlane (ha v) (by simpa)

/-- If `‖a v‖ ≤ 1` and `s > 1`, the series `∑ v, log (1 - a v * q ^ (-s))` converges, its sum is
continuous at `s`, and `New.eulerProd a s` is the exponential of minus this sum. -/
@[local simp]
lemma eulerProd_eq_exp (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1) (hs : 1 < s) :
    let logFactor (s : ℝ) (v : FinPlace K) : ℂ := Complex.log (1 + -(a v * v.q ^ (-s : ℂ)))
    eulerProd a s = exp (-∑' v : FinPlace K, logFactor s v) ∧
    Summable (logFactor s) ∧
    ContinuousAt (fun t : ℝ ↦ -∑' v : FinPlace K, logFactor t v) s := by
  intro logFactor
  have h_eq (t : ℝ) : -∑' v : FinPlace K, logFactor t v =
      ∑' v : FinPlace K, -Complex.log (1 - a v / (Ideal.absNorm v.asIdeal : ℂ) ^ (t : ℂ)) := by
    rw [← tsum_neg]
    exact tsum_congr fun v ↦ by dsimp only [logFactor]; rw [log_factor_eq, neg_neg]
  have h_cont : ContinuousAt (fun t : ℝ ↦ -∑' v : FinPlace K, logFactor t v) s := by
    simpa only [h_eq] using
      (TauCeti.continuousOn_tsum_neg_log_one_sub_div_absNorm_cpow ha).continuousAt (Ioi_mem_nhds hs)
  have h_sum : Summable (logFactor s) := by
    simpa only [logFactor, log_factor_eq] using
      (TauCeti.summable_neg_log_one_sub_div_absNorm_cpow ha (by simpa)).neg
  exact ⟨extendFrom_eq (subset_closure hs) h_cont.cexp.continuousWithinAt.tendsto, h_sum, h_cont⟩

/-- For `‖a v‖ ≤ 1` and real `s > 1`, `New.eulerProd a s` is the exponential of minus the sum of
the logarithms of the Euler factors `1 - a v * q ^ (-s)`. -/
lemma eulerProd_eq_exp_neg_tsum_log_of_norm_le_one (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1) (hs : 1 < s) :
    eulerProd a s = exp (-∑' v : FinPlace K, Complex.log (1 + -(a v * v.q ^ (-s : ℂ)))) :=
  (eulerProd_eq_exp ha hs).1

/-- For `‖a v‖ ≤ 1` and real `s > 1`, the logarithms of the Euler factors `1 - a v * q ^ (-s)` are
summable over the primes `v`. -/
lemma summable_log_one_add_neg_mul_cpow_of_norm_le_one (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1)
    (hs : 1 < s) : Summable fun v : FinPlace K ↦ Complex.log (1 + -(a v * v.q ^ (-s : ℂ))) :=
  (eulerProd_eq_exp ha hs).2.1

private lemma eulerProd_eq_primeEulerProduct (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1) (hs : 1 < s) :
    eulerProd a s = TauCeti.primeEulerProduct a s := by
  rw [eulerProd_eq_exp_neg_tsum_log_of_norm_le_one ha hs,
    TauCeti.primeEulerProduct_eq_exp ha (by simpa), ← tsum_neg]
  exact congrArg exp (tsum_congr fun v ↦ by rw [log_factor_eq, neg_neg])

/-- For `‖a v‖ ≤ 1` and real `s > 1`, the product of the Euler factors `(1 - a v * q ^ (-s))⁻¹`
converges to `New.eulerProd a s`. -/
lemma hasProd_eulerProd (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1) (hs : 1 < s) :
    HasProd (fun v : FinPlace K ↦ (1 - a v * v.q ^ (-s : ℂ))⁻¹) (eulerProd a s) := by
  rw [eulerProd_eq_primeEulerProduct ha hs]
  simpa only [mul_q_cpow_neg] using TauCeti.hasProd_primeEulerProduct ha (by simpa)

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
  refine ⟨(hP_analytic.restrictScalars (𝕜' := ℂ)).comp_of_eq (ofRealCLM.analyticAt 1) (by simp),
    prod_ne_zero_iff.mpr fun w _ ↦ by simpa using h_factor_ne le_rfl w, fun s hs ↦ ?_⟩
  rw [eulerProd_eq_primeEulerProduct (fun v ↦ (norm_indicator_le_norm_self a v).trans (ha v)) hs,
    eulerProd_eq_primeEulerProduct ha hs,
    ← TauCeti.primeEulerProduct_indicator_compl_mul_prod ha (by simpa) Q,
    mul_assoc, ← prod_mul_distrib, prod_eq_one, mul_one]
  intro w _
  rw [← mul_q_cpow_neg, inv_mul_cancel₀ (h_factor_ne hs.le w)]

/-- If `‖a v‖ ≤ 1` for all `v` and `(s - 1) ^ l * eulerProd a s` tends to some `c ≠ 0` as real
`s ↓ 1`, with `l` a complex number, then `a` has density `l` over the primes of degree one. This
means `HasPrimeDensity a l`: the sum of `a v * q_v ^ (-s)` over the primes `v` of prime norm `q_v`
equals `l * log (1 / (s - 1))` plus a term bounded as `s ↓ 1`. (A pole of order `m` is the case
`l = m`, a zero of order `m` the case `l = -m`.) -/
lemma hasPrimeDensity_of_tendsto (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1) {l : ℂ} {c : ℂ} (hc : c ≠ 0)
    (h_lim : Tendsto (fun s : ℝ ↦ (s - 1) ^ l * eulerProd a s) (𝓝[>] 1) (𝓝 c)) :
    HasPrimeDensity a l := by
  rw [hasPrimeDensity_iff_tauCeti, TauCeti.hasPrimeDensity_iff]
  set F : ℝ → ℂ := fun s ↦ ∑' v : FinPlace K,
    -Complex.log (1 - a v / (Ideal.absNorm v.asIdeal : ℂ) ^ (s : ℂ))
  set G : ℝ → ℂ := fun s ↦ (s - 1).log * l + F s
  have hlog : ContinuousOn (fun t : ℝ ↦ ((t - 1).log : ℂ) * l) (Set.Ioi 1) :=
    (continuous_ofReal.comp_continuousOn (Real.continuousOn_log.comp
      (s := Set.Ioi 1) (f := fun t : ℝ ↦ t - 1) (continuous_id.sub continuous_const).continuousOn
      fun t (ht : 1 < t) ↦ Set.mem_compl_singleton_iff.mpr (sub_pos.mpr ht).ne')).mul
      continuousOn_const
  have hGcont : ContinuousOn G (Set.Ioi 1) :=
    hlog.add (TauCeti.continuousOn_tsum_neg_log_one_sub_div_absNorm_cpow ha)
  have hexp : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), (s - 1 : ℂ) ^ l * eulerProd a s = exp (G s) := by
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    have h_ne : (s : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (mod_cast hs.ne')
    rw [eulerProd_eq_primeEulerProduct ha hs, TauCeti.primeEulerProduct_eq_exp ha (by simpa),
      cpow_def_of_ne_zero h_ne, ← exp_add]
    simp [G, F, ofReal_log (sub_nonneg.mpr hs.le)]
  obtain ⟨C, hC⟩ := Complex.exists_tendsto_of_tendsto_exp hGcont hc (h_lim.congr' hexp)
  refine ⟨TauCeti.eventually_summable_indicator_div_absNorm_cpow ha, ?_⟩
  have hE : (fun s : ℝ ↦ F s - TauCeti.degreeOnePrimeSum a s) =O[𝓝[>] 1] fun _ ↦ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound (5 * finrank ℚ K) ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    rw [norm_one, mul_one]
    exact TauCeti.norm_tsum_neg_log_sub_degreeOnePrimeSum_le ha (by simpa)
  refine ((hC.isBigO_one ℝ).sub hE).congr' (.of_forall fun s ↦ ?_) .rfl
  simp only [G, one_div, Real.log_inv]
  push_cast
  ring

open Real

/-- If `‖a v‖ ≤ 1` for all `v` and `s ≥ σ ≥ 2` are real, the Euler product with coefficients `a` is
nonzero at `s`, and the logarithm of its modulus has absolute value at most
`2 * [K : ℚ] * 2 ^ (2 - σ)`. -/
lemma eulerProd_ne_zero_and_abs_log_norm_le (ha : ∀ v : FinPlace K, ‖a v‖ ≤ 1) {σ : ℝ} (hσ : 2 ≤ σ)
    (hs : σ ≤ s) :
    eulerProd a s ≠ 0 ∧ |Real.log ‖eulerProd a s‖| ≤ 2 * finrank ℚ K * 2 ^ (2 - σ) := by
  have hs_one : 1 < s := by linarith
  have h_summable := summable_log_one_add_neg_mul_cpow_of_norm_le_one ha hs_one
  have h_term (v : FinPlace K) :
      ‖log (1 + -(a v * v.q ^ (-s : ℂ)))‖ ≤ 2 * 2 ^ (2 - σ) * (v.q.minFac ^ 2 : ℝ)⁻¹ := by
    have hq : (2 : ℝ) ≤ v.q := mod_cast v.one_lt_q
    have hp : 0 < v.q.minFac := v.q.minFac_pos
    calc _ ≤ 2 * (v.q : ℝ) ^ (-σ) :=
          norm_log_one_add_neg_mul_cpow_le_of_norm_le_one ha (by linarith) hs v
      _ = 2 * v.q ^ (2 - σ) * (v.q ^ 2 : ℝ)⁻¹ := by simp [rpow_sub, v.q_bounds, field, rpow_neg]
      _ ≤ _ := by
        grw [rpow_le_rpow_of_nonpos two_pos hq (sub_nonpos.mpr hσ), Nat.minFac_le v.one_lt_q.le]
  have h_sum : ‖∑' v, log (1 + -(a v * v.q ^ (-s : ℂ)))‖ ≤ 2 * finrank ℚ K * 2 ^ (2 - σ) := by
    refine le_of_tendsto' h_summable.hasSum.norm fun u ↦ ?_
    grw [norm_sum_le, h_term, ← Finset.mul_sum, sum_inv_minFac_sq_le_finrank u, mul_right_comm]
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
  let χ₀ : Ideal (𝓞 K) →*₀ ℂ :=
    { toFun I := if I = ⊥ then 0 else χ I
      map_zero' := by simp
      map_one' := by simp only [show (1 : Ideal (𝓞 K)) ≠ ⊥ by rw [one_eq_top]; exact top_ne_bot,
        ↓reduceIte, map_one]
      map_mul' I J := by
        by_cases hI : I = ⊥ <;> by_cases hJ : J = ⊥ <;> simp [hI, hJ] }
  have hχ₀ (I : Ideal (𝓞 K)) : ‖χ₀ I‖ ≤ 1 := by
    by_cases hI : I = ⊥ <;> simp [χ₀, hI, hχ]
  have h_sub := TauCeti.hasSum_primeEulerProduct χ₀ hχ₀ (s := (s : ℂ)) (by simpa)
  have h_coeff : (fun v : FinPlace K ↦ χ₀ v.asIdeal) = fun v ↦ χ v.asIdeal :=
    funext fun v ↦ by simp [χ₀, v.ne_bot]
  rw [h_coeff, ← eulerProd_eq_primeEulerProduct (fun v ↦ hχ v.asIdeal) hs] at h_sub
  refine (hasSum_subtype_iff_of_support_subset (s := (nonZeroDivisors (Ideal (𝓞 K)) : Set _))
    fun I hI ↦ ?_).mp ?_
  · exact mem_nonZeroDivisors_of_ne_zero fun hbot ↦ hI (by
      simp [hbot, zero_cpow (neg_ne_zero.mpr (ofReal_ne_zero.mpr (zero_lt_one.trans hs).ne'))])
  · refine h_sub.congr_fun fun I ↦ ?_
    have hne : (I : Ideal (𝓞 K)) ≠ ⊥ := nonZeroDivisors.ne_zero I.property
    simp [χ₀, hne, cpow_neg, div_eq_mul_inv]

/-- Densities are linear: if each `a i` has density `l i` over the primes of degree one, then
`∑ i, w i * a i` has density `∑ i, w i * l i`. -/
lemma HasPrimeDensity.sum {ι : Type*} [Fintype ι] {a : ι → FinPlace K → ℂ} (w : ι → ℂ) {l : ι → ℂ}
    (h : ∀ i : ι, HasPrimeDensity (a i) (l i)) :
    HasPrimeDensity (fun v : FinPlace K ↦ ∑ i : ι, w i * a i v) (∑ i : ι, w i * l i) := by
  rw [hasPrimeDensity_iff_tauCeti,
    show (fun v ↦ ∑ i, w i * a i v) = ∑ i, fun v ↦ w i * a i v by ext; simp]
  exact TauCeti.HasPrimeDensity.sum Finset.univ fun i _ ↦
    (hasPrimeDensity_iff_tauCeti.mp (h i)).const_mul (w i)

/-- Suppose `a` has density `l` and `b` has density `l'` in the Dirichlet sense of
`HasPrimeDensity`: over the primes `v` of degree one (prime norm `q_v`),
`∑ a v * q_v ^ (-s) = l * log (1 / (s - 1)) + O(1)` as `s ↓ 1`, and likewise for `b` and `l'`.
Suppose also that `Re (a v) ≤ Re (b v)` for all but finitely many primes `v` of degree one. Then
`Re l ≤ Re l'`. -/
lemma HasPrimeDensity.re_le_re (ha : HasPrimeDensity a l) (hb : HasPrimeDensity b l')
    (h_le : ∀ᶠ v : FinPlace K in cofinite, v.q.Prime → (a v).re ≤ (b v).re) :
    l.re ≤ l'.re :=
  (hasPrimeDensity_iff_tauCeti.mp ha).re_le_re (hasPrimeDensity_iff_tauCeti.mp hb) h_le

/-- For `c ∈ ℂ` the constant family `v ↦ c` has density `c` over the primes of degree one of `K`, in
the sense of `New.HasPrimeDensity`. -/
lemma hasPrimeDensity_const (c : ℂ) : HasPrimeDensity (fun _ : FinPlace K ↦ c) c :=
  hasPrimeDensity_iff_tauCeti.mpr (TauCeti.hasPrimeDensity_const c)

/-- A number field `K` has infinitely many primes of degree one, that is, finite places `w` whose
absolute norm `w.q` is a prime number. -/
lemma frequently_prime_q : ∃ᶠ w : FinPlace K in cofinite, w.q.Prime := by
  rw [Filter.Frequently, Filter.eventually_cofinite]
  simpa using TauCeti.infinite_setOf_prime_absNorm (K := K)

/-- Let `L/K` be an extension of number fields and `c ∈ ℂ`. Consider the family that sends `v` to
`c` times the number of places `w` of `L` above `v` whose residue field has the same cardinality
`q_w = q_v`, that is, those of relative residue degree one. This family has density `c` over the
primes of degree one of `K`: the sum of its values times `q_v ^ (-s)` over the `v` of prime norm is
`c * log (1 / (s - 1))` plus a term bounded as `s ↓ 1`. -/
lemma hasPrimeDensity_card_degree_one (L : Type*) [Field L] [NumberField L] [Algebra K L] (c : ℂ) :
    HasPrimeDensity (fun v : FinPlace K ↦ c * {w : FinPlace L | w.below K = v ∧ w.q = v.q}.ncard)
      c :=
  hasPrimeDensity_iff_tauCeti.mpr
    (TauCeti.hasPrimeDensity_mul_ncard_setOf_under_eq_and_absNorm_eq (K := K) L c)

end New

end
