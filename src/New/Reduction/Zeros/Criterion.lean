module

public import New.Reduction.Zeros.PrimeError
import Lib.Analytic.Landau
import Lib.Analytic.QuadraticTwist

/-!
# The one-sided criterion for a zero-free half-plane

`New.LFunction_ne_zero_of_primeRemainder_le`: an eventual upper bound `R_q(x) ≤ A * x ^ (β - 1)` for
the remainder of a sum over prime powers `≡ 1` mod `q` with weights depending on a prime `d`, for
all `d` of a suitable class, excludes zeros `s ≠ 1` of the `L(s, ψ)`, `ψ` mod `q`, in `re s > β`.

For a single fixed prime, `New.sum_entireL_orders_eq_twisted_of_primeRemainder_le` first
compares the twisted and untwisted zero multiplicities in the half-plane.

Notions from other files:
* `primeRemainder d q x`: the remainder `R_q(x) = ∑_{n ≤ x} λ(n) (1/n - 1/x) - log x / φ(q) - c_q`,
  where `λ(n) = Λ(n) (1 - (n/d))` for `n ≡ 1` mod `q` and `0` otherwise, and `c_q` is a constant.
* `entireL ψ`: the entire function `L(s, ψ)`, times `s - 1` if `ψ` is principal.
* `quadTwist ψ d`: the product of `ψ` and the Legendre symbol `(·/d)`.
* `IsPolar E r`: the transform `∫₀^∞ E(v) e^{(1-s)v} dv` continues meromorphically, with at most
  simple poles in `re s > 0` and residues `r`.

## Relation to the literature

The hypotheses concern only the remainders, for all primes `d` of the class, and not the real zeros
of the `L(s, ψ)`. In the literature: a one-sided bound for a weighted sum over primes `≡ 1` modulo
`q` gives a zero-free half-plane if there are no real zeros. Related work: M. Suzuki, On variants of
Chebyshev's conjecture, arXiv 2411.07436, 2024; Montgomery–Vaughan, Multiplicative Number Theory I,
§15.1–15.2, 2007; Landau, Über einen Satz von Tschebyschef, 1905.
-/

@[expose] public section

open Complex Filter Nat Real Set MeasureTheory Topology

/-- For one prime with the one-sided remainder bound, suppose that on the real interval
`(β, 1)` the total order of the twisted zeros is at most the untwisted total. Then the
two totals agree at every complex point to the right of `β`, with multiplicities. -/
theorem New.sum_entireL_orders_eq_twisted_of_primeRemainder_le
    {q d : ℕ} [NeZero q] [Fact d.Prime] (hd : d % 8 = 7) (hcop : q.Coprime d)
    {A β : ℝ} (hβ : 0 < β)
    (hbound : ∀ᶠ x : ℝ in atTop, primeRemainder d q x ≤ A * x ^ (β - 1))
    (hreal : ∀ x : ℝ, β < x → x < 1 →
      (∑ χ : DirichletCharacter ℂ q, analyticOrderNatAt (entireL (quadTwist χ d)) x) ≤
        ∑ χ : DirichletCharacter ℂ q, analyticOrderNatAt (entireL χ) x)
    {ρ : ℂ} (hρ : β < ρ.re) :
    (∑ χ : DirichletCharacter ℂ q, analyticOrderNatAt (entireL χ) ρ) =
      ∑ χ : DirichletCharacter ℂ q, analyticOrderNatAt (entireL (quadTwist χ d)) ρ := by
  let untwisted (s : ℂ) := ∑ χ : DirichletCharacter ℂ q, analyticOrderNatAt (entireL χ) s
  let twisted (s : ℂ) :=
    ∑ χ : DirichletCharacter ℂ q, analyticOrderNatAt (entireL (quadTwist χ d)) s
  have vanish (s : ℂ) (hs : 1 ≤ s.re) : untwisted s = 0 ∧ twisted s = 0 := by
    constructor <;> exact Finset.sum_eq_zero fun χ _ ↦
      (analyticOrderNatAt_entireL_eq_zero_iff _ s).2 (entireL_ne_zero _ hs)
  obtain rfl | hρ₁ := eq_or_ne ρ 1
  · exact (vanish 1 le_rfl).1.trans (vanish 1 le_rfl).2.symm
  -- The difference of orders gives a nonnegative residue for real x > β. Landau's lemma
  -- then makes the residue at ρ vanish, so the two orders agree there.
  let r (s : ℂ) : ℂ := ((untwisted s : ℂ) - twisted s) / φ q / (s * (1 - s))
  have polar : IsPolar (fun v : ℝ ↦ primeRemainder d q v.exp) r := by
    simpa [r, untwisted, twisted, Finset.sum_sub_distrib] using isPolar_primeRemainder hd hcop
  have nonneg (x : ℝ) (hx : β < x) : 0 ≤ (r x).re := by
    have eq : r x = (((untwisted x : ℝ) - twisted x) / φ q / (x * (1 - x)) : ℝ) := by simp [r]
    rw [eq, ofReal_re]
    obtain hx' | hx' := lt_or_ge x 1
    · have num : (twisted x : ℝ) ≤ untwisted x := by exact_mod_cast hreal x hx hx'
      exact div_nonneg (div_nonneg (sub_nonneg.2 num) (by positivity))
        (mul_nonneg (hβ.trans hx).le (sub_nonneg.2 hx'.le))
    · obtain ⟨hu, ht⟩ := vanish x hx'
      simp [hu, ht]
  have exp_bound : ∀ᶠ v : ℝ in atTop, primeRemainder d q v.exp ≤ A * Real.exp ((β - 1) * v) := by
    filter_upwards [tendsto_exp_atTop.eventually hbound] with v hv
    rwa [mul_comm (β - 1) v, Real.exp_mul]
  have hzero : r ρ = 0 := polar.landau hβ nonneg exp_bound hρ
  have h₀ : ρ ≠ 0 := ne_zero_of_re_pos (hβ.trans hρ)
  have eq : (untwisted ρ : ℂ) = twisted ρ := by
    simpa [r, sub_eq_zero, h₀, sub_ne_zero.2 hρ₁.symm, NeZero.ne] using hzero
  exact_mod_cast eq

/-- **One-sided criterion.** Let `q₀` be a positive multiple of `8`, let `d₀ ≡ 7` mod `8` be prime
to `q₀`, and let `β > 1/2`. Suppose that for each prime `d ≡ d₀` mod `q₀` the remainder
`primeRemainder d q₀ x = ∑_{n ≤ x} λ(n) (1/n - 1/x) - log x / φ(q₀) - c` is at most
`A * x ^ (β - 1)` for some `A` and all large `x`. Here `λ(n) = Λ(n) (1 - (n/d))` for `n ≡ 1` mod
`q₀` and `0` otherwise, and `c` is the constant for which the remainder tends to `0`. Then
`L(ρ, ψ) ≠ 0` for every character `ψ` modulo `q₀` and every `ρ ≠ 1` with `re ρ > β`. -/
theorem New.LFunction_ne_zero_of_primeRemainder_le {q₀ : ℕ} [NeZero q₀] (hq₀ : 8 ∣ q₀) {d₀ : ℕ}
    (hd₀_mod : d₀ % 8 = 7) (hd₀_cop : d₀.Coprime q₀) {β : ℝ} (hβ : 1 / 2 < β)
    (h_bound : ∀ d : Primes, (d : ℕ) ≡ d₀ [MOD q₀] →
      ∃ A : ℝ, ∀ᶠ x : ℝ in atTop, primeRemainder d q₀ x ≤ A * x ^ (β - 1))
    (ψ : DirichletCharacter ℂ q₀) {ρ : ℂ} (hρ_ne : ρ ≠ 1) (hρ_re : β < ρ.re) :
    ψ.LFunction ρ ≠ 0 := by
  -- Choose a prime whose quadratic twists have no zero in the box containing ρ.
  have h_mod (d : Primes) (hd : ((d : ℕ) : ZMod q₀) = d₀) : (d : ℕ) ≡ d₀ [MOD q₀] :=
    (ZMod.natCast_eq_natCast_iff d d₀ q₀).1 hd
  have h_class (d : Primes) (hd : ((d : ℕ) : ZMod q₀) = d₀) : (d : ℕ) % 8 = 7 ∧ q₀.Coprime d := by
    have h_mod_eight : (d : ℕ) % 8 = d₀ % 8 := (h_mod d hd).of_dvd hq₀
    exact ⟨h_mod_eight.trans hd₀_mod, Coprime.symm ((h_mod d hd).gcd_eq.trans hd₀_cop)⟩
  obtain ⟨d, hd, h_twist⟩ : ∃ d : Primes, ((d : ℕ) : ZMod q₀) = d₀ ∧
      ∀ (χ : DirichletCharacter ℂ q₀) (s : ℂ),
        β ≤ re s → |im s| ≤ |ρ.im| → entireL (quadTwist χ d) s ≠ 0 :=
    exists_entireL_quadTwist_ne_zero |ρ.im| hβ ((ZMod.isUnit_iff_coprime d₀ q₀).2 hd₀_cop) h_class
  obtain ⟨hd_mod, hd_cop⟩ := h_class d hd
  -- The upper bound compares the total zero orders at this fixed prime. The chosen twists
  -- contribute zero throughout the box, including its real points and the target ρ.
  have twisted_order (s : ℂ) (hs : β ≤ s.re) (him : |s.im| ≤ |ρ.im|) :
      (∑ χ : DirichletCharacter ℂ q₀, analyticOrderNatAt (entireL (quadTwist χ d)) s) = 0 :=
    Finset.sum_eq_zero fun χ _ ↦
      (analyticOrderNatAt_entireL_eq_zero_iff _ s).2 (h_twist χ s hs him)
  obtain ⟨A, hA⟩ := h_bound d (h_mod d hd)
  have counts := sum_entireL_orders_eq_twisted_of_primeRemainder_le hd_mod hd_cop
    (by linarith : 0 < β) hA (fun x hx _ ↦ by
      rw [twisted_order x hx.le (by simp)]
      exact Nat.zero_le _) hρ_re
  rw [twisted_order ρ hρ_re.le le_rfl] at counts
  have h_entire : entireL ψ ρ ≠ 0 := (analyticOrderNatAt_entireL_eq_zero_iff ψ ρ).1
    (Finset.sum_eq_zero_iff.1 counts ψ (Finset.mem_univ ψ))
  exact (entireL_ne_zero_iff ψ hρ_ne).1 h_entire
