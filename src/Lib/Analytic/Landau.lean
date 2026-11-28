module

public import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.MeasureTheory.Order.Group.Lattice
public import Lib.Analytic.EntireLFunction
import TauCeti.Analysis.LaplaceTransform.Meromorphic

/-!
# Landau's lemma

This part applies Landau's lemma, that the Laplace transform of a function of one sign is not
analytic at its abscissa of convergence, to transforms satisfying `New.IsPolar`. Assume a one-sided
bound on the error term `E`, and assume that the residues `r x` at real `x > β` have non-negative
real part. Then there is no pole to the right of `β`. Together with `Lib.Analytic.EntireLFunction`,
these are the analytic tools for passing from a one-sided bound on an error term to the absence of
zeros of L-functions.

Landau's lemma in the one-sided form used here is Tau Ceti's
`TauCeti.hasLaplace_toMeromorphicNFOn_of_ae_le_exp`.

## Main results

* `New.IsPolar.landau`: let `β > 0`. If `E v ≤ A e^{(β-1)v}` for all large `v` and `re (r x) ≥ 0`
  for real `x > β`, then `r ρ = 0` for `re ρ > β`.

Notions from other files:
* `New.IsPolar` (from `Lib.Analytic.EntireLFunction`): `∫₀^∞ E(v) e^{(1-s)v} dv`, the Laplace
  transform of `E(v) e^v`, converges for `re s > 2` and continues meromorphically to `re s > 0`
  with at most simple poles of residue (trailing coefficient) `r ρ` there.

## Relation to the literature

Known result: Landau's lemma on Dirichlet integrals of one sign. It is applied to transforms with
simple poles whose residues at real points have non-negative real part: no pole lies to the right
of the abscissa given by the one-sided bound. Source: Montgomery and Vaughan, Multiplicative
Number Theory I, 2007, Lemma 15.1 (Widder, The Laplace Transform, 1941, II Thm 5b).
-/

@[expose] public section

open Complex Set Filter MeasureTheory Topology

namespace New

variable {E : ℝ → ℝ}

/-- **No pole to the right of `β`**, by Landau's lemma and the sign of the residues at real points.
Suppose `IsPolar E r`: the transform `∫₀^∞ E(v) e^{(1-s)v} dv` converges for `re s > 2` and has a
meromorphic continuation to `re s > 0` with at most simple poles of residue `r ρ` there. Let
`β > 0`. If `E(v) ≤ A e^{(β-1)v}` for all large `v` and the residues at real points right of `β`
have real part `≥ 0`, then there is no pole in `re s > β`, that is, `r ρ = 0`. -/
lemma IsPolar.landau {r : ℂ → ℂ} (h : IsPolar E r) {A β : ℝ} (hβ : 0 < β)
    (hr : ∀ x : ℝ, β < x → 0 ≤ (r x).re)
    (hE_le : ∀ᶠ v : ℝ in atTop, E v ≤ A * Real.exp ((β - 1) * v))
    {ρ : ℂ} (hρ : β < ρ.re) :
    r ρ = 0 := by
  -- `Φ` is the Laplace transform of `g(v) = E(v) e^v`, and `g(v) ≤ A e^{βv}` for large `v`.
  obtain ⟨Φ, hΦ, hL, h_res⟩ := h
  obtain ⟨u₀, hu₀⟩ := hE_le.exists_forall_of_atTop
  have hg : ∀ᵐ u ∂volume.restrict (Ioi u₀), E u * Real.exp u ≤ A * Real.exp (β * u) :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : u₀ < u) ↦
      calc E u * Real.exp u ≤ A * Real.exp ((β - 1) * u) * Real.exp u := by grw [hu₀ u hu.le]
        _ = A * Real.exp (β * u) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
  have h_sign (x : ℝ) (hx : x ∈ Ioc β 2) (h_neg : meromorphicOrderAt Φ x < 0) :
      0 ≤ (meromorphicTrailingCoeffAt Φ x).re := by
    simpa [(h_res x (by simpa using hβ.trans hx.1)).2, h_neg] using hr x hx.1
  obtain ⟨h_order, -⟩ := TauCeti.hasLaplace_toMeromorphicNFOn_of_ae_le_exp hg
    (fun z (hz : β < z.re) ↦ hΦ z (hβ.trans hz)) hL h_sign
  simp [(h_res ρ (hβ.trans hρ)).2, not_lt.2 (h_order ρ hρ)]

end New
