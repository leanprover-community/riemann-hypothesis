module

import TauCeti.MeasureTheory.Group.OrbitCutoff.Discrete
public import Lib.Adelic.QuotientMeasure.Basic

/-!
# Moving a quotient from one variable to another

Let `Λ → R` be a homomorphism from a countable group to a subgroup `R` of a group `G`, and let `F`
on `R × G` be invariant under the diagonal action of `Λ`. The integral of `F` over
`Λ \ (R × G)` may be computed as an integral over `R × (Λ \ G)` or over `(Λ \ R) × G`
(`New.integral_cutoff_swap`).

Notions from other files:
* `New.orbitMeasure ν μ`: the measure `μ` weighted by a chosen cutoff; it computes integrals over
  the quotient.

## Relation to the literature

A consequence of a known result: the integral over a quotient does not depend on the cutoff. See
`Lib.Adelic.QuotientMeasure.Basic`.
-/

@[expose] public section

open MeasureTheory Measure

namespace New

/-- Let `ν` be an inversion invariant measure on a group `H`, `μ` an `H`-invariant measure on `X`
and `β` a cutoff, that is, a measurable weight with `∫_H β (h • x) dν = 1` for every `x`. A
measurable `H`-invariant function `f` is integrable for the quotient measure `orbitMeasure ν μ`
(the measure `μ` weighted by a chosen cutoff) if and only if `β • f` is integrable for `μ`. -/
lemma IsCutoff.integrable_orbitMeasure_iff {H X : Type*} [Group H] [MeasurableSpace H]
    [MeasurableInv H] [MeasurableSpace X] [MulAction H X] [MeasurableSMul₂ H X]
    {ν : Measure H} [SFinite ν] [ν.IsInvInvariant]
    {μ : Measure X} [SFinite μ] [SMulInvariantMeasure H X μ]
    {β : X → ENNReal} (hβ : IsCutoff ν β) {f : X → ℂ}
    (h_inv : ∀ (h : H) (x : X), f (h • x) = f x) (hf : Measurable f) :
    Integrable f (orbitMeasure ν μ) ↔ Integrable (fun x : X ↦ (β x).toReal • f x) μ := by
  have hβ_meas : Measurable β := hβ.1
  rw [(identDistrib_orbitMeasure hβ hf h_inv).integrable_iff,
    integrable_withDensity_iff_integrable_smul' hβ_meas hβ.ae_cutoff_lt_top]

/-- **Moving the quotient from one variable to the other.** Let `R` be a subgroup of `G`, with left
invariant measures `ν` and `μ`, and let `i` be a homomorphism from a countable group `Λ` to `R`.
Let the translates under `Λ` of the measurable weight `β` on `G` add up to one, so that `β μ` and
`β ν` compute integrals over `Λ \ G` and `Λ \ R`. If `F` on `R × G` is measurable, invariant under
the diagonal action of `Λ` and integrable over `(Λ \ R) × G`, then
`∫_{Λ \ G} ∫_R F = ∫_{Λ \ R} ∫_G F`. -/
theorem integral_cutoff_swap {G Λ : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [Group Λ] [Countable Λ] {R : Subgroup G} [MeasurableMul R]
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    (ν : Measure R) [SFinite ν] [ν.IsMulLeftInvariant] (i : Λ →* R) {β : G → ENNReal}
    (hβ : Measurable β) (hβ_one : ∀ x : G, ∑' l : Λ, β (i l * x) = 1) {F : R × G → ℂ}
    (hF : Measurable F) (hF_inv : ∀ (l : Λ) (s : R) (x : G), F (i l * s, i l * x) = F (s, x))
    (h_int : Integrable (fun p : R × G ↦ (β p.1).toReal • F p) (ν.prod μ)) :
    ∫ x : G, (β x).toReal • ∫ s : R, F (s, x) ∂ν ∂μ =
      ∫ s : R, (β s).toReal • ∫ x : G, F (s, x) ∂μ ∂ν :=
  MeasureTheory.integral_cutoff_swap μ ν i hβ hβ_one hF hF_inv h_int

/-- If `a` is integrable on a subgroup `R` of `G` and `e` is integrable on `G` for a left invariant
measure, then `(s, x) ↦ a s * e (g * s⁻¹ * x)` is integrable on `R × G`. -/
lemma integrable_mul_comp_inv_mul {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [MeasurableInv G] {R : Subgroup G} {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant]
    {ν : Measure R} [SFinite ν] {a : R → ℂ} (ha : Integrable a ν) {e : G → ℂ}
    (he : Integrable e μ) (g : G) :
    Integrable (fun p : R × G ↦ a p.1 * e (g * (p.1 : G)⁻¹ * p.2)) (ν.prod μ) := by
  -- The shear `(s, x) ↦ (s, g * s⁻¹ * x)` preserves the product measure.
  have h_shear : MeasurePreserving (fun p : R × G ↦ (p.1, g * (p.1 : G)⁻¹ * p.2))
      (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product (g := fun (s : R) (x : G) ↦ g * (s : G)⁻¹ * x)
      (by fun_prop) (.of_forall fun s ↦ map_mul_left_eq_self μ (g * (s : G)⁻¹))
  exact h_shear.integrable_comp_of_integrable (ha.mul_prod he)

end New
