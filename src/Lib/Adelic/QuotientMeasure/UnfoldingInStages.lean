module

import TauCeti.MeasureTheory.Group.OrbitCutoff.Stages
public import Lib.Adelic.QuotientMeasure.Basic

/-!
# Pushing forward quotient measures, unfolding in stages and vanishing criteria

This file studies integrals over a quotient `Γ \ G` by a discrete subgroup `Γ`, with `μ` a Haar
measure. For a `Γ`-invariant `F`, `(Γ.quotMeasure μ)[F]` is the integral of `F` over `Γ \ G`. Such
integrals are compared with integrals over a quotient `Λ \ H` of a second group mapping to `G`, and
are written as iterated integrals with inner integral over `Λ \ H`. From this follow two criteria
for the integral of a continuous left `Γ`-invariant function to vanish.

## Main definitions and results

* `New.exists_integral_comp_quotMeasure_eq_smul`: for a continuous surjection `H → G` of unimodular
  groups taking `Λ` into `Γ`, the integral over `Λ \ H` of a pulled-back invariant function is a
  fixed multiple of its integral over `Γ \ G`. Unimodular means the Haar measures are also right
  invariant.
* `New.integral_quotMeasure_stages`: the integral over `Γ \ G` is an iterated integral whose inner
  integral is over `Λ \ H`.
* `New.integral_quotMeasure_eq_integral_cosetMeasure`: the case of a closed subgroup, with the outer
  integral over `i(H) \ G` (`New.cosetMeasure`).
* `New.Exchange.exists_integral_stages_eq_mul`: for a subgroup `L × H`, if the inner integrals
  through every `g` are `ρ g * c`, with `re ρ` nonnegative and nonzero near some point, then the
  integral over `Γ \ G` is `R * c` for a fixed `R ≠ 0`, with `Γ` the image of `Λ ≤ H`.
* `New.integral_quotMeasure_eq_zero_of_mean`: the integral vanishes if an average of translates of
  `F` by elements of a closed subgroup `H ≥ Γ` is `a • F` and these elements scale the Haar measure
  of `H` by `d ≠ a`.
* `New.integral_quotMeasure_eq_zero_of_twist`: the integral vanishes if `F (u * y) = c • F y` with
  `‖c‖ = 1` and `c ≠ 1`.

## Relation to the literature

Known; see `Lib.Adelic.QuotientMeasure.Basic` for sources.
-/

@[expose] public section

/-! ## Pushing forward quotient measures and unfolding in stages -/

section UnfoldingInStages

open MeasureTheory Measure Topology MulAction Function ProbabilityTheory

variable {G H V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  {Γ : Subgroup G} [DiscreteTopology Γ]
  (Λ : Subgroup H) [DiscreteTopology Λ]
  (μ : Measure G) [IsHaarMeasure μ]
  (ν : Measure H) [IsHaarMeasure ν]

private lemma identDistrib_cutoffMeasure_quotMeasure {G Y : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace Y]
    {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G} [SFinite μ]
    [SMulInvariantMeasure Γ G μ] {F : G → Y} (hF : Measurable F) (hF_inv : Γ.FixesLeft F) :
    IdentDistrib F F (Γ.cutoffMeasure μ) (Γ.quotMeasure μ) := by
  have : Countable Γ := countable_of_Lindelof_of_discrete
  have hβ := New.isCutoff_chosenCutoff (count : Measure Γ) (X := G)
  exact MeasureTheory.IsOrbitCutoff.identDistrib_cutoffMeasure ⟨hβ.1, hβ.2⟩ hF fun γ g ↦
    hF_inv γ γ.property g

/-- Let `π : H → G` be a continuous surjective homomorphism with `π Λ ≤ Γ` (both discrete), and let
`μ` and `ν` be Haar measures on `G` and `H` that are also right invariant. There is a real `c` such
that, for all measurable left `Γ`-invariant `F`, the integral of `F ∘ π` over `Λ \ H` is `c` times
the integral of `F` over `Γ \ G`. -/
lemma New.exists_integral_comp_quotMeasure_eq_smul [T2Space H]
    [μ.IsMulRightInvariant] [ν.IsMulRightInvariant]
    {π : H →* G} (hπ : Continuous π) (hπ_surj : Surjective π) (hΛ : Λ ≤ Γ.comap π) :
    ∃ c : ℝ, ∀ F : G → V, Measurable F → Γ.FixesLeft F →
      ∫ r : H, F (π r) ∂Λ.quotMeasure ν = c • ∫ g : G, F g ∂Γ.quotMeasure μ := by
  obtain ⟨c, hc⟩ :=
    Subgroup.exists_integral_comp_cutoffMeasure_eq_smul (V := V) Λ μ ν hπ hπ_surj hΛ
  refine ⟨c, fun F hF hF_inv ↦ ?_⟩
  have hF_inv_Λ : Λ.FixesLeft (fun r ↦ F (π r)) := fun γ hγ r ↦ by
    simpa [map_mul] using hF_inv (π γ) (hΛ hγ) (π r)
  rw [← (identDistrib_cutoffMeasure_quotMeasure (F := fun r ↦ F (π r)) (hF.comp hπ.measurable)
    hF_inv_Λ).integral_eq,
    ← (identDistrib_cutoffMeasure_quotMeasure hF hF_inv).integral_eq]
  exact hc F hF hF_inv

/-- Unfolding in stages. Let `i : H → G` be an injective homomorphism with `i Λ = Γ` (both
discrete), `ν` a Haar measure on `H`, and let `(z, h) ↦ i h * T z` carry `m ⊗ ν` to `μ`. Let `F`
be measurable, left `Γ`-invariant and integrable on `Γ \ G`. Then (a) the integral of
`a ↦ F (i a * T z)` over `Λ \ H` is `m`-integrable in `z` and (b) its integral against `m` is the
integral of `F` over `Γ \ G`. -/
lemma New.integral_quotMeasure_stages [T2Space H] {Z : Type*} [MeasurableSpace Z] {m : Measure Z}
    {μ : Measure G} [SFinite m] (T : Z → G) {i : H →* G} (hi : Injective i)
    (hT : MeasurePreserving (fun p : Z × H ↦ i p.2 * T p.1) (m.prod ν) μ) (hΓ : Λ.map i = Γ)
    {F : G → V} (hF : Measurable F) (hF_inv : Γ.FixesLeft F)
    (hF_int : Integrable F (Γ.quotMeasure μ)) :
    Integrable (fun z : Z ↦ ∫ a : H, F (i a * T z) ∂Λ.quotMeasure ν) m ∧
    ∫ g : G, F g ∂Γ.quotMeasure μ = ∫ z : Z, ∫ a : H, F (i a * T z) ∂Λ.quotMeasure ν ∂m := by
  -- The map `((z, a), l) ↦ i l * (i a * T z)` unfolds `m ⊗ Λ.quotMeasure ν` to `μ`, so `F` on
  -- `Γ \ G` is distributed as `(z, a) ↦ F (i a * T z)`; Fubini's theorem finishes.
  let e : Λ ≃* Γ := (Λ.equivMapOfInjective _ hi).trans (.subgroupCongr hΓ)
  have h_unfold : MeasurePreserving (fun p : (Z × H) × Λ ↦ e p.2 • (i p.1.2 * T p.1.1))
      ((m.prod (Λ.quotMeasure ν)).prod count) μ := by
    -- Unfold `Λ \ H` to `H` in the second factor by `(a, l) ↦ l • a`, then apply `hT`.
    simpa [Function.comp_def, MeasurableEquiv.prodAssoc, Subgroup.smul_def, e, mul_assoc] using
      hT.comp (((MeasurePreserving.id m).prod measurePreserving_orbitMeasure).comp
        (measurePreserving_prodAssoc m (Λ.quotMeasure ν) count))
  have h_dist :
      IdentDistrib F (fun p : Z × H ↦ F (i p.2 * T p.1)) (Γ.quotMeasure μ)
        (m.prod (Λ.quotMeasure ν)) :=
    identDistrib_orbitMeasure_of_unfold (measurePreserving_count e.toEquiv) h_unfold hF
      hT.measurable fun γ ↦ hF_inv γ γ.property
  have h_int := h_dist.integrable_snd hF_int
  exact ⟨h_int.integral_prod_left, h_dist.integral_eq.trans (integral_prod _ h_int)⟩

/-- The quotient measure on `i(H) \ G`, carried by `G`, of the Haar measures `μ` on `G` and `ν` on
`H`, for `H` acting on `G` by left translation through `i`; it is used for closed embeddings
`i : H → G`. -/
noncomputable def New.cosetMeasure (i : H →* G) : Measure G :=
  letI := compHom G i
  orbitMeasure ν μ

/-- Integration in stages. Let `i : H → G` be a closed embedding, `Λ` a discrete subgroup of the
unimodular group `H`, and `F` measurable, left `i(Λ)`-invariant and integrable on `i(Λ) \ G`. Then
(a) the integral of `a ↦ F (i a * g)` over `Λ \ H` is integrable in `g` on `i(H) \ G` and (b) its
integral there is the integral of `F` over `i(Λ) \ G`. -/
lemma New.integral_quotMeasure_eq_integral_cosetMeasure [T2Space H]
    [ν.IsMulRightInvariant] {i : H →* G}
    (hi : IsClosedEmbedding i) {F : G → V} (hF : Measurable F) (hF_inv : (Λ.map i).FixesLeft F)
    (hF_int : Integrable F ((Λ.map i).quotMeasure μ)) :
    Integrable (fun g : G ↦ ∫ a : H, F (i a * g) ∂Λ.quotMeasure ν) (cosetMeasure μ ν i) ∧
    ∫ g : G, F g ∂(Λ.map i).quotMeasure μ =
      ∫ g : G, ∫ a : H, F (i a * g) ∂Λ.quotMeasure ν ∂cosetMeasure μ ν i := by
  let : MulAction H G := compHom G i
  have : SMulInvariantMeasure H G μ := ⟨by simp [compHom_smul_def]⟩
  have : ProperSMul H G := properSMul_of_isClosedEmbedding i hi fun _ _ ↦ rfl
  have : HasCutoff ν G := hasCutoff_of_proper
  have : DiscreteTopology (Λ.map i) := (hi.isEmbedding.homeomorphImage Λ).discreteTopology
  have : SFinite (cosetMeasure μ ν i) := inferInstanceAs (SFinite (orbitMeasure ν μ))
  -- The quotient measure unfolds to `μ` along the action of `H` through `i`.
  have h_unfold : MeasurePreserving (fun p : G × H ↦ i p.2 * p.1)
      ((cosetMeasure μ ν i).prod ν) μ := measurePreserving_orbitMeasure
  exact integral_quotMeasure_stages Λ ν (T := fun g : G ↦ g) hi.injective h_unfold (hΓ := rfl) hF
    hF_inv hF_int

/-- Let `i : H → G` be a closed embedding of a unimodular group and `ρ ≥ 0` a function on `G`,
invariant under left translation by `i(H)`, integrable and with integral zero for the quotient
measure `New.cosetMeasure` on `i(H) \ G`. Then `ρ` vanishes on a dense set. -/
lemma New.dense_eq_zero_of_integral_cosetMeasure_eq_zero [ν.IsMulRightInvariant] {i : H →* G}
    (hi : IsClosedEmbedding i) {ρ : G → ℝ} (hρ_nonneg : 0 ≤ ρ)
    (hρ_inv : ∀ (a : H) (g : G), ρ (i a * g) = ρ g) (hρ_int : Integrable ρ (cosetMeasure μ ν i))
    (h_zero : ∫ g : G, ρ g ∂cosetMeasure μ ν i = 0) : Dense {g : G | ρ g = 0} := by
  let : MulAction H G := compHom G i
  have : SMulInvariantMeasure H G μ := ⟨by simp [compHom_smul_def]⟩
  have : ProperSMul H G := properSMul_of_isClosedEmbedding i hi fun _ _ ↦ rfl
  have : HasCutoff ν G := hasCutoff_of_proper
  exact dense_of_ae_orbitMeasure (fun a g hg ↦ (hρ_inv a g).trans hg)
    ((integral_eq_zero_iff_of_nonneg hρ_nonneg hρ_int).1 h_zero)

/-- Let `i : H → G` be a closed embedding of a unimodular group and `ρ ≥ 0` a continuous function
on `G`, invariant under left translation by `i(H)` and integrable for the quotient measure
`New.cosetMeasure` on `i(H) \ G`. If its integral is zero, then `ρ = 0`. -/
lemma New.eq_zero_of_integral_cosetMeasure_eq_zero [ν.IsMulRightInvariant] {i : H →* G}
    (hi : IsClosedEmbedding i) {ρ : G → ℝ} (hρ_cont : Continuous ρ) (hρ_nonneg : 0 ≤ ρ)
    (hρ_inv : ∀ (a : H) (g : G), ρ (i a * g) = ρ g) (hρ_int : Integrable ρ (cosetMeasure μ ν i))
    (h_zero : ∫ g : G, ρ g ∂cosetMeasure μ ν i = 0) : ρ = 0 :=
  hρ_cont.ext_on (dense_eq_zero_of_integral_cosetMeasure_eq_zero μ ν hi hρ_nonneg hρ_inv hρ_int
    h_zero) continuous_zero fun _ hg ↦ hg

/-- Let `i : H → G` be a closed embedding of a unimodular group and `ρ : G → ℂ` invariant under
left translation by `i(H)`, with nonnegative real part, integrable and with integral zero for the
quotient measure `New.cosetMeasure` on `i(H) \ G`. Then the real part of `ρ` vanishes on a dense
set. -/
lemma New.dense_re_eq_zero_of_integral_cosetMeasure_eq_zero [ν.IsMulRightInvariant] {i : H →* G}
    (hi : IsClosedEmbedding i) {ρ : G → ℂ} (hρ_nonneg : ∀ g : G, 0 ≤ (ρ g).re)
    (hρ_inv : ∀ (a : H) (g : G), ρ (i a * g) = ρ g) (hρ_int : Integrable ρ (cosetMeasure μ ν i))
    (h_zero : ∫ g : G, ρ g ∂cosetMeasure μ ν i = 0) : Dense {g : G | (ρ g).re = 0} :=
  dense_eq_zero_of_integral_cosetMeasure_eq_zero μ ν hi (ρ := fun g ↦ (ρ g).re) hρ_nonneg
    (fun a g ↦ by rw [hρ_inv]) hρ_int.re ((integral_re hρ_int).trans (congrArg Complex.re h_zero))

variable [T2Space H]

omit [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
  [BorelSpace G] in
/-- Let `i : L × H → G` be a continuous homomorphism, `κ` a right invariant measure on `L`, `ν` a
right invariant Haar measure on `H`, and `F` continuous, left invariant under the image of the
discrete `Λ ≤ H`. The integral of `F (i (l, a) * g)` over `a` in `Λ \ H` and then over `l` in `L`
is unchanged if `g` is replaced by `i k * g`. -/
lemma New.integral_integral_quotMeasure_translate {L : Type*} [Group L] [TopologicalSpace L]
    [MeasurableSpace L] [MeasurableMul L] (κ : Measure L) [κ.IsMulRightInvariant]
    [ν.IsMulRightInvariant] {i : L × H →* G} (hi : Continuous i) {F : G → ℂ} (hF : Continuous F)
    (hF_inv : (Λ.map (i.comp (MonoidHom.inr L H))).FixesLeft F) (k : L × H) (g : G) :
    ∫ l : L, ∫ a : H, F (i (l, a) * (i k * g)) ∂Λ.quotMeasure ν ∂κ =
      ∫ l : L, ∫ a : H, F (i (l, a) * g) ∂Λ.quotMeasure ν ∂κ := by
  -- Translate first in `Λ \ H`, then in `L`.
  have h_fibre (l : L) :
      ∫ a, F (i (l, a * k.2) * g) ∂Λ.quotMeasure ν = ∫ a, F (i (l, a) * g) ∂Λ.quotMeasure ν := by
    have h_left (γ : Λ) (a : H) : F (i (l, γ • a) * g) = F (i (l, a) * g) := by
      simpa [Subgroup.smul_def, ← mul_assoc, ← map_mul] using
        hF_inv (i (1, γ)) ⟨γ, γ.property, rfl⟩ (i (l, a) * g)
    exact (identDistrib_orbitMeasure_mul_right (F := fun a ↦ F (i (l, a) * g)) k.2 h_left
      (Continuous.measurable (by fun_prop))).integral_eq
  calc
    _ = ∫ l, ∫ a, F (i (l * k.1, a * k.2) * g) ∂Λ.quotMeasure ν ∂κ := by
      simp [Prod.mul_def, ← mul_assoc, ← map_mul]
    _ = ∫ l, ∫ a, F (i (l * k.1, a) * g) ∂Λ.quotMeasure ν ∂κ := by simp only [h_fibre]
    _ = ∫ l, ∫ a, F (i (l, a) * g) ∂Λ.quotMeasure ν ∂κ :=
      integral_mul_right_eq_self (fun l ↦ ∫ a, F (i (l, a) * g) ∂Λ.quotMeasure ν) k.1

/-- Let `i` embed `L × H` as a closed subgroup of `G`, with `L` and `H` unimodular, and let `Λ ≤ H`
be discrete with image `Γ`. For `F` continuous, left `Γ`-invariant and integrable on `Γ \ G`, the
integral of `F (i (l, a) * g)` over `a` in `Λ \ H` and then over `l` in `L` is integrable in `g` on
the quotient of `G` by `L × H`, and its integral there is the integral of `F` over `Γ \ G`. -/
lemma New.integral_quotMeasure_eq_integral_cosetMeasure_prod {L : Type*} [Group L]
    [TopologicalSpace L] [IsTopologicalGroup L] [PolishSpace L] [LocallyCompactSpace L]
    [MeasurableSpace L] [BorelSpace L] (κ : Measure L) [IsHaarMeasure κ] [κ.IsMulRightInvariant]
    [ν.IsMulRightInvariant] {i : L × H →* G} (hi : IsClosedEmbedding i) {F : G → ℂ}
    (hF : Continuous F) (hF_inv : (Λ.map (i.comp (MonoidHom.inr L H))).FixesLeft F)
    (hF_int : Integrable F ((Λ.map (i.comp (MonoidHom.inr L H))).quotMeasure μ)) :
    Integrable (fun g : G ↦ ∫ l : L, ∫ a : H, F (i (l, a) * g) ∂Λ.quotMeasure ν ∂κ)
      (cosetMeasure μ (κ.prod ν) i) ∧
    ∫ g : G, F g ∂(Λ.map (i.comp (MonoidHom.inr L H))).quotMeasure μ =
      ∫ g : G, ∫ l : L, ∫ a : H, F (i (l, a) * g) ∂Λ.quotMeasure ν ∂κ
        ∂cosetMeasure μ (κ.prod ν) i := by
  -- Unfold `Γ \ G` over `((L × H) \ G) × L` with fibre `Λ \ H`, then integrate over `L` first.
  let : MulAction (L × H) G := compHom G i
  have : SMulInvariantMeasure (L × H) G μ := ⟨by simp [compHom_smul_def]⟩
  have : ProperSMul (L × H) G := properSMul_of_isClosedEmbedding i hi fun _ _ ↦ rfl
  have : HasCutoff (κ.prod ν) G := hasCutoff_of_proper
  have hi_inr : IsEmbedding (i ∘ Prod.mk 1) := hi.isEmbedding.comp (isEmbedding_prodMkRight 1)
  have : DiscreteTopology (Λ.map (i.comp (.inr L H))) := (hi_inr.homeomorphImage Λ).discreteTopology
  let m : Measure G := cosetMeasure μ (κ.prod ν) i -- the measure on the quotient by `L × H`
  have : SFinite m := inferInstanceAs (SFinite (orbitMeasure (κ.prod ν) μ))
  have h_orbit : MeasurePreserving (fun p : G × (L × H) ↦ i p.2 * p.1) (m.prod (κ.prod ν)) μ :=
    measurePreserving_orbitMeasure
  have h_unfold : MeasurePreserving
      (fun p : (G × L) × H ↦ i (1, p.2) * (i (p.1.2, 1) * p.1.1)) ((m.prod κ).prod ν) μ := by
    simpa [Function.comp_def, MeasurableEquiv.prodAssoc, ← mul_assoc, ← map_mul] using
      h_orbit.comp (measurePreserving_prodAssoc m κ ν)
  obtain ⟨h_int, h_eq⟩ := integral_quotMeasure_stages Λ ν
    (T := fun p : G × L ↦ i (p.2, 1) * p.1) (i := i.comp (.inr L H)) hi_inr.injective h_unfold
    (hΓ := rfl) hF.measurable hF_inv hF_int
  rw [h_eq, integral_prod _ h_int]
  constructor
  · simpa [← mul_assoc, ← map_mul] using h_int.integral_prod_left
  · simp [m, ← mul_assoc, ← map_mul]

/-- Let `i` embed `L × H` as a closed subgroup of `G`, with `L` and `H` unimodular, let `Λ ≤ H` be
discrete, and write `Γ` for the image of `Λ` under `a ↦ i (1, a)`. Let `ρ : G → ℂ` have real part
that is nonnegative, and nonzero near some point `g₀`. There is `R ≠ 0`, independent of `F` and
`c`, with the following property. Suppose (a) `F` is continuous, left `Γ`-invariant and integrable
on `Γ \ G`. Suppose (b) each `g` has a `k` in `L × H` for which the integral of
`F (i (l, a) * (i k * g))` over `a` in `Λ \ H` and then over `l` in `L` is `ρ g * c`. Then the
integral of `F` over `Γ \ G` is `R * c`. -/
lemma New.Exchange.exists_integral_stages_eq_mul {L : Type*} [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] [PolishSpace L] [LocallyCompactSpace L] [MeasurableSpace L]
    [BorelSpace L] (κ : Measure L) [IsHaarMeasure κ] [κ.IsMulRightInvariant] [ν.IsMulRightInvariant]
    (i : L × H →* G) (hi : IsClosedEmbedding i) {g₀ : G} (ρ : G → ℂ)
    (hρ_nonneg : ∀ g : G, 0 ≤ (ρ g).re) (hρ_ne : ∀ᶠ g : G in 𝓝 g₀, (ρ g).re ≠ 0) :
    ∃ R : ℂ, R ≠ 0 ∧ ∀ F : G → ℂ, Continuous F →
      (Λ.map (i.comp (MonoidHom.inr L H))).FixesLeft F →
      Integrable F ((Λ.map (i.comp (MonoidHom.inr L H))).quotMeasure μ) →
      ∀ c : ℂ,
        (∀ g : G, ∃ k : L × H,
          ∫ l : L, ∫ a : H, F (i (l, a) * (i k * g)) ∂Λ.quotMeasure ν ∂κ = ρ g * c) →
        ∫ g : G, F g ∂(Λ.map (i.comp (MonoidHom.inr L H))).quotMeasure μ = R * c := by
  -- By unfolding in stages the integral of `F` is `ρ_integral * c`. If `c ≠ 0`, then `ρ_integral`
  -- is nonzero, as `ρ` is then invariant and integrable on the quotient.
  let ρ_integral : ℂ := ∫ g : G, ρ g ∂cosetMeasure μ (κ.prod ν) i
  obtain ⟨R, hR_ne, hR_eq⟩ : ∃ R : ℂ, R ≠ 0 ∧ (ρ_integral ≠ 0 → R = ρ_integral) :=
    ⟨if ρ_integral = 0 then 1 else ρ_integral, by grind⟩
  refine ⟨R, hR_ne, fun F hF hF_inv hF_int c h_inner ↦ ?_⟩
  -- The inner integral is unchanged by translation in `L × H`; this removes the element `k`.
  let innerIntegral (g : G) : ℂ := ∫ l : L, ∫ a : H, F (i (l, a) * g) ∂Λ.quotMeasure ν ∂κ
  have h_translate (k : L × H) (g : G) : innerIntegral (i k * g) = innerIntegral g :=
    integral_integral_quotMeasure_translate Λ ν κ hi.continuous hF hF_inv k g
  have h_inner_eq : innerIntegral = fun g : G ↦ ρ g * c :=
    funext fun g ↦ (h_inner g).elim fun k hk ↦ (h_translate k g).symm.trans hk
  obtain ⟨h_int, h_stages⟩ : Integrable innerIntegral (cosetMeasure μ (κ.prod ν) i) ∧
      _ = ∫ g : G, innerIntegral g ∂cosetMeasure μ (κ.prod ν) i :=
    integral_quotMeasure_eq_integral_cosetMeasure_prod Λ μ ν κ hi hF hF_inv hF_int
  rw [h_inner_eq, integral_mul_const] at h_stages
  obtain rfl | hc := eq_or_ne c 0
  · simpa using h_stages
  suffices h_ne : ρ_integral ≠ 0 by rwa [hR_eq h_ne]
  intro h_zero
  have hρ_int : Integrable ρ (cosetMeasure μ (κ.prod ν) i) := by
    simpa [h_inner_eq, hc] using h_int.div_const c
  have hρ_inv (k : L × H) (g : G) : ρ (i k * g) = ρ g :=
    mul_right_cancel₀ hc (by simpa only [h_inner_eq] using h_translate k g)
  exact mem_closure_iff_frequently.1 (dense_re_eq_zero_of_integral_cosetMeasure_eq_zero μ
    (κ.prod ν) hi hρ_nonneg hρ_inv hρ_int h_zero g₀) hρ_ne

end UnfoldingInStages

/-!
## Vanishing of quotient integrals by averaging or by a twist

The first criterion is proved by unfolding the integral along `H`
(`New.integral_quotMeasure_stages`). The second follows from the first, applied to a closed
subgroup built from the twist.
-/

section QuotientVanishing

open MeasureTheory Measure MulAction ProbabilityTheory Subgroup

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  (μ : Measure G) [IsHaarMeasure μ]
  {Γ : Subgroup G} [DiscreteTopology Γ] {F : G → V}

/-- Let `Γ ≤ H ≤ G` with `Γ` discrete and `H` closed, and let `F` be continuous and left
`Γ`-invariant. Let `κ` be a probability measure and `translator x b` elements of `H`, measurable in
`b`, such that right translation by `translator x b` carries the Haar measure of `H` to `d` times
itself and the `κ`-average over `b` of `F (s * translator x b * x)` is `a • F (s * x)` for all `s`
in `H`. If `a ≠ d`, the integral of `F` over `Γ \ G` vanishes. -/
lemma New.integral_quotMeasure_eq_zero_of_mean (hF_inv : Γ.FixesLeft F) (hF : Continuous F)
    {H : Subgroup G} [IsClosed (H : Set G)] (hΓH : Γ ≤ H)
    {C : Type*} [MeasurableSpace C] (κ : Measure C) [IsProbabilityMeasure κ]
    (translator : G → C → H) (h_meas : ∀ x : G, Measurable (translator x)) (d : NNReal)
    (h_scale : ∀ (x : G) (b : C), (haar : Measure H).map (· * translator x b) = d • haar)
    {a : ℂ} (ha : a ≠ (d : ℂ))
    (h_mean : ∀ (s : H) (x : G), ∫ b : C, F (↑(s * translator x b) * x) ∂κ = a • F (s * x)) :
    (Γ.quotMeasure μ)[F] = 0 := by
  borelize V
  rw [← (identDistrib_cutoffMeasure_quotMeasure hF.measurable hF_inv).integral_eq]
  exact Subgroup.integral_cutoffMeasure_eq_zero_of_mean μ hF hF_inv inferInstance hΓH haar κ
    translator h_meas d h_scale ha h_mean

/-- Let `F` be continuous and left invariant under the discrete subgroup `Γ`. If left translation
by some `u` multiplies `F` by a constant `c ≠ 1` of modulus one, the integral of `F` over
`Γ \ G` vanishes. -/
lemma New.integral_quotMeasure_eq_zero_of_twist (hF_inv : Γ.FixesLeft F) (hF : Continuous F)
    {u : G} {c : ℂ} (hc : ‖c‖ = 1) (hc_ne : c ≠ 1) (hu : ∀ y : G, F (u * y) = c • F y) :
    (Γ.quotMeasure μ)[F] = 0 := by
  borelize V
  rw [← (identDistrib_cutoffMeasure_quotMeasure hF.measurable hF_inv).integral_eq]
  exact Subgroup.integral_cutoffMeasure_eq_zero_of_twist μ hF hF_inv hc hc_ne hu

end QuotientVanishing
