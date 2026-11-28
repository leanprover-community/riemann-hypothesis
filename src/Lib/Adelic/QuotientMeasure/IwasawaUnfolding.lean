module

import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Topology.Algebra.ProperAction.Torsor
import Mathlib.Topology.Separation.CompletelyRegular
import TauCeti.Algebra.Group.Subgroup.SubgroupOf
import TauCeti.MeasureTheory.Group.OrbitCutoff.Iwasawa
import TauCeti.MeasureTheory.Integral.Bochner.SMulMeasure
public import Lib.Adelic.QuotientMeasure.Basic

/-!
# Unfolding over orbits and integration in Iwasawa coordinates

This file proves integration formulas on a quotient `Γ \ G` by a discrete subgroup `Γ`. An integral
over `Γ \ G` of a sum over translates is unfolded to an integral over the quotient by the subgroup
that keeps a block, in particular by the stabiliser of a point. Integrals of functions invariant
under a closed subgroup `N` are then written in Iwasawa coordinates `G = N · i(M) · K`.

* `Γ.quotMeasure μ`: the measure on `G` that integrates left `Γ`-invariant functions over `Γ \ G`.
* `N.FixesLeft F`: `F (γ * g) = F g` for all `γ ∈ N` and `g ∈ G`.

## Main definitions and results

* `New.integral_tsum_eq_integral_tsum_block`: the integral over `Γ \ G` of the sum over all
  translates of a block `C` is the integral over `S \ G` of the sum over `C`, where `S` is the
  group that keeps `C`. `New.integral_tsum_block` adds integrability and termwise integration.
* `New.integral_tsum_orbit_eq_integral_stabilizer`: the case of one orbit, with `S` the image of the
  stabiliser of a point.
* `New.integral_quotMeasure_iwasawa`: the integral over `Γ \ G` of a function `F` invariant under
  `N` and `Γ` is a nonzero constant times the integral of `w m * F (i m * k)`, where conjugation by
  `i m` scales the Haar measure of `N` by `w m`. It rests on Tau Ceti's Iwasawa formula
  `MeasureTheory.exists_lintegral_iwasawa_eq_mul`: `dn dm dk` in the coordinates `i m * n * k` is a
  multiple of Haar measure.

## Relation to the literature

Known result: The unfolding trick and the integration formula in Iwasawa coordinates on a quotient
by a discrete subgroup. Weil's formula for invariant integration on a quotient is in
`Lib.Adelic.QuotientMeasure.Basic`.
-/

@[expose] public section

/-!
## Unfolding a sum over an orbit

The unfolding trick for sums over a countable set `Y` with an action of a group `Λ`, which `i`
identifies with a discrete subgroup `Γ` of `G`. The summands `k y : G → ℂ` are measurable and
equivariant: `k (γ • y) (i γ * x) = k y x`.
-/

section OrbitUnfolding

open MeasureTheory Measure MulAction ProbabilityTheory ENNReal Set

open scoped Classical in
/-- Let `i` be injective, and let `γ` carry a point of `C` into `C` exactly when `i γ` lies in the
subgroup `S` of the range of `i`. If `β` has sum `1` over each `S`-orbit in `G`, then the sum of
`β (i γ * x)` over the `γ` that carry `y` into `C` is `1`, provided that there is such a `γ`. -/
lemma New.tsum_cutoff_smul_mem_eq_one {Λ G Y : Type*} [Group Λ] [Group G] [MulAction Λ Y]
    {i : Λ →* G} (hi : Function.Injective i) {S : Subgroup G} (hS : S ≤ i.range) {C : Set Y}
    (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S) {β : G → ℝ≥0∞}
    (hβ_one : ∀ x : G, ∑' s : S, β (s * x) = 1) {y : Y} {γ₀ : Λ} (hγ₀ : γ₀ • y ∈ C) (x : G) :
    ∑' γ : Λ, (if γ • y ∈ C then β (i γ * x) else 0) = 1 := by
  -- The point `(γ * γ₀) • y` lies in `C` exactly when `i γ ∈ S`.
  let b : G → ℝ≥0∞ := (S : Set G).indicator fun g ↦ β (g * (i γ₀ * x))
  calc ∑' γ : Λ, (if γ • y ∈ C then β (i γ * x) else 0)
    _ = ∑' γ : Λ, (if (γ * γ₀) • y ∈ C then β (i (γ * γ₀) * x) else 0) :=
        ((Equiv.mulRight γ₀).tsum_eq _).symm
    _ = ∑' γ : Λ, b (i γ) := by simp [b, indicator, mul_smul, mul_assoc, hC _ _ hγ₀]
    _ = ∑' g : G, b g := hi.tsum_eq fun g hg ↦ hS (support_indicator_subset hg)
    _ = ∑' s : S, β (s * (i γ₀ * x)) := (tsum_subtype (S : Set G) _).symm
    _ = 1 := hβ_one (i γ₀ * x)

/-- If the `k y` are measurable and `∑ ‖k y‖` has finite integral for `ν`, then `(x, y) ↦ k y x` is
integrable for the product of `ν` with the counting measure. -/
lemma New.integrable_prod_count_of_lintegral_lt_top {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y] [Countable Y] {ν : Measure X} {k : Y → X → ℂ}
    (hk_meas : ∀ y : Y, Measurable (k y)) (h_fin : ∫⁻ x : X, ∑' y : Y, ‖k y x‖ₑ ∂ν < ∞) :
    Integrable (fun p : X × Y ↦ k p.2 p.1) (ν.prod count) := by
  have h_meas : Measurable fun p : X × Y ↦ k p.2 p.1 := measurable_from_prod_countable_left hk_meas
  refine ⟨h_meas.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod _ h_meas.eNorm.aemeasurable]
  simpa only [lintegral_count] using h_fin

/-- If the `k y` are measurable and `∑ ‖k y‖` has finite integral, then `∑ k y` is integrable. -/
lemma New.integrable_tsum_of_lintegral_lt_top {X Y : Type*} [MeasurableSpace X] [Countable Y]
    {ν : Measure X} {k : Y → X → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (h_fin : ∫⁻ x : X, ∑' y : Y, ‖k y x‖ₑ ∂ν < ∞) :
    Integrable (fun x : X ↦ ∑' y : Y, k y x) ν := by
  let : MeasurableSpace Y := ⊤
  have h_prod : Integrable (fun p : X × Y ↦ k p.2 p.1) (ν.prod count) :=
    integrable_prod_count_of_lintegral_lt_top hk_meas h_fin
  simpa only [integral_count_eq_tsum] using h_prod.integral_prod_left

variable {Λ G Y : Type*} [Group Λ] [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [MulAction Λ Y] [Countable Y] {i : Λ →* G}

omit [Group G] [TopologicalSpace G] in
/-- If the `k y` are almost everywhere strongly measurable and `∑ ‖k y‖` has finite integral, then
the integrals of the `k y` sum to the integral of `∑ k y`. -/
lemma New.hasSum_integral_of_lintegral_tsum_lt_top {k : Y → G → ℂ} {ν : Measure G}
    (h_fin : ∫⁻ x : G, ∑' y : Y, ‖k y x‖ₑ ∂ν < ∞)
    (h_meas : ∀ y : Y, AEStronglyMeasurable (k y) ν := by fun_prop) :
    HasSum (fun y : Y ↦ ∫ x : G, k y x ∂ν) (∫ x : G, ∑' y : Y, k y x ∂ν) := by
  rw [lintegral_tsum (by fun_prop)] at h_fin
  rw [integral_tsum h_meas h_fin.ne]
  have h_le : ∑' y : Y, ‖∫ x, k y x ∂ν‖ₑ ≤ ∑' y : Y, ∫⁻ x, ‖k y x‖ₑ ∂ν :=
    tsum_le_tsum fun y ↦ eNorm_integral_le_lintegral_eNorm (k y)
  exact (Summable.of_eNorm (h_le.trans_lt h_fin).ne).hasSum

open scoped Classical in
omit [MeasurableSpace G] [Countable Y] in
/-- Let `i` map `Λ` isomorphically onto `Γ`, let `γ` carry a point of `C` into `C` exactly when
`i γ` lies in the subgroup `S` of `Γ`, and let `D` be the union of the translates of `C`. If `β` has
sum `1` over each `S`-orbit in `G`, then the sum of `β (i γ * x)` over the `γ` that carry `y` into
`C` is `1` if `y ∈ D` and `0` otherwise. -/
lemma New.tsum_cutoff_smul_mem_block (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {C D : Set Y} (hS : S ≤ Γ)
    (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S) (hD : ∀ y : Y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C)
    {β : G → ℝ≥0∞} (hβ_one : ∀ x : G, ∑' s : S, β (s * x) = 1) (y : Y) (x : G) :
    ∑' γ : Λ, (if γ • y ∈ C then β (i γ * x) else 0) = if y ∈ D then 1 else 0 := by
  subst hΓ
  split_ifs with hy
  · obtain ⟨γ₀, hγ₀⟩ := (hD y).1 hy
    exact tsum_cutoff_smul_mem_eq_one hi hS hC hβ_one hγ₀ x
  · simp [not_exists.1 (mt (hD y).2 hy)]

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [BorelSpace G]

/-- Unfolding of a sum of nonnegative terms over the translates of a block. Let `i` map `Λ`
isomorphically onto the discrete subgroup `Γ`, let `γ` carry a point of `C` into `C` exactly when
`i γ` lies in `S ≤ Γ`, and let `D` be the union of the translates of `C`. For measurable `g y` with
`g (γ • y) (i γ * x) = g y x`, the integral of `∑_D g y` over `Γ \ G` (that is, against
`Γ.quotMeasure μ`) is the integral of `∑_C g y` over `S \ G`. -/
lemma New.lintegral_tsum_block (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {C D : Set Y}
    (hS : S ≤ Γ) (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S)
    (hD : ∀ y : Y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C)
    {g : Y → G → ℝ≥0∞} (hg_meas : ∀ y : Y, Measurable (g y))
    (hg_inv : ∀ (γ : Λ) (y : Y) (x : G), g (γ • y) (i γ * x) = g y x) :
    ∫⁻ x : G, ∑' y : D, g y x ∂Γ.quotMeasure μ = ∫⁻ x : G, ∑' y : C, g y x ∂S.quotMeasure μ := by
  classical
  -- With `β` the cutoff of `S`, unfold the integral of `β x * ∑_C g y x` over `G` along `Γ` and
  -- substitute `y ↦ γ • y` in the term of `i γ`.
  have : DiscreteTopology S := .of_subset (s := Γ) inferInstance hS
  let β : G → ℝ≥0∞ := chosenCutoff (count : Measure S)
  obtain ⟨hβ_meas, hβ_int⟩ : IsCutoff (count : Measure S) β := isCutoff_chosenCutoff count
  have hβ_one (x : G) : ∑' s : S, β (s * x) = 1 := by
    simpa [lintegral_count, Subgroup.smul_def] using hβ_int x
  have h_term (γ : Λ) (x : G) : β (i γ * x) * ∑' y : C, g y (i γ * x) =
      ∑' y : Y, (if γ • y ∈ C then β (i γ * x) else 0) * g y x := by
    rw [tsum_subtype C fun y ↦ g y (i γ * x), ← (MulAction.toPerm γ).tsum_eq,
      ← ENNReal.tsum_mul_left]
    simp [indicator, hg_inv]
  have h_sum (x : G) : ∑' δ : Γ, β (δ * x) * ∑' y : C, g y (δ * x) = ∑' y : D, g y x := by
    subst hΓ
    calc ∑' δ : i.range, β (δ * x) * ∑' y : C, g y (δ * x)
      _ = ∑' γ : Λ, β (i γ * x) * ∑' y : C, g y (i γ * x) := ((i.ofInjective hi).tsum_eq _).symm
      _ = ∑' y : Y, (∑' γ : Λ, if γ • y ∈ C then β (i γ * x) else 0) * g y x := by
          simp only [h_term, ← ENNReal.tsum_mul_right]
          exact tsum_comm
      _ = ∑' y : D, g y x := by
          simp [tsum_cutoff_smul_mem_block hi rfl hS hC hD hβ_one, tsum_subtype D fun y ↦ g y x,
            indicator]
  have hS_meas : S.quotMeasure μ = μ.withDensity β := rfl
  calc ∫⁻ x, ∑' y : D, g y x ∂Γ.quotMeasure μ
    _ = ∫⁻ x, ∫⁻ δ : Γ, β (δ • x) * ∑' y : C, g y (δ • x) ∂count ∂Γ.quotMeasure μ := by
        simp only [lintegral_count, ← h_sum, Subgroup.smul_def, smul_eq_mul]
    _ = ∫⁻ x, β x * ∑' y : C, g y x ∂μ :=
        lintegral_orbitMeasure_lintegral (f := fun x ↦ β x * ∑' y : C, g y x) (by fun_prop)
    _ = ∫⁻ x, ∑' y : C, g y x ∂S.quotMeasure μ := by
        simp (disch := fun_prop) [hS_meas, lintegral_withDensity_eq_lintegral_mul]

/-- Let `i` map `Λ` isomorphically onto the discrete subgroup `Γ`, let `γ` carry a point of `C` into
`C` exactly when `i γ` lies in `S ≤ Γ`, and let `D` be the union of the translates of `C`. For
measurable `k y` with `k (γ • y) (i γ * x) = k y x`, the integral of `∑_D ‖k y‖` over `Γ \ G` is
the integral of `∑_C ‖k y‖` over `S \ G`. -/
lemma New.lintegral_tsum_enorm_block (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {C D : Set Y}
    (hS : S ≤ Γ) (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S)
    (hD : ∀ y : Y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C) {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x) :
    ∫⁻ x : G, ∑' y : D, ‖k y x‖ₑ ∂Γ.quotMeasure μ = ∫⁻ x : G, ∑' y : C, ‖k y x‖ₑ ∂S.quotMeasure μ :=
  lintegral_tsum_block hi hΓ hS hC hD (g := fun y x ↦ ‖k y x‖ₑ) (fun y ↦ (hk_meas y).eNorm)
    fun γ y x ↦ congrArg eNorm (hk γ y x)

/-- Unfolding of the integral of a sum over the translates of a block. Let `i` map `Λ`
isomorphically onto the discrete subgroup `Γ`, let `γ` carry a point of `C` into `C` exactly when
`i γ` lies in `S ≤ Γ`, and let `D` be the union of the translates of `C`. Let the `k y` be
measurable with `k (γ • y) (i γ * x) = k y x`. If `∑_C ‖k y‖` has finite integral over `S \ G`,
then the integral of `∑_D k y` over `Γ \ G` is the integral of `∑_C k y` over `S \ G`. -/
lemma New.integral_tsum_eq_integral_tsum_block (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {C D : Set Y}
    (hS : S ≤ Γ) (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S)
    (hD : ∀ y : Y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C) {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x)
    (h_fin : ∫⁻ x : G, ∑' y : C, ‖k y x‖ₑ ∂S.quotMeasure μ < ∞) :
    ∫ x : G, ∑' y : D, k y x ∂Γ.quotMeasure μ = ∫ x : G, ∑' y : C, k y x ∂S.quotMeasure μ := by
  -- The functions `(x, y) ↦ k y x` on `(Γ \ G) × D` and on `(S \ G) × C` have the same
  -- distribution; the claim follows by Fubini.
  let : MeasurableSpace Y := ⊤
  have h_meas : Measurable fun p : Y × G ↦ k p.1 p.2 := measurable_from_prod_countable_right hk_meas
  have h_unfold (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
      ∫⁻ x, ∑' y : D, f (k y x) ∂Γ.quotMeasure μ = ∫⁻ x, ∑' y : C, f (k y x) ∂S.quotMeasure μ :=
    lintegral_tsum_block hi hΓ hS hC hD (g := fun y x ↦ f (k y x)) (by fun_prop) (by simp [hk])
  have h_dist : IdentDistrib (fun p : G × D ↦ k p.2 p.1) (fun p : G × C ↦ k p.2 p.1)
      ((Γ.quotMeasure μ).prod count) ((S.quotMeasure μ).prod count) := by
    refine ⟨by fun_prop, by fun_prop, ext_of_lintegral _ fun f hf ↦ ?_⟩
    simpa (disch := fun_prop) only [lintegral_map, lintegral_prod, lintegral_count]
      using h_unfold f hf
  have hC_int : Integrable (fun p : G × C ↦ k p.2 p.1) ((S.quotMeasure μ).prod count) :=
    integrable_prod_count_of_lintegral_lt_top (fun y : C ↦ hk_meas y) h_fin
  have hD_int := h_dist.integrable_iff.2 hC_int
  calc ∫ x, ∑' y : D, k y x ∂Γ.quotMeasure μ
    _ = ∫ p : G × D, k p.2 p.1 ∂(Γ.quotMeasure μ).prod count := by
        simp only [integral_prod _ hD_int, integral_count_eq_tsum]
    _ = ∫ p : G × C, k p.2 p.1 ∂(S.quotMeasure μ).prod count := h_dist.integral_eq
    _ = ∫ x, ∑' y : C, k y x ∂S.quotMeasure μ := by
        simp only [integral_prod _ hC_int, integral_count_eq_tsum]

/-- Unfolding of a sum of integrals over the translates of a block. Let `i` map `Λ` isomorphically
onto the discrete subgroup `Γ`, let `γ` carry a point of `C` into `C` exactly when `i γ` lies in
`S ≤ Γ`, and let `D` be the union of the translates of `C`. Let the `k y` be measurable with
`k (γ • y) (i γ * x) = k y x`. If `∑_C ‖k y‖` has finite integral over `S \ G`, then the sum over
`D` of the integrals of `k y` against the measure of `Γ \ G` is the integral of `∑_C k y` over
`S \ G`. -/
lemma New.tsum_integral_eq_integral_tsum_block (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {C D : Set Y}
    (hS : S ≤ Γ) (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S)
    (hD : ∀ y : Y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C) {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x)
    (h_fin : ∫⁻ x : G, ∑' y : C, ‖k y x‖ₑ ∂S.quotMeasure μ < ∞) :
    ∑' y : D, ∫ x : G, k y x ∂Γ.quotMeasure μ = ∫ x : G, ∑' y : C, k y x ∂S.quotMeasure μ := by
  rw [← integral_tsum_eq_integral_tsum_block hi hΓ hS hC hD hk_meas hk h_fin]
  rw [← lintegral_tsum_enorm_block hi hΓ hS hC hD hk_meas hk] at h_fin
  exact (hasSum_integral_of_lintegral_tsum_lt_top h_fin).tsum_eq

/-- Unfolding of a sum over the translates of a block. The group `Λ` acts on `Y` and `i` maps it
isomorphically onto the discrete subgroup `Γ` of `G`; the terms are measurable and satisfy
`k (γ • y) (i γ * x) = k y x`. The block `C ⊆ Y` is such that `γ` carries a point of `C` into `C`
exactly when `i γ` lies in `S ≤ Γ`, and `D` is the union of the translates of `C`. Suppose that
`∑_D ‖k y‖` has finite integral over `Γ \ G` or that `∑_C ‖k y‖` has finite integral over `S \ G`.
Then `∑_C k y` is integrable over `S \ G`. Its integral equals the integral of `∑_D k y` over
`Γ \ G`. It also equals the sum over `D` of the integrals of `k y` against the measure of `Γ \ G`.
-/
lemma New.integral_tsum_block (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {C D : Set Y}
    (hS : S ≤ Γ) (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S)
    (hD : ∀ y : Y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C) {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x)
    (h_fin : ∫⁻ x : G, ∑' y : D, ‖k y x‖ₑ ∂Γ.quotMeasure μ < ∞ ∨
      ∫⁻ x : G, ∑' y : C, ‖k y x‖ₑ ∂S.quotMeasure μ < ∞) :
    Integrable (fun x : G ↦ ∑' y : C, k y x) (S.quotMeasure μ) ∧
    ∫ x : G, ∑' y : D, k y x ∂Γ.quotMeasure μ = ∫ x : G, ∑' y : C, k y x ∂S.quotMeasure μ ∧
    ∑' y : D, ∫ x : G, k y x ∂Γ.quotMeasure μ = ∫ x : G, ∑' y : C, k y x ∂S.quotMeasure μ := by
  -- The two finiteness hypotheses are equivalent.
  rw [lintegral_tsum_enorm_block hi hΓ hS hC hD hk_meas hk, or_self] at h_fin
  exact ⟨integrable_tsum_of_lintegral_lt_top (fun y : C ↦ hk_meas y) h_fin,
    integral_tsum_eq_integral_tsum_block hi hΓ hS hC hD hk_meas hk h_fin,
    tsum_integral_eq_integral_tsum_block hi hΓ hS hC hD hk_meas hk h_fin⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [Countable Y] in
/-- If `k (γ • y) (i γ * x) = k y x`, then the term `k y` is invariant on the left under the image
`S` of the stabiliser of `y`. -/
lemma New.fixesLeft_map_stabilizer {S : Subgroup G} {k : Y → G → ℂ}
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x)
    {y : Y} (h_stab : (stabilizer Λ y).map i = S) : S.FixesLeft (k y) := by
  subst h_stab
  rintro _ ⟨γ, hγ, rfl⟩ x
  rw [← hk γ y x, mem_stabilizer_iff.1 hγ]

/-- Unfolding of a sum over an orbit. Let `i` be injective with discrete range `Γ`, let the terms
`k z` be measurable and equivariant, and let `S` be the image under `i` of the stabiliser of `y`.
Suppose that the sum of the `‖k z‖` over the orbit of `y` has finite integral over `Γ \ G`, or that
`k y` is integrable over `S \ G`. Then `k y` is integrable over `S \ G`, and its integral equals the
integral over `Γ \ G` of the sum of the `k z` over the orbit, and also the sum of their
integrals. -/
lemma New.integral_tsum_orbit_eq_integral_stabilizer (hi : Function.Injective i)
    [DiscreteTopology i.range] {μ : Measure G} [IsHaarMeasure μ]
    {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x) {y : Y}
    (h_fin : ∫⁻ x : G, ∑' z : orbit Λ y, ‖k z x‖ₑ ∂i.range.quotMeasure μ < ∞ ∨
      Integrable (k y) (((stabilizer Λ y).map i).quotMeasure μ)) :
    Integrable (k y) (((stabilizer Λ y).map i).quotMeasure μ) ∧
    ∫ x : G, ∑' z : orbit Λ y, k z x ∂i.range.quotMeasure μ =
      ∫ x : G, k y x ∂((stabilizer Λ y).map i).quotMeasure μ ∧
    ∑' z : orbit Λ y, ∫ x : G, k z x ∂i.range.quotMeasure μ =
      ∫ x : G, k y x ∂((stabilizer Λ y).map i).quotMeasure μ := by
  -- The case `C = {y}` of `integral_tsum_block`: the orbit is the union of the translates of `{y}`.
  have hC : ∀ γ : Λ, ∀ z ∈ ({y} : Set Y),
      γ • z ∈ ({y} : Set Y) ↔ i γ ∈ (stabilizer Λ y).map i := by
    simp [Subgroup.mem_map_iff_mem hi]
  have hD (z : Y) : z ∈ orbit Λ y ↔ ∃ γ : Λ, γ • z ∈ ({y} : Set Y) := by
    simp [mem_orbit_symm (a₁ := z), mem_orbit_iff]
  have h_block : ∫⁻ x, ∑' z : orbit Λ y, ‖k z x‖ₑ ∂i.range.quotMeasure μ < ∞ ∨
      ∫⁻ x, ∑' z : ({y} : Set Y), ‖k z x‖ₑ ∂((stabilizer Λ y).map i).quotMeasure μ < ∞ :=
    h_fin.imp_right fun h_int ↦ by simpa [HasFiniteIntegral] using h_int.hasFiniteIntegral
  simpa using
    integral_tsum_block hi rfl ((stabilizer Λ y).map_le_range i) hC hD hk_meas hk h_block

/-- Unfolding of a sum over an orbit, with the subgroups and the orbit given by equations: `Γ` is
the discrete range of the injective map `i`, `S` the image of the stabiliser of `y`, and `D` the
orbit of `y`. Here `Γ.quotMeasure μ` is the measure on `G` that computes integrals over `Γ \ G`: the
Haar measure `μ` weighted by a cutoff for `Γ`, and likewise for `S`. The terms `k z` are measurable
and equivariant. Suppose that `∑ ‖k z‖`, over all `z : Y`, has finite integral over `Γ \ G` or that
`k y` is integrable over `S \ G`. Then `k y` is integrable over `S \ G`, and its integral equals the
integral of `∑_D k z` over `Γ \ G` and also the sum over `D` of the integrals of `k z` against
`Γ.quotMeasure μ`. -/
lemma New.integral_tsum_orbit_of_lt_top_or_integrable (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {D : Set Y}
    {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x)
    {y : Y} (h_stab : (stabilizer Λ y).map i = S) (h_orbit : ∀ z : Y, z ∈ D ↔ y ∈ orbit Λ z)
    (h_fin : ∫⁻ x : G, ∑' z : Y, ‖k z x‖ₑ ∂Γ.quotMeasure μ < ∞ ∨
      Integrable (k y) (S.quotMeasure μ)) :
    Integrable (k y) (S.quotMeasure μ) ∧
    ∫ x : G, ∑' z : D, k z x ∂Γ.quotMeasure μ = ∫ x : G, k y x ∂S.quotMeasure μ ∧
    ∑' z : D, ∫ x : G, k z x ∂Γ.quotMeasure μ = ∫ x : G, k y x ∂S.quotMeasure μ := by
  obtain rfl : D = orbit Λ y := Set.ext fun z ↦ (h_orbit z).trans mem_orbit_symm
  subst hΓ h_stab
  -- The sum over the orbit is at most the sum over all of `Y`.
  exact integral_tsum_orbit_eq_integral_stabilizer hi hk_meas hk <| h_fin.imp_left <|
    (lintegral_mono fun x ↦ tsum_comp_le_tsum_of_injective Subtype.val_injective _).trans_lt

/-- Left invariance of `k y` and unfolding over the orbit `D` of `y`, as one statement. Here `i`
maps `Λ` isomorphically onto the discrete subgroup `Γ`, `S` is the image under `i` of the stabiliser
of `y`, and the `k z` are measurable and equivariant. The conclusion has two parts. The first says
that `k y` is left `S`-invariant (`S.FixesLeft (k y)`). The second is the implication proved in
`integral_tsum_orbit_of_lt_top_or_integrable`: if `∑ ‖k z‖` has finite integral over `Γ \ G` or
`k y` is integrable over `S \ G`, then `k y` is integrable over `S \ G`, and its integral equals
both the integral of `∑_D k z` over `Γ \ G` and the sum over `D` of the integrals of the `k z`. -/
lemma New.integral_tsum_orbit (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {D : Set Y}
    {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x)
    {y : Y} (h_stab : (stabilizer Λ y).map i = S) (h_orbit : ∀ z : Y, z ∈ D ↔ y ∈ orbit Λ z) :
    S.FixesLeft (k y) ∧
    ((∫⁻ x : G, ∑' z : Y, ‖k z x‖ₑ ∂Γ.quotMeasure μ < ∞ ∨ Integrable (k y) (S.quotMeasure μ)) →
      Integrable (k y) (S.quotMeasure μ) ∧
      ∫ x : G, ∑' z : D, k z x ∂Γ.quotMeasure μ = ∫ x : G, k y x ∂S.quotMeasure μ ∧
      ∑' z : D, ∫ x : G, k z x ∂Γ.quotMeasure μ = ∫ x : G, k y x ∂S.quotMeasure μ) :=
  ⟨fixesLeft_map_stabilizer hk h_stab,
    integral_tsum_orbit_of_lt_top_or_integrable hi hΓ hk_meas hk h_stab h_orbit⟩

end OrbitUnfolding

/-!
## Iwasawa integration formula

Integration in Iwasawa coordinates on a unimodular group `G = N · i(M) · K`, with `N` closed, `K`
compact and `i : M →* G` continuous. It is used for constant terms along a unipotent radical `N`.
-/

section IwasawaIntegration

open MeasureTheory Measure ENNReal NeZero ProbabilityTheory Function

variable {G M : Type*} [Group G] [Group M] [TopologicalSpace G] [IsTopologicalGroup G]
  [PolishSpace G] (w : M → ℝ) [MeasurableSpace G] [BorelSpace G] [TopologicalSpace M]
  [IsTopologicalGroup M] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure G) [IsHaarMeasure μ] [IsMulRightInvariant μ]
  (ν : Measure M) [IsHaarMeasure ν]
  {N K Γ : Subgroup G} [IsMulRightInvariant ν] [CompactSpace K]
  (κ : Measure K) [IsHaarMeasure κ]
  {lam : Measure N} [IsHaarMeasure lam] (i : M →* G)

variable [LocallyCompactSpace G]

omit [TopologicalSpace M] [IsTopologicalGroup M] [MeasurableSpace M] [BorelSpace M] in
/-- Let `i a` lie in the closed unimodular subgroup `N` only for `a = 1`, let `δ` be injective, and
let the discrete group `Γ` contain every `i (δ d)` and lie in the union of the `N · i (δ d)⁻¹`.
Suppose that conjugation by `i m` multiplies integrals over `N` by `w m`. Then `w m` times the
integral over `(Γ ∩ N) \ N` (that is, against `quotMeasure lam`) of a sum over `Γ` unfolds to a sum
over `d` of integrals over `N` against the Haar measure `lam`. -/
lemma New.ofReal_mul_lintegral_quotMeasure_tsum
    (hN : IsClosed (N : Set G))
    (h_conj : ∀ (m : M) (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = ENNReal.ofReal (w m) * ∫⁻ n : N, f n ∂lam)
    (h_triv : ∀ a : M, i a ∈ N → a = 1) {D : Type*} [Countable D] {δ : D → M} (hδ : δ.Injective)
    (hδ_mem : ∀ d : D, i (δ d) ∈ Γ) (hΓ : ∀ g ∈ Γ, ∃ d : D, g * i (δ d) ∈ N) [DiscreteTopology Γ]
    {f : G → ℝ≥0∞} (hf : Measurable f) (m : M) (k : G) :
    ENNReal.ofReal (w m) *
        ∫⁻ n : N, ∑' γ : Γ, f (γ * (n * (i m * k))) ∂(Γ.subgroupOf N).quotMeasure lam =
      ∑' d : D, ∫⁻ n : N, f (i (δ d * m) * n * k) ∂lam := by
  -- Write the elements of `Γ` as `i (δ d) * γ` with `γ ∈ Γ ∩ N`, unfold the quotient measure to
  -- `lam`, and move `i m` past `n`.
  obtain ⟨e, he⟩ := Subgroup.exists_equiv_prod_subgroupOf h_triv hδ hδ_mem hΓ
  simp only [← e.tsum_eq, tsum_prod', he]
  rw [lintegral_tsum (by fun_prop), ← ENNReal.tsum_mul_left]
  refine tsum_congr fun d ↦ ?_
  calc ENNReal.ofReal (w m) * ∫⁻ n : N, ∑' γ : Γ.subgroupOf N,
        f (i (δ d) * (γ : N) * (n * (i m * k))) ∂(Γ.subgroupOf N).quotMeasure lam
    _ = ENNReal.ofReal (w m) * ∫⁻ n : N, f (i (δ d) * n * i m * k) ∂lam := by
      rw [← lintegral_orbitMeasure_lintegral (ν := (count : Measure (Γ.subgroupOf N)))
        (f := fun n : N ↦ f (i (δ d) * n * i m * k)) (by fun_prop)]
      simp [lintegral_count, Subgroup.smul_def, mul_assoc]
    _ = ∫⁻ n : N, f (i (δ d) * (i m * n * (i m)⁻¹) * i m * k) ∂lam :=
      (h_conj m (fun y ↦ f (i (δ d) * y * i m * k)) (by fun_prop)).symm
    _ = ∫⁻ n : N, f (i (δ d * m) * n * k) ∂lam := by simp [mul_assoc]

/-- Unfolding in Iwasawa coordinates. Let `μ`, `ν`, `κ`, `lam` be Haar measures on the unimodular
group `G`, the unimodular group `M`, the compact subgroup `K` and the closed subgroup `N`, and let
`i` and `w` be continuous. Suppose that `G = N · i(M) · K`, that conjugation by `i m` multiplies
integrals over `N` by `w m > 0`, and that `i a` lies in `N` only for `a = 1`. Let `δ` be injective,
and let `Γ` be discrete, contain every `i (δ d)` and lie in the union of the `N · i (δ d)⁻¹`, with
`Γ ∩ N` cocompact in `N` (`IsCocompact`: every element of `N` has a left translate by `Γ ∩ N` in a
fixed compact set). Let `α` be a measure on `M` that unfolds to `ν` along `δ`. There is `c ≠ 0` such
that for measurable `F`, left invariant under `N` and `Γ` (`FixesLeft`): if
`(m, k) ↦ w m * F (i m * k)` is integrable for `α × κ`, then `F` is integrable over `Γ \ G` (against
`Γ.quotMeasure μ`), and its integral is `c` times the integral of `w m * F (i m * k)`. -/
lemma New.integral_quotMeasure_iwasawa [PolishSpace M] [LocallyCompactSpace M]
    (hN : IsClosed (N : Set G)) (hw : Continuous w) (hw_pos : ∀ m : M, 0 < w m) (hi : Continuous i)
    (h_dec : ∀ g : G, ∃ n : N, ∃ m : M, ∃ k : K, g = n * i m * k)
    (h_conj : ∀ (m : M) (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = ENNReal.ofReal (w m) * ∫⁻ n : N, f n ∂lam)
    (h_triv : ∀ a : M, i a ∈ N → a = 1) {D : Type*}
    [Countable D] {δ : D → M} (hδ : δ.Injective) (α : Measure M) [SFinite α]
    (hα : ∀ f : M → ℝ≥0∞, Measurable f → ∫⁻ m : M, f m ∂ν = ∫⁻ m : M, ∑' d : D, f (δ d * m) ∂α)
    (hδ_mem : ∀ d : D, i (δ d) ∈ Γ) (hΓ : ∀ g ∈ Γ, ∃ d : D, g * i (δ d) ∈ N) [DiscreteTopology Γ]
    (h_cocpt : (Γ.subgroupOf N).IsCocompact) :
    ∃ c ≠ (0 : ℝ), ∀ F : G → ℂ, Measurable F → N.FixesLeft F → Γ.FixesLeft F →
      Integrable (fun p : M × K ↦ (w p.1 : ℂ) * F (i p.1 * p.2)) (α.prod κ) →
      Integrable F (Γ.quotMeasure μ) ∧
      ∫ g : G, F g ∂Γ.quotMeasure μ =
        c * ∫ p : M × K, (w p.1 : ℂ) * F (i p.1 * p.2) ∂α.prod κ := by
  -- The Iwasawa formula with factor `r`, unfolded along `Γ = {i (δ d) * γ}`, says that the measure
  -- `w · (α × κ) × (Γ ∩ N)\N` in the coordinates `n * i m * k` is the quotient of `r • μ` by `Γ`.
  -- The cocompact subgroup `Γ ∩ N` is a lattice in `N`, so `N` is unimodular.
  let lam' : Measure N := (Γ.subgroupOf N).quotMeasure lam
  have h_finite : IsFiniteMeasure lam' := isFiniteMeasure_quotMeasure_of_cocompact lam h_cocpt
  have : lam.IsMulRightInvariant := isMulRightInvariant_of_finite_covolume h_finite
  obtain ⟨r, h_iwa⟩ := exists_lintegral_iwasawa_eq_mul (ν := ν) (κ := κ) (lam := lam) μ hN hw_pos hi
    h_dec h_conj
  -- For `f = 1` the left side of `h_iwa` is a product of nonzero total masses.
  have hr : r ≠ 0 := fun h ↦ by simpa [h, NeZero.ne] using h_iwa 1 measurable_one
  have hw_meas : Measurable fun p : M × K ↦ ENNReal.ofReal (w p.1) := by fun_prop
  let ρ : Measure (M × K) := (α.prod κ).withDensity fun p ↦ .ofReal (w p.1)
  let σ (p : M × K) : G := i p.1 * p.2
  let τ (p : (M × K) × N) : G := p.2 * σ p.1
  have h_unfold : MeasurePreserving (fun p : ((M × K) × N) × Γ ↦ p.2 • τ p.1)
      ((ρ.prod lam').prod count) (r • μ) := by
    refine ⟨by fun_prop, ext_of_lintegral _ fun f hf ↦ ?_⟩
    calc
      _ = ∫⁻ p : M × K, ∫⁻ n : N, ∑' γ : Γ, f (γ * (n * (i p.1 * p.2))) ∂lam' ∂ρ := by
        simp (disch := fun_prop) only [lintegral_map, lintegral_prod, lintegral_count,
          Subgroup.smul_def, smul_eq_mul, τ, σ]
      _ = ∫⁻ k : K, ∫⁻ m : M, ∑' d : D, ∫⁻ n : N, f (i (δ d * m) * n * k) ∂lam ∂α ∂κ := by
        rw [lintegral_withDensity_eq_lintegral_mul _ hw_meas (by fun_prop),
          lintegral_prod_symm _ (by fun_prop)]
        simp only [Pi.mul_apply, lam',
          ofReal_mul_lintegral_quotMeasure_tsum w i hN h_conj h_triv hδ hδ_mem hΓ hf]
      _ = ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, f (i m * n * k) ∂lam ∂ν ∂κ :=
        lintegral_congr fun k ↦ (hα (fun m ↦ ∫⁻ n : N, f (i m * n * k) ∂lam) (by fun_prop)).symm
      _ = ∫⁻ g, f g ∂(r • μ) := by rw [h_iwa f hf, lintegral_smul_measure, smul_eq_mul]
  obtain ⟨c, hc, h_div⟩ := exists_integral_eq_mul_of_smul_measure (E := ℂ) (Γ.quotMeasure μ) hr
    (NeZero.ne (lam' .univ)) (measure_ne_top lam' .univ)
  refine ⟨c, hc, fun F hF hFN hFΓ h_weighted ↦ ?_⟩
  -- By `h_unfold`, `F` on `Γ \ G` has the law of `F ∘ τ`, and `F ∘ τ` does not depend on `n`.
  have hFτ (p : (M × K) × N) : F (τ p) = F (σ p.1) := hFN p.2 p.2.property (σ p.1)
  have h_law : IdentDistrib F (fun p : M × K ↦ F (σ p)) (r • Γ.quotMeasure μ)
      (lam' .univ • ρ) := by
    rw [← show Γ.quotMeasure (r • μ) = r • Γ.quotMeasure μ from withDensity_smul_measure r _]
    refine (identDistrib_orbitMeasure_of_unfold (T := τ) (.id (count : Measure Γ)) h_unfold hF
      (by fun_prop) fun γ x ↦ hFΓ γ γ.property x).trans ⟨by fun_prop, by fun_prop, ?_⟩
    simp (disch := fun_prop) only [hFτ, ← map_fst_prod, map_map, comp_def]
  have h_int : Integrable (fun p : M × K ↦ F (σ p)) ρ := by
    simpa [ρ, integrable_withDensity_iff_integrable_smul' hw_meas, hw_pos, le_of_lt]
      using h_weighted
  rw [← Complex.real_smul]
  refine h_div F _ (h_law.integrable_iff.2 (h_int.smul_measure (measure_ne_top lam' .univ))) ?_
  rw [h_law.integral_eq, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hw_meas (by simp)]
  simp [σ, hw_pos, le_of_lt]

end IwasawaIntegration
