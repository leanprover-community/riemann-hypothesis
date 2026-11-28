module

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.Finset.Functor
import Mathlib.Topology.Algebra.Group.Units
public import Lib.SiegelWeil.UnramifiedSeries.VacuumCoefficients
public import Lib.Adelic.AutomorphicForms.Basic
import Lib.Adelic.Adeles.StrongApproximation
import Lib.Shimura.ComplexTheta.AppellHumbertData
import Lib.SiegelWeil.RallisInner.VacuumSummability

/-!
# The series of translates weighted by the coefficients of the vacuum

This file proves, for `2 n < m`, that the series `New.SiegelWeil.rallisSeries` converges uniformly
(the coefficients are absolutely summable by `New.SiegelWeil.summable_norm_vacuumCoeff`, from the
doubling formula), that it keeps levels and forms and that it is multiplicative over the places. The
last section defines the sum of the coefficients `New.SiegelWeil.vacuumSum` and writes it as a
product over the pairs of conjugate places.

Let `G_f` be the finite adelic unitary group of rank `n` over the CM field `E`, and let `A` be a set
of finite places. The series `∑ mc(γ) R(γ) y` runs over the cosets `γ` of the points integral at
`A`; here `R` is right translation and `mc(γ)` is the coefficient of the vacuum for a second space
of rank `m`, of modulus `[γ L : L ∩ γ L] ^ (-m / 2)` for the standard lattice `L`. In the inner
product formula `A` is the set of the places off the level and its conjugate.

## Main definitions and results

* `New.SiegelWeil.exists_form_eq_rallisSeries`: the series keeps forms and their levels.
* `New.SiegelWeil.rallisSeries_union`: the series is multiplicative over the places.

Notions from other files:
* `localLevel n A`: the points of `G_f` integral at the places of `A`; `stdLevel E n`: the points
  integral at all finite places; `supportedOn n A`: the points with component `1` outside `A` and
  its conjugate, whose union is `A.conjClosure`.
* `HasLevel y K`: right translation by each point of `K` fixes the function `y` on the adelic points
  `G E s`, the products of a point of `GInf E s` (the real points, the only part that depends on the
  signs `s : n → ℤˣ`) and a point of `Gf E n`.
* `New.SiegelWeil.rallisSeries M b A y`: the series `∑ mc(q) R(q) y`, with coefficient
  `New.SiegelWeil.vacuumCoeff M b` and right translation taken at `New.SiegelWeil.cosetRep q`.
* `New.SiegelWeil.IsUnramifiedOn`: `b ∘ det` is trivial on the integral finite points supported on
  `A` and its conjugate.

## Relation to the literature

Part of a known result: non-vanishing of theta lifts in large rank. See
`Lib.SiegelWeil.RallisInner.SharpData`. The series is the contribution of the unramified places to
Rallis' inner product formula, left as a sum over cosets instead of being evaluated as an L-value;
for the constant `1` in rank one it is evaluated in `New.vacuumSum_eq_L_div_eulerProd`.
-/

@[expose] public section

noncomputable section

namespace New.SiegelWeil

open Matrix MeasureTheory Fintype Space Gf G WeilData NumberField Rows

variable {E n m : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] [Fintype m]
  {s : n → ℤˣ} {b : AutChar E} {A : Set (FinPlace E)} {y : G E s → ℂ}

/-! ### Convergence, level and forms -/

/-- For `2 * card n < card m` and `y` bounded, the series `rallisSeries` converges uniformly: its
partial sums over finite sets of cosets tend to it uniformly. -/
lemma tendstoUniformly_rallisSeries (h_rank : 2 * card n < card m) (b : AutChar E)
    (A : Set (FinPlace E)) (hy : ∃ C : ℝ, ∀ g : G E s, ‖y g‖ ≤ C) :
    TendstoUniformly
      (fun (Q : Finset (Gf E n ⧸ localLevel n A)) (g : G E s) ↦
        ∑ q ∈ Q, vacuumCoeff (card m) b (cosetRep q).val * y (g * (1, (cosetRep q).val)))
      (rallisSeries (card m) b A y) Filter.atTop := by
  obtain ⟨C, hC⟩ := hy
  exact tendstoUniformly_tsum ((summable_norm_vacuumCoeff h_rank b A).mul_right C)
    fun q g ↦ norm_mul_le_of_le le_rfl (hC _)

/-- For `2 * card n < card m` and `y` bounded by `C`, the series `rallisSeries` is bounded by `C`
times the sum of the moduli of the coefficients of the vacuum. -/
lemma norm_rallisSeries_le (h_rank : 2 * card n < card m) (b : AutChar E)
    (A : Set (FinPlace E)) {C : ℝ} (hC : ∀ g : G E s, ‖y g‖ ≤ C) (g : G E s) :
    ‖rallisSeries (card m) b A y g‖ ≤
      (∑' q : Gf E n ⧸ localLevel n A, ‖vacuumCoeff (card m) b (cosetRep q).val‖) * C :=
  tsum_of_norm_bounded ((summable_norm_vacuumCoeff h_rank b A).hasSum.mul_right C)
    fun _ ↦ norm_mul_le_of_le le_rfl (hC _)

/-- For `2 * card n < card m` and `y` continuous and bounded, the series `rallisSeries` is
continuous. -/
lemma continuous_rallisSeries (h_rank : 2 * card n < card m) (b : AutChar E)
    (A : Set (FinPlace E)) (hy_cont : Continuous y) (hy_bdd : ∃ C : ℝ, ∀ g : G E s, ‖y g‖ ≤ C) :
    Continuous (rallisSeries (card m) b A y) :=
  (tendstoUniformly_rallisSeries h_rank b A hy_bdd).continuous
    (.of_forall fun _ ↦ by fun_prop)

/-- The series `rallisSeries M b A y` is `∑_q vacuumCoeff M b (cosetRep q) · R(cosetRep q) y`, a sum
of right translates of a function `y` on the adelic points `G E s`. The sum runs over the cosets
`q`, in the finite points, of the subgroup of points integral at `A`, with representatives supported
on `A` and its conjugate. The series commutes with left translations with no convergence hypothesis:
applied to `g' ↦ y (x * g')` and evaluated at `g`, it equals `rallisSeries M b A y` at `x * g`. -/
lemma rallisSeries_comp_mul_left (M : ℕ) (b : AutChar E) (A : Set (FinPlace E)) (y : G E s → ℂ)
    (x g : G E s) :
    rallisSeries M b A (fun g' : G E s ↦ y (x * g')) g = rallisSeries M b A y (x * g) := by
  simp only [rallisSeries, mul_assoc]

/-- Let `b ∘ det` be trivial on the integral points supported on `A` and its conjugate, and let `y`
be fixed by these points. A finite point `k` integral at `A` that fixes `y` also fixes
`rallisSeries M b A y`, the series of translates of `y` weighted by the coefficients of the
vacuum. -/
lemma rallisSeries_mul_of_mem_localLevel (hb : IsUnramifiedOn b n A) (M : ℕ)
    (hy : HasLevel y (stdLevel E n ⊓ supportedOn n A)) {k : Gf E n} (hk : k ∈ localLevel n A)
    (hk_fix : ∀ g : G E s, y (g * (1, k)) = y g) (g : G E s) :
    rallisSeries M b A y (g * (1, k)) = rallisSeries M b A y g := by
  -- Write `k = a * d` with `a` supported on `A` and its conjugate and `d` trivial at `A`. Both fix
  -- `y`; `d` commutes with the representatives, and `a` permutes the cosets.
  obtain ⟨a, ha : a ∈ supportedOn n A, d, hd : d ∈ trivialOn n A, rfl : k = a * d, -⟩ :=
    k.exists_supportedOn_mul_trivialOn A
  have d_int : d ∈ localLevel n A := fun w hw ↦ by simp [mem_trivialOn.1 hd w hw]
  have a_int : a ∈ localLevel n A := (mul_mem_cancel_right d_int).1 hk
  have a_level : a ∈ stdLevel E n ⊓ supportedOn n A :=
    Subgroup.mem_inf.2 ⟨(mem_stdLevel_iff_of_supportedOn ha).2 a_int, ha⟩
  have d_fix (g : G E s) : y (g * (1, d)) = y g := by
    rw [show g * (1, d) = g * (1, a⁻¹) * (1, a * d) by simp [mul_assoc], hk_fix,
      hy a⁻¹ (inv_mem a_level)]
  let term (g : G E s) (q : Gf E n ⧸ localLevel n A) : ℂ :=
    vacuumCoeff M b (cosetRep q).val * y (g * (1, (cosetRep q).val))
  have h_term (q : Gf E n ⧸ localLevel n A) : term (g * (1, a * d)) q = term g (a • q) := by
    set r : Gf E n := (cosetRep q).val with h_rep
    have hr : r ∈ supportedOn n A := (cosetRep q).property
    have h_coset : a • q = (a * r : Gf E n) := by
      rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, mk_cosetRep]
    have h_coeff : vacuumCoeff M b (a * r) = vacuumCoeff M b r := by
      simpa using vacuumCoeff_mul_mul_of_mem hb M a_level (one_mem _) r
    have h_comm : g * (1, a * d) * (1, r) = g * (1, a * r) * (1, d) := by
      simp [mul_assoc, (commute_supportedOn_trivialOn hr hd).eq]
    simp only [term, h_coset, vacuumCoeff_mul_apply_cosetRep hb M hy (mul_mem ha hr), ← h_rep,
      h_coeff, h_comm, d_fix]
  rw [rallisSeries, rallisSeries]
  calc ∑' q, term (g * (1, a * d)) q = ∑' q, term g (a • q) := tsum_congr h_term
    _ = ∑' q, term g q := (MulAction.toPerm a).tsum_eq (term g)

/-- The series `rallisSeries M b A y` (the sum over cosets `q` of the points integral at `A` of the
right translates `R(cosetRep q) y`, weighted by `vacuumCoeff M b (cosetRep q)`) keeps the level. Let
`b ∘ det` be trivial on the integral points supported on `A` and its conjugate (`IsUnramifiedOn`).
Let the subgroup `J` of the finite points contain those points and lie in `localLevel n A`, the
points integral with integral inverse at each place of `A`; then if `y` is right invariant under
`J`, so is `rallisSeries M b A y`. -/
lemma hasLevel_rallisSeries (hb : IsUnramifiedOn b n A) (M : ℕ) {J : Subgroup (Gf E n)}
    (h_ge : stdLevel E n ⊓ supportedOn n A ≤ J) (h_le : J ≤ localLevel n A) (hy : HasLevel y J) :
    HasLevel (rallisSeries M b A y) J := fun k hk ↦
  rallisSeries_mul_of_mem_localLevel hb M (fun j hj ↦ hy j (h_ge hj)) (h_le hk) (hy k hk)

/-- The series `rallisSeries` may be integrated term by term. Let `2 * card n < card m`, let `y` be
bounded and measurable, `f` integrable and `j` measurable. The integral of `f z` times the series
at `j z` is the sum over the cosets `q` of the coefficient of the vacuum at `u = cosetRep q` times
the integral of `f z * y (j z * u)`. -/
lemma hasSum_integral_mul_rallisSeries (h_rank : 2 * card n < card m) (b : AutChar E)
    (A : Set (FinPlace E)) (hy : IsBoundedMeasurable y) {Z : Type*} [MeasurableSpace Z]
    {μ : Measure Z} {f : Z → ℂ} (hf : Integrable f μ) {j : Z → G E s} (hj : Measurable j) :
    HasSum (fun q : Gf E n ⧸ localLevel n A ↦ vacuumCoeff (card m) b (cosetRep q).val *
        ∫ z : Z, f z * y (j z * (1, (cosetRep q).val)) ∂μ)
      (∫ z : Z, f z * rallisSeries (card m) b A y (j z) ∂μ) := by
  obtain ⟨C, hC⟩ := hy.bounded
  let term (q : Gf E n ⧸ localLevel n A) (z : Z) : ℂ :=
    vacuumCoeff (card m) b (cosetRep q).val * (f z * y (j z * (1, (cosetRep q).val)))
  have h_int (q : Gf E n ⧸ localLevel n A) : Integrable (term q) μ :=
    (hy.integrable_mul_comp hf (fun z ↦ j z * (1, (cosetRep q).val)) (hj.mul_const _)).const_mul _
  have h_le (q : Gf E n ⧸ localLevel n A) : ∫ z, ‖term q z‖ ∂μ ≤
      ‖vacuumCoeff (card m) b (cosetRep q).val‖ * ∫ z, ‖f z‖ * C ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono (h_int q).norm ((hf.norm.mul_const C).const_mul _) fun z ↦ ?_
    simp only [term, norm_mul]
    gcongr
    exact hC _
  have h_summable : Summable fun q ↦ ∫ z, ‖term q z‖ ∂μ :=
    ((summable_norm_vacuumCoeff h_rank b A).mul_right _).of_nonneg_of_le
      (fun q ↦ integral_nonneg fun z ↦ norm_nonneg _) h_le
  have h_series (z : Z) : ∑' q, term q z = f z * rallisSeries (card m) b A y (j z) := by
    simp [term, rallisSeries, ← tsum_mul_left, mul_left_comm]
  have : Countable (Gf E n ⧸ localLevel n A) := countable_quotient_localLevel A
  simpa only [h_series, term, integral_const_mul] using
    hasSum_integral_of_summable_integral_norm h_int h_summable

/-- For `2 * card n < card m` and `y` bounded and measurable, the series `rallisSeries` commutes
with `realConv κ`, the right convolution by an integrable function `κ` on the real points. -/
lemma realConv_rallisSeries (h_rank : 2 * card n < card m) (b : AutChar E)
    (A : Set (FinPlace E)) (hy : IsBoundedMeasurable y) {κ : GInf E s → ℂ} (hκ : Integrable κ) :
    realConv κ (rallisSeries (card m) b A y) = rallisSeries (card m) b A (realConv κ y) := by
  ext g
  have h_comm (x : GInf E s) (u : Gf E n) : g * (1, u) * (x, 1) = g * (x, 1) * (1, u) := by
    simp [mul_assoc]
  have h_sum : ∑' q : Gf E n ⧸ localLevel n A, vacuumCoeff (card m) b (cosetRep q).val *
        ∫ x, κ x * y (g * (x, 1) * (1, (cosetRep q).val)) =
      ∫ x, κ x * rallisSeries (card m) b A y (g * (x, 1)) :=
    (hasSum_integral_mul_rallisSeries h_rank b A hy hκ (by fun_prop)).tsum_eq
  simpa only [rallisSeries, realConv, h_comm] using h_sum.symm

/-- The Petersson product with the series `rallisSeries` may be taken term by term. Let `S` be a
hermitian space of rank `card n` over `E` with signs `s` and adelic points `G E s`, and let
`⟨y', z⟩ = S.petersson y' z` be the integral of `conj (y' g) * z g` against `S.quotMeasure`, the
measure that computes integrals over the quotient by the rational points of `S`. Let
`2 * card n < card m`, let `y` be bounded and strongly measurable, let `y'` be integrable for this
measure, let `x` be an adelic point, and write `R(x) z` for the translate `g ↦ z (g * x)`.
Let `q` run over the cosets of `localLevel n A`, the finite points integral at `A`, with
representatives `u = cosetRep q`. Then the numbers `vacuumCoeff (card m) b u * ⟨y', R(x u) y⟩`,
where `vacuumCoeff M b u = (b(det u) * finMultiplier u ^ M)⁻¹`, have sum `⟨y', R(x) z⟩` for the
series `z = rallisSeries (card m) b A y = ∑ vacuumCoeff (card m) b u * R(u) y`. -/
lemma hasSum_petersson_rallisSeries {s : n → ℤˣ} {y : G E s → ℂ} {S : Space E n s}
    (h_rank : 2 * card n < card m) (b : AutChar E) (A : Set (FinPlace E))
    (hy : IsBoundedMeasurable y) {y' : G E s → ℂ} (hy' : Integrable y' S.quotMeasure) (x : G E s) :
    HasSum (fun q : Gf E n ⧸ localLevel n A ↦ vacuumCoeff (card m) b (cosetRep q).val *
        S.petersson y' fun g : G E s ↦ y (g * x * (1, (cosetRep q).val)))
      (S.petersson y' fun g : G E s ↦ rallisSeries (card m) b A y (g * x)) := by
  have h_conj : Integrable (fun g : G E s ↦ starRingEnd ℂ (y' g)) S.quotMeasure :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hy'
  unfold Space.petersson
  exact hasSum_integral_mul_rallisSeries h_rank b A hy h_conj (measurable_mul_const x)

/-- Let `2 * card n < card m` and let `b ∘ det` be trivial on the integral points supported on `A`
and its conjugate (`IsUnramifiedOn`). The series `rallisSeries` of a bounded automorphic function
fixed by these points is automorphic: continuous, invariant on the left by the rational points of
`S` and fixed by an open subgroup of the finite points. -/
lemma isAutomorphic_rallisSeries {S : Space E n s} (h_rank : 2 * card n < card m)
    (hb : IsUnramifiedOn b n A) (hy : S.IsAutomorphic y) (hy_bdd : ∃ C : ℝ, ∀ g : G E s, ‖y g‖ ≤ C)
    (h_level : HasLevel y (stdLevel E n ⊓ supportedOn n A)) :
    S.IsAutomorphic (rallisSeries (card m) b A y) where
  continuous := continuous_rallisSeries h_rank b A hy.continuous hy_bdd
  rat_mul δ hδ g := by simp only [← rallisSeries_comp_mul_left, hy.rat_mul δ hδ]
  exists_level := by
    -- The points of a level `K` of `y` that are integral at `A` form a level of the series.
    obtain ⟨K, hK⟩ := hy.exists_level
    refine ⟨K ⊓ ⟨localLevel n A, isOpen_coe_localLevel A⟩, fun k hk ↦ ?_⟩
    obtain ⟨k_mem, k_int⟩ : k ∈ K ∧ k ∈ localLevel n A := hk
    exact rallisSeries_mul_of_mem_localLevel hb (card m) h_level k_int (hK k k_mem)

/-- The series `rallisSeries (card m) b A y` is the sum, over the cosets `q` of the finite points
modulo those integral at `A`, of the right translates of `y` by a representative of `q`, each
weighted by the vacuum coefficient `vacuumCoeff (card m) b`; it keeps the forms of each type. Let
`2 * card n < card m` and let `b ∘ det` be unramified on `A`. Let `y` be a form of type `e` for the
hermitian space `S`, meaning it is automorphic, bounded and, if `e` is integrable, fixed by
convolution with `e` over the real points, and let it be right invariant under the integral points
supported on `A` and its conjugate. Then `rallisSeries (card m) b A y` is a form of type `e` for
`S`. -/
lemma isForm_rallisSeries {S : Space E n s} (h_rank : 2 * card n < card m)
    (hb : IsUnramifiedOn b n A) {e : GInf E s → ℂ} (hy : S.IsForm e y)
    (h_level : HasLevel y (stdLevel E n ⊓ supportedOn n A)) :
    S.IsForm e (rallisSeries (card m) b A y) where
  toIsAutomorphic := isAutomorphic_rallisSeries h_rank hb hy.toIsAutomorphic hy.bounded h_level
  bounded := by
    obtain ⟨C, hC⟩ := hy.bounded
    exact ⟨_, norm_rallisSeries_le h_rank b A hC⟩
  realConv_eq he := by
    rw [realConv_rallisSeries h_rank b A hy.isBoundedMeasurable he, hy.realConv_eq he]

/-- The series `rallisSeries (card m) b A` keeps the forms of each type and level for a hermitian
space `S : Space E n s`. This series is `∑ mc(q) R(q) y`, summed over the cosets `q` of the finite
points integral at `A`, with coefficient `vacuumCoeff (card m) b` and right translation taken at
`cosetRep q`. Let `2 * card n < card m`, let `b ∘ det` be unramified on `A`, and let `J` consist of
points integral at `A` and contain the integral points supported on `A` and its conjugate; then the
series of a form `y` of type `e` for `S` (automorphic, bounded and, if `e` is integrable, fixed by
convolution with `e`) that is fixed by `J` is again a form of type `e` for `S` fixed by `J`. -/
theorem exists_form_eq_rallisSeries {S : Space E n s} (h_rank : 2 * card n < card m)
    (hb : IsUnramifiedOn b n A) {J : Subgroup (Gf E n)} (h_ge : stdLevel E n ⊓ supportedOn n A ≤ J)
    (h_le : J ≤ localLevel n A) {e : GInf E s → ℂ} {y : S.Form e} (hy : HasLevel y J) :
    ∃ z : S.Form e, HasLevel z J ∧ ⇑z = rallisSeries (card m) b A y := by
  have h_form : S.IsForm e (rallisSeries (card m) b A y) :=
    isForm_rallisSeries h_rank hb y.property fun k hk ↦ hy k (h_ge hk)
  exact ⟨⟨_, h_form⟩, hasLevel_rallisSeries hb (card m) h_ge h_le hy, rfl⟩

/-! ### Multiplicativity over the places -/

/-- The series is multiplicative over the places. Let `2 * card n < card m`, let `A₂` be disjoint
from `A₁` and its conjugate, let `b ∘ det` be unramified on `A₁ ∪ A₂`, and let `y` be bounded and
fixed by the integral points supported on `A₁ ∪ A₂` and its conjugate. The series of `y` at
`A₁ ∪ A₂` is the series at `A₁` of the series of `y` at `A₂`. -/
lemma rallisSeries_union {A₁ A₂ : Set (FinPlace E)} (h_rank : 2 * card n < card m)
    (h_disj : Disjoint A₁.conjClosure A₂) (hb : IsUnramifiedOn b n (A₁ ∪ A₂))
    (hy_bdd : ∃ C : ℝ, ∀ g : G E s, ‖y g‖ ≤ C)
    (hy : HasLevel y (stdLevel E n ⊓ supportedOn n (A₁ ∪ A₂))) :
    rallisSeries (card m) b (A₁ ∪ A₂) y =
      rallisSeries (card m) b A₁ (rallisSeries (card m) b A₂ y) := by
  ext g
  obtain ⟨C, hC⟩ := hy_bdd
  let e : (Gf E n ⧸ localLevel n A₁) × (Gf E n ⧸ localLevel n A₂) ≃
      Gf E n ⧸ localLevel n (A₁ ∪ A₂) := .ofBijective _ (bijective_mk_cosetRep_mul h_disj)
  let term (q : Gf E n ⧸ localLevel n (A₁ ∪ A₂)) : ℂ :=
    vacuumCoeff (card m) b (cosetRep q).val * y (g * (1, (cosetRep q).val))
  have h_summable : Summable term :=
    .of_norm_bounded ((summable_norm_vacuumCoeff h_rank b _).mul_right C)
      fun q ↦ norm_mul_le_of_le le_rfl (hC _)
  have h_term (q₁ : Gf E n ⧸ localLevel n A₁) (q₂ : Gf E n ⧸ localLevel n A₂) :
      term (e (q₁, q₂)) = vacuumCoeff (card m) b (cosetRep q₁).val *
        (vacuumCoeff (card m) b (cosetRep q₂).val *
          y (g * (1, (cosetRep q₁).val) * (1, (cosetRep q₂).val))) := by
    have h_supp : (cosetRep q₁).val * (cosetRep q₂).val ∈ supportedOn n (A₁ ∪ A₂) :=
      mul_mem (supportedOn_mono Set.subset_union_left (cosetRep _).property)
        (supportedOn_mono Set.subset_union_right (cosetRep _).property)
    simp only [term, e, Equiv.ofBijective_apply, vacuumCoeff_mul_apply_cosetRep hb _ hy h_supp,
      vacuumCoeff_mul_of_disjoint h_disj _ b (cosetRep q₁).property (cosetRep q₂).property,
      mul_assoc, Prod.mk_mul_mk, mul_one]
  calc rallisSeries (card m) b (A₁ ∪ A₂) y g = ∑' p, term (e p) := (e.tsum_eq term).symm
    _ = ∑' q₁, ∑' q₂, term (e (q₁, q₂)) := (e.summable_iff.2 h_summable).tsum_prod
    _ = _ := by simp only [h_term, tsum_mul_left, rallisSeries]

/-! ### The sum of the coefficients as a product over the places -/

variable (n) in
/-- The sum `∑ mc(q)` of the coefficients of the vacuum `mc = vacuumCoeff M b` over the cosets `q`,
in the finite points, of the subgroup of the points integral at `A`, taken at the representatives
`cosetRep q`. It is the value of the series of the constant function `1` (`rallisSeries_const`),
and it is `0` if the terms are not summable. -/
def vacuumSum (M : ℕ) (b : AutChar E) (A : Set (FinPlace E)) : ℂ :=
  ∑' q : Gf E n ⧸ localLevel n A, vacuumCoeff M b (cosetRep q).val

/-- Translations fix a constant function, so its series is the constant times the sum of the
coefficients of the vacuum. -/
lemma rallisSeries_const (M : ℕ) (b : AutChar E) (A : Set (FinPlace E)) (c : ℂ) :
    rallisSeries M b A (fun _ : G E s ↦ c) = fun _ : G E s ↦ vacuumSum n M b A * c :=
  funext fun _ ↦ tsum_mul_right

omit [WeilData E] in
lemma IsUnramifiedOn.mono (hb : IsUnramifiedOn b n A) {A' : Set (FinPlace E)} (h_sub : A' ⊆ A) :
    IsUnramifiedOn b n A' :=
  fun k hk ↦ hb k (inf_le_inf_left (stdLevel E n) (supportedOn_mono h_sub) hk)

/-- Let `b ∘ det` be unramified on `A`. The coefficient of the vacuum at the chosen representative
of the coset of a point `u` supported on `A` and its conjugate is the coefficient at `u`. -/
lemma vacuumCoeff_cosetRep_mk (hb : IsUnramifiedOn b n A) (M : ℕ) {u : Gf E n}
    (hu : u ∈ supportedOn n A) :
    vacuumCoeff M b (cosetRep (u : Gf E n ⧸ localLevel n A)).val = vacuumCoeff M b u := by
  simpa only [one_mul, mul_inv_cancel_left] using
    vacuumCoeff_mul_mul_of_mem hb M (one_mem _) (inv_mul_cosetRep_mem hu) u

/-- Let `b ∘ det` be unramified on `A`. The sum `vacuumSum` may be computed with any points `r γ`
that are supported on `A` and its conjugate and represent the cosets of the points integral at
`A`. -/
lemma vacuumSum_eq_tsum (hb : IsUnramifiedOn b n A) (M : ℕ) {ι : Type*} {r : ι → Gf E n}
    (h_supp : ∀ γ : ι, r γ ∈ supportedOn n A)
    (h_rep : ∀ g : Gf E n, ∃! γ : ι, (r γ)⁻¹ * g ∈ localLevel n A) :
    vacuumSum n M b A = ∑' γ : ι, vacuumCoeff M b (r γ) := by
  have h_bij : Function.Bijective fun γ : ι ↦ (r γ : Gf E n ⧸ localLevel n A) := by
    refine (Function.bijective_iff_existsUnique _).2 fun q ↦ ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    simpa only [QuotientGroup.eq] using h_rep g
  rw [vacuumSum, ← (Equiv.ofBijective _ h_bij).tsum_eq]
  exact tsum_congr fun γ ↦ vacuumCoeff_cosetRep_mk hb M (h_supp γ)

/-- Over the empty set of places there is one coset, and the sum `vacuumSum` is `1`. -/
lemma vacuumSum_empty (M : ℕ) (b : AutChar E) : vacuumSum n M b ∅ = 1 := by
  have hb : IsUnramifiedOn b n ∅ := by
    rintro k ⟨-, hk_supp⟩
    have hk_one : k = 1 := eq_of_supportedOn hk_supp (one_mem _) (by simp)
    simp [hk_one, Prod.mk_one_one]
  rw [vacuumSum_eq_tsum hb M (r := fun _ : Unit ↦ 1) (fun _ ↦ one_mem _) (by simp [mem_localLevel]),
    vacuumCoeff_eq_one_of_mem hb M (one_mem _), tsum_const, Nat.card_unique, one_smul]

/-- The sum `vacuumSum` is multiplicative over the places. Let `2 * card n < card m`, let `A₂` be
disjoint from `A₁` and its conjugate, and let `b ∘ det` be unramified on `A₁ ∪ A₂`. The sum at
`A₁ ∪ A₂` is the product of the sums at `A₁` and at `A₂`. -/
lemma vacuumSum_union {A₁ A₂ : Set (FinPlace E)} (h_rank : 2 * card n < card m)
    (h_disj : Disjoint A₁.conjClosure A₂) (hb : IsUnramifiedOn b n (A₁ ∪ A₂)) :
    vacuumSum n (card m) b (A₁ ∪ A₂) =
      vacuumSum n (card m) b A₁ * vacuumSum n (card m) b A₂ := by
  let one : G E (1 : n → ℤˣ) → ℂ := fun _ ↦ 1
  have h_series : rallisSeries (card m) b (A₁ ∪ A₂) one =
      rallisSeries (card m) b A₁ (rallisSeries (card m) b A₂ one) :=
    rallisSeries_union h_rank h_disj hb ⟨1, by simp [one]⟩ fun _ _ _ ↦ rfl
  simpa only [one, rallisSeries_const, mul_one] using congrFun h_series 1

/-- Let `2 * card n < card m`, and let `b ∘ det` be trivial on the integral finite points supported
on `A` and its conjugate (`IsUnramifiedOn`). Let `vacuumSum n (card m) b A` be the sum, over the
cosets `q` in the finite adelic unitary group `Gf E n` of the points integral at `A`, of the vacuum
coefficients `(b(det g) * finMultiplier g ^ card m)⁻¹` at the representatives `g = cosetRep q` (and
`0` if the sum is not summable). Then, as the finite set `R` of places grows, `vacuumSum` at `A ∩ R`
tends to `vacuumSum` at `A`. -/
lemma tendsto_vacuumSum_inter (h_rank : 2 * card n < card m) (hb : IsUnramifiedOn b n A) :
    Filter.Tendsto (fun R : Finset (FinPlace E) ↦ vacuumSum n (card m) b (A ∩ R)) Filter.atTop
      (nhds (vacuumSum n (card m) b A)) := by
  -- The cosets at `A ∩ R` embed in those at `A` and exhaust them, as a point is integral off a
  -- finite set; the series at `A` converges absolutely.
  let c (q : Gf E n ⧸ localLevel n A) : ℂ := vacuumCoeff (card m) b (cosetRep q).val
  let incl (R : Finset (FinPlace E)) (q : Gf E n ⧸ localLevel n (A ∩ R)) :
      Gf E n ⧸ localLevel n A := (cosetRep q).val
  have h_inj (R : Finset (FinPlace E)) : Function.Injective (incl R) :=
    cosetRep_injective_of_subset Set.inter_subset_left
  have h_sum (R : Finset (FinPlace E)) :
      ∑' q : Gf E n ⧸ localLevel n A, (Set.range (incl R)).indicator c q =
        vacuumSum n (card m) b (A ∩ R) := by
    rw [← tsum_subtype, tsum_range c (h_inj R)]
    exact tsum_congr fun q ↦
      vacuumCoeff_cosetRep_mk hb _ (supportedOn_mono Set.inter_subset_left (cosetRep q).property)
  have h_exhaust (g : Gf E n) :
      ∀ᶠ R : Finset (FinPlace E) in Filter.atTop, ↑g ∈ Set.range (incl R) := by
    have h_finite : {w : FinPlace E | g.atPlace w ∉ localIntGL n w}.Finite :=
      eventually_atPlace_mem_localIntGL
    filter_upwards [Filter.eventually_ge_atTop h_finite.toFinset] with R hR
    let r : supportedOn n (A ∩ R) := cosetRep (g : Gf E n ⧸ localLevel n (A ∩ R))
    have hr : r.val⁻¹ * g ∈ localLevel n (A ∩ R) := QuotientGroup.eq.1 (mk_cosetRep _)
    refine ⟨g, QuotientGroup.eq.2 fun w hw ↦ ?_⟩
    change (r.val⁻¹ * g).atPlace w ∈ localIntGL n w
    by_cases hw_mem : w ∈ A ∩ R
    · exact hr w hw_mem
    by_cases hw_star : star w ∈ A ∩ R
    · exact atPlace_star_mem_iff.1 (hr _ hw_star)
    · have hg : g.atPlace w ∈ localIntGL n w :=
        by_contra fun h_not ↦ hw_mem ⟨hw, hR (h_finite.mem_toFinset.2 h_not)⟩
      simpa [mem_supportedOn.1 r.property w hw_mem hw_star] using hg
  simp only [← h_sum]
  refine tendsto_tsum_of_dominated_convergence (summable_norm_vacuumCoeff h_rank b A)
    (fun q ↦ ?_) (.of_forall fun R q ↦ norm_indicator_le_norm_self c q)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact tendsto_const_nhds.congr' ((h_exhaust g).mono fun R hR ↦ (Set.indicator_of_mem hR c).symm)

open scoped Classical in
/-- Let `vacuumSum n (card m) b A` be the sum, over the cosets `q` in `Gf E n` of the points
integral at `A`, of the vacuum coefficients `(b(det g) * finMultiplier g ^ card m)⁻¹` at
`g = cosetRep q`. It is a product over the pairs of conjugate places: let `2 * card n < card m`, let
`A` be stable under conjugation, and let `b ∘ det` be unramified on `A`; let the factors `loc w` be
`1` off `A` and have product `L`. If for each `w` in `A` the sum at `{w, w̄}` is `loc w * loc w̄` (a
single factor when `w = w̄`), then the sum at `A` is `L`. -/
lemma vacuumSum_eq_of_hasProd (h_rank : 2 * card n < card m)
    (hA : ∀ w : FinPlace E, star w ∈ A ↔ w ∈ A) (hb : IsUnramifiedOn b n A)
    {loc : FinPlace E → ℂ} {L : ℂ} (h_prod : HasProd loc L)
    (h_off : ∀ w : FinPlace E, w ∉ A → loc w = 1)
    (h_pair : ∀ w : FinPlace E, w ∈ A → vacuumSum n (card m) b {w, star w} =
      ∏ u ∈ ({w, star w} : Finset (FinPlace E)), loc u) :
    vacuumSum n (card m) b A = L := by
  -- `T R` consists of the places of `R` and their conjugates; add the places of `R` one by one.
  let T (R : Finset (FinPlace E)) : Finset (FinPlace E) := R.image star ∪ R
  have h_mem (R : Finset (FinPlace E)) (u : FinPlace E) : u ∈ T R ↔ star u ∈ R ∨ u ∈ R := by
    simp [T, star_involutive.eq_iff]
  have h_finite (R : Finset (FinPlace E)) :
      vacuumSum n (card m) b (A ∩ T R) = ∏ u ∈ T R, loc u := by
    induction R using Finset.induction with
    | empty => simp [T, vacuumSum_empty, Set.inter_empty]
    | insert w R _ ih =>
      have h_insert : T (insert w R) = {w, star w} ∪ T R := by simp [T]
      have h_star : star w ∈ T R ↔ w ∈ T R := by simp [h_mem, or_comm]
      by_cases hw : w ∈ T R
      · have h_subset : {w, star w} ⊆ T R := by simp [Finset.insert_subset_iff, hw, h_star]
        rwa [h_insert, Finset.union_eq_right.2 h_subset]
      have h_disj : Disjoint {w, star w} (T R) := by simp [hw, h_star]
      rw [h_insert, Finset.prod_union h_disj, ← ih, Finset.coe_union, Finset.coe_pair,
        Set.inter_union_distrib_left]
      by_cases hw_mem : w ∈ A
      · have h_sub : {w, star w} ⊆ A := Set.pair_subset hw_mem ((hA w).2 hw_mem)
        have h_closure : ({w, star w} : Set (FinPlace E)).conjClosure = {w, star w} := by
          ext u
          simp [star_involutive.eq_iff, or_comm]
        have h_disj_conj : Disjoint ({w, star w} : Set (FinPlace E)).conjClosure (A ∩ T R) := by
          rw [h_closure, ← Finset.coe_pair]
          exact (Finset.disjoint_coe.2 h_disj).mono_right Set.inter_subset_right
        have hb_union : IsUnramifiedOn b n ({w, star w} ∪ A ∩ T R) :=
          hb.mono (Set.union_subset h_sub Set.inter_subset_left)
        rw [Set.inter_eq_right.2 h_sub, vacuumSum_union h_rank h_disj_conj hb_union,
          h_pair w hw_mem]
      · have hw_star : star w ∉ A := (hA w).not.2 hw_mem
        have h_one : ∏ u ∈ {w, star w}, loc u = 1 :=
          Finset.prod_eq_one (by simp [h_off, hw_mem, hw_star])
        simp [h_one, Set.inter_insert_of_notMem hw_mem, hw_star]
  -- Let `R` exhaust the places.
  have h_frequently : ∃ᶠ R : Finset (FinPlace E) in Filter.atTop,
      vacuumSum n (card m) b (A ∩ R) = ∏ u ∈ R, loc u :=
    Filter.frequently_atTop.2 fun R ↦ ⟨T R, le_sup_right, h_finite R⟩
  exact tendsto_nhds_unique_of_frequently_eq (tendsto_vacuumSum_inter h_rank hb) h_prod
    h_frequently

end New.SiegelWeil
