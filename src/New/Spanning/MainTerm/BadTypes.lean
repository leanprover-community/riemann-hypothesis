module

public import New.UpperBound.Objects.LabelsAndIndexTypes
import TauCeti.Data.Nat.Totient.LowerBound
import TauCeti.FieldTheory.Finite.PrimitivePolynomial
import TauCeti.NumberTheory.SecondMoment.AllowedLabel

/-!
# The share of non-allowed polynomials and the bad share

This file bounds the share of the bad types for tuples of polynomials over fields with q elements.
A label is a monic squarefree polynomial of degree `r` that does not vanish at `0`. The file
counts the monic polynomials that are not allowed and the primitive polynomials. It then bounds
the coefficient at the identity of one minus the sum of the idempotents of the good tuples.

## Main definitions and results

* `New.card_not_primitive_mul_le`: for `1 < r < q`, with every polynomial weighted by
  `(1 - r / q) / q ^ r`, the monic polynomials of degree `r` that are not primitive polynomials
  weigh at most `exp (-1 / (2 r (2 r log q + 1)))` in total.
* `New.re_coeff_one_sub_sum_tupleIdem_le`: the bound on the coefficient at the identity of one minus
  the sum of the idempotents of the good tuples.

Notions from other files:
* `New.tupleIdem`: For a tuple (c_w) of polynomials over the fields k_w, the tensor product of the
  polynomial idempotents e_{c_w} in the group algebra of ∏ GL_n(k_w).

## Relation to the literature

In the regular representation of a product of groups GL_r(F_q), types that are not good have share
at most a multiple of 1/q per factor plus a term decaying exponentially in the number of factors. So
the projection to good types discards little when translates of the Poincaré series fill the rows.
It computes the Plancherel shares for GL_r(F_q) from Green's degree formula and counts of squarefree
and primitive polynomials over F_q, followed by a union bound over the factors. Related work: Green,
The characters of the finite general linear groups, 1955; Dudko, Plancherel measures for GL(n,q),
arXiv 0806.1345, 2008; Lidl–Niederreiter, Finite Fields, ch. 3, 1983.
-/

@[expose] public section

section BadShare

open Finset Fintype Real Polynomial Nat ComplexOrder

attribute [local instance low] Fintype.ofFinite

private lemma New.isAllowedPolynomial_iff {k : Type*} [Field k] {M r : ℕ} {c : k[X]} :
    IsAllowedPolynomial M r c ↔ c.natDegree = r ∧ TauCeti.SecondMoment.IsAllowedLabel M c := by
  simp only [IsAllowedPolynomial, IsLabel, TauCeti.SecondMoment.isAllowedLabel_iff,
    TauCeti.SecondMoment.isLabel_iff]
  tauto

open scoped Classical in
/-- Over a field `k` with `q` elements, at most `(1 + M + r) q ^ (r - 1)` monic polynomials of
degree `r` are not allowed polynomials (`IsAllowedPolynomial M r`). Such a polynomial either fails
to be a label, or has a root `x` in `k` with `x ^ M = 1`. -/
lemma New.card_not_isAllowedPolynomial_le (k : Type*) [Field k] [Finite k] (M : ℕ) [NeZero M]
    (r : ℕ) :
    #{c ∈ monicsOfDegree k r | ¬IsAllowedPolynomial M r c} ≤
      (1 + M + r) * Nat.card k ^ (r - 1) := by
  have hset : (({c ∈ monicsOfDegree k r | ¬IsAllowedPolynomial M r c} : Finset k[X]) : Set k[X]) =
      {c : k[X] | c.Monic ∧ c.natDegree = r ∧ ¬TauCeti.SecondMoment.IsAllowedLabel M c} := by
    ext c
    simp only [coe_filter, Set.mem_ofPred_eq, monicsOfDegree, Set.mem_toFinset,
      isAllowedPolynomial_iff]
    tauto
  rw [← Set.ncard_coe_finset, hset]
  exact TauCeti.SecondMoment.ncard_monic_not_isAllowedLabel_le (NeZero.ne M) r

open scoped Classical in
/-- Over a field `k` with `q` elements and for `r ≠ 0`, there are at least `φ (q ^ r - 1) / r`
primitive polynomials of degree `r`. These are the irreducible monic polynomials of degree `r`, not
vanishing at `0`, with a root of order `q ^ r - 1`. -/
lemma New.totient_le_mul_card_isPrimitivePolynomial (k : Type*) [Field k] [Finite k] {r : ℕ}
    (hr : r ≠ 0) :
    φ (Nat.card k ^ r - 1) ≤ r * #{c ∈ monicsOfDegree k r | IsPrimitivePolynomial r c} := by
  have hsub : {c : k[X] | c.IsPrimitivePolynomial ∧ c.natDegree = r} ⊆
      ({c ∈ monicsOfDegree k r | New.IsPrimitivePolynomial r c} : Finset k[X]) := by
    rintro c ⟨hc, hdeg⟩
    have hdeg_ne : c.degree ≠ 0 := by
      rw [degree_eq_natDegree hc.monic.ne_zero, hdeg]
      exact_mod_cast hr
    obtain ⟨ξ, hξ⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure k) c hdeg_ne
    have hord := ((Polynomial.isPrimitivePolynomial_iff_orderOf_eq hξ).mp hc).2.2
    rw [hdeg] at hord
    have hprim : IsPrimitiveRoot ξ (Nat.card k ^ r - 1) := IsPrimitiveRoot.iff_orderOf.mpr hord
    exact mem_coe.mpr (mem_filter.mpr ⟨by simp [monicsOfDegree, hc.monic, hdeg],
      ⟨hc.monic, hc.irreducible.squarefree, hdeg, hc.coeff_zero_ne_zero⟩, hc.irreducible, ξ, hξ,
      hprim⟩)
  refine (Polynomial.totient_le_mul_ncard_isPrimitivePolynomial (K := k) r).trans ?_
  rw [← Set.ncard_coe_finset]
  exact Nat.mul_le_mul_left r (Set.ncard_le_ncard hsub (Finset.finite_toSet _))

open scoped Classical in
/-- Over a field with `q` elements and for `1 < r < q`, weight every polynomial by
`(1 - r / q) / q ^ r`. Then the allowed polynomials of degree `r` (monic, squarefree, no root at `0`
or at an `M`-th root of unity in the field) weigh at least `1 - ε` in total if
`(1 + M + 2 r) / q ≤ ε`. -/
lemma New.one_sub_le_card_allowed_mul (k : Type*) [Field k] [Finite k] {q M r : ℕ} [NeZero M]
    {ε : ℝ} (hq : Nat.card k = q) (_hr_one_lt : 1 < r) (_hrq : r < q)
    (hε_ge : (1 + M + 2 * r) / q ≤ ε) :
    1 - ε ≤ #{c ∈ monicsOfDegree k r | IsAllowedPolynomial M r c} * ((1 - r / q) / q ^ r) := by
  subst hq
  have hset : (({c ∈ monicsOfDegree k r | IsAllowedPolynomial M r c} : Finset k[X]) : Set k[X]) =
      {c : k[X] | c.natDegree = r ∧ TauCeti.SecondMoment.IsAllowedLabel M c} := by
    ext c
    simp only [coe_filter, Set.mem_ofPred_eq, monicsOfDegree, Set.mem_toFinset,
      isAllowedPolynomial_iff]
    refine ⟨fun h ↦ h.2, fun h ↦ ⟨⟨?_, h.1⟩, h⟩⟩
    exact (TauCeti.SecondMoment.isLabel_iff.mp (TauCeti.SecondMoment.isAllowedLabel_iff.mp h.2).1).1
  rw [← Set.ncard_coe_finset, hset]
  exact TauCeti.SecondMoment.one_sub_le_ncard_isAllowedLabel_mul (NeZero.ne M) hε_ge

open scoped Classical in
/-- Over a field `k` with `q` elements and for `1 < r < q`, weight every polynomial by
`(1 - r / q) / q ^ r`. The monic polynomials of degree `r` that are not primitive polynomials weigh
at most `exp (-1 / (2 r (2 r log q + 1)))` in total. -/
lemma New.card_not_primitive_mul_le (k : Type*) [Field k] [Finite k] {q r : ℕ}
    (hq : Nat.card k = q) (hr_one_lt : 1 < r) (hrq : r < q) :
    #{c ∈ monicsOfDegree k r | ¬IsPrimitivePolynomial r c} * ((1 - r / q) / q ^ r : ℝ) ≤
      exp (-(1 / (2 * r * (2 * (r * Real.log q) + 1)))) := by
  set nPrim : ℕ := #{c ∈ monicsOfDegree k r | IsPrimitivePolynomial r c}
  have hr_pos : (0 : ℝ) < r := mod_cast (by lia : 0 < r)
  have hqr_pos : 0 < (q : ℝ) ^ r := pow_pos (mod_cast (by lia : 0 < q)) r
  have totient_le : (φ (q ^ r - 1) : ℝ) / (r * (q : ℝ) ^ r) ≤ (nPrim : ℝ) / (q : ℝ) ^ r := by
    rw [div_le_div_iff₀ (by positivity) hqr_pos]
    have h := totient_le_mul_card_isPrimitivePolynomial k hr_one_lt.ne_zero
    rw [hq] at h
    have h' : (φ (q ^ r - 1) : ℝ) ≤ r * nPrim := by exact_mod_cast h
    nlinarith
  have card_split :
      (nPrim : ℝ) + #{c ∈ monicsOfDegree k r | ¬IsPrimitivePolynomial r c} = q ^ r := by
    simp [nPrim, ← cast_add, card_filter_add_card_filter_not, monicsOfDegree, ofEquiv_card, ← hq]
  have h_notPrim : (#{c ∈ monicsOfDegree k r | ¬IsPrimitivePolynomial r c} : ℝ) / (q : ℝ) ^ r =
      1 - (nPrim : ℝ) / (q : ℝ) ^ r := by
    rw [eq_sub_iff_add_eq, ← add_div, add_comm, card_split, div_self hqr_pos.ne']
  calc _ ≤ #{c ∈ monicsOfDegree k r | ¬IsPrimitivePolynomial r c} * (1 / (q : ℝ) ^ r) := by
        bound [(by positivity : 0 ≤ (r : ℝ) / q)]
    _ = 1 - (nPrim : ℝ) / (q : ℝ) ^ r := by rw [mul_one_div, h_notPrim]
    _ ≤ 1 - (φ (q ^ r - 1) : ℝ) / (r * (q : ℝ) ^ r) := by linarith
    _ ≤ exp (-(1 / (2 * r * (2 * (r * Real.log q) + 1)))) := by
        simpa [mul_assoc] using TauCeti.Nat.one_sub_totient_pow_sub_one_div_le_exp (by lia) r

/-- Let `k w` be finitely many fields with `q` elements, `r = card n < q`, and `c w` a label of
degree `r` over `k w`: a monic squarefree polynomial of degree `r` that does not vanish at `0`. The
idempotent `tupleIdem n c` is the tensor product over `w` of the `labelIdem n (c w)`; it lies in the
complex group algebra of ∏ GL_n(k w). The real part of its coefficient at the identity element of
that group is at least the product of `(1 - r / q) / q ^ r` over all `w`. -/
lemma New.prod_le_re_tupleIdem_coeff_one {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    [DecidableEq ι] {k : ι → Type*} [∀ w : ι, Field (k w)] [∀ w : ι, Finite (k w)] {q r : ℕ}
    (hq : ∀ w : ι, Nat.card (k w) = q) (hr : Fintype.card n = r) (hrq : r < q)
    {c : ∀ w : ι, (k w)[X]} (hc : ∀ w : ι, IsLabel r (c w)) :
    ∏ _ : ι, ((1 - r / q) / q ^ r : ℝ) ≤ ((tupleIdem n c).coeff 1).re := by
  subst r
  have weight_nonneg : 0 ≤ (1 - card n / q : ℝ) / q ^ card n := by
    bound [(mod_cast hrq.le : (card n : ℝ) ≤ q)]
  -- each factor of the coefficient at 1 is at least the weight, by labelChar_degree_bounds
  have prod_ge : ∏ _ : ι, (((1 - card n / q) / q ^ card n : ℝ) : ℂ) ≤
      ∏ w, (labelIdem n (c w)).coeff 1 :=
    prod_le_prod₀ (fun _ _ ↦ Complex.zero_le_real.mpr weight_nonneg) fun w _ ↦ by
      simpa [labelIdem, ← hq w, hc w] using (labelChar_degree_bounds _ (hc w)).2
  -- the real parts; the coefficient of a tensor product at `1` is the product of the coefficients
  exact_mod_cast (Complex.le_def.mp prod_ge).1

/-- Let `k w` be `f` fields with `q` elements each and `r = card n`. A tuple `c` of labels is good
if no `c w` vanishes at an `M`-th root of unity of `k w` and some `c w` is primitive: irreducible
with a root of order `q ^ r - 1`. In the complex group algebra of ∏ GL_n(k w), take one minus the
sum over the good tuples of `tupleIdem n c`, the tensor product over `w` of the idempotents
`∑ g, (Ξ(1) / |G|) conj Ξ(g) • g` of ℂ[G], where G = GL_n(k w) and Ξ is the character `labelChar` of
the label `c w`. Its coefficient at the identity has real part at most `f * ε + exp (-L)` if
`1 < r < q`, `(1 + M + 2 r) / q ≤ ε ≤ 1` and `2 r (2 r log q + 1) L ≤ f`. -/
lemma New.re_coeff_one_sub_sum_tupleIdem_le {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    [DecidableEq ι]
    {k : ι → Type*} [∀ w : ι, Field (k w)] [∀ w : ι, Finite (k w)] {q M r f : ℕ} [NeZero M]
    (ε L : ℝ) (hq : ∀ w : ι, Nat.card (k w) = q) (hr : Fintype.card n = r) (hf : Fintype.card ι = f)
    (hr_one_lt : 1 < r) (hrq : r < q) (hε_le : ε ≤ 1) (hε_ge : (1 + M + 2 * r) / q ≤ ε)
    (hL : 2 * r * (2 * (r * Real.log q) + 1) * L ≤ f) :
    ((1 - ∑ c ∈ goodTuples M r, tupleIdem (k := k) n c).coeff 1).re ≤ f * ε + exp (-L) := by
  classical
  -- Each good tuple contributes at least `m ^ f` to the coefficient of the sum at `1`. A tuple of
  -- allowed polynomials is good, or none of its polynomials is primitive. Weighted by `m ^ f`,
  -- allowed tuples count at least `(1 - ε) ^ f`, those without primitive polynomial at most
  -- `exp (-u) ^ f`.
  let u : ℝ := 1 / (2 * r * (2 * (r * Real.log q) + 1))
  let m : ℝ := (1 - r / q) / q ^ r
  let allowed (w : ι) : Finset (k w)[X] := {c ∈ monicsOfDegree (k w) r | IsAllowedPolynomial M r c}
  let nonPrim (w : ι) : Finset (k w)[X] := {c ∈ monicsOfDegree (k w) r | ¬IsPrimitivePolynomial r c}
  set good : Finset (∀ w : ι, (k w)[X]) := goodTuples M r
  have m_nonneg : 0 ≤ m := by bound [(mod_cast hrq.le : (r : ℝ) ≤ q)]
  have nonPrim_le (w : ι) : #(nonPrim w) * m ≤ exp (-u) :=
    card_not_primitive_mul_le (k w) (hq w) hr_one_lt hrq
  have tuple_ge (c : ∀ w : ι, (k w)[X]) (hc : c ∈ good) :
      ∏ _ : ι, m ≤ ((tupleIdem n c).coeff 1).re :=
    prod_le_re_tupleIdem_coeff_one hq hr hrq fun w ↦ ((mem_goodTuples.mp hc).1 w).isLabel
  have cover : piFinset allowed \ piFinset nonPrim ⊆ good := by
    intro c hc
    simp only [mem_sdiff, mem_piFinset, allowed, nonPrim, mem_filter] at hc
    grind [mem_goodTuples]
  have pow_le_sum : (1 - ε) ^ f ≤ ∑ c ∈ good, ((tupleIdem n c).coeff 1).re + exp (-(f * u)) := calc
    _ = ∏ _ : ι, (1 - ε) := by simp [hf]
    _ ≤ ∏ w, #(allowed w) * m := prod_le_prod₀ (by bound) fun w _ ↦
      one_sub_le_card_allowed_mul (k w) (hq w) hr_one_lt hrq hε_ge
    _ = #(piFinset allowed) * ∏ _ : ι, m := by simp [prod_mul_distrib]
    _ ≤ (#good + #(piFinset nonPrim)) * ∏ _ : ι, m := by
      grw [card_le_card_sdiff_add_card, card_le_card cover, cast_add]
    _ = #good • ∏ _ : ι, m + ∏ w, #(nonPrim w) * m := by simp [add_mul, prod_mul_distrib]
    _ ≤ ∑ c ∈ good, ((tupleIdem n c).coeff 1).re + exp (-(f * u)) := by
      grw [card_nsmul_le_sum good _ (∏ _ : ι, m) tuple_ge, nonPrim_le]
      simp [hf, ← exp_nsmul]
  have bernoulli : 1 - f * ε ≤ (1 - ε) ^ f := by
    simpa [sub_eq_add_neg] using one_add_mul_le_pow (show -2 ≤ -ε by linarith) f
  calc _ = 1 - ∑ c ∈ good, ((tupleIdem n c).coeff 1).re := by simp
    _ ≤ f * ε + exp (-(f * u)) := by linarith
    _ ≤ f * ε + exp (-L) := by
      gcongr
      rwa [mul_one_div, le_div_iff₀' (by positivity)]

end BadShare
