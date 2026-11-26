module

public import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Lib.General.Algebra.SeriesBounds

/-!
# The integrality principle in one variable

* `New.CMLattice.mem_span_monomialSection`: a section of degree `m` that is at most `h ^ m`, where
  `h` is the naive height, is an integral combination of monomials;
  `New.CMLattice.exists_polynomial_of_even` treats even sections.
* `New.CMLattice.exists_taylorVia_eq_theta_pow_mul`: its Taylor series lies in `θ ^ m 𝒪[[y]]`.

Write the section as `θ ^ m (P₀(x) + y P₁(x))`, where `P₁ = 0` if the section is even. Take an
integral number `c` at which `P₀`, `P₁` and the cubic `Q` with `x' ^ 2 = Q(x)` are at least as
large as all their coefficients, and a point `z` with `x(z) = c`. There the height is the norm of
`θ(z)`, so the bracket is integral at `z` and at `-z`. As `x'(z)` is a unit, `P₁(c)` is integral,
and then so is `P₀(c)`.

Notions from other files:

For a lattice `Λ = C.Λ` with a point `t = C.t` of order two modulo `Λ`:
* `θ` is the normalised twisted translate of the sigma function `σ` by `t`; it vanishes on `t + Λ`.
* `x = translatedX` is `℘(z + t) - ℘(t)` and `y = translatedY` is `(℘'(z + t) - a₁ x(z)) / 2`, where
  `a₁ = C.a₁` is a constant of `C` with `‖ιₚ a₁‖ ≤ 1`; off `t + Λ`,
  `x' ^ 2 = x (4 x ^ 2 + a₁ ^ 2 x + 4)`.
* `sections m` is the space of theta functions of degree `m`; the monomial of `(a, b, c)` is
  `θ ^ (a + 2 b + 3 c) x ^ b y ^ c` off `t + Λ`, with degree
  `monomialDeg (a, b, c) = a + 2 b + 3 c`, and `spanningExponents m` is the set of triples with
  `c ≤ 1` and `a + 2 b + 3 c = m`.
* The naive height `h = naiveHeight` is `max (‖ιₚ (σ z)‖, ‖ιₚ (θ z)‖)`, where `σ` is the sigma
  function of `Λ` and `ιₚ : ℂ →+* ℂ_[p]` is the ring homomorphism fixed by the instance
  `PadicPlace p`.

## Relation to the literature

Known result: integral expansions of theta functions of CM elliptic curves, at ordinary primes
`p ≥ 5`. Here `p` is arbitrary, but `d` is a prime congruent to `7` modulo `8`. Source: Bannai and
Kobayashi, Algebraic theta functions and the p-adic interpolation of Eisenstein-Kronecker numbers,
Duke Math. J. 153 (2010), 229-295, after Norman and Mazur–Tate.
-/

@[expose] public section

open PowerSeries

namespace New

namespace CMLattice
variable {d : ℕ} (C : CMLattice d) {p : ℕ} [Fact p.Prime] [PadicPlace p] {f : ℂ → ℂ} {m : ℕ}

/-! ### Sections as polynomials in `x` and `y` -/

/-- The difference `y(z) - y(-z)` is the derivative of `x = translatedX`, where
`y = translatedY`. -/
lemma translatedY_sub_translatedY_neg (z : ℂ) :
    C.translatedY z - C.translatedY (-z) = deriv C.translatedX z := by
  rw [deriv_translatedX, translatedY, translatedY, translatedX_neg,
    show -z + C.t = -(z + C.t) + (⟨C.t + C.t, C.two_t_mem⟩ : C.Λ) by ring,
    PeriodPair.derivWeierstrassP_add_coe, PeriodPair.derivWeierstrassP_neg]
  ring

/-- A section of degree `m` is `θ ^ m (P₀(x) + y P₁(x))` off `t + Λ`, where `x = translatedX`,
`y = translatedY`, and `P₀`, `P₁` are polynomials whose terms `x ^ i`, `y x ^ i` have pole order
at most `m`. -/
lemma exists_eq_theta_pow_mul_eval (hf : f ∈ C.sections m) :
    ∃ P₀ P₁ : Polynomial ℂ, (∀ i : ℕ, P₀.coeff i ≠ 0 → 2 * i ≤ m) ∧
      (∀ i : ℕ, P₁.coeff i ≠ 0 → 2 * i + 3 ≤ m) ∧
      ∀ z : ℂ, z + C.t ∉ C.Λ → f z = C.θ z ^ m *
        (P₀.eval (C.translatedX z) + C.translatedY z * P₁.eval (C.translatedX z)) := by
  -- It suffices to treat zero, sums, and multiples of one monomial.
  refine Submodule.closure_induction ⟨0, 0, by simp⟩ ?_ ?_ (C.sections_le_span_monomialSection m hf)
  · rintro F G - - ⟨P₀, P₁, hP₀, hP₁, hF⟩ ⟨Q₀, Q₁, hQ₀, hQ₁, hG⟩
    refine ⟨P₀ + Q₀, P₁ + Q₁, by grind [Polynomial.coeff_add], by grind [Polynomial.coeff_add],
      fun z hz ↦ ?_⟩
    rw [Pi.add_apply, hF z hz, hG z hz, Polynomial.eval_add, Polynomial.eval_add]
    ring
  · rintro c _ ⟨⟨j, k, e⟩, h_mem, rfl⟩
    obtain ⟨he, rfl⟩ : e ≤ 1 ∧ monomialDeg (j, k, e) = m := mk_mem_spanningExponents.1 h_mem
    -- The monomial of `(j, k, e)` contributes `c x ^ k` to `P₀` if `e = 0`, and to `P₁` if `e = 1`.
    obtain rfl | rfl : e = 0 ∨ e = 1 := Nat.le_one_iff_eq_zero_or_eq_one.1 he
    · refine ⟨.monomial k c, 0, by grind [Polynomial.coeff_monomial], by simp, fun z hz ↦ ?_⟩
      simp [C.monomialSection_eq _ z hz, mul_left_comm]
    · refine ⟨0, .monomial k c, by simp, by grind [Polynomial.coeff_monomial], fun z hz ↦ ?_⟩
      simp [C.monomialSection_eq _ z hz, mul_comm, mul_assoc]

lemma exists_translatedX_eq (c : ℂ) : ∃ z : ℂ, z + C.t ∉ C.Λ ∧ C.translatedX z = c := by
  let a : ℂ := c + C.weierstrassP C.t
  obtain ⟨b, hb⟩ : ∃ b : ℂ, b ^ 2 = 4 * a ^ 3 - C.g₂ * a - C.g₃ :=
    IsSepClosed.exists_pow_nat_eq _ 2
  obtain ⟨w, hw, hw_eq, -⟩ := C.exists_weierstrassP_eq_of_cubic a b hb
  exact ⟨w - C.t, by simpa using hw, by simp [translatedX, hw_eq, a]⟩

/-- If an even function `f` is `θ ^ m (P₀(x) + y P₁(x))` off `t + Λ`, where `x = translatedX` and
`y = translatedY`, then `P₁ = 0`. -/
lemma eq_zero_of_even_of_eq_theta_pow_mul_eval {P₀ P₁ : Polynomial ℂ} (hf_even : f.Even)
    (h_eq : ∀ z : ℂ, z + C.t ∉ C.Λ → f z = C.θ z ^ m *
      (P₀.eval (C.translatedX z) + C.translatedY z * P₁.eval (C.translatedX z))) : P₁ = 0 := by
  -- As `θ` and `x` are even, the odd part `x' P₁(x) / 2` of the bracket vanishes.
  have h_odd (z : ℂ) (hz : z + C.t ∉ C.Λ) :
      deriv C.translatedX z * P₁.eval (C.translatedX z) = 0 := by
    have h_neg : f z = C.θ z ^ m * (P₀.eval (C.translatedX z) +
        C.translatedY (-z) * P₁.eval (C.translatedX z)) := by
      simpa only [hf_even z, theta_neg, translatedX_neg] using
        h_eq (-z) (by rwa [← theta_eq_zero_iff, theta_neg, theta_eq_zero_iff])
    refine mul_left_cancel₀ (pow_ne_zero m (mt C.theta_eq_zero_iff.1 hz)) ?_
    rw [← translatedY_sub_translatedY_neg]
    linear_combination h_neg - h_eq z hz
  -- Multiply by `x'`, whose square is `x Q(x)`; as `x` takes every value, `X Q P₁ = 0`.
  let Q : Polynomial ℂ := 4 * .X ^ 2 + .C (C.a₁ ^ 2) * .X + 4
  have hQ (c : ℂ) : Q.eval c = 4 * c ^ 2 + C.a₁ ^ 2 * c + 4 := by simp [Q]
  have hQ_ne : Q ≠ 0 := fun h ↦ by simpa [h] using hQ 0
  have h_prod : Polynomial.X * Q * P₁ = 0 := by
    refine Polynomial.funext fun c ↦ ?_
    obtain ⟨z, hz, rfl⟩ := C.exists_translatedX_eq c
    rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_X, hQ, Polynomial.eval_zero,
      ← C.deriv_translatedX_sq hz, sq, mul_assoc, h_odd z hz, mul_zero]
  exact (mul_eq_zero_iff_left (mul_ne_zero Polynomial.X_ne_zero hQ_ne)).1 h_prod

/-- An even section of degree `m` is `θ ^ m P(x)` off `t + Λ`, with `x = translatedX` and
`2 i ≤ m` for every term `x ^ i` of `P`. -/
lemma exists_eq_theta_pow_mul_eval_of_even (hf : f ∈ C.sections m) (hf_even : f.Even) :
    ∃ P : Polynomial ℂ, (∀ i : ℕ, P.coeff i ≠ 0 → 2 * i ≤ m) ∧
      ∀ z : ℂ, z + C.t ∉ C.Λ → f z = C.θ z ^ m * P.eval (C.translatedX z) := by
  obtain ⟨P₀, P₁, h_deg, -, h_eq⟩ := C.exists_eq_theta_pow_mul_eval hf
  obtain rfl : P₁ = 0 := C.eq_zero_of_even_of_eq_theta_pow_mul_eval hf_even h_eq
  exact ⟨P₀, h_deg, fun z hz ↦ by simpa using h_eq z hz⟩

lemma monomialDeg_sub_sub {i e : ℕ} (h_le : 2 * i + 3 * e ≤ m) :
    monomialDeg (m - 2 * i - 3 * e, i, e) = m := by
  grind

/-- A section that agrees off `t + Λ` with an entire function `g` equals `g`. -/
lemma eq_of_mem_sections_of_eq_off_translate (hf : f ∈ C.sections m) {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (h_eq : ∀ z : ℂ, z + C.t ∉ C.Λ → f z = g z) : f = g :=
  funext (C.eq_of_eq_off_lattice C.t hf.left hg h_eq)

/-- If every exponent `i` of `P` has `2 i + 3 e ≤ m`, then `θ ^ m y ^ e P(x)` is the combination of
the monomials of degree `m` with the coefficients of `P`, off `t + Λ`. Here `x = translatedX`
and `y = translatedY`. -/
lemma theta_pow_mul_eval_eq_sum {P : Polynomial ℂ} {e : ℕ}
    (hP : ∀ i : ℕ, P.coeff i ≠ 0 → 2 * i + 3 * e ≤ m) {z : ℂ} (hz : z + C.t ∉ C.Λ) :
    C.θ z ^ m * (C.translatedY z ^ e * P.eval (C.translatedX z)) =
      ∑ i ∈ P.support, P.coeff i * C.monomialSection (m - 2 * i - 3 * e, i, e) z := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [C.monomialSection_eq _ z hz, monomialDeg_sub_sub (hP i (Polynomial.mem_support_iff.1 hi))]
  ring

/-- If `P` has degree at most `m / 2`, then `θ ^ m P(x)`, with `x = translatedX`, is the
combination of the monomials of `(m - 2 i, i, 0)`, `i ≤ m / 2`, with the coefficients of `P`, off
`t + Λ`. -/
lemma theta_pow_mul_eval_eq_sum_range {P : Polynomial ℂ} (hP : 2 * P.natDegree ≤ m) {z : ℂ}
    (hz : z + C.t ∉ C.Λ) :
    C.θ z ^ m * P.eval (C.translatedX z) =
      ∑ i ∈ Finset.range (m / 2 + 1), P.coeff i * C.monomialSection (m - 2 * i, i, 0) z := by
  rw [Polynomial.eval_eq_sum_range' (n := m / 2 + 1) (by omega), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [C.monomialSection_eq _ z hz, show monomialDeg (m - 2 * i, i, 0) = m by grind]
  ring

/-- Let `e ≤ 1`, and let `P` have coefficients integral in `ℂ_p` and `2 i + 3 e ≤ m` for each of its
exponents `i`. Then `θ ^ m translatedY ^ e P(translatedX)` agrees off `t + Λ` with an entire
function that is an integral combination of the monomials of the triples `(a, b, c)` with `c ≤ 1`
and degree `a + 2 b + 3 c = m` (the set `spanningExponents m`). -/
lemma exists_mem_span_monomialSection_eq_theta_pow_mul_eval {P : Polynomial ℂ} {e : ℕ} (he : e ≤ 1)
    (h_deg : ∀ i : ℕ, P.coeff i ≠ 0 → 2 * i + 3 * e ≤ m) (h_int : ∀ i : ℕ, ‖ιₚ (P.coeff i)‖ ≤ 1) :
    ∃ g ∈ Submodule.span ((valRingCp p).comap ιₚ) (C.monomialSection '' spanningExponents m),
      Differentiable ℂ g ∧ ∀ z : ℂ, z + C.t ∉ C.Λ →
        g z = C.θ z ^ m * (C.translatedY z ^ e * P.eval (C.translatedX z)) := by
  refine ⟨∑ i ∈ P.support, P.coeff i • C.monomialSection (m - 2 * i - 3 * e, i, e),
    sum_mem fun i hi ↦ ?_, by fun_prop, fun z hz ↦ ?_⟩
  · exact Submodule.smul_mem _ (⟨P.coeff i, h_int i⟩ : (valRingCp p).comap ιₚ)
      (Submodule.subset_span (Set.mem_image_of_mem C.monomialSection (mk_mem_spanningExponents.2
        ⟨he, monomialDeg_sub_sub (h_deg i (Polynomial.mem_support_iff.1 hi))⟩)))
  · simp only [C.theta_pow_mul_eval_eq_sum h_deg hz, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- If `f = θ ^ m P(x)` off `t + Λ`, with `x = translatedX`, then the same identity holds for the
Taylor series at `0`, with `ιₚ` applied to the coefficients. -/
lemma taylorVia_eq_of_eq_theta_pow_mul_eval {P : Polynomial ℂ}
    (h_eq : ∀ z : ℂ, z + C.t ∉ C.Λ → f z = C.θ z ^ m * P.eval (C.translatedX z)) :
    taylorVia ιₚ f = taylorVia ιₚ C.θ ^ m * (P.map ιₚ).aeval (taylorVia ιₚ C.translatedX) := by
  have h_eval : map ιₚ (P.aeval (taylorAtZero C.translatedX)) =
      (P.map ιₚ).aeval (taylorVia ιₚ C.translatedX) :=
    Polynomial.map_aeval_eq_aeval_map (RingHom.ext fun c ↦ (map_C ιₚ c).symm) P _
  simp (disch := fun_prop) only [taylorVia, C.taylorAtZero_congr h_eq, taylorAtZero_mul,
    taylorAtZero_pow, taylorAtZero_eval, map_mul, map_pow, h_eval]

/-! ### A general integral point and the integrality principle -/

omit C in
/-- Some integral `c` makes each of finitely many polynomials as large as its coefficients. -/
lemma exists_norm_coeff_le_norm_eval {n : ℕ} (F : Fin n → Polynomial ℂ) :
    ∃ c : ℂ, ‖ιₚ c‖ ≤ 1 ∧ ∀ (i : Fin n) (k : ℕ), ‖ιₚ ((F i).coeff k)‖ ≤ ‖ιₚ ((F i).eval c)‖ := by
  -- Read the polynomials as polynomials in one variable indexed by `Unit`, with the valuation
  -- `c ↦ ‖ιₚ c‖` on `ℂ`.
  let v : Valuation ℂ NNReal := NormedField.valuation.comap ιₚ
  obtain ⟨y, hy⟩ := exists_val_coeff_le_val_eval v fun i : Fin n ↦
    (MvPolynomial.uniqueAlgEquiv ℂ Unit).symm (F i)
  refine ⟨y (), (y ()).property, fun i k ↦ ?_⟩
  have h_eval : MvPolynomial.eval (algebraMap v.valuationSubring ℂ ∘ y)
      ((MvPolynomial.uniqueAlgEquiv ℂ Unit).symm (F i)) = (F i).eval (y () : ℂ) :=
    MvPolynomial.eval₂_uniqueAlgEquiv_symm
  have h_le := hy i (Finsupp.single () k)
  rw [MvPolynomial.coeff_uniqueAlgEquiv_symm, Finsupp.single_eq_same, h_eval] at h_le
  exact h_le

variable [PrimeSevenModEight d]

/-- Let `C` be a CM lattice for a prime `d ≡ 7 mod 8`, with point `t` of order two, and let
`ιₚ : ℂ → ℂ_p` be a `p`-adic place. Suppose `f z = θ z ^ m (P₀(x z) + y z · P₁(x z))` whenever
`z + t ∉ Λ`, where `x = translatedX` is `℘(z + t) - ℘(t)` and `y = translatedY` is
`½(℘'(z + t) - a₁ x(z))`. Suppose also that `‖ιₚ (f z)‖ ≤ h(z) ^ m` for all `z`, where `h` is the
naive height `max (‖ιₚ (σ z)‖, ‖ιₚ (θ z)‖)`. Then every coefficient of `P₀` and `P₁` has image under
`ιₚ` of norm at most `1`. -/
lemma norm_coeff_le_one_of_norm_le_naiveHeight_pow {P₀ P₁ : Polynomial ℂ}
    (h_eq : ∀ z : ℂ, z + C.t ∉ C.Λ → f z = C.θ z ^ m *
      (P₀.eval (C.translatedX z) + C.translatedY z * P₁.eval (C.translatedX z)))
    (h_le : ∀ z : ℂ, ‖ιₚ (f z)‖ ≤ C.naiveHeight z ^ m) :
    (∀ n : ℕ, ‖ιₚ (P₀.coeff n)‖ ≤ 1) ∧ ∀ n : ℕ, ‖ιₚ (P₁.coeff n)‖ ≤ 1 := by
  -- Take an integral `c` at which `P₀`, `P₁` and the cubic `Q` with `x'² = Q(x)` are at least as
  -- large as their coefficients. It suffices to show that `P₀(c)` and `P₁(c)` are integral.
  let Q : Polynomial ℂ := .monomial 3 4 + .monomial 2 (C.a₁ ^ 2) + .monomial 1 4
  obtain ⟨c, hc, h_general⟩ := exists_norm_coeff_le_norm_eval (p := p) ![P₀, P₁, Q]
  have hQ_eval : Q.eval c = c * (4 * c ^ 2 + C.a₁ ^ 2 * c + 4) := by
    simp only [Q, Polynomial.eval_add, Polynomial.eval_monomial]
    ring
  -- The value `Q(c)` is a unit: otherwise `4` and `a₁²` are not units, but `a₁ ^ 4 - 64` is one.
  have hc_mem : ιₚ c ∈ valRingCp p := hc
  have ha₁ : ιₚ C.a₁ ∈ valRingCp p := C.norm_a₁_le_one
  have h_four : (4 : ℂ_[p]) ∈ valRingCp p := ofNat_mem _ 4
  have hQ_norm : ‖ιₚ (Q.eval c)‖ = 1 := by
    refine le_antisymm ?_ (not_lt.1 fun h_lt ↦ ?_)
    · rw [hQ_eval]
      simp only [map_mul, map_add, map_pow, map_ofNat]
      exact mul_mem hc_mem (add_mem (add_mem (mul_mem h_four (pow_mem hc_mem 2))
        (mul_mem (pow_mem ha₁ 2) hc_mem)) h_four)
    · have h_coeff₁ : ‖(4 : ℂ_[p])‖ < 1 := by
        simpa [Q, Polynomial.coeff_monomial, map_ofNat] using (h_general 2 1).trans_lt h_lt
      have h_coeff₂ : ‖ιₚ C.a₁ ^ 2‖ < 1 := by
        simpa [Q, Polynomial.coeff_monomial] using (h_general 2 2).trans_lt h_lt
      have h_disc : ιₚ C.a₁ ^ 4 - 64 = ιₚ C.a₁ ^ 2 * ιₚ C.a₁ ^ 2 + -16 * 4 := by ring
      exact (norm_lt_one_of_eq_mul_add_mul (pow_mem ha₁ 2) (intCast_mem (valRingCp p) (-16))
        (by simpa using h_disc) h_coeff₂ h_coeff₁).ne (C.norm_disc_eq_one ιₚ)
  obtain ⟨z, hz, rfl⟩ := C.exists_translatedX_eq c
  have hz_neg : -z + C.t ∉ C.Λ := by rwa [← theta_eq_zero_iff, theta_neg, theta_eq_zero_iff]
  -- Where `x` is integral and finite, the height is `‖ιₚ θ‖`, so the bracket is integral.
  let F (w : ℂ) : ℂ := P₀.eval (C.translatedX w) + C.translatedY w * P₁.eval (C.translatedX w)
  have hF {w : ℂ} (hw : w + C.t ∉ C.Λ) (hx : ‖ιₚ (C.translatedX w)‖ ≤ 1) : ‖ιₚ (F w)‖ ≤ 1 := by
    have h_sq : ‖ιₚ (C.σ w)‖ ^ 2 ≤ ‖ιₚ (C.θ w)‖ ^ 2 := by
      rw [← norm_pow, ← map_pow, C.sigma_sq_eq_translatedX_mul_theta_sq hw, map_mul, norm_mul,
        map_pow, norm_pow]
      exact mul_le_of_le_one_left (by positivity) hx
    have h_height : C.naiveHeight w = ‖ιₚ (C.θ w)‖ :=
      max_eq_right ((pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h_sq)
    have hθ : 0 < ‖ιₚ (C.θ w)‖ ^ m :=
      pow_pos (norm_pos_iff.2 ((map_ne_zero ιₚ).2 (mt C.theta_eq_zero_iff.1 hw))) m
    have h_bound : ‖ιₚ (C.θ w)‖ ^ m * ‖ιₚ (F w)‖ ≤ ‖ιₚ (C.θ w)‖ ^ m * 1 := by
      simpa only [h_eq w hw, map_mul, norm_mul, map_pow, norm_pow, h_height, mul_one]
        using h_le w
    exact le_of_mul_le_mul_left h_bound hθ
  have hFz : ‖ιₚ (F z)‖ ≤ 1 := hF hz hc
  have hFz_neg : ‖ιₚ (F (-z))‖ ≤ 1 := hF hz_neg (by rwa [translatedX_neg])
  -- The difference of the brackets at `z` and `-z` is `x' P₁(x)`, and `x'² = Q(x)` is a unit.
  have h_deriv : ‖ιₚ (deriv C.translatedX z)‖ = 1 := by
    have h_sq : ‖ιₚ (deriv C.translatedX z)‖ ^ 2 = 1 := by
      rw [← norm_pow, ← map_pow, C.deriv_translatedX_sq hz, ← hQ_eval, hQ_norm]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h_sq
  have h₁ : ‖ιₚ (P₁.eval (C.translatedX z))‖ ≤ 1 := by
    have h_diff : deriv C.translatedX z * P₁.eval (C.translatedX z) = F z - F (-z) := by
      simp only [F, ← translatedY_sub_translatedY_neg, translatedX_neg]
      ring
    have h_mul : ‖ιₚ (deriv C.translatedX z * P₁.eval (C.translatedX z))‖ ≤ 1 := by
      rw [h_diff, map_sub]
      exact sub_mem (mem_valRingCp.2 hFz) (mem_valRingCp.2 hFz_neg)
    rwa [map_mul, norm_mul, h_deriv, one_mul] at h_mul
  -- The coordinate `y` is integral, as a root of the cubic equation, so `P₀(x)` is integral.
  have hy : ‖ιₚ (C.translatedY z)‖ ≤ 1 := by
    refine norm_le_of_sq_add_mul_eq (u := ιₚ C.a₁ * ιₚ (C.translatedX z))
      (v := ιₚ (C.translatedX z) ^ 3 + ιₚ (C.translatedX z)) ?_ ?_ ?_
    · exact mul_mem ha₁ hc_mem
    · rw [one_pow]
      exact add_mem (pow_mem hc_mem 3) hc_mem
    · simpa only [map_add, map_mul, map_pow] using congrArg ιₚ (C.weierstrass_equation hz)
  have h₀ : ‖ιₚ (P₀.eval (C.translatedX z))‖ ≤ 1 := by
    have h_sum : ιₚ (P₀.eval (C.translatedX z)) + ιₚ (C.translatedY z) *
        ιₚ (P₁.eval (C.translatedX z)) ∈ valRingCp p := by
      simpa only [F, map_add, map_mul] using mem_valRingCp.2 hFz
    exact (add_mem_cancel_right (mul_mem (mem_valRingCp.2 hy) (mem_valRingCp.2 h₁))).1 h_sum
  exact ⟨fun n ↦ (h_general 0 n).trans h₀, fun n ↦ (h_general 1 n).trans h₁⟩

/-- Let `d` be a prime `≡ 7 (mod 8)` and fix a `p`-adic place `ιₚ`. Let `f` be a section of degree
`m` (a theta function for `Λ` of degree `m`) with `‖ιₚ (f z)‖ ≤ h(z) ^ m` for all `z`, where `h` is
the naive height `max (‖ιₚ (σ z)‖, ‖ιₚ (θ z)‖)`. Then `f` is a combination, with coefficients
integral in `ℂ_p`, of the monomials of the triples `(a, b, c)` with `c ≤ 1` and degree
`a + 2 b + 3 c = m` (the set `spanningExponents m`); off `t + Λ` these monomials are
`θ ^ m translatedX ^ b translatedY ^ c`. The scalars are the complex numbers whose image under `ιₚ`
lies in the valuation ring `valRingCp p`. -/
lemma mem_span_monomialSection {f : ℂ → ℂ} {m : ℕ} (hf : f ∈ C.sections m)
    (h_le : ∀ z : ℂ, ‖ιₚ (f z)‖ ≤ C.naiveHeight z ^ m) :
    f ∈ Submodule.span ((valRingCp p).comap ιₚ) (C.monomialSection '' spanningExponents m) := by
  obtain ⟨P₀, P₁, h_deg₀, h_deg₁, h_eq⟩ := C.exists_eq_theta_pow_mul_eval hf
  obtain ⟨h_int₀, h_int₁⟩ := C.norm_coeff_le_one_of_norm_le_naiveHeight_pow h_eq h_le
  -- The summands `θ ^ m P₀(x)` and `θ ^ m y P₁(x)` extend to entire `g₀` and `g₁` in the span.
  obtain ⟨g₀, hg₀_mem, hg₀_diff, hg₀⟩ :=
    C.exists_mem_span_monomialSection_eq_theta_pow_mul_eval zero_le_one h_deg₀ h_int₀
  obtain ⟨g₁, hg₁_mem, hg₁_diff, hg₁⟩ :=
    C.exists_mem_span_monomialSection_eq_theta_pow_mul_eval le_rfl h_deg₁ h_int₁
  have h_off (z : ℂ) (hz : z + C.t ∉ C.Λ) : f z = (g₀ + g₁) z := by
    rw [Pi.add_apply, h_eq z hz, hg₀ z hz, hg₁ z hz]
    ring
  rw [C.eq_of_mem_sections_of_eq_off_translate hf (hg₀_diff.add hg₁_diff) h_off]
  exact add_mem hg₀_mem hg₁_mem

/-- The polynomial `R` is an integral expansion of `f` in degree `m` in the monomials
`θ ^ (m - 2 i) σ ^ (2 i)`, which are `θ ^ m x ^ i` off `t + Λ`, where `x = translatedX`. -/
structure IsIntegralEvenExpansion (m : ℕ) (f : ℂ → ℂ) (R : Polynomial ℂ) : Prop where
  /-- The coefficients of `R` are integral in `ℂ_p`. -/
  norm_coeff_le_one : ∀ i : ℕ, ‖ιₚ (R.coeff i)‖ ≤ 1
  /-- The degree of `R` is at most `m / 2`. -/
  two_mul_natDegree_le : 2 * R.natDegree ≤ m
  /-- The function `f` is `∑ Rᵢ θ ^ (m - 2 i) σ ^ (2 i)`, the sum being over `i ≤ m / 2`. -/
  eq_sum : ∀ z : ℂ, f z = ∑ i ∈ Finset.range (m / 2 + 1),
    R.coeff i * C.monomialSection (m - 2 * i, i, 0) z
  /-- The Taylor series of `f` at `0`, with `ιₚ` applied to the coefficients, is `θ ^ m R(x)`. -/
  taylorVia_eq :
    taylorVia ιₚ f = taylorVia ιₚ C.θ ^ m * (R.map ιₚ).aeval (taylorVia ιₚ C.translatedX)

/-- Let `C` be a CM lattice for a prime `d ≡ 7 mod 8`, with point `t` of order two, and let `ιₚ` be
a `p`-adic place. Let `f` be an even section of degree `m` (a theta function for `Λ` with hermitian
form `m H` and multiplier `χ ^ m`) with `‖ιₚ (f z)‖ ≤ h(z) ^ m` for all `z`, where `h` is the naive
height `max (‖ιₚ (σ z)‖, ‖ιₚ (θ z)‖)`. Then
`f = ∑ Rᵢ θ ^ (m - 2 i) σ ^ (2 i)` for a polynomial `R` with `ιₚ`-integral coefficients and degree
at most `m / 2`, and the Taylor series of `f` at `0` is that of `θ ^ m R(x)`, where
`x(z) = ℘(z + t) - ℘(t)` is `translatedX`; these are the clauses of `IsIntegralEvenExpansion`. -/
lemma exists_polynomial_of_even {f : ℂ → ℂ} {m : ℕ} (hf : f ∈ C.sections m)
    (h_le : ∀ z : ℂ, ‖ιₚ (f z)‖ ≤ C.naiveHeight z ^ m) (hf_even : f.Even) :
    ∃ R : Polynomial ℂ, C.IsIntegralEvenExpansion m f R := by
  obtain ⟨R, h_deg, h_eq⟩ : ∃ R : Polynomial ℂ, (∀ i : ℕ, R.coeff i ≠ 0 → 2 * i ≤ m) ∧
      ∀ z : ℂ, z + C.t ∉ C.Λ → f z = C.θ z ^ m * R.eval (C.translatedX z) :=
    C.exists_eq_theta_pow_mul_eval_of_even hf hf_even
  -- This is the form `θ ^ m (P₀(x) + y P₁(x))` with `P₀ = R` and `P₁ = 0`.
  have hR_int : ∀ i : ℕ, ‖ιₚ (R.coeff i)‖ ≤ 1 :=
    (C.norm_coeff_le_one_of_norm_le_naiveHeight_pow (P₁ := 0) (by simpa using h_eq) h_le).left
  have h_natDegree : 2 * R.natDegree ≤ m := by
    rcases eq_or_ne R 0 with rfl | hR
    · simp
    · exact h_deg R.natDegree (Polynomial.leadingCoeff_ne_zero.2 hR)
  have h_off (z : ℂ) (hz : z + C.t ∉ C.Λ) : f z = ∑ i ∈ Finset.range (m / 2 + 1),
      R.coeff i * C.monomialSection (m - 2 * i, i, 0) z :=
    (h_eq z hz).trans (C.theta_pow_mul_eval_eq_sum_range h_natDegree hz)
  exact ⟨R, hR_int, h_natDegree,
    congrFun (C.eq_of_mem_sections_of_eq_off_translate hf (by fun_prop) h_off),
    C.taylorVia_eq_of_eq_theta_pow_mul_eval h_eq⟩

/-- Let `f` be a combination, with coefficients integral in `ℂ_p`, of monomials of degree `m`.
Then `f` is analytic at `0` and its Taylor series lies in `θ ^ m 𝒪[[y]]`, where
`𝒪[[y]] = integralSeriesRing` is the ring of integral power series in the Taylor series of
`y = translatedY`. -/
lemma exists_taylorVia_eq_theta_pow_mul_of_mem_span {s : Set (ℕ × ℕ × ℕ)}
    (h_deg : ∀ x ∈ s, monomialDeg x = m)
    (hf : f ∈ Submodule.span ((valRingCp p).comap ιₚ) (C.monomialSection '' s)) :
    AnalyticAt ℂ f 0 ∧ ∃ u ∈ C.integralSeriesRing, taylorVia ιₚ f = taylorVia ιₚ C.θ ^ m * u := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    -- A monomial is `θ ^ m x ^ b y ^ c`, and `x = translatedX` and `y` lie in `𝒪[[y]]`.
    obtain ⟨⟨a, b, c⟩, h_mem, rfl⟩ := hg
    have h_coord : taylorVia ιₚ C.translatedX ^ b * taylorVia ιₚ C.translatedY ^ c ∈
        C.integralSeriesRing :=
      mul_mem (pow_mem C.taylorVia_translatedX_mem_integralSeriesRing b)
        (pow_mem C.isSeriesGenerator_translatedY.generator_mem c)
    refine ⟨by fun_prop, _, h_coord, ?_⟩
    simp [← h_deg _ h_mem, taylorVia, taylorAtZero_monomialSection_eq]
  | zero => exact ⟨analyticAt_const, 0, zero_mem _, by simp [Pi.zero_def]⟩
  | add g₁ g₂ _ _ h₁ h₂ =>
    obtain ⟨hg₁, u₁, hu₁, h_eq₁⟩ := h₁
    obtain ⟨hg₂, u₂, hu₂, h_eq₂⟩ := h₂
    refine ⟨hg₁.add hg₂, u₁ + u₂, add_mem hu₁ hu₂, ?_⟩
    rw [mul_add, ← h_eq₁, ← h_eq₂, Pi.add_def, taylorVia, taylorAtZero_add hg₁ hg₂, map_add]
  | smul a g _ h =>
    obtain ⟨hg, u, hu, h_eq⟩ := h
    refine ⟨analyticAt_const.mul hg, ιₚ (a : ℂ) • u,
      C.isSeriesGenerator_translatedY.smul_mem a.property hu, ?_⟩
    rw [show a • g = fun z : ℂ ↦ (a : ℂ) * g z from rfl, mul_smul_comm, ← h_eq, taylorVia,
      taylorAtZero_mul analyticAt_const hg, taylorAtZero_const, map_mul, map_C, smul_eq_C_mul]

/-- Let `d` be a prime congruent to 7 mod 8. Let `f` be a section of degree `m` (a theta function
for `Λ` with hermitian form `m H` and multiplier `χ ^ m`) with `‖ιₚ (f z)‖ ≤ h(z) ^ m` for all `z`,
where `h` is the naive height `max (‖ιₚ (σ z)‖, ‖ιₚ (θ z)‖)`. Then the Taylor series of `f` at `0`,
with `ιₚ` applied to its coefficients, is the `m`-th power of that of the degree-one theta function
`θ` times an element of `integralSeriesRing`, the ring `𝒪[[y]]` of integral power series in the
series of `y(z) = ½(℘′(z + t) − a₁ x(z))` (`translatedY`), where `x(z) = ℘(z + t) − ℘(t)` and `t` is
the chosen point of order two. -/
lemma exists_taylorVia_eq_theta_pow_mul (hf : f ∈ C.sections m)
    (h_le : ∀ z : ℂ, ‖ιₚ (f z)‖ ≤ C.naiveHeight z ^ m) :
    ∃ u ∈ C.integralSeriesRing, taylorVia ιₚ f = taylorVia ιₚ C.θ ^ m * u :=
  (C.exists_taylorVia_eq_theta_pow_mul_of_mem_span
    (fun ⟨_, _, _⟩ hx ↦ (mk_mem_spanningExponents.1 hx).right)
    (C.mem_span_monomialSection hf h_le)).right

end CMLattice

end New
