module

public import Lib.CM.GoodReduction
public import Lib.CM.Integrality.Doubling

/-!
# Integrality of values of sections at torsion points

The file defines the value `torsionValue` at a point of a function with a degree `n` (the function
value times an exponential factor that depends on `n`), which is used for sections at torsion
points, and the property `HasIntegralValues`. For a prime `d ≡ 7 (mod 8)` the file shows that `a₁`
is integral and that monomials in `θ`, `σ²` and the section `translatedYThetaCube` have integral
torsion values. Here `translatedYThetaCube` is `y θ³`, where `y` is the coordinate `translatedY` in
the cubic `y² + a₁ x y = x³ + x`.

The proof uses the naive height `h(w) = max (|σ(w)|_p, |θ(w)|_p)` of a complex number `w`. Because
`a₁ ^ 4 - 64` is a unit, doubling raises the height to the fourth power exactly. From this the file
proves the height comparison: the height of a pull-back along an isogeny of degree `N` is at most
the `N`-th power of the height, and a twisted translation by a torsion point does not increase the
height. At `0` the height is `1`, which gives the integrality of torsion values.

Notions from other files:
* `CMLattice d`: a lattice `Λ` with a point `t` of order two in `ℂ / Λ` and a coefficient `a₁` of
  its cubic. For `d ≠ 0` the lattice has complex multiplication by the integers of `ℚ(√-d)`.
* `σ` and `θ`: the sigma function of `Λ`, normalised so that twisted translation by a period
  multiplies it by a sign, and the theta function that vanishes exactly on `-t + Λ`.
* `twistedTranslate n v G`: the translate of a function `G` by `v`, multiplied by the `n`-th power
  of the exponential factor `exp (-(H(v, z) + H(v, v) / 2))`, where `H(l, z) = (π / area Λ) l̄ z` is
  the Hermitian form.
* `C.sections m`: the sections of degree `m`, spanned by the monomials `monomialSection` in `θ`,
  `σ²` and `translatedYThetaCube`.
* `ιₚ`: the fixed embedding of `ℂ` into `ℂ_p` (`PadicPlace p`); integral means of norm at most `1`,
  that is, lying in `valRingCp p`, the set of elements of `ℂ_p` of norm at most `1`.

## Main definitions and results

* `New.CMLattice.torsionValue`, `New.CMLattice.HasIntegralValues`: the torsion value `G[u]` and the
  property that all of these are integral at torsion points.
* `New.CMLattice.norm_a₁_le_one`: `a₁` is integral, because `a₁ ^ 4 - 64` is a unit.
* `New.CMLattice.naiveHeight`, `New.CMLattice.naiveHeight_two_mul`: the height `h`, and
  `h(2 w) = h(w) ^ 4`.
* `New.CMLattice.naiveHeight_mul_le`, `New.CMLattice.translateHeight_le_naiveHeight`: the height
  comparison for an isogeny and for a translation by a torsion point.
* `New.CMLattice.norm_twistedTranslate_mul_le`: if `|g|_p ≤ h' ^ m` on `ℂ`, then the twisted
  translate of `g` by a torsion point, pulled back along an isogeny of degree `N`, is at most
  `h ^ (m N)`.
* `New.CMLattice.hasIntegralValues_monomialSection`: monomials have integral torsion values.

## Relation to the literature

Known result: the Weber invariants of discriminant `-d` with `d ≡ 7 mod 8` are integral. Source:
Birch, *Weber's class invariants*.

Known result: the integrality of Siegel functions at torsion points. Source: Kubert and Lang,
*Modular Units*.
-/

@[expose] public section

/-! ## Integrality of the coefficient `a₁` -/

namespace New.CMLattice

variable {d : ℕ} [PrimeSevenModEight d] (C : CMLattice d) {p : ℕ} [Fact p.Prime]

/-- If `g ^ 2 + u g = v` in `ℂ_p` with `‖u‖ ≤ c` and `‖v‖ ≤ c ^ 2`, then `‖g‖ ≤ c`: a root of a
monic quadratic whose coefficients are bounded by `c` and `c ^ 2` is bounded by `c`. -/
lemma norm_le_of_sq_add_mul_eq {g u v : ℂ_[p]} {c : ℝ} (hu : ‖u‖ ≤ c) (hv : ‖v‖ ≤ c ^ 2)
    (hg : g ^ 2 + u * g = v) : ‖g‖ ≤ c := by
  by_contra! h_lt
  have hc : 0 ≤ c := (norm_nonneg u).trans hu
  have h_eq : g ^ 2 = u * -g + v := by linear_combination hg
  have h_sq : ‖g‖ ^ 2 ≤ c * ‖g‖ := calc
    ‖g‖ ^ 2 = ‖u * -g + v‖ := by rw [← norm_pow, h_eq]
    _ ≤ max (‖u‖ * ‖g‖) ‖v‖ := by grw [IsUltrametricDist.norm_add_le_max, norm_mul, norm_neg]
    _ ≤ max (c * ‖g‖) (c ^ 2) := by gcongr
    _ = c * ‖g‖ := max_eq_left (by nlinarith)
  nlinarith

/-- For a prime `d ≡ 7 (mod 8)` the coefficient `a₁` of the cubic of a CM lattice is integral in
`ℂ_p`. -/
lemma norm_a₁_le_one [PadicPlace p] : ‖ιₚ C.a₁‖ ≤ 1 := by
  -- `a₁ ^ 4 = (a₁ ^ 4 - 64) + 64` is a sum of two integral elements.
  have h_pow : ιₚ C.a₁ ^ 4 - 64 + 64 ∈ valRingCp p :=
    add_mem (mem_valRingCp.2 (C.norm_disc_eq_one ιₚ).le) (ofNat_mem _ 64)
  rwa [sub_add_cancel, mem_valRingCp, norm_pow,
    pow_le_one_iff_of_nonneg (norm_nonneg _) four_ne_zero] at h_pow

end New.CMLattice

/-!
## Torsion values

The torsion value of a function with a degree, and its rules for powers and pull-backs.
-/

section TorsionValues

open Complex ComplexConjugate
open scoped Real

namespace New.CMLattice
variable {d : ℕ} (C : CMLattice d)

/-- `u` lies in `ℚ Λ`, that is, it represents a torsion point of `ℂ / Λ`. -/
def IsTorsion (u : ℂ) : Prop := ∃ n : ℕ, n ≠ 0 ∧ n * u ∈ C.Λ

/-- The torsion value `G[u]` of a function `G` with the degree `n`: the value at `0` of the twisted
translate of `G` by `u` for `n` times the Hermitian form of the lattice. -/
noncomputable def torsionValue (n : ℕ) (G : ℂ → ℂ) (u : ℂ) : ℂ := C.twistedTranslate n u G 0

/-- The torsion value of `G` at `u` is `G(u) exp (-n π |u|² / (2 area Λ))`. -/
lemma torsionValue_eq (n : ℕ) (G : ℂ → ℂ) (u : ℂ) :
    C.torsionValue n G u = G u * exp (-(π * ‖u‖ ^ 2 / (2 * C.area))) ^ n := by
  have h_exponent : -((n • C.hermitianForm) u u / 2) = n * -(π * ‖u‖ ^ 2 / (2 * C.area)) := by
    change -(n • C.hermitianForm u u / 2) = _
    rw [nsmul_eq_mul, hermitianForm_apply, mul_conj']
    ring
  simp only [torsionValue, thetaShift_apply, zero_add, neg_zero, add_zero, map_zero,
    ← exp_natCast_mul, ← h_exponent, mul_comm (G u)]

lemma torsionValue_pow (k n : ℕ) (G : ℂ → ℂ) (u : ℂ) :
    C.torsionValue (k * n) (G ^ k) u = C.torsionValue n G u ^ k := by
  simp only [torsionValue_eq, Pi.pow_apply]
  ring

/-- Pull-backs: if `z ↦ a z` is an isogeny of degree `N` from the lattice of `C` to that of `C'`,
then with the degree `n N` the function `G(a z)` has at `u` the torsion value `G[a u]`. -/
lemma torsionValue_comp_isogeny {C' : CMLattice d} {a : ℂ} {N : ℕ}
    (h : C.IsIsogeny C'.periodPair a N) (n : ℕ) (G : ℂ → ℂ) (u : ℂ) :
    C.torsionValue (n * N) (fun z : ℂ ↦ G (a * z)) u = C'.torsionValue n G (a * u) := by
  simp only [torsionValue, C.twistedTranslate_comp_isogeny h, mul_zero]

variable {p : ℕ} [Fact p.Prime] [PadicPlace p]

/-- The torsion values of `G` with the degree `n` are all integral in `ℂ_p`: for every torsion
point `u`, the image of `G[u]` under `ιₚ` has norm at most `1`. -/
def HasIntegralValues (n : ℕ) (G : ℂ → ℂ) : Prop :=
  ∀ u : ℂ, C.IsTorsion u → ‖ιₚ (C.torsionValue n G u)‖ ≤ 1

end New.CMLattice

end TorsionValues

namespace New

/-- A bounded real `r` with some value at least `r z ^ 2` whenever `r z > 1` is at most `1`. -/
lemma le_one_of_forall_exists_sq_le {α : Type*} {r : α → ℝ} {K : ℝ} (h_bdd : ∀ z : α, r z ≤ K)
    (h_sq : ∀ z : α, 1 < r z → ∃ z' : α, r z ^ 2 ≤ r z') (z : α) : r z ≤ 1 := by
  by_contra! h_lt
  have h_iterate (k : ℕ) : ∃ z' : α, r z ^ 2 ^ k ≤ r z' := by
    induction k with
    | zero => exact ⟨z, by simp⟩
    | succ k ih =>
      obtain ⟨z₁, h₁⟩ := ih
      obtain ⟨z₂, h₂⟩ := h_sq z₁ ((one_lt_pow₀ h_lt (by positivity)).trans_le h₁)
      refine ⟨z₂, le_trans ?_ h₂⟩
      rw [pow_succ, pow_mul]
      exact pow_le_pow_left₀ (by positivity) h₁ 2
  obtain ⟨n, hn⟩ : ∃ n : ℕ, K < r z ^ n := pow_unbounded_of_one_lt K h_lt
  obtain ⟨z', hz'⟩ := h_iterate n
  have h_exp : r z ^ n ≤ r z ^ 2 ^ n := pow_le_pow_right₀ h_lt.le Nat.lt_two_pow_self.le
  exact (hn.trans_le (h_exp.trans hz')).not_ge (h_bdd z')

end New

/-!
## The naive height

The height `h(w) = max (|σ(w)|_p, |θ(w)|_p)` is positive, and `h(2 w) = h(w) ^ 4` by the doubling
formulas. The monomials of degree `m` are at most `h ^ m`, so every section of degree `m` is at
most a constant times `h ^ m`.
-/

section NaiveHeight

open Complex

namespace New.CMLattice
variable {d : ℕ} (C : CMLattice d) {p : ℕ} [Fact p.Prime] [PadicPlace p]

/-- The naive height `h(w) = max (‖ιₚ (σ w)‖, ‖ιₚ (θ w)‖)` of a complex number `w`. -/
noncomputable def naiveHeight (w : ℂ) : ℝ := max ‖ιₚ (C.σ w)‖ ‖ιₚ (C.θ w)‖

/-- The value of `σ` is at most the naive height. -/
lemma norm_sigma_le_naiveHeight (w : ℂ) : ‖ιₚ (C.σ w)‖ ≤ C.naiveHeight w := le_max_left _ _

/-- The value of `θ` is at most the naive height. -/
lemma norm_theta_le_naiveHeight (w : ℂ) : ‖ιₚ (C.θ w)‖ ≤ C.naiveHeight w := le_max_right _ _

/-- The naive height is positive, because `σ` and `θ` have no common zero: `t ∉ Λ`. -/
lemma naiveHeight_pos (w : ℂ) : 0 < C.naiveHeight w := by
  by_cases hw : w ∈ C.Λ
  · have hθ : C.θ w ≠ 0 := fun h ↦
      C.t_notMem ((add_mem_cancel_left hw).1 (C.theta_eq_zero_iff.1 h))
    exact lt_max_of_lt_right (by simpa using hθ)
  · have hσ : C.σ w ≠ 0 := mt sigma_eq_zero_iff.1 hw
    exact lt_max_of_lt_left (by simpa using hσ)

variable [PrimeSevenModEight d]

/-- Doubling raises the naive height to the fourth power: `h(2 w) = h(w) ^ 4`. -/
lemma naiveHeight_two_mul (w : ℂ) : C.naiveHeight (2 * w) = C.naiveHeight w ^ 4 := by
  -- Doubling acts on the pair `(θ², σ²)` through the quartic forms `doublingForms`, which raise
  -- the norm of a pair to the fourth power; the norm of the pair is the square of the height.
  let v : ℂ → ℂ_[p] × ℂ_[p] := fun z : ℂ ↦ (ιₚ (C.θ z) ^ 2, ιₚ (C.σ z) ^ 2)
  have h_norm (z : ℂ) : ‖v z‖ = C.naiveHeight z ^ 2 := by
    simp only [v, Prod.norm_mk, norm_pow, naiveHeight, max_comm ‖ιₚ (C.σ z)‖]
    exact (pow_left_monotoneOn.map_max (norm_nonneg _) (norm_nonneg _)).symm
  have h_double : v (2 * w) = doublingForms (ιₚ C.a₁) (v w) := by
    ext
    · simp only [v, doublingForms, C.theta_two_mul w, map_sub, map_pow, ← pow_mul]
    · simpa only [v, doublingForms, map_mul, map_add, map_pow, map_ofNat, ← pow_mul]
        using congrArg ιₚ (C.sigma_two_mul_sq w)
  have h_sq : C.naiveHeight (2 * w) ^ 2 = (C.naiveHeight w ^ 4) ^ 2 := by
    rw [← h_norm, h_double, norm_doublingForms C.norm_a₁_le_one (C.norm_disc_eq_one ιₚ), h_norm]
    ring
  exact (sq_eq_sq₀ (C.naiveHeight_pos _).le (pow_pos (C.naiveHeight_pos w) 4).le).1 h_sq

/-- The section `y θ³` (`translatedYThetaCube`) is at most `h ^ 3`. -/
lemma norm_translatedYThetaCube_le (w : ℂ) :
    ‖ιₚ (C.translatedYThetaCube w)‖ ≤ C.naiveHeight w ^ 3 := by
  have hσ : ‖ιₚ (C.σ w)‖ ≤ C.naiveHeight w := C.norm_sigma_le_naiveHeight w
  have hθ : ‖ιₚ (C.θ w)‖ ≤ C.naiveHeight w := C.norm_theta_le_naiveHeight w
  have h_pos : 0 < C.naiveHeight w := C.naiveHeight_pos w
  have h_linear : ‖ιₚ C.a₁ * ιₚ (C.σ w) ^ 2 * ιₚ (C.θ w)‖ ≤ C.naiveHeight w ^ 3 := by
    grw [norm_mul, norm_mul, norm_pow, C.norm_a₁_le_one, hσ, hθ, one_mul, ← pow_succ]
  have h_const :
      ‖ιₚ (C.σ w) ^ 6 + ιₚ (C.σ w) ^ 2 * ιₚ (C.θ w) ^ 4‖ ≤ (C.naiveHeight w ^ 3) ^ 2 := by
    grw [IsUltrametricDist.norm_add_le_max, norm_mul, norm_pow, norm_pow, norm_pow, hσ, hθ,
      ← pow_add, max_self, ← pow_mul]
  exact norm_le_of_sq_add_mul_eq h_linear h_const <| by
    simpa only [map_add, map_mul, map_pow] using congrArg ιₚ (C.translatedYThetaCube_sq_add w)

/-- The monomial `θ^a (σ²)^b G^c` (`monomialSection`) is at most `h ^ (a + 2b + 3c)`. -/
lemma norm_monomialSection_le (x : ℕ × ℕ × ℕ) (w : ℂ) :
    ‖ιₚ (C.monomialSection x w)‖ ≤ C.naiveHeight w ^ monomialDeg x := by
  obtain ⟨a, b, c⟩ := x
  have hσ : ‖ιₚ (C.σ w)‖ ≤ C.naiveHeight w := C.norm_sigma_le_naiveHeight w
  have hθ : ‖ιₚ (C.θ w)‖ ≤ C.naiveHeight w := C.norm_theta_le_naiveHeight w
  have hG : ‖ιₚ (C.translatedYThetaCube w)‖ ≤ C.naiveHeight w ^ 3 :=
    C.norm_translatedYThetaCube_le w
  have h_pos : 0 < C.naiveHeight w := C.naiveHeight_pos w
  simp only [monomialSection, monomialDeg, Pi.mul_apply, Pi.pow_apply, map_mul, map_pow, norm_mul,
    norm_pow, pow_add, pow_mul', mul_assoc]
  gcongr

/-- A section `g` of degree `m` is at most a constant times `h ^ m`. -/
lemma exists_norm_le_mul_naiveHeight_pow {m : ℕ} {g : ℂ → ℂ} (hg : g ∈ C.sections m) :
    ∃ K : ℝ, ∀ w : ℂ, ‖ιₚ (g w)‖ ≤ K * C.naiveHeight w ^ m := by
  refine Submodule.span_induction ?_ ⟨0, by simp⟩ ?_ ?_ (C.sections_le_span_monomialSection m hg)
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨1, fun w ↦ by simpa only [one_mul, ← hx.2] using C.norm_monomialSection_le x w⟩
  · rintro f₁ f₂ - - ⟨K₁, h₁⟩ ⟨K₂, h₂⟩
    refine ⟨max K₁ K₂, fun w ↦ ?_⟩
    calc ‖ιₚ ((f₁ + f₂) w)‖ ≤ max ‖ιₚ (f₁ w)‖ ‖ιₚ (f₂ w)‖ := by
          rw [Pi.add_apply, map_add]
          exact IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max (K₁ * C.naiveHeight w ^ m) (K₂ * C.naiveHeight w ^ m) := max_le_max (h₁ w) (h₂ w)
      _ = max K₁ K₂ * C.naiveHeight w ^ m :=
          (max_mul_of_nonneg _ _ (pow_pos (C.naiveHeight_pos w) m).le).symm
  · rintro c f - ⟨K, hK⟩
    refine ⟨‖ιₚ c‖ * K, fun w ↦ ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, map_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hK w) (norm_nonneg _)

/-- If `g ^ e` (`e ≠ 0`) is a section of degree `e m`, `g` is at most a constant times `h ^ m`. -/
lemma exists_norm_le_of_pow_mem_sections {e m : ℕ} (he : e ≠ 0) {g : ℂ → ℂ}
    (hg : g ^ e ∈ C.sections (e * m)) :
    ∃ K : ℝ, ∀ w : ℂ, ‖ιₚ (g w)‖ ≤ K * C.naiveHeight w ^ m := by
  obtain ⟨K, hK⟩ := C.exists_norm_le_mul_naiveHeight_pow (p := p) hg
  -- Replace the constant `K` by `max 1 K`, which is at most its own `e`-th power.
  refine ⟨max 1 K, fun w ↦ ?_⟩
  have h_pos : 0 < C.naiveHeight w := C.naiveHeight_pos w
  have h_pow : ‖ιₚ (g w)‖ ^ e ≤ (max 1 K * C.naiveHeight w ^ m) ^ e := calc
    ‖ιₚ (g w)‖ ^ e = ‖ιₚ ((g ^ e) w)‖ := by rw [Pi.pow_apply, map_pow, norm_pow]
    _ ≤ K * C.naiveHeight w ^ (e * m) := hK w
    _ ≤ max 1 K ^ e * C.naiveHeight w ^ (e * m) := by
      gcongr
      exact (le_max_right 1 K).trans (le_self_pow₀ (le_max_left 1 K) he)
    _ = (max 1 K * C.naiveHeight w ^ m) ^ e := by rw [mul_pow, ← pow_mul, mul_comm e m]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) he).1 h_pow

end New.CMLattice

end NaiveHeight

/-!
## Height comparison

Let `r` be the ratio of the height of a pull-back, or of a translate, to the bound that is claimed
for it. The ratio is bounded, because powers of the functions involved are sections. Doubling
raises the height to the fourth power, which gives `r(z) ^ 4 = r(2 z)` for a pull-back and
`r(z) ^ 4 = r(2 z + y) r(2 z)` for the translation by `y`. A bounded function with such a law is
at most `1`.
-/

section HeightComparison

open Complex

namespace New.CMLattice
variable {d : ℕ} [PrimeSevenModEight d] (C : CMLattice d) {p : ℕ} [Fact p.Prime] [PadicPlace p]

/-- An isogeny `z ↦ a z` of degree `N` from `C` to `C'` satisfies `h'(a z) ≤ h(z) ^ N`. -/
lemma naiveHeight_mul_le {C' : CMLattice d} {a : ℂ} {N : ℕ} (h : C.IsIsogeny C'.periodPair a N)
    (z : ℂ) : C'.naiveHeight (p := p) (a * z) ≤ C.naiveHeight z ^ N := by
  -- The pull-backs of `σ'²` and `θ'` are sections of degrees `2 N` and `N`, so the ratio
  -- `r(z) = h'(a z) / h(z) ^ N` is bounded.
  have hσ_mem : (fun z : ℂ ↦ C'.σ (a * z) ^ 2) ∈ C.sections (2 * N) := by
    simpa [monomialSection] using C.comp_mul_mem_sections h (C'.monomialSection_mem (0, 1, 0))
  have hθ_mem : (fun z : ℂ ↦ C'.θ (a * z)) ^ 1 ∈ C.sections (1 * N) := by
    simpa only [pow_one] using C.comp_mul_mem_sections h C'.theta_mem
  obtain ⟨K₁, h₁⟩ := C.exists_norm_le_of_pow_mem_sections (p := p) two_ne_zero
    (g := fun z : ℂ ↦ C'.σ (a * z)) hσ_mem
  obtain ⟨K₂, h₂⟩ := C.exists_norm_le_of_pow_mem_sections (p := p) one_ne_zero hθ_mem
  let r : ℂ → ℝ := fun z : ℂ ↦ C'.naiveHeight (a * z) / C.naiveHeight z ^ N
  have h_pos (z : ℂ) : 0 < C.naiveHeight z ^ N := pow_pos (C.naiveHeight_pos z) N
  have h_bdd (z : ℂ) : r z ≤ max K₁ K₂ := by
    rw [div_le_iff₀ (h_pos z), max_mul_of_nonneg _ _ (h_pos z).le]
    exact max_le_max (h₁ z) (h₂ z)
  -- Doubling raises both heights to the fourth power.
  have h_four (z : ℂ) : r z ^ 4 = r (2 * z) := by
    simp only [r]
    rw [div_pow, ← C'.naiveHeight_two_mul, ← pow_mul, mul_comm N 4, pow_mul,
      ← C.naiveHeight_two_mul, mul_left_comm]
  refine (div_le_one (h_pos z)).1 (le_one_of_forall_exists_sq_le h_bdd (fun z hz ↦ ⟨2 * z, ?_⟩) z)
  rw [← h_four]
  exact pow_le_pow_right₀ hz.le (by norm_num)

/-- Height of the twisted translate by `y`: `h(w + y)` times the norm of its exponential factor. -/
noncomputable def translateHeight (y w : ℂ) : ℝ :=
  ‖ιₚ (exp (-(C.hermitianForm y w + C.hermitianForm y y / 2)))‖ * C.naiveHeight (w + y)

omit [PrimeSevenModEight d] in
/-- The degree `m` twisted translate is the translate times `exp (-(H(y, w) + H(y, y) / 2)) ^ m`. -/
lemma twistedTranslate_eq_exp_pow_mul (m : ℕ) (y : ℂ) (g : ℂ → ℂ) (w : ℂ) :
    C.twistedTranslate m y g w =
      exp (-(C.hermitianForm y w + C.hermitianForm y y / 2)) ^ m * g (w + y) := by
  rw [twistedTranslate, thetaShift_apply_apply, ← exp_natCast_mul]
  simp [mul_add, mul_div_assoc]

omit [PrimeSevenModEight d] in
/-- If `g` is at most `h ^ m`, its degree `m` twisted translate is at most `translateHeight ^ m`. -/
lemma norm_twistedTranslate_le_translateHeight_pow {m : ℕ} {g : ℂ → ℂ}
    (hg : ∀ w : ℂ, ‖ιₚ (g w)‖ ≤ C.naiveHeight w ^ m) (y w : ℂ) :
    ‖ιₚ (C.twistedTranslate m y g w)‖ ≤ C.translateHeight y w ^ m := by
  rw [C.twistedTranslate_eq_exp_pow_mul, map_mul, map_pow, norm_mul, norm_pow, translateHeight,
    mul_pow]
  exact mul_le_mul_of_nonneg_left (hg _) (by positivity)

/-- The height `k` of the translate by `y` satisfies `k(w) ^ 4 h(2 w + y) = k(2 w + y) k(2 w)`. -/
lemma translateHeight_pow_four_mul (y w : ℂ) :
    C.translateHeight y w ^ 4 * C.naiveHeight (2 * w + y) =
      C.translateHeight (p := p) y (2 * w + y) * C.translateHeight y (2 * w) := by
  have h_factor : exp (-(C.hermitianForm y w + C.hermitianForm y y / 2)) ^ 4 =
      exp (-(C.hermitianForm y (2 * w + y) + C.hermitianForm y y / 2)) *
        exp (-(C.hermitianForm y (2 * w) + C.hermitianForm y y / 2)) := by
    rw [← exp_natCast_mul, ← exp_add]
    simp only [hermitianForm_apply]
    ring_nf
  simp only [translateHeight]
  rw [mul_pow, ← norm_pow, ← map_pow, h_factor, map_mul, norm_mul, ← C.naiveHeight_two_mul,
    mul_add 2 w y, two_mul y, ← add_assoc]
  ring

/-- For a torsion point `y`, the height of the translate by `y` is at most the naive height. -/
lemma translateHeight_le_naiveHeight {y : ℂ} (hy : C.IsTorsion y) (w : ℂ) :
    C.translateHeight (p := p) y w ≤ C.naiveHeight w := by
  obtain ⟨n, hn, hny⟩ := hy
  -- If `f ^ (2 n)` is a section of degree `2 n`, so is the `2 n`-th power of the twisted translate
  -- of `f` by `y`, because `2 n y` lies in the lattice. This holds for `f = σ` and `f = θ`.
  have h_mem {f : ℂ → ℂ} (hf : f ^ (n * 2) ∈ C.sections (n * 2)) :
      C.twistedTranslate 1 y f ^ (n * 2) ∈ C.sections (n * 2 * 1) := by
    have h_lattice : (n * 2) • y ∈ C.Λ := by
      have h_two : (n * 2) • y = 2 • ((n : ℂ) * y) := by
        simp only [nsmul_eq_mul]
        push_cast
        ring
      exact h_two ▸ nsmul_mem hny 2
    have h_dual : y ∈ ((n * 2) • C.hermitianForm).dualLattice :=
      ThetaTori.mem_dualLattice_nsmul.2 (C.isAppellHumbert_multiplier.le_dualLattice h_lattice)
    rw [mul_one, twistedTranslate, one_smul, ← thetaShift_pow]
    exact (C.isAppellHumbert_multiplier.nsmul (n * 2)).thetaShift_mem_of_mem_dualLattice h_dual hf
  have hσ_mem : C.σ ^ (n * 2) ∈ C.sections (n * 2) := by
    simpa [monomialSection, ← pow_mul, mul_comm 2 n] using C.monomialSection_mem (0, n, 0)
  have hθ_mem : C.θ ^ (n * 2) ∈ C.sections (n * 2) := by
    simpa [monomialSection] using C.monomialSection_mem (n * 2, 0, 0)
  have h_ne : n * 2 ≠ 0 := mul_ne_zero hn two_ne_zero
  obtain ⟨K₁, h₁⟩ := C.exists_norm_le_of_pow_mem_sections (p := p) h_ne (h_mem hσ_mem)
  obtain ⟨K₂, h₂⟩ := C.exists_norm_le_of_pow_mem_sections (p := p) h_ne (h_mem hθ_mem)
  -- So the ratio `r(z) = k(z) / h(z)` is bounded, where `k` is the height of the translate.
  let r : ℂ → ℝ := fun z : ℂ ↦ C.translateHeight y z / C.naiveHeight z
  have h_pos (z : ℂ) : 0 < C.naiveHeight z := C.naiveHeight_pos z
  have hr_nonneg (z : ℂ) : 0 ≤ r z :=
    div_nonneg (mul_nonneg (norm_nonneg _) (h_pos _).le) (h_pos z).le
  have h_bdd (z : ℂ) : r z ≤ max K₁ K₂ := by
    rw [div_le_iff₀ (h_pos z), max_mul_of_nonneg _ _ (h_pos z).le, translateHeight, naiveHeight,
      mul_max_of_nonneg _ _ (norm_nonneg _), ← norm_mul, ← norm_mul, ← map_mul, ← map_mul]
    simpa only [C.twistedTranslate_eq_exp_pow_mul, pow_one] using max_le_max (h₁ z) (h₂ z)
  -- Doubling gives `r(z) ^ 4 = r(2 z + y) r(2 z)`.
  have h_four (z : ℂ) : r z ^ 4 = r (2 * z + y) * r (2 * z) := by
    simp only [r]
    rw [div_pow, ← C.naiveHeight_two_mul, div_mul_div_comm, div_eq_div_iff (h_pos _).ne'
      (mul_pos (h_pos _) (h_pos _)).ne', ← C.translateHeight_pow_four_mul]
    ring
  refine (div_le_one (h_pos w)).1 (le_one_of_forall_exists_sq_le h_bdd (fun z hz ↦ ?_) w)
  -- One of the two factors of `r(z) ^ 4` is at least `r(z) ^ 2`.
  by_contra! h_lt
  have h_mul : r (2 * z + y) * r (2 * z) < r z ^ 2 * r z ^ 2 :=
    mul_lt_mul'' (h_lt _) (h_lt _) (hr_nonneg _) (hr_nonneg _)
  rw [← h_four, ← pow_add] at h_mul
  exact lt_irrefl _ h_mul

/-- If `g ≤ h' ^ m`, a torsion translate of `g` along an isogeny of degree `N` is `≤ h ^ (m N)`. -/
theorem norm_twistedTranslate_mul_le {C' : CMLattice d} {a : ℂ} {N m : ℕ}
    (h : C.IsIsogeny C'.periodPair a N) {y : ℂ} (hy : C'.IsTorsion y) {g : ℂ → ℂ}
    (hg : ∀ w : ℂ, ‖ιₚ (g w)‖ ≤ C'.naiveHeight w ^ m) (z : ℂ) :
    ‖ιₚ (C'.twistedTranslate m y g (a * z))‖ ≤ C.naiveHeight z ^ (m * N) := by
  have h_nonneg : 0 ≤ C'.translateHeight (p := p) y (a * z) :=
    mul_nonneg (norm_nonneg _) (C'.naiveHeight_pos _).le
  calc ‖ιₚ (C'.twistedTranslate m y g (a * z))‖
      ≤ C'.translateHeight y (a * z) ^ m := C'.norm_twistedTranslate_le_translateHeight_pow hg y _
    _ ≤ C'.naiveHeight (a * z) ^ m :=
        pow_le_pow_left₀ h_nonneg (C'.translateHeight_le_naiveHeight hy _) m
    _ ≤ (C.naiveHeight z ^ N) ^ m :=
        pow_le_pow_left₀ (C'.naiveHeight_pos _).le (C.naiveHeight_mul_le h z) m
    _ = C.naiveHeight z ^ (m * N) := by rw [← pow_mul, mul_comm]

end New.CMLattice

end HeightComparison

/-! ## Integral torsion values of monomials -/

namespace New.CMLattice
variable {d : ℕ} [PrimeSevenModEight d] (C : CMLattice d) {p : ℕ} [Fact p.Prime] [PadicPlace p]

/-- For `d` a prime `≡ 7 (mod 8)` and a `p`-adic place `ιₚ`, take a triple `(a, b, c)` and the
monomial `θ^a (σ²)^b G^c` (`monomialSection`), a section of degree `a + 2b + 3c`. Here `σ` is the
sigma function of the lattice and `G = translatedYThetaCube` is the entire function equal to `y θ³`
off `t + Λ`. For every torsion point `u`, the torsion value of this monomial in degree `a + 2b + 3c`
at `u` has `ιₚ`-image of norm at most `1`. -/
lemma hasIntegralValues_monomialSection (x : ℕ × ℕ × ℕ) :
    C.HasIntegralValues (p := p) (monomialDeg x) (C.monomialSection x) := by
  -- The torsion value is the value at `0` of the twisted translate, and the height of `0` is `1`.
  intro u hu
  have h_zero : C.naiveHeight (p := p) 0 = 1 := by simp [naiveHeight, theta_zero]
  calc ‖ιₚ (C.torsionValue (monomialDeg x) (C.monomialSection x) u)‖
      ≤ C.translateHeight u 0 ^ monomialDeg x :=
        C.norm_twistedTranslate_le_translateHeight_pow (C.norm_monomialSection_le x) u 0
    _ ≤ C.naiveHeight 0 ^ monomialDeg x :=
        pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (C.naiveHeight_pos _).le)
          (C.translateHeight_le_naiveHeight hu 0) _
    _ = 1 := by rw [h_zero, one_pow]

end New.CMLattice
