module

public import New.Reduction.Data.Magnitudes

/-!
# Tight frames in `𝔞₀`

A tight frame of length `h` is a finite family of vectors `y` of the lattice `𝔞₀`, counted with
multiplicities, such that `∑ y, (y† z) y = h z` for all `z`: a resolution of `h`.

* `New.Parameters.exists_isTightFrame_coprime`: a tight frame in `𝔞₀` of length `h ≤ (d q₁) ^ 6`
  prime to `q₁`, together with the unit-linear-form property.
* `New.Parameters.exists_isTightFrame_of_coprime`: this frame and the powers of `ζ` give tight
  frames of every length `m ≥ q₁ h + R (q₁ + h)` with multiplicities at least `R`.
* `New.Data.exists_isTightFrame`: a tight frame of length `p₀ p₁ = D.M` with large multiplicities,
  where `p₀` and `p₁` are the two primes `D.levelPrime 0` and `D.levelPrime 1` of the data.

The powers of `ζ` form a tight frame of length `q₁`. To construct a tight frame of coprime length
`h` without using a dual basis, we solve a quadratic congruence `n z² + z + 1 ≡ 0 (mod q₁)` where
`n = (d + 1) / 4 = β (1 - β)`, set `t = (1 - β) + n z`, and for each prime factor `ℓ ∣ q₁` with
`q₁ = ℓ r` and `r = ℓ^a M` (`ℓ ∤ M`), we form the family
`u(ℓ, j, k, i) = ζ^j (0^k a_ℓ^i + (t M / q₁) (a_ℓ^i - a_ℓ^k))` where `a_ℓ = ζ^r`.
Summing over `(ℓ, j, k, i)` gives a tight frame whose length `h` is bounded by `(d q₁) ^ 6` and
coprime to `q₁`.

Notions from other files:
* `P.E s` is the field `E = K(ζ)`, where `K = ℚ(√-d)` and `ζ = P.ζ s` is a primitive root of unity
  of order `q₁ = P.q₁ s = P.q₀ * towerDeg s`. `P.zetaInt s` is `ζ` as an element of `𝓞 E`.
* `P.Φ s` is the set of infinite places of `E`; `Φ τ` is the complex embedding of `E` chosen at `τ`.
* `finiteImage id y ∈ Ô E` says that `y` lies in the lattice `𝔞₀ = E ∩ α Ô`, where `α` is the idele
  of the Weil data and `Ô` is the ring of integral finite adeles.
* `P.periodFactor s` is a complex number; by `norm_iota_periodFactor` its absolute value at an
  embedding `ιₚ : ℂ →+* ℂ_[p]` is given by the idele `α`.
* `β = (1 + √-d) / 2` is `quadGen d` in `ℂ`, `QuadField.betaK d` in `𝓞 K` and `P.betaKInE s` in
  `𝓞 E`.
-/

@[expose] public section

open Polynomial Finset ComplexConjugate NumberField

namespace New

section Families

variable {E I J : Type} [Field E] [CMType E] [WeilData E] [Fintype I] [Fintype J]

/-- The disjoint union of a tight frame `w` with multiplicities `m` and frame bound `M` and a tight
frame `w'` with multiplicities `m'` and frame bound `M'` is a tight frame with frame bound `M + M'`.
This disjoint union is the family `Sum.elim w w'` with multiplicities `Sum.elim m m'`. -/
lemma IsTightFrame.sumElim {w : I → E} {w' : J → E} {m : I → ℕ} {m' : J → ℕ} {M M' : ℕ}
    (hw : IsTightFrame w m M) (hw' : IsTightFrame w' m' M') :
    IsTightFrame (Sum.elim w w') (Sum.elim m m') (M + M') := by
  refine ⟨Sum.forall.2 ⟨hw.finiteImage_mem, hw'.finiteImage_mem⟩, fun σ τ ↦ ?_⟩
  simp [Fintype.sum_sum_type, hw.sum_mul_conj, hw'.sum_mul_conj, ite_add_ite]

end Families

/-- Let `d` be a prime with `d ≡ 7 mod 8`. An element of `K = ℚ(√-d)` fixed by complex conjugation
is rational. -/
lemma QuadField.exists_algebraMap_eq_of_star_eq {d : ℕ} [PrimeSevenModEight d] {a : QuadField d}
    (ha : star a = a) : ∃ q : ℚ, algebraMap ℚ (QuadField d) q = a := by
  -- The maximal real subfield of the quadratic field `K` does not contain `√-d`, so it is `ℚ`.
  let R : IntermediateField ℚ (QuadField d) :=
    (maximalRealSubfield (QuadField d)).toIntermediateField (by simp)
  have h_mem {x : QuadField d} : x ∈ R ↔ star x = x := mem_maximalRealSubfield_iff_star_eq
  have h_prime : (Module.finrank ℚ (QuadField d)).Prime := by
    simp [QuadField.finrank_eq_two, Nat.prime_two]
  have h_sqrt : QuadField.sqrtNegD d ∉ R := by
    simp [h_mem, neg_eq_self, Subtype.ext_iff, NeZero.ne]
  rcases (IntermediateField.isSimpleOrder_of_finrank_prime ℚ (QuadField d) h_prime).eq_bot_or_eq_top
    R with h_bot | h_top
  · exact IntermediateField.mem_bot.1 (h_bot.le (h_mem.2 ha))
  · exact absurd (h_top.ge IntermediateField.mem_top) h_sqrt

/-- Let `d` be a prime with `d ≡ 7 mod 8`. If a complex number `z` lies in `quadInt d`, the ring of
integers of `K = ℚ(√-d)` as a subring of `ℂ`, and is real, then `z` is a rational integer. -/
lemma exists_eq_intCast_of_mem_quadInt_of_conj_eq {d : ℕ} [PrimeSevenModEight d] {z : ℂ}
    (hz : z ∈ quadInt d) (h_real : conj z = z) : ∃ n : ℤ, z = n := by
  obtain ⟨a, rfl⟩ : ∃ a : 𝓞 (QuadField d), ((a : QuadField d) : ℂ) = z := RingHom.mem_range.1 hz
  have ha_real : star (a : QuadField d) = a :=
    Subtype.ext ((QuadField.coe_star_eq_conj d a).trans h_real)
  obtain ⟨q, hq⟩ : ∃ q : ℚ, algebraMap ℚ (QuadField d) q = a :=
    QuadField.exists_algebraMap_eq_of_star_eq ha_real
  have h_int : IsIntegral ℤ q := by
    rw [← isIntegral_algebraMap_iff (B := QuadField d), hq]
    exact a.isIntegral_coe
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, algebraMap ℤ ℚ n = q :=
    IsIntegrallyClosed.algebraMap_eq_of_integral h_int
  exact ⟨n, by simp [← hq]⟩

namespace Parameters

variable {P : Parameters} {s : ℕ}

open scoped Classical in
/-- An element `y` of `E` lies in the lattice `𝔞₀`, that is `finiteImage id y ∈ Ô E`, if and only if
`relDifferentGen * y` is integral at the finite places dividing `betaKInE = (1 + √-d) / 2` and `y`
is integral at the other finite places. Here `relDifferentGen` generates the different of `E/K`. -/
lemma finiteImage_mem_iff {y : P.E s} :
    finiteImage id y ∈ Ô (P.E s) ↔
      ∀ w : FinPlace (P.E s), w.valuation (P.E s)
        ((if P.betaKInE s ∈ w.asIdeal then (P.relDifferentGen s : P.E s) else 1) * y) ≤ 1 := by
  refine mem_Ô.trans (forall_congr' fun w ↦ ?_)
  by_cases hw : P.betaKInE s ∈ w.asIdeal <;> simp [finiteImage, WeilData.α, α, hw]

/-- `Φ τ (betaKInE s) = quadGen P.d` for every infinite place `τ` of `E`. -/
private lemma phi_betaKInE (τ : P.Φ s) : Φ τ (P.betaKInE s : P.E s) = quadGen P.d := by
  rw [show (P.betaKInE s : P.E s) = algebraMap P.K (P.E s) (QuadField.betaK P.d) from rfl,
    P.phi_algebraMap s τ]
  rfl

/-- Let `ζ` be a primitive `N`-th root of unity in a characteristic-zero domain `R`, and let `ℓ`
be a prime factor of `N = ℓ * r`. Writing `r = ℓ ^ a * M` with `ℓ ∤ M`, we have `M ≤ N`, the prime
factors of `N` dividing `M` are precisely those different from `ℓ`, and there exists `V ∈ R` with
`V ∣ M` and `Φ_N'(ζ) * (ζ ^ r - 1) * M = N * V`. -/
lemma exists_cyclotomic_different_factor {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {N : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ N) (ℓ : N.primeFactors) :
    ∃ r M : ℕ, M ≤ N ∧ N = ℓ.val * r ∧ (∀ p ∈ N.primeFactors, p ∣ M ↔ p ≠ ℓ.val) ∧
      ∃ V : R, V ∣ (M : R) ∧
        (cyclotomic N R).derivative.eval ζ * (ζ ^ r - 1) * M = N * V := by
  rcases ℓ with ⟨l, hl⟩
  obtain ⟨hl_prime, ⟨r, hN_eq⟩, hN_ne⟩ := Nat.mem_primeFactors.1 hl
  have hN_pos : 0 < N := Nat.pos_of_ne_zero hN_ne
  have hr_pos : 0 < r := Nat.pos_of_ne_zero fun hr0 ↦ hN_ne (by simp [hN_eq, hr0])
  have hr_lt : r < N := by
    rw [hN_eq]
    exact lt_mul_of_one_lt_left hr_pos hl_prime.one_lt
  obtain ⟨q, hq⟩ : (X ^ r - 1) * cyclotomic N R ∣ X ^ N - 1 :=
    X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd R
      (Nat.mem_properDivisors.2 ⟨⟨l, by rw [hN_eq, mul_comm]⟩, hr_lt⟩)
  obtain ⟨a, M, hl_ndvd_M, hr_eq⟩ := r.exists_eq_pow_mul_and_not_dvd hr_pos.ne' l hl_prime.ne_one
  have hM_le : M ≤ N := by
    calc M ≤ l ^ a * M := Nat.le_mul_of_pos_left M (pow_pos hl_prime.pos a)
      _ = r := hr_eq.symm
      _ ≤ N := hr_lt.le
  have hM_primes : ∀ p ∈ N.primeFactors, p ∣ M ↔ p ≠ l := by
    intro p hp
    obtain ⟨hp_prime, hp_dvd, -⟩ := Nat.mem_primeFactors.1 hp
    constructor
    · rintro hpM rfl
      exact hl_ndvd_M hpM
    · intro hp_ne
      have hp_r : p ∣ r := by
        rw [hN_eq] at hp_dvd
        exact (hp_prime.dvd_mul.1 hp_dvd).resolve_left
          fun h ↦ hp_ne ((Nat.prime_dvd_prime_iff_eq hp_prime hl_prime).1 h)
      rw [hr_eq] at hp_r
      exact (hp_prime.dvd_mul.1 hp_r).resolve_left fun h ↦
        hp_ne ((Nat.prime_dvd_prime_iff_eq hp_prime hl_prime).1 (hp_prime.dvd_of_dvd_pow h))
  -- Differentiate `X ^ N - 1 = (X ^ r - 1) * Φ_N(X) * q(X)` at `ζ` and multiply by `ζ`.
  have h_root : (cyclotomic N R).eval ζ = 0 := hζ.isRoot_cyclotomic hN_pos
  have h_deriv_N :
      (N : R) = (ζ ^ r - 1) * (cyclotomic N R).derivative.eval ζ * (q.eval ζ * ζ) := by
    have h_eq := congrArg (fun f : R[X] ↦ f.derivative.eval ζ * ζ) hq
    simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, eval_mul, eval_sub,
      eval_one, eval_C, eval_pow, eval_X, derivative_mul, eval_add, h_root, zero_mul, mul_zero,
      add_zero, zero_add] at h_eq
    have h_pow : ζ ^ (N - 1) * ζ = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hN_pos, hζ.pow_eq_one]
    calc (N : R) = (N : R) * (ζ ^ (N - 1) * ζ) := by rw [h_pow, mul_one]
      _ = (N : R) * ζ ^ (N - 1) * ζ := by ring
      _ = (ζ ^ r - 1) * (cyclotomic N R).derivative.eval ζ * (q.eval ζ * ζ) := by
          rw [h_eq]; ring
  -- Expand `Φ_M(X ^ l) = Φ_{M l}(X) * Φ_M(X)` by `l ^ a` and differentiate at `ζ`.
  have hN_fac : M * l * l ^ a = N := by rw [hN_eq, hr_eq]; ring
  have h_exp_eq : expand R (l ^ a * l) (cyclotomic M R) =
      cyclotomic N R * expand R (l ^ a) (cyclotomic M R) := by
    have h_step :=
      congrArg (expand R (l ^ a)) (cyclotomic_expand_eq_cyclotomic_mul hl_prime hl_ndvd_M R)
    rw [expand_mul, h_step, map_mul, expand_pow_cyclotomic hl_prime (dvd_mul_left l M), hN_fac]
  have h_deriv_exp :
      (N : R) * ((cyclotomic M R).derivative.eval (ζ ^ (l ^ a * l)) * ζ ^ (l ^ a * l - 1)) =
        (M : R) * ((cyclotomic N R).derivative.eval ζ *
          (expand R (l ^ a) (cyclotomic M R)).eval ζ) := by
    have h_eq := congrArg (fun f : R[X] ↦ f.derivative.eval ζ) h_exp_eq
    simp only [derivative_expand, derivative_mul, eval_mul, eval_add, eval_natCast, eval_pow,
      eval_X, expand_eval, h_root, zero_mul, add_zero] at h_eq
    have h_mul := congrArg (fun x : R ↦ (M : R) * x) h_eq
    have hN_cast : (M : R) * ((l ^ a * l : ℕ) : R) = (N : R) := by
      exact_mod_cast (show M * (l ^ a * l) = N by rw [hN_eq, hr_eq]; ring)
    calc (N : R) * ((cyclotomic M R).derivative.eval (ζ ^ (l ^ a * l)) * ζ ^ (l ^ a * l - 1))
        = (M : R) * ((cyclotomic M R).derivative.eval (ζ ^ (l ^ a * l)) *
            (((l ^ a * l : ℕ) : R) * ζ ^ (l ^ a * l - 1))) := by
          rw [← hN_cast]; ring
      _ = (M : R) * ((cyclotomic N R).derivative.eval ζ *
            (expand R (l ^ a) (cyclotomic M R)).eval ζ) := by simpa [expand_eval] using h_mul
  have h_dvd_exp : (expand R (l ^ a) (cyclotomic M R)).eval ζ ∣ ζ ^ r - 1 := by
    obtain ⟨p, hp⟩ := cyclotomic.dvd_X_pow_sub_one M R
    refine ⟨p.eval (ζ ^ l ^ a), ?_⟩
    have h1 := congrArg (Polynomial.eval (ζ ^ l ^ a)) hp
    simpa [expand_eval, ← pow_mul, ← hr_eq] using h1
  have h_dvd_N : (N : R) ∣ (cyclotomic N R).derivative.eval ζ * (ζ ^ r - 1) * M := by
    have h1 : (N : R) ∣ (M : R) * ((cyclotomic N R).derivative.eval ζ *
        (expand R (l ^ a) (cyclotomic M R)).eval ζ) :=
      ⟨_, h_deriv_exp.symm⟩
    have h2 : (N : R) ∣ (M : R) * ((cyclotomic N R).derivative.eval ζ * (ζ ^ r - 1)) :=
      h1.trans (mul_dvd_mul_left (M : R) (mul_dvd_mul_left _ h_dvd_exp))
    simpa [mul_assoc, mul_left_comm, mul_comm] using h2
  obtain ⟨V, hV_eq⟩ := h_dvd_N
  have hV_dvd_M : V ∣ (M : R) := by
    refine ⟨q.eval ζ * ζ, ?_⟩
    have h_mul : (N : R) * (V * (q.eval ζ * ζ)) = (N : R) * (M : R) := by
      calc (N : R) * (V * (q.eval ζ * ζ))
          = (N : R) * V * (q.eval ζ * ζ) := by ring
        _ = (cyclotomic N R).derivative.eval ζ * (ζ ^ r - 1) * M * (q.eval ζ * ζ) := by
            rw [← hV_eq]
        _ = ((ζ ^ r - 1) * (cyclotomic N R).derivative.eval ζ * (q.eval ζ * ζ)) * (M : R) := by
            ring
        _ = (N : R) * (M : R) := by rw [← h_deriv_N]
    exact (mul_left_cancel₀ (Nat.cast_ne_zero.2 hN_ne) h_mul).symm
  exact ⟨r, M, hM_le, hN_eq, hM_primes, V, hV_dvd_M, hV_eq⟩

/-- Every prime factor of `q₁ = P.q₁ s` divides `n = (d + 1) / 4`, so `q₁ ∣ n ^ q₁`. -/
private lemma q₁_dvd_pow_q₁ : P.q₁ s ∣ ((P.d + 1) / 4) ^ P.q₁ s := by
  refine (Nat.dvd_iff_prime_pow_dvd_dvd _ _).2 fun p k hp h_dvd ↦ ?_
  obtain rfl | hk_pos := k.eq_zero_or_pos
  · exact one_dvd _
  have hk_le : k ≤ P.q₁ s :=
    (Nat.lt_pow_self hp.one_lt).le.trans (Nat.le_of_dvd (NeZero.pos _) h_dvd)
  exact pow_dvd_pow_of_dvd_of_le
    (P.dvd_d_add_one_div_four_of_dvd_q₁ hp ((dvd_pow_self p hk_pos.ne').trans h_dvd)) hk_le

/-- Since `n = (d + 1) / 4` is nilpotent modulo `q₁`, the quadratic polynomial `n y² + y + 1` has
a root `z < q₁` modulo `q₁`. -/
private lemma exists_quad_congr_mod_q₁ :
    ∃ z < P.q₁ s, ∃ e : ℕ, ((P.d + 1) / 4) * z ^ 2 + z + 1 = P.q₁ s * e := by
  set N : ℕ := P.q₁ s
  set n : ℕ := (P.d + 1) / 4
  -- The map `y ↦ n * y ^ 2 + y` on `ZMod N` is injective because `1 + n * (a + b)` is a unit.
  have h_inj : Function.Injective fun y : ZMod N ↦ (n : ZMod N) * y ^ 2 + y := by
    intro a b hab
    have h_nilp : IsNilpotent ((n : ZMod N) * (a + b)) :=
      ⟨N, by rw [mul_pow, ← Nat.cast_pow, (ZMod.natCast_eq_zero_iff _ N).2 q₁_dvd_pow_q₁, zero_mul]⟩
    have h_unit : IsUnit ((n : ZMod N) * (a + b) + 1) := h_nilp.isUnit_add_one
    have h_fac : ((n : ZMod N) * (a + b) + 1) * (a - b) = 0 := by linear_combination hab
    exact sub_eq_zero.1 (h_unit.mul_left_cancel (by simpa using h_fac))
  obtain ⟨y, hy⟩ := Finite.surjective_of_injective h_inj (-1 : ZMod N)
  have h_dvd : N ∣ n * y.val ^ 2 + y.val + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    linear_combination hy
  obtain ⟨e, he⟩ := h_dvd
  exact ⟨y.val, y.val_lt, e, he⟩

/-- Inner sum identity for the cyclotomic-orbit tight frame: for `α, β', W : ℂ` with
`∑ i : Fin l, α ^ i = 0` and `∑ i : Fin l, β' ^ i = 0` (`0 < l`), summing
`(0 ^ k * α ^ i + W * (α ^ i - α ^ k)) * (0 ^ k * β' ^ i + conj W * (β' ^ i - β' ^ k))`
over `k, i : Fin l` yields `(1 + W + conj W + 2 * l * (W * conj W)) * ∑ i : Fin l, (α * β') ^ i`. -/
private lemma sum_inner_frame {l : ℕ} (hl : 0 < l) {α β' W : ℂ}
    (hα : ∑ i : Fin l, α ^ i.val = 0) (hβ' : ∑ i : Fin l, β' ^ i.val = 0) :
    ∑ k : Fin l, ∑ i : Fin l,
      ((0 : ℂ) ^ k.val * α ^ i.val + W * (α ^ i.val - α ^ k.val)) *
        ((0 : ℂ) ^ k.val * β' ^ i.val + conj W * (β' ^ i.val - β' ^ k.val)) =
      (1 + W + conj W + 2 * (l : ℂ) * (W * conj W)) * ∑ i : Fin l, (α * β') ^ i.val := by
  have h_zeroPow (g : Fin l → ℂ) : ∑ k : Fin l, (0 : ℂ) ^ k.val * g k = g ⟨0, hl⟩ := by
    rw [Finset.sum_eq_single ⟨0, hl⟩]
    · simp
    · intro k _ hk; simp [zero_pow (fun h ↦ hk (Fin.ext h))]
    · simp
  -- Expand each summand into a `0 ^ k` term and a `W * conj W` term.
  have h_expand (k i : Fin l) :
      ((0 : ℂ) ^ k.val * α ^ i.val + W * (α ^ i.val - α ^ k.val)) *
        ((0 : ℂ) ^ k.val * β' ^ i.val + conj W * (β' ^ i.val - β' ^ k.val)) =
      (0 : ℂ) ^ k.val * ((0 : ℂ) ^ k.val * (α * β') ^ i.val +
        conj W * ((α * β') ^ i.val - α ^ i.val * β' ^ k.val) +
        W * ((α * β') ^ i.val - α ^ k.val * β' ^ i.val)) +
      W * conj W * ((α * β') ^ i.1 - α ^ i.1 * β' ^ k.1 - α ^ k.1 * β' ^ i.1 + (α * β') ^ k.1) := by
    rw [mul_pow, mul_pow]; ring
  simp_rw [h_expand, Finset.sum_add_distrib, ← Finset.mul_sum, h_zeroPow]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    pow_zero, one_mul, mul_one, hα, hβ', mul_zero, zero_mul, sub_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  simp_rw [Finset.sum_sub_distrib, hα, hβ', sub_zero]
  ring

/-- `periodFactor * conj (Φ τ y)` has absolute value 1 at the embedding `ιₚ : ℂ →+* ℂ_[p]` (the
instance `PadicPlace p`) for all `τ` in the CM type. These numbers are the coefficients of the
linear form `z ↦ periodFactor * ∑ τ, conj (Φ τ y) * Φ τ z`. -/
def HasUnitLinearForm (P : Parameters) (s p : ℕ) [Fact p.Prime] [PadicPlace p] (y : P.E s) :
    Prop :=
  ∀ τ : InfinitePlace (P.E s), ‖(ιₚ (P.periodFactor s * conj (Φ τ y)) : ℂ_[p])‖ = 1

/-- There is a tight frame `v` in `𝔞₀` with multiplicities `1` of length `h ≤ (d q₁) ^ 6` prime to
`q₁`, such that for every prime `p` and embedding `ιₚ : ℂ →+* ℂ_[p]`, either `1` or some member
`v i` has `HasUnitLinearForm`. -/
theorem exists_isTightFrame_coprime (P : Parameters) (s : ℕ) :
    ∃ (h : ℕ) (I : Type) (_ : Fintype I) (v : I → P.E s),
      IsTightFrame v 1 h ∧
      h ≤ (P.d * P.q₁ s) ^ 6 ∧
      h.Coprime (P.q₁ s) ∧
      ∀ (p : ℕ) [Fact p.Prime] [PadicPlace p],
        P.HasUnitLinearForm s p 1 ∨ ∃ i : I, P.HasUnitLinearForm s p (v i) := by
  classical
  set N : ℕ := P.q₁ s
  set n : ℕ := (P.d + 1) / 4
  have hN_ne : N ≠ 0 := NeZero.ne N
  have hN_pos : 0 < N := NeZero.pos N
  have hζ : IsPrimitiveRoot (P.zetaInt s) N := isPrimitiveRoot_zetaInt
  have hβ_mul : P.betaKInE s * (1 - P.betaKInE s) = (n : 𝓞 (P.E s)) := P.betaKInE_mul_one_sub s
  -- Factor `Φ_N'(ζ)` at each prime `ℓ ∣ N`, and solve `n z² + z + 1 = N e`.
  choose r M hM_le hN_eq hM_primes V hV_dvd hV_eq using
    fun ℓ : N.primeFactors ↦ exists_cyclotomic_different_factor hζ ℓ
  obtain ⟨z, hz_lt, e, he_eq⟩ := exists_quad_congr_mod_q₁ (P := P) (s := s)
  obtain ⟨f, hf_eq⟩ : N ∣ n ^ N := q₁_dvd_pow_q₁
  let t : 𝓞 (P.E s) := 1 - P.betaKInE s + (n : 𝓞 (P.E s)) * (z : 𝓞 (P.E s))
  let a (ℓ : N.primeFactors) : 𝓞 (P.E s) := P.zetaInt s ^ r ℓ
  -- The frame vectors indexed by `(ℓ, j, k, i) ∈ Σ ℓ : N.primeFactors, Fin (r ℓ) × Fin ℓ × Fin ℓ`.
  let I : Type := Σ ℓ : N.primeFactors, Fin (r ℓ) × Fin ℓ.val × Fin ℓ.val
  let u : I → P.E s := fun ⟨ℓ, j, k, i⟩ ↦
    (P.zetaInt s : P.E s) ^ j.val *
      ((0 : P.E s) ^ k.val * (a ℓ : P.E s) ^ i.val +
        ((t : P.E s) * (M ℓ : P.E s) / (N : P.E s)) *
          ((a ℓ : P.E s) ^ i.val - (a ℓ : P.E s) ^ k.val))
  let c : ℕ := ∑ ℓ : N.primeFactors, (N + M ℓ * (1 + 2 * n * (z + ℓ.val * (M ℓ * e))))
  -- Step 1: Every `u x` lies in the lattice `𝔞₀ = E ∩ α Ô`.
  have hu_mem (x : I) : finiteImage id (u x) ∈ Ô (P.E s) := by
    rcases x with ⟨ℓ, j, k, i⟩
    refine finiteImage_mem_iff.2 fun v ↦ ?_
    obtain ⟨g, hg⟩ : a ℓ - 1 ∣ a ℓ ^ i.val - a ℓ ^ k.val := by
      simpa using dvd_sub (sub_one_dvd_pow_sub_one (a ℓ) i.1) (sub_one_dvd_pow_sub_one (a ℓ) k.1)
    have h_int_of_dvd (y : 𝓞 (P.E s)) (hdvd : (N : 𝓞 (P.E s)) ∣ y * t * (M ℓ * (a ℓ - 1))) :
        v.valuation (P.E s) ((y : P.E s) * u ⟨ℓ, j, k, i⟩) ≤ 1 := by
      obtain ⟨q, hq⟩ := hdvd
      have h_eq : (y : P.E s) * u ⟨ℓ, j, k, i⟩ =
          ((P.zetaInt s ^ j.val * (y * (0 : 𝓞 (P.E s)) ^ k.val * a ℓ ^ i.val + q * g) : 𝓞 (P.E s)) :
            P.E s) := by
        have hN_E : (N : P.E s) ≠ 0 := Nat.cast_ne_zero.2 hN_ne
        have hg_E : (a ℓ : P.E s) ^ i.1 - (a ℓ : P.E s) ^ k.1 =
            ((a ℓ : P.E s) - 1) * (g : P.E s) := by
          exact_mod_cast hg
        have hq_E : (y : P.E s) * (t : P.E s) * ((M ℓ : P.E s) * ((a ℓ : P.E s) - 1)) =
            (N : P.E s) * (q : P.E s) := by
          exact_mod_cast hq
        simp only [u]
        rw [hg_E]
        field_simp [hN_E]
        push_cast
        linear_combination (P.zetaInt s : P.E s) ^ j.val * (g : P.E s) * hq_E
      rw [h_eq]
      exact v.valuation_le_one _
    by_cases hv : P.betaKInE s ∈ v.asIdeal
    · rw [ite_eq_left hv]
      refine h_int_of_dvd (P.relDifferentGen s) ⟨t * V ℓ, ?_⟩
      have hV_mul : P.relDifferentGen s * (a ℓ - 1) * M ℓ = N * V ℓ := hV_eq ℓ
      linear_combination t * hV_mul
    · rw [ite_eq_right hv, one_mul]
      have h_unit : v.valuation (P.E s) (P.betaKInE s : P.E s) = 1 :=
        v.valuation_eq_one_iff_notMem.2 hv
      have h_beta_dvd : (N : 𝓞 (P.E s)) ∣ P.betaKInE s ^ N * t := by
        obtain ⟨w, hw⟩ :=
          sub_dvd_pow_sub_pow (P.betaKInE s) (-(n : 𝓞 (P.E s)) * (z : 𝓞 (P.E s))) N
        have h_prod : (P.betaKInE s - (-(n : 𝓞 (P.E s)) * (z : 𝓞 (P.E s)))) * t =
            (n : 𝓞 (P.E s)) * ((N : 𝓞 (P.E s)) * (e : 𝓞 (P.E s))) := by
          have he_O : (n : 𝓞 (P.E s)) * (z : 𝓞 (P.E s)) ^ 2 + (z : 𝓞 (P.E s)) + 1 =
              (N : 𝓞 (P.E s)) * (e : 𝓞 (P.E s)) := by exact_mod_cast he_eq
          linear_combination hβ_mul + (n : 𝓞 (P.E s)) * he_O
        have hf_O : (n : 𝓞 (P.E s)) ^ N = (N : 𝓞 (P.E s)) * (f : 𝓞 (P.E s)) := by
          exact_mod_cast hf_eq
        refine ⟨(n : 𝓞 (P.E s)) * (e : 𝓞 (P.E s)) * w +
          (f : 𝓞 (P.E s)) * (-(z : 𝓞 (P.E s))) ^ N * t, ?_⟩
        have h_pow_neg : (-(n : 𝓞 (P.E s)) * (z : 𝓞 (P.E s))) ^ N =
            (n : 𝓞 (P.E s)) ^ N * (-(z : 𝓞 (P.E s))) ^ N := by
          rw [show -(n : 𝓞 (P.E s)) * (z : 𝓞 (P.E s)) =
            (n : 𝓞 (P.E s)) * (-(z : 𝓞 (P.E s))) by ring, mul_pow]
        linear_combination t * hw + w * h_prod + (-(z : 𝓞 (P.E s))) ^ N * t * hf_O +
          t * h_pow_neg
      have h_le := h_int_of_dvd (P.betaKInE s ^ N) (dvd_mul_of_dvd_left h_beta_dvd _)
      simpa [map_mul, h_unit] using h_le
  -- Step 2: Compute the frame Gram matrix `∑ x, Φ σ (u x) * conj (Φ τ (u x)) = δ(σ, τ) * c`.
  have h_frame_sum (σ τ : P.Φ s) :
      ∑ x : I, Φ σ (u x) * conj (Φ τ (u x)) = if σ = τ then (c : ℂ) else 0 := by
    have h_zeta_frame :
        ∑ m : Fin N, Φ σ ((P.zetaInt s : P.E s) ^ m.val) *
          conj (Φ τ ((P.zetaInt s : P.E s) ^ m.val)) = if σ = τ then (N : ℂ) else 0 := by
      have h1 := (P.isTightFrame_zeta_pow s 1).sum_mul_conj σ τ
      have hN_C : ((P.q₀ : ℂ) * (towerDeg s : ℂ)) = (N : ℂ) := by exact_mod_cast rfl
      simpa [hN_C] using h1
    have h_phi_t (ρ : P.Φ s) : Φ ρ (t : P.E s) = 1 - quadGen P.d + (n : ℂ) * (z : ℂ) := by
      simp [t, phi_betaKInE]
    have hβ_sum : quadGen P.d + conj (quadGen P.d) = 1 := by
      have := congrArg (fun x : 𝓞 (P.E s) ↦ Φ σ (x : P.E s)) (P.star_betaKInE s)
      simp only [coe_star_ringOfIntegers, map_star_complex, Complex.star_def, map_sub, map_one,
        phi_betaKInE] at this
      linear_combination this
    have h_t_add : (1 - quadGen P.d + (n : ℂ) * (z : ℂ)) +
        conj (1 - quadGen P.d + (n : ℂ) * (z : ℂ)) = 1 + 2 * (n : ℂ) * (z : ℂ) := by
      simp only [map_add, map_sub, map_one, map_mul, map_natCast]
      linear_combination -hβ_sum
    have h_t_mul : (1 - quadGen P.d + (n : ℂ) * (z : ℂ)) *
        conj (1 - quadGen P.d + (n : ℂ) * (z : ℂ)) = (n : ℂ) * ((N : ℂ) * (e : ℂ)) := by
      have hβ_prod : quadGen P.d * (1 - quadGen P.d) = (n : ℂ) := by
        have := congrArg (fun x : 𝓞 (P.E s) ↦ Φ σ (x : P.E s)) hβ_mul
        simpa [phi_betaKInE] using this
      have he_C : (n : ℂ) * (z : ℂ) ^ 2 + (z : ℂ) + 1 = (N : ℂ) * (e : ℂ) := by
        exact_mod_cast he_eq
      simp only [map_add, map_sub, map_one, map_mul, map_natCast]
      linear_combination (1 - quadGen P.d + (n : ℂ) * (z : ℂ)) * (-hβ_sum) + hβ_prod +
        (n : ℂ) * he_C
    -- Compute the contribution of each prime factor `ℓ ∣ N`.
    have h_block (ℓ : N.primeFactors) :
        ∑ p : Fin (r ℓ) × Fin ℓ.val × Fin ℓ.val,
          Φ σ (u ⟨ℓ, p⟩) * conj (Φ τ (u ⟨ℓ, p⟩)) =
            if σ = τ then ((N + M ℓ * (1 + 2 * n * (z + ℓ.val * (M ℓ * e))) : ℕ) : ℂ) else 0 := by
      have hℓ_prime : ℓ.val.Prime := Nat.prime_of_mem_primeFactors ℓ.property
      have hN_comm : N = r ℓ * ℓ.val := (hN_eq ℓ).trans (mul_comm _ _)
      have h_prim_a : IsPrimitiveRoot (a ℓ) ℓ.val := hζ.pow hN_pos hN_comm
      have h_sum_a : ∑ i : Fin ℓ.val, (a ℓ : P.E s) ^ i.val = 0 := by
        have h0 : ∑ i ∈ range ℓ.val, (a ℓ) ^ i = 0 := h_prim_a.geom_sum_eq_zero hℓ_prime.one_lt
        rw [← Fin.sum_univ_eq_sum_range] at h0
        exact_mod_cast h0
      let α : ℂ := Φ σ (a ℓ : P.E s)
      let β' : ℂ := conj (Φ τ (a ℓ : P.E s))
      have h_sum_ασ : ∑ i : Fin ℓ.val, α ^ i.val = 0 := by
        simpa [α, map_sum, map_pow] using congrArg (Φ σ) h_sum_a
      have h_sum_ατ : ∑ i : Fin ℓ.val, β' ^ i.val = 0 := by
        simpa [β', map_sum, map_pow] using congrArg (conj ∘ Φ τ) h_sum_a
      let γ : ℂ := Φ σ (P.zetaInt s : P.E s) * conj (Φ τ (P.zetaInt s : P.E s))
      have h_prod_sum :
          (∑ j : Fin (r ℓ), γ ^ j.val) * (∑ i : Fin ℓ.val, (γ ^ r ℓ) ^ i.val) =
            if σ = τ then (N : ℂ) else 0 := by
        have h_bij :
            ∑ m : Fin N, γ ^ m.val =
              (∑ j : Fin (r ℓ), γ ^ j.val) * (∑ i : Fin ℓ.val, (γ ^ r ℓ) ^ i.val) := by
          let eN : Fin ℓ.val × Fin (r ℓ) ≃ Fin N :=
            finProdFinEquiv.trans (finCongr (hN_eq ℓ).symm)
          rw [← eN.sum_comp, Fintype.sum_prod_type, Finset.sum_mul, Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hval : (eN (i, j)).val = r ℓ * i.val + j.val := by
            simp [eN, finProdFinEquiv, add_comm, mul_comm]
          rw [hval, pow_add, pow_mul, mul_comm]
        rw [← h_bij]
        simpa [γ, mul_pow, map_pow] using h_zeta_frame
      set W : ℂ := (1 - quadGen P.d + (n : ℂ) * (z : ℂ)) * (M ℓ : ℂ) / (N : ℂ)
      have h_αβ : α * β' = γ ^ r ℓ := by simp [α, β', γ, a, mul_pow, map_pow]
      have h_inner :
          ∑ k : Fin ℓ.val, ∑ i : Fin ℓ.val,
            ((0 : ℂ) ^ k.val * α ^ i.val + W * (α ^ i.val - α ^ k.val)) *
              ((0 : ℂ) ^ k.val * β' ^ i.val + conj W * (β' ^ i.val - β' ^ k.val)) =
            (1 + W + conj W + 2 * (ℓ.val : ℂ) * (W * conj W)) *
              ∑ i : Fin ℓ.val, (γ ^ r ℓ) ^ i.val := by
        simpa [h_αβ] using sum_inner_frame hℓ_prime.pos h_sum_ασ h_sum_ατ
      have h_factor_val :
          (1 + W + conj W + 2 * (ℓ.val : ℂ) * (W * conj W)) * (N : ℂ) =
            ((N + M ℓ * (1 + 2 * n * (z + ℓ.val * (M ℓ * e))) : ℕ) : ℂ) := by
        have hN_C : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN_ne
        have hW_conj : conj W =
            conj (1 - quadGen P.d + (n : ℂ) * (z : ℂ)) * (M ℓ : ℂ) / (N : ℂ) := by simp [W]
        rw [hW_conj]
        simp only [W]
        field_simp [hN_C]
        push_cast
        linear_combination (M ℓ : ℂ) * (N : ℂ) * h_t_add +
          2 * (ℓ.val : ℂ) * (M ℓ : ℂ) ^ 2 * h_t_mul
      have h_u_apply (j : Fin (r ℓ)) (k i : Fin ℓ.val) :
          Φ σ (u ⟨ℓ, j, k, i⟩) * conj (Φ τ (u ⟨ℓ, j, k, i⟩)) =
            γ ^ j.val *
              (((0 : ℂ) ^ k.val * α ^ i.val + W * (α ^ i.val - α ^ k.val)) *
                ((0 : ℂ) ^ k.val * β' ^ i.val + conj W * (β' ^ i.val - β' ^ k.val))) := by
        simp only [u, map_mul, map_add, map_sub, map_div₀, map_pow, map_zero, map_natCast,
          h_phi_t, W, α, β', γ, mul_pow]
        ring
      calc ∑ p : Fin (r ℓ) × Fin ℓ.val × Fin ℓ.val, Φ σ (u ⟨ℓ, p⟩) * conj (Φ τ (u ⟨ℓ, p⟩))
          = ∑ j : Fin (r ℓ), ∑ k : Fin ℓ.val, ∑ i : Fin ℓ.val,
              Φ σ (u ⟨ℓ, j, k, i⟩) * conj (Φ τ (u ⟨ℓ, j, k, i⟩)) := by
            simp [Fintype.sum_prod_type]
        _ = (∑ j : Fin (r ℓ), γ ^ j.val) *
              ((1 + W + conj W + 2 * (ℓ.val : ℂ) * (W * conj W)) *
                ∑ i : Fin ℓ.val, (γ ^ r ℓ) ^ i.val) := by
            simp_rw [h_u_apply, ← Finset.mul_sum, h_inner, ← Finset.sum_mul]
        _ = (1 + W + conj W + 2 * (ℓ.val : ℂ) * (W * conj W)) *
              ((∑ j : Fin (r ℓ), γ ^ j.val) * (∑ i : Fin ℓ.val, (γ ^ r ℓ) ^ i.val)) := by ring
        _ = if σ = τ then ((N + M ℓ * (1 + 2 * n * (z + ℓ.val * (M ℓ * e))) : ℕ) : ℂ) else 0 := by
            rw [h_prod_sum]
            split_ifs
            · exact h_factor_val
            · ring
    rw [Fintype.sum_sigma]
    simp_rw [h_block]
    split_ifs <;> simp [c]
  -- Step 3: `c` is coprime to `N`.
  have hc_coprime : c.Coprime N := by
    refine Nat.coprime_of_dvd fun p hp hpc hpN ↦ ?_
    have hp_mem : p ∈ N.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpN, hN_ne⟩
    have hp_n : p ∣ n := P.dvd_d_add_one_div_four_of_dvd_q₁ hp hpN
    have h_zero : (c : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff c p).2 hpc
    have h_eval : (c : ZMod p) = (M ⟨p, hp_mem⟩ : ZMod p) := by
      simp only [c, Nat.cast_sum]
      rw [Finset.sum_eq_single ⟨p, hp_mem⟩]
      · have hN0 : (N : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff N p).2 hpN
        have hn0 : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).2 hp_n
        simp [hN0, hn0]
      · intro ℓ _ hℓ_ne
        have hN0 : (N : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff N p).2 hpN
        have hM0 : (M ℓ : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff (M ℓ) p).2
            ((hM_primes ℓ p hp_mem).2 fun h ↦ hℓ_ne (Subtype.ext h.symm))
        simp [hN0, hM0]
      · simp
    have hp_M : p ∣ M ⟨p, hp_mem⟩ := (ZMod.natCast_eq_zero_iff _ p).1 (h_eval.symm.trans h_zero)
    exact (hM_primes ⟨p, hp_mem⟩ p hp_mem).1 hp_M rfl
  -- Step 4: Elementary polynomial bound `c ≤ (d * N) ^ 6`.
  have hc_le : c ≤ (P.d * N) ^ 6 := by
    have hd_ge : 7 ≤ P.d := by
      have hmod : P.d % 8 = 7 := PrimeSevenModEight.mod_eight
      omega
    have hn_le : n ≤ P.d := by omega
    have h_card : Fintype.card N.primeFactors ≤ N := by
      rw [Fintype.card_coe]
      calc N.primeFactors.card ≤ (Finset.Icc 1 N).card :=
            Finset.card_le_card fun p hp ↦
              Finset.mem_Icc.2 ⟨(Nat.prime_of_mem_primeFactors hp).pos,
                Nat.le_of_mem_primeFactors hp⟩
        _ = N := by simp
    have h_e_le : e ≤ n * N + 2 := by
      have h1 : N * e ≤ n * N ^ 2 + N + 1 := by
        have he' : n * z ^ 2 + z + 1 = N * e := he_eq
        have hz_le : z ≤ N := hz_lt.le
        have hmul : n * z ^ 2 ≤ n * N ^ 2 := Nat.mul_le_mul_left n (Nat.pow_le_pow_left hz_le 2)
        omega
      have h2 : N * e ≤ N * (n * N + 2) := by
        calc N * e ≤ n * N ^ 2 + N + 1 := h1
          _ ≤ n * N ^ 2 + N + N := by omega
          _ = N * (n * N + 2) := by ring
      exact Nat.le_of_mul_le_mul_left h2 hN_pos
    have h_term_le (ℓ : N.primeFactors) :
        N + M ℓ * (1 + 2 * n * (z + ℓ.val * (M ℓ * e))) ≤ P.d ^ 6 * N ^ 5 := by
      have hℓ_le : ℓ.val ≤ N := Nat.le_of_mem_primeFactors ℓ.property
      have hM : M ℓ ≤ N := hM_le ℓ
      have hz_le : z ≤ N := hz_lt.le
      have h_inner1 : M ℓ * e ≤ (P.d + 2) * N ^ 2 := by
        calc M ℓ * e ≤ N * (n * N + 2) := Nat.mul_le_mul hM h_e_le
          _ ≤ N * (P.d * N + 2 * N) := by gcongr; omega
          _ = (P.d + 2) * N ^ 2 := by ring
      have h_inner2 : z + ℓ.val * (M ℓ * e) ≤ (P.d + 3) * N ^ 4 := by
        calc z + ℓ.val * (M ℓ * e)
            ≤ N + N * ((P.d + 2) * N ^ 2) :=
              Nat.add_le_add hz_le (Nat.mul_le_mul hℓ_le h_inner1)
          _ ≤ N ^ 4 + (P.d + 2) * N ^ 4 := by
              have hN4 : N ≤ N ^ 4 := Nat.le_self_pow (by norm_num) N
              have hN34 : N ^ 3 ≤ N ^ 4 := Nat.pow_le_pow_right hN_pos (by norm_num)
              have h_mul : N * ((P.d + 2) * N ^ 2) = (P.d + 2) * N ^ 3 := by ring
              rw [h_mul]
              exact Nat.add_le_add hN4 (Nat.mul_le_mul_left _ hN34)
          _ = (P.d + 3) * N ^ 4 := by ring
      have h_inner3 : 1 + 2 * n * (z + ℓ.val * (M ℓ * e)) ≤ (2 * P.d * (P.d + 3) + 1) * N ^ 4 := by
        calc 1 + 2 * n * (z + ℓ.val * (M ℓ * e))
            ≤ N ^ 4 + 2 * P.d * ((P.d + 3) * N ^ 4) :=
              Nat.add_le_add (one_le_pow₀ hN_pos)
                (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn_le) h_inner2)
          _ = (2 * P.d * (P.d + 3) + 1) * N ^ 4 := by ring
      have h_coeff : 1 + (2 * P.d * (P.d + 3) + 1) ≤ P.d ^ 6 := by
        have h2 : P.d ^ 2 * 7 ≤ P.d ^ 3 := by
          calc P.d ^ 2 * 7 ≤ P.d ^ 2 * P.d := Nat.mul_le_mul_left _ hd_ge
            _ = P.d ^ 3 := by ring
        have h3 : P.d ^ 3 ≤ P.d ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
        have h4 : 2 * P.d * (P.d + 3) + 2 ≤ P.d ^ 2 * 7 := by nlinarith
        omega
      calc N + M ℓ * (1 + 2 * n * (z + ℓ.val * (M ℓ * e)))
          ≤ N ^ 5 + N * ((2 * P.d * (P.d + 3) + 1) * N ^ 4) :=
            Nat.add_le_add (Nat.le_self_pow (by norm_num) N) (Nat.mul_le_mul hM h_inner3)
        _ = (1 + (2 * P.d * (P.d + 3) + 1)) * N ^ 5 := by ring
        _ ≤ P.d ^ 6 * N ^ 5 := Nat.mul_le_mul_right _ h_coeff
    calc c ≤ ∑ _ℓ : N.primeFactors, P.d ^ 6 * N ^ 5 := Finset.sum_le_sum fun ℓ _ ↦ h_term_le ℓ
      _ = Fintype.card N.primeFactors * (P.d ^ 6 * N ^ 5) := by simp
      _ ≤ N * (P.d ^ 6 * N ^ 5) := Nat.mul_le_mul_right _ h_card
      _ = (P.d * N) ^ 6 := by ring
  -- Step 5: Unit linear form for every prime `p` and embedding `ιₚ : ℂ →+* ℂ_[p]`.
  have h_unit (p : ℕ) [Fact p.Prime] [PadicPlace p] :
      P.HasUnitLinearForm s p 1 ∨ ∃ x : I, P.HasUnitLinearForm s p (u x) := by
    by_cases h1 : P.HasUnitLinearForm s p 1
    · exact .inl h1
    right
    have hp_dvd : p ∣ N := by
      by_contra hp_ndvd
      exact h1 fun τ ↦ by simp [P.norm_iota_periodFactor_eq_one s hp_ndvd]
    have hp_prime : p.Prime := Fact.out
    let ℓ : N.primeFactors := ⟨p, Nat.mem_primeFactors.2 ⟨hp_prime, hp_dvd, hN_ne⟩⟩
    have hr_pos : 0 < r ℓ := Nat.pos_of_ne_zero fun hr0 ↦ hN_ne (by simp [hN_eq ℓ, hr0])
    have h_emb (τ : P.Φ s) (y : P.E s) : weightEmbedding ιₚ τ y = ιₚ (conj (Φ τ y)) :=
      congrArg ιₚ (map_star_complex _ y)
    have hβ_mem (τ : P.Φ s) : P.betaKInE s ∈ (placeOfEmb (weightEmbedding ιₚ τ)).asIdeal := by
      have h_const : ∀ τ₁ τ₂ : P.Φ s,
          P.betaKInE s ∈ (placeOfEmb (weightEmbedding ιₚ τ₁)).asIdeal ↔
            P.betaKInE s ∈ (placeOfEmb (weightEmbedding ιₚ τ₂)).asIdeal := fun τ₁ τ₂ ↦ by
        simp [mem_placeOfEmb, h_emb, phi_betaKInE]
      by_contra h_not
      refine h1 fun τ' ↦ ?_
      have h_not' : P.betaKInE s ∉ (placeOfEmb (weightEmbedding ιₚ τ')).asIdeal :=
        mt (h_const τ' τ).1 h_not
      simp [norm_iota_periodFactor τ', adeleExtension_alpha, h_not']
    refine ⟨⟨ℓ, ⟨0, hr_pos⟩, ⟨1, hp_prime.one_lt⟩, ⟨0, hp_prime.pos⟩⟩, fun τ ↦ ?_⟩
    let φ : P.E s →+* ℂ_[p] := weightEmbedding ιₚ τ
    have h_factor : ‖ιₚ (P.periodFactor s)‖ = ‖φ (P.relDifferentGen s)‖ := by
      rw [norm_iota_periodFactor τ, adeleExtension_alpha, ite_eq_left (hβ_mem τ), norm_inv, inv_inv]
    have h_u_eq : (P.relDifferentGen s : P.E s) *
        u ⟨ℓ, ⟨0, hr_pos⟩, ⟨1, hp_prime.one_lt⟩, ⟨0, hp_prime.pos⟩⟩ =
        ((-t * V ℓ : 𝓞 (P.E s)) : P.E s) := by
      have hN_E : (N : P.E s) ≠ 0 := Nat.cast_ne_zero.2 hN_ne
      have hV_E : (P.relDifferentGen s : P.E s) * ((a ℓ : P.E s) - 1) * (M ℓ : P.E s) =
          (N : P.E s) * (V ℓ : P.E s) := by exact_mod_cast hV_eq ℓ
      simp only [u, pow_zero, pow_one, one_mul, zero_mul, zero_add]
      field_simp [hN_E]
      push_cast
      linear_combination -(t : P.E s) * hV_E
    rw [map_mul, norm_mul, ← h_emb, h_factor, ← norm_mul, ← map_mul, h_u_eq]
    refine (norm_ringOfIntegers_le φ (-t * V ℓ)).eq_of_not_lt fun h_lt ↦ ?_
    have h_mem : -t * V ℓ ∈ (placeOfEmb φ).asIdeal := (mem_placeOfEmb φ _).2 h_lt
    have h_t_notMem : t ∉ (placeOfEmb φ).asIdeal := by
      intro ht_mem
      have h1_mem : (1 : 𝓞 (P.E s)) ∈ (placeOfEmb φ).asIdeal := by
        have h_n_mem : (n : 𝓞 (P.E s)) ∈ (placeOfEmb φ).asIdeal := by
          rw [← hβ_mul]
          exact Ideal.mul_mem_right _ _ (hβ_mem τ)
        have h_eq : (1 : 𝓞 (P.E s)) = t + P.betaKInE s - (n : 𝓞 (P.E s)) * (z : 𝓞 (P.E s)) := by
          dsimp only [t]; ring
        rw [h_eq]
        exact sub_mem (add_mem ht_mem (hβ_mem τ)) (Ideal.mul_mem_right _ _ h_n_mem)
      exact (placeOfEmb φ).isPrime.one_notMem h1_mem
    have hV_mem : V ℓ ∈ (placeOfEmb φ).asIdeal := by
      rcases (placeOfEmb φ).isPrime.mem_or_mem h_mem with ht | hV
      · exact absurd (neg_mem_iff.1 ht) h_t_notMem
      · exact hV
    have hM_mem : (M ℓ : 𝓞 (P.E s)) ∈ (placeOfEmb φ).asIdeal :=
      Ideal.mem_of_dvd _ (hV_dvd ℓ) hV_mem
    have hp_M : p ∣ M ℓ :=
      (FinPlace.natCast_mem_iff_dvd (placeOfEmb φ) (natCast_mem_placeOfEmb φ)).1 hM_mem
    exact (hM_primes ℓ p ℓ.property).1 hp_M rfl
  refine ⟨c, I, inferInstance, u, ⟨hu_mem, ?_⟩, hc_le, hc_coprime, h_unit⟩
  simpa using h_frame_sum

/-- Let `v` be a tight frame with multiplicities 1 of a length `h` prime to `q₁`. For every
`m ≥ q₁ h + R (q₁ + h)`, the powers `ζ ^ i`, `i < q₁`, and the members of `v` form a tight frame of
length `m` with suitable multiplicities, all at least `R`. -/
lemma exists_isTightFrame_of_coprime {h : ℕ} {I : Type} [Fintype I] {v : I → P.E s}
    (hv : IsTightFrame v 1 h) (h_coprime : h.Coprime (P.q₁ s)) {m R : ℕ}
    (h_large : P.q₁ s * h + R * (P.q₁ s + h) ≤ m) :
    ∃ c : Fin (P.q₁ s) ⊕ I → ℕ,
      IsTightFrame (Sum.elim (fun i : Fin (P.q₁ s) ↦ P.ζ s ^ i.val) v) c m ∧
      ∀ j : Fin (P.q₁ s) ⊕ I, R ≤ c j := by
  -- Every integer from `q₁ h` on is a sum of multiples of the coprime numbers `q₁` and `h`.
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, a * P.q₁ s + b * h = m - R * (P.q₁ s + h) :=
    Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le (P.q₁ s) h _
      (by simp [h_coprime.symm.gcd_eq_one])
      ((Nat.mul_le_mul (Nat.pred_le _) (Nat.pred_le _)).trans (Nat.le_sub_of_add_le h_large))
  have h_sum : (a + R) * P.q₁ s + (b + R) * h = m := by lia
  -- Take the powers of `ζ` `a + R` times and the frame `v` `b + R` times.
  have h_pow : IsTightFrame (fun i : Fin (P.q₁ s) ↦ P.ζ s ^ i.val) (fun _ ↦ a + R)
      ((a + R) * P.q₁ s) := by
    simpa using (isTightFrame_pow isPrimitiveRoot_zeta).mul_left (a + R)
  have hv_mul : IsTightFrame v (fun _ ↦ b + R) ((b + R) * h) := by simpa using hv.mul_left (b + R)
  exact ⟨_, by simpa only [h_sum] using h_pow.sumElim hv_mul, by simp⟩

end Parameters

namespace Data

open Real

variable {P : Parameters} (D : Data P)

/-- Let `D` be data for the parameters `P` (a `Data P`), with field `E = D.E = P.E s` for the
exponent `s = D.towerExp`, weight `b = D.b`, and `f = D.f` the number of infinite places of `E`. The
principal level `M = D.M` is the product of the two distinct primes `D.levelPrime 0` and
`D.levelPrime 1` of the data, which lie in `[b ^ 10, b ^ 11]`. There is a tight frame `v` of length
`M` with multiplicities `c i ≥ 6 f b`. Moreover, for every prime `p` and embedding
`ιₚ : ℂ →+* ℂ_[p]`, some `y = v i` makes `periodFactor * conj (τ(y))` a unit at `ιₚ` for all `τ` in
the CM type. -/
theorem exists_isTightFrame :
    ∃ (I : Type) (_ : Fintype I) (v : I → D.E) (c : I → ℕ),
      IsTightFrame v c D.M ∧
      (∀ i : I, 6 * D.f * D.b ≤ c i) ∧
      ∀ (p : ℕ) [Fact p.Prime] [PadicPlace p], ∃ i : I, P.HasUnitLinearForm D.towerExp p (v i) := by
  obtain ⟨h, I, _, v, hv, h_le, h_coprime, h_unit⟩ := P.exists_isTightFrame_coprime D.towerExp
  -- Since `h ≤ (d q₁) ^ 6`, the threshold `q₁ h + ⌈6 f b⌉ (q₁ + h)` is at most `D.M`.
  have h_large : D.q₁ * h + ⌈6 * D.f * D.b⌉₊ * (D.q₁ + h) ≤ D.M := by
    have h_bound : (h : ℝ) ≤ D.b := by
      calc (h : ℝ) ≤ ((P.d * D.q₁) ^ 6 : ℕ) := Nat.cast_le.2 h_le
        _ ≤ D.b := D.le_of_hasLogBound
    have h_log : D.HasLogUpper h D.logB := ⟨by rwa [ite_eq_left rfl, Nat.abs_cast]⟩
    exact D.nat_le_of_hasLogBound
  let u : Fin D.q₁ ⊕ I → D.E := Sum.elim (fun i : Fin D.q₁ ↦ P.ζ D.towerExp ^ i.val) v
  obtain ⟨c, hu, hc⟩ : ∃ c : Fin D.q₁ ⊕ I → ℕ,
      IsTightFrame u c D.M ∧ ∀ j : Fin D.q₁ ⊕ I, ⌈6 * D.f * D.b⌉₊ ≤ c j :=
    Parameters.exists_isTightFrame_of_coprime hv h_coprime h_large
  refine ⟨Fin D.q₁ ⊕ I, inferInstance, u, c, hu, fun j ↦ Nat.ceil_le.1 (hc j), fun p _ _ ↦ ?_⟩
  rcases h_unit p with h1 | ⟨i, hi⟩
  · exact ⟨.inl ⟨0, NeZero.pos _⟩, by simpa [u] using h1⟩
  · exact ⟨.inr i, hi⟩

end Data

end New
