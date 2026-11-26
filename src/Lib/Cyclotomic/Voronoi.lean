module

public import TauCeti.LinearAlgebra.Matrix.GroupMatrix
public import TauCeti.NumberTheory.Bernoulli.Basic
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.TrivialZeros
public import TauCeti.NumberTheory.MulChar.Orthogonality
import TauCeti.NumberTheory.ZetaValues
public import Mathlib.Algebra.Order.Star.Rat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Internal.Order.Automation
public import Std.Tactic.BVDecide.Normalize.Prop
public import Lib.Speed

/-!
# A small nonzero integer in all Stickelberger ideals via Voronoi's congruence

The analytic input to the bound for the odd part of Ш: one nonzero integer X of controlled size
that, times c ^ (e + 1) - 1, lies in all the Stickelberger ideals for N and e.

* `New.OddPart.IsStickelbergerBound`: the two properties required of X, as a structure.
* `New.OddPart.exists_isStickelbergerBound`: such an X exists with X ≤ 2 ^ (N + e + 3) ^ 6, for
  e ≥ 1.

The idea: the generalised Bernoulli numbers of all characters mod N, corrected where they vanish for
reasons of parity, are the eigenvalues of one integer matrix. Its determinant is nonzero
(`New.OddPart.det_ne_zero_of_forall_sum_mul_ne_zero` and
`DirichletCharacter.generalizedBernoulli_ne_zero`), is divisible by each eigenvalue, and is bounded
by the Fourier series of the Bernoulli polynomial. Voronoi's congruence
(`New.OddPart.voronoi_congruence_bernoulli`) links the Bernoulli numbers to the Stickelberger sums;
it rests on a congruence for power sums along an arithmetic progression
(`New.OddPart.exists_sq_dvd_factorial_mul_sum_pow_sub`).

## Relation to the literature

Known result: Voronoi's congruence for twisted power sums and the trivial zeros of Dirichlet
L-functions. Here the congruence is twisted by a possibly imprimitive character and stated for power
sums. One non-zero integer with an explicit size bound has the following property. For c ≡ 1 mod N,
(c ^ (e + 1) - 1) X is congruent, modulo every m prime to c, to 2 w times the twisted Stickelberger
sum, where w does not depend on m. This holds for every character ψ with ψ(-1) = -(-1) ^ e and
values in a domain of characteristic 0. In addition, for every prime l, some c ≡ 1 mod N prime to l
has (c ^ e - 1) (c ^ (e + 1) - 1) ∣ X. Source: K. Ireland, M. Rosen, A Classical Introduction to
Modern Number Theory, 2nd ed. 1990; for the untwisted statement also M. Eberl, Kummer's congruence,
Archive of Formal Proofs 2024.
-/

@[expose] public section

open Finset DirichletCharacter Matrix Nat Polynomial Complex NeZero ZMod Real

lemma Nat.ModEq.coprime_of_modEq_one {a b : ℕ} (h : a ≡ 1 [MOD b]) : a.Coprime b := by
  simpa using h.gcd_eq

namespace New.OddPart

variable (N e : ℕ) [NeZero N]

/-- For every `i`, the number `(i + 1)! Bᵢ` is an integer. -/
lemma exists_intCast_eq_factorial_mul_bernoulli (i : ℕ) :
    ∃ c : ℤ, (c : ℚ) = (i + 1)! * _root_.bernoulli i := by
  -- `primorial (i + 1) Bᵢ` is an integer, by von Staudt–Clausen.
  obtain ⟨z, hz⟩ := TauCeti.exists_intCast_eq_primorial_mul_bernoulli (le_refl i)
  obtain ⟨d, hd⟩ : primorial (i + 1) ∣ (i + 1)! :=
    prod_primes_dvd _ (fun _ hp ↦ (mem_filter.1 hp).2.prime) fun _ hp ↦
      dvd_factorial (mem_filter.1 hp).2.pos (Nat.lt_succ_iff.1 (mem_range.1 (mem_filter.1 hp).1))
  refine ⟨z * d, ?_⟩
  rw [hd, Nat.cast_mul, Int.cast_mul, hz, Int.cast_natCast]
  ring

/-- The polynomial `(e + 1)! N ^ (e + 2) (B_{e+2}(X / N) - B_{e+2}(0))` has integer coefficients. -/
lemma exists_map_eq_bernoulli_sub_comp :
    ∃ p : ℤ[X], p.map (Int.castRingHom ℚ) = C (((e + 1)! : ℚ) * N ^ (e + 2)) *
      (Polynomial.bernoulli (e + 2) - C (_root_.bernoulli (e + 2))).comp (C (N : ℚ)⁻¹ * X) := by
  -- The coefficient of `X ^ (k + 1)` is `(e + 1)! (e + 2).choose (k + 1) N ^ j Bⱼ` with
  -- `j + k = e + 1`, and `(j + 1)!` divides `(e + 1)! (e + 2).choose (k + 1)`.
  refine (mem_lifts _).mp ((lifts_iff_coeff_lifts _).mpr fun n ↦ ?_)
  rw [coeff_C_mul, comp_C_mul_X_coeff, coeff_sub, coeff_bernoulli]
  obtain _ | k := n
  · exact ⟨0, by simp⟩
  split_ifs with hk
  swap
  · exact ⟨0, by simp⟩
  obtain ⟨j, hj⟩ : ∃ j : ℕ, e + 1 = j + k := ⟨e + 1 - k, by omega⟩
  obtain ⟨c, hc⟩ := exists_intCast_eq_factorial_mul_bernoulli j
  obtain ⟨d, hd⟩ : (j + 1)! ∣ (e + 1)! * (e + 2).choose (k + 1) := by
    obtain rfl | hk_pos : k = 0 ∨ 0 < k := k.eq_zero_or_pos
    · rw [zero_add, choose_one_right, mul_comm, ← factorial_succ, hj]
    · exact (factorial_dvd_factorial (by omega)).mul_right _
  have hd_cast : ((e + 1)! : ℚ) * (e + 2).choose (k + 1) = (j + 1)! * d := mod_cast hd
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne N)
  have h_pow : (N : ℚ) ^ (e + 2) * (N : ℚ)⁻¹ ^ (k + 1) = N ^ j := by
    simp [show e + 2 = j + (k + 1) by omega, pow_add, field]
  refine ⟨c * d * N ^ j, ?_⟩
  rw [show e + 2 - (k + 1) = j by omega, coeff_C_succ, eq_intCast]
  push_cast
  linear_combination (d * N ^ j : ℚ) * hc - (_root_.bernoulli j * N ^ j) * hd_cast -
    ((e + 1)! * (e + 2).choose (k + 1) * _root_.bernoulli j : ℚ) * h_pow

/-- Power sums along an arithmetic progression. For a natural number `a`, the number
`β = (e + 2)! N ^ (e + 1) B_{e+1}(a / N)` is an integer, and for every `u`,
`(e + 2)! ∑_{i<u} (a + i N) ^ (e + 1) ≡ β u` modulo `u²`. -/
theorem exists_sq_dvd_factorial_mul_sum_pow_sub (a : ℕ) :
    ∃ β : ℤ,
      (β : ℚ) = (e + 2)! * N ^ (e + 1) * (Polynomial.bernoulli (e + 1)).eval ((a : ℚ) / N) ∧
      ∀ u : ℕ, (u : ℤ) ^ 2 ∣ (e + 2)! * ∑ i ∈ range u, ((a : ℤ) + i * N) ^ (e + 1) - β * u := by
  -- Let `p = (e + 1)! N ^ (e + 2) (B_{e+2}(X / N) - B_{e+2}(0))`, so that `β = p'(a)`. Then
  -- `p(a + u N) - p(a)` is `N (e + 2)!` times the power sum, and it is `β u N` modulo `(u N)²`.
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne N)
  obtain ⟨p, hp⟩ := exists_map_eq_bernoulli_sub_comp N e
  have h_eval (q : ℤ[X]) (t : ℤ) : ((q.eval t : ℤ) : ℚ) = (q.map (Int.castRingHom ℚ)).eval ↑t := by
    simp
  have hp_eval (t : ℤ) : ((p.eval t : ℤ) : ℚ) = (e + 1)! * N ^ (e + 2) *
      ((Polynomial.bernoulli (e + 2)).eval ((t : ℚ) / N) - _root_.bernoulli (e + 2)) := by
    simp [h_eval, hp, div_eq_inv_mul]
  -- The difference equation of the Bernoulli polynomial.
  have h_step (t : ℤ) : p.eval (t + N) = p.eval t + N * ((e + 2)! * t ^ (e + 1)) := by
    have h_arg : ((t + N : ℤ) : ℚ) / N = 1 + t / N := by simp [field, add_comm]
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_add, hp_eval, hp_eval, h_arg, bernoulli_eval_one_add, factorial_succ (e + 1),
      show e + 2 - 1 = e + 1 from rfl, div_pow]
    push_cast
    field
  have h_sum (u : ℕ) : p.eval (a + u * N : ℤ) =
      p.eval (a : ℤ) + N * ((e + 2)! * ∑ i ∈ range u, ((a : ℤ) + i * N) ^ (e + 1)) := by
    induction u with
    | zero => simp
    | succ u ih =>
      simp [_root_.add_one_mul, ← add_assoc, h_step, ih, sum_range_succ, mul_add]
  refine ⟨p.derivative.eval (a : ℤ), ?_, fun u ↦ ?_⟩
  · rw [h_eval, ← derivative_map, hp, derivative_C_mul]
    simp [derivative_comp, derivative_bernoulli_add_one, factorial_succ (e + 1), div_eq_inv_mul]
    field
  · obtain ⟨k, hk⟩ := p.exists_mul_sq_add_linear_part_eq_eval_add a (u * N)
    refine ⟨k * N, mul_left_cancel₀ (Nat.cast_ne_zero.mpr (ne N) : (N : ℤ) ≠ 0) ?_⟩
    linear_combination -h_sum u - hk

/-- The Stickelberger property of `X` for `N` and `e`: a divisibility for each prime, and a
congruence for the Stickelberger sums. -/
structure IsStickelbergerBound (X : ℕ) : Prop where
  /-- For every prime `l`, some `c ≡ 1 mod N` prime to `l` has
  `(c ^ e - 1) (c ^ (e + 1) - 1) ∣ X`. -/
  exists_modEq_one_coprime_dvd {l : ℕ} (hl : l.Prime) :
    ∃ c : ℕ, c ≡ 1 [MOD N] ∧ l.Coprime c ∧ (c ^ e - 1) * (c ^ (e + 1) - 1) ∣ X
  /-- Let `c ≡ 1 mod N`, and let `ψ` be a character mod `N` with values in a domain `O` of
  characteristic `0` and `ψ(-1) = -(-1) ^ e`. Then some `w` in `O`, the same for every `m`, has
  `(c ^ (e + 1) - 1) X ≡ 2 w ∑ ⌊c a / (N m)⌋ a ^ e ψ(a)` modulo `m` for all `m ≥ 1` prime to `c`,
  the sum over `0 ≤ a < N m`. -/
  exists_natCast_dvd_sub_mul_sum {c : ℕ} (hc : c ≡ 1 [MOD N]) (O : Type) [CommRing O] [IsDomain O]
    [CharZero O] (ψ : DirichletCharacter O N) (hψ : ψ (-1) = -(-1) ^ e) :
    ∃ w : O, ∀ (m : ℕ) [NeZero m], m.Coprime c →
      (m : O) ∣
        (c ^ (e + 1) - 1) * X - 2 * w * ∑ a ∈ range (N * m), ↑(c * a / (N * m)) * (a ^ e * ψ a)

/-- The twisted Bernoulli sums are generalised Bernoulli numbers. Let `χ` be a Dirichlet character
mod `N` with values in a `ℚ`-algebra, let `e ≥ 1`, and let `β a` be the integer
`(e + 2)! N ^ (e + 1) B_{e+1}(a / N)`. Then `∑ χ(a) β a = (e + 2)! N B_{e+1,χ}`, the sum over
`0 ≤ a < N`. -/
lemma sum_mul_bernoulli_eq_generalizedBernoulli {R : Type*} [CommRing R] [Algebra ℚ R]
    (χ : DirichletCharacter R N) (he : e ≠ 0) (β : ℕ → ℤ) (hβ : ∀ a : ℕ,
      (β a : ℚ) = (e + 2)! * N ^ (e + 1) * (Polynomial.bernoulli (e + 1)).eval ((a : ℚ) / N)) :
    ∑ a : ZMod N, χ a * β a.val = (e + 2)! * N * χ.generalizedBernoulli (e + 1) := by
  rw [generalizedBernoulli_eq_pow_mul_sum_bernoulli_eval χ (by omega), add_tsub_cancel_right,
    mul_sum, mul_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  have h := congr_arg (algebraMap ℚ R) (hβ a.val)
  simp only [map_intCast, map_mul, map_pow, map_natCast] at h
  rw [h]
  ring

omit [NeZero N] in
/-- Voronoi's congruence, twisted by a Dirichlet character χ mod N. For f = N m and c ≡ 1 mod N
prime to m, (c ^ (e + 1) - 1) ∑ χ(t) t ^ (e + 1) ≡ (e + 1) c ^ e f ∑ ⌊c t / f⌋ t ^ e χ(t) modulo f²,
both sums over 0 ≤ t < f. -/
lemma voronoi_congruence {O : Type*} [CommRing O] (χ : DirichletCharacter O N) {f m c : ℕ}
    [NeZero f] (hf : f = N * m) (hcm : m.Coprime c) (hcN : c ≡ 1 [MOD N]) :
    (f : O) ^ 2 ∣
      (c ^ (e + 1) - 1) * ∑ t : ZMod f, χ t.val * t.val ^ (e + 1) -
        (e + 1) * c ^ e * f * ∑ t : ZMod f, ↑(c * t.val / f) * (χ t.val * t.val ^ e) := by
  -- Substitute `t ↦ c t` in the copy of the sum `∑ χ(t) t^(e+1)` without the factor `c^(e+1)`,
  -- and compare term by term.
  have h_c_coprime : c.Coprime f := by simpa [hf] using hcN.coprime_of_modEq_one.mul_right hcm.symm
  have h_c_eq_one : (c : ZMod N) = 1 := mod_cast (natCast_eq_natCast_iff c 1 N).mpr hcN
  rw [sub_one_mul, mul_sum, sub_sub, dvd_sub_comm,
    ← Equiv.sum_comp (unitOfCoprime c h_c_coprime).mulLeft, mul_sum, ← sum_add_distrib,
    ← sum_sub_distrib]
  refine dvd_sum fun t _ ↦ ?_
  -- The representative of `c t` is `c t - f k`, with `k = ⌊c t / f⌋`. Expand its power to first
  -- order in `f k`.
  set k : ℕ := c * t.val / f with hk
  have h_binomial : ((f : O) * -k) ^ 2 ∣ (c * t.val + f * -k) ^ (e + 1) -
      (c * t.val) ^ e * (f * -k) * (e + 1) - (c * t.val) ^ (e + 1) := by
    simpa using sq_dvd_add_pow_sub_sub ((f : O) * -k) (c * t.val) (e + 1)
  refine .trans ⟨(k : O) ^ 2, by ring⟩ (h_binomial.trans ⟨χ t.val, ?_⟩)
  -- `χ` has the same value at `c t - f k` and at `t`, as `N ∣ f` and `c ≡ 1`; the rest is `ring`.
  simp [val_mul, (c * _).mod_def, mul_div_le, k, hf, h_c_eq_one, natCast_self]
  ring

omit [NeZero N] in
/-- A sum over `0 ≤ t < N K` equals the double sum over `t = a + i N` with `0 ≤ a < N` and
`0 ≤ i < K`. -/
lemma sum_range_mul_eq_sum_sum {α : Type*} [AddCommMonoid α] (F : ℕ → α) (K : ℕ) :
    ∑ t ∈ range (N * K), F t = ∑ a ∈ range N, ∑ i ∈ range K, F (a + i * N) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.mul_succ, sum_range_add, ih, ← sum_add_distrib]
    refine sum_congr rfl fun a _ ↦ ?_
    rw [sum_range_succ, add_comm (N * K) a, mul_comm N K]

/-- Voronoi's congruence for the Stickelberger sums. Let `χ` be a character mod `N` with values in
a commutative ring without additive torsion, let `c ≡ 1 mod N` be prime to `m ≥ 1`, and let
`β a = (e + 2)! N ^ (e + 1) B_{e+1}(a / N)`. Then
`(e + 2)! (e + 1) N c ^ e ∑ ⌊c a / (N m)⌋ a ^ e χ(a) ≡ (c ^ (e + 1) - 1) ∑ χ(a) β a` modulo `m`,
the first sum over `0 ≤ a < N m` and the second over `0 ≤ a < N`. -/
theorem voronoi_congruence_bernoulli {O : Type*} [CommRing O] [HasUniqueDiv O]
    (χ : DirichletCharacter O N) {m c : ℕ} [NeZero m] (hcm : m.Coprime c) (hcN : c ≡ 1 [MOD N])
    (β : ℕ → ℤ) (hβ : ∀ a : ℕ,
      (β a : ℚ) = (e + 2)! * N ^ (e + 1) * (Polynomial.bernoulli (e + 1)).eval ((a : ℚ) / N)) :
    (m : O) ∣
      (e + 2)! * (e + 1) * N * c ^ e * ∑ a ∈ range (N * m), ↑(c * a / (N * m)) * (a ^ e * χ a) -
        (c ^ (e + 1) - 1) * ∑ a : ZMod N, χ a * β a.val := by
  -- Multiply the congruence for power sums modulo `(N m)²` by `(e + 2)!`, replace
  -- `(e + 2)! ∑ χ(t) t ^ (e + 1)` by `m ∑ χ(a) β a` modulo `m²`, and divide by `m`.
  have h_range : ∀ (f : ℕ) [NeZero f] (F : ℕ → O), (range f).sum F = ∑ a : ZMod f, F a.val
    | _ + 1, _ => sum_range
  have h_class (a : ℕ) : (m : O) ^ 2 ∣
      χ a * ((e + 2)! * ∑ i ∈ range m, ((a : O) + i * N) ^ (e + 1) - β a * m) := by
    obtain ⟨β', hβ', h_dvd⟩ := exists_sq_dvd_factorial_mul_sum_pow_sub N e a
    obtain rfl : β' = β a := Int.cast_injective (hβ'.trans (hβ a).symm)
    exact .mul_left (by simpa using map_dvd (Int.castRingHom O) (h_dvd m)) _
  have h_split : (e + 2)! * ∑ t ∈ range (N * m), χ t * (t : O) ^ (e + 1) -
      m * ∑ a ∈ range N, χ a * β a =
      ∑ a ∈ range N, χ a * ((e + 2)! * ∑ i ∈ range m, ((a : O) + i * N) ^ (e + 1) - β a * m) := by
    rw [sum_range_mul_eq_sum_sum, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun a _ ↦ ?_
    simp only [Nat.cast_add, Nat.cast_mul, natCast_self, mul_zero, add_zero, ← mul_sum]
    ring
  obtain ⟨w, hw⟩ : (m : O) ^ 2 ∣ (e + 2)! * ∑ t ∈ range (N * m), χ t * (t : O) ^ (e + 1) -
      m * ∑ a ∈ range N, χ a * β a := by
    simpa only [h_split] using dvd_sum fun a _ ↦ h_class a
  obtain ⟨v, hv⟩ : ((N * m : ℕ) : O) ^ 2 ∣
      (c ^ (e + 1) - 1) * ∑ t : ZMod (N * m), χ t.val * t.val ^ (e + 1) -
        (e + 1) * c ^ e * (N * m : ℕ) *
          ∑ t : ZMod (N * m), ↑(c * t.val / (N * m)) * (χ t.val * t.val ^ e) :=
    voronoi_congruence N e χ (f := N * m) rfl hcm hcN
  refine ⟨(c ^ (e + 1) - 1) * w - (e + 2)! * N ^ 2 * v, nsmul_right_injective (ne m) ?_⟩
  simp only [h_range, natCast_zmod_val, nsmul_eq_mul, Nat.cast_mul, mul_comm _ (χ _)] at hw hv ⊢
  linear_combination (c ^ (e + 1) - 1) * hw - (e + 2)! * hv

/-- A group matrix `(g(t / s))_{s,t}` of `(ZMod N)ˣ` over `ℂ` has nonzero determinant if no
eigenvalue `∑ χ(u) g(u)` is zero. This is one direction of `TauCeti.det_of_div_ne_zero_iff`, proved
here to avoid the import closure of its module. -/
lemma det_ne_zero_of_forall_sum_mul_ne_zero (g : (ZMod N)ˣ → ℂ)
    (hg : ∀ χ : DirichletCharacter ℂ N, ∑ u : (ZMod N)ˣ, χ u * g u ≠ 0) :
    (of fun s t : (ZMod N)ˣ ↦ g (t / s)).det ≠ 0 := by
  -- A vector in the left kernel is orthogonal to all characters, so it is zero by Fourier
  -- inversion on the units.
  intro hA
  obtain ⟨w, hw0, hw⟩ := exists_vecMul_eq_zero_iff.2 hA
  have h_orth (χ : DirichletCharacter ℂ N) : w ⬝ᵥ (fun t ↦ χ t) = 0 := by
    have h := congr_arg (dotProduct w)
      (TauCeti.Matrix.of_div_mulVec_monoidHom g ((χ : ZMod N →* ℂ).comp (Units.coeHom _)))
    rw [dotProduct_mulVec, hw, zero_dotProduct, dotProduct_smul, smul_eq_mul] at h
    simp only [MulChar.coe_comp_coeHom_apply] at h
    exact (mul_eq_zero.1 h.symm).resolve_left (hg χ)
  simp only [dotProduct] at h_orth
  refine hw0 (funext fun a ↦ ?_)
  have h := TauCeti.card_units_mul_apply_eq_sum_mulChar_units w a
  rw [sum_eq_zero fun χ _ ↦ by rw [h_orth χ⁻¹, mul_zero]] at h
  exact (mul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 Nat.card_pos.ne')

omit [NeZero N] in
/-- For a prime `l`, one of `c = 1 + N` and `c = 1 + 2 N` is prime to `l`. This `c` is `≡ 1 mod N`,
and `(c ^ e - 1) (c ^ (e + 1) - 1)` divides, for every `Y`,
`((1 + N) ^ e - 1) ((1 + N) ^ (e + 1) - 1) ((1 + 2 N) ^ e - 1) ((1 + 2 N) ^ (e + 1) - 1) Y`. -/
lemma exists_modEq_one_coprime_dvd_of_prime {l : ℕ} (hl : l.Prime) (Y : ℕ) :
    ∃ c : ℕ, c ≡ 1 [MOD N] ∧ l.Coprime c ∧ (c ^ e - 1) * (c ^ (e + 1) - 1) ∣
      ((1 + N) ^ e - 1) * ((1 + N) ^ (e + 1) - 1) *
        (((1 + N + N) ^ e - 1) * ((1 + N + N) ^ (e + 1) - 1) * Y) := by
  -- `l` does not divide both `1 + N` and `1 + 2 N`.
  obtain hl_cop | hl_dvd := coprime_or_dvd_of_prime hl (1 + N)
  · exact ⟨1 + N, add_modEq_right, hl_cop, dvd_mul_right _ _⟩
  · have h_cop : l.Coprime (1 + N + N) := .of_dvd_left hl_dvd (by simp)
    exact ⟨1 + N + N, by simp, h_cop, .mul_left (dvd_mul_right _ _) _⟩

omit [NeZero N] in
/-- The size bound for `X`. If `d ≤ (φ N)! (64 M) ^ φ N`, where
`M = (e + 2)! Nᵉ⁺¹ (e + 1)!`, then
`((1 + N)ᵉ - 1) ((1 + N)ᵉ⁺¹ - 1) ((1 + 2 N)ᵉ - 1) ((1 + 2 N)ᵉ⁺¹ - 1) d ≤ 2 ^ (N + e + 3) ^ 6`. -/
lemma mul_sub_one_mul_le_two_pow_of_le {d : ℕ}
    (hd : d ≤ (φ N)! * ((e + 2)! * N ^ (e + 1) * (e + 1)! * 2 ^ 6) ^ φ N) :
    ((1 + N) ^ e - 1) * ((1 + N) ^ (e + 1) - 1) *
      (((1 + N + N) ^ e - 1) * ((1 + N + N) ^ (e + 1) - 1) * d) ≤ 2 ^ (N + e + 3) ^ 6 := by
  grw [hd]
  -- Bound every base `a` by `2 ^ a` and `a !` by `a ^ a`, then compare the exponents.
  trans
  · apply_rules only [(sub_le ..).trans, (factorial_le_pow _).trans, pow_le_pow_left',
      mul_le_mul', Nat.lt_two_pow_self.le]
  · simp only [← pow_mul, ← pow_add]
    refine Nat.pow_le_pow_right two_pos ?_
    grw [totient_le]
    lia

/-- For `N, e ≥ 1` there is an integer `1 ≤ X ≤ 2^{(N+e+3)^6}` with the Stickelberger property
`New.OddPart.IsStickelbergerBound N e X`, namely a divisibility condition for each prime together
with a congruence for the Stickelberger sums. It comes from one integer matrix over the units mod
`N` whose eigenvalues are built from the twisted Bernoulli sums; Voronoi's congruence links these
sums to the Stickelberger sums.

This is a finite-level analogue of the interpolation property of Kubota–Leopoldt ℓ-adic L-functions
at negative integers; no ℓ-adic L-function appears, and the interpolation formula itself is not
asserted. -/
lemma exists_isStickelbergerBound (he : e ≠ 0) :
    ∃ X ≠ (0 : ℕ), X ≤ 2 ^ (N + e + 3) ^ 6 ∧ IsStickelbergerBound N e X := by
  -- Let `b t = (e + 2)! N ^ (e + 1) B_{e+1}(t / N)`, an integer. `X` is the product of the two
  -- possible factors of the first clause and of `|det T|`, where the integer matrix `T` has one
  -- eigenvalue `∑ ψ t * g t = 2 ∑ ψ t * b t + (-1) ^ e + ψ (-1)` for each character `ψ` mod `N`.
  have hN : N ≠ 0 := ne N
  obtain ⟨b, hb_rat⟩ : ∃ b : ℕ → ℤ, ∀ t : ℕ,
      (b t : ℚ) = (e + 2)! * N ^ (e + 1) * (Polynomial.bernoulli (e + 1)).eval ((t : ℚ) / N) := by
    choose b hb _ using exists_sq_dvd_factorial_mul_sum_pow_sub N e
    exact ⟨b, hb⟩
  -- `17 M` will bound `|b t|` for `0 ≤ t ≤ N`.
  let M : ℕ := (e + 2)! * N ^ (e + 1) * (e + 1)!
  have hb (K : Type) [RCLike K] (t : ℕ) :
      b t = (e + 2)! * N ^ (e + 1) * aeval (t / N : K) (bernoulli (e + 1)) := by
    have h_cast := congr_arg (algebraMap ℚ K) (hb_rat t)
    rw [map_mul, ← aeval_algebraMap_apply_eq_algebraMap_eval] at h_cast
    simpa using h_cast
  let g (t : ZMod N) : ℤ :=
    2 * b t.val + (if t = 1 then (-1) ^ e else 0) + if t = -1 then 1 else 0
  let T : Matrix (ZMod N)ˣ (ZMod N)ˣ ℤ := of fun s t ↦ g (t / s).val
  have hT_cast (S : Type) [CommRing S] :
      (T.det : S) = (of fun s t : (ZMod N)ˣ ↦ (g (t / s).val : S)).det := by
    rw [← eq_intCast (Int.castRingHom S), RingHom.map_det]
    rfl
  -- No complex eigenvalue is zero: the sum `∑ χ t * b t` is `(e + 2)! N B_{e+1,χ}`, which
  -- vanishes exactly when `χ (-1) = (-1) ^ e`, that is, when `(-1) ^ e + χ (-1)` is `±2`, not `0`.
  have h_eigen_ne (χ : DirichletCharacter ℂ N) : ∑ t, χ t * g t ≠ 0 := by
    have h_value : ∑ t, χ t * g t = 2 * ∑ t : ZMod N, χ t * b t.val + ((-1) ^ e + χ (-1)) := by
      simp [g, mul_add, sum_add_distrib, mul_sum, mul_left_comm, add_assoc]
    rw [h_value, sum_mul_bernoulli_eq_generalizedBernoulli N e χ he b hb_rat]
    rcases χ.apply_neg_one_eq_neg_one_pow_or e with hχ | hχ
    · rw [generalizedBernoulli_eq_zero_of_apply_neg_one_eq_neg (.inl (by omega))
        (by rw [hχ, pow_succ]; ring), hχ]
      simp [← two_mul]
    · rw [hχ, add_neg_cancel, add_zero]
      refine mul_ne_zero two_ne_zero (mul_ne_zero (by simp [factorial_ne_zero, hN]) ?_)
      exact generalizedBernoulli_ne_zero (by omega) (by rw [hχ, pow_succ]; ring)
  have hT_ne : T.det ≠ 0 := by
    have h := det_ne_zero_of_forall_sum_mul_ne_zero N (fun u : (ZMod N)ˣ ↦ (g u.val : ℂ)) fun χ ↦ by
      rw [← χ.sum_mul_eq_sum_units fun t ↦ (g t : ℂ)]
      exact h_eigen_ne χ
    rw [← hT_cast] at h
    exact_mod_cast h
  let X : ℕ := ((1 + N) ^ e - 1) * ((1 + N) ^ (e + 1) - 1) *
    (((1 + N + N) ^ e - 1) * ((1 + N + N) ^ (e + 1) - 1) * T.det.natAbs)
  refine ⟨X, ?_, ?_, fun {l} hl ↦ ?_, fun {c} hc_mod O _ _ _ χ hχ ↦ ?_⟩
  · simpa [X, tsub_eq_zero_iff_le, add_assoc, hN, he] using hT_ne
  · have hb_lt (t : ℕ) (ht : t ≤ N) : |b t| < M * 17 := by
      have h_bound : |bernoulliFun (e + 1) (t / N)| < (e + 1)! * 17 :=
        (TauCeti.abs_bernoulliFun_le_four_mul_factorial_div _
          ⟨by positivity, div_le_one_of_le₀ (mod_cast ht) (by positivity)⟩).trans_lt <|
          (_root_.div_le_self (by positivity) (one_le_pow₀ (by linarith [two_le_pi]))).trans_lt
            (by linarith [show (0 : ℝ) < (e + 1)! by positivity])
      simpa [← Int.cast_lt (R := ℝ), M, hb ℝ, abs_mul, mul_assoc, bernoulliFun] using
        mul_lt_mul_of_pos_left h_bound (by positivity : (0 : ℝ) < (e + 2)! * N ^ (e + 1))
    -- The entries of `T` are at most `34 M + 2 ≤ 64 M`.
    have h_entry (s t : (ZMod N)ˣ) : |T s t| ≤ M * 2 ^ 6 := by
      simp only [T, of_apply]
      grind [val_le, neg_one_pow_eq_ite]
    refine mul_sub_one_mul_le_two_pow_of_le N e ?_
    simpa [← Int.ofNat_le, M] using T.det_le (abv := .abs) h_entry
  · exact exists_modEq_one_coprime_dvd_of_prime N e hl T.det.natAbs
  -- The eigenvalue divides `det T`, hence `X`.
  have h_dvd : ∑ t, χ t * g t ∣ (T.det : O) := by
    rw [χ.sum_mul_eq_sum_units fun t ↦ (g t : O), hT_cast]
    simpa using TauCeti.Matrix.sum_mul_dvd_det_of_div (fun u : (ZMod N)ˣ ↦ (g u.val : O))
      ((χ : ZMod N →* O).comp (Units.coeHom _))
  obtain ⟨u, hu⟩ : ∑ t, χ t * g t ∣ (X : O) :=
    h_dvd.trans (by simp [X, ← mul_assoc, ← sign_mul_self])
  -- By the parity `hχ` the eigenvalue is `2 ∑ χ t * b t`; apply Voronoi's congruence.
  have h_parity : ∑ t, χ t * g t = 2 * ∑ t : ZMod N, χ t * b t.val := by
    simp [g, mul_add, sum_add_distrib, hχ, mul_sum, mul_left_comm]
  refine ⟨u * ((e + 2)! * (e + 1) * N * c ^ e), fun m _ hm ↦ ?_⟩
  obtain ⟨v, hv⟩ : (m : O) ∣
      (e + 2)! * (e + 1) * N * c ^ e * ∑ a ∈ range (N * m), ↑(c * a / (N * m)) * (a ^ e * χ a) -
        (c ^ (e + 1) - 1) * ∑ a : ZMod N, χ a * b a.val :=
    voronoi_congruence_bernoulli N e χ hm hc_mod b hb_rat
  refine ⟨-2 * u * v, ?_⟩
  rw [hu, h_parity]
  linear_combination -2 * u * hv

end New.OddPart
