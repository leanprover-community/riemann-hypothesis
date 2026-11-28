module

public import Aesop.BuiltinRules
public import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Algebra.Ring.IsFormallyReal
import TauCeti.NumberTheory.NumberField.Countable
public import TauCeti.NumberTheory.Height.FamilyOverPairs
public import Lib.General.NumberTheory.ImaginaryQuadraticField
import Lib.General.Geometry.GaloisCovers
import Lib.General.NumberTheory.PadicLimitsValuation
import Lib.PadicComparison.Descent.TestCategory

/-!
# The height of a family over all places: products, monotonicity and the product formula

Heights of families of complex numbers indexed by the pairs `ι` of a prime `l` and an isomorphism
`ℂ ≃+* ℚ̄_l`. The pairs (`TauCeti.PrimePadicIso`), the bound `TauCeti.PrimePadicIso.HeightLe y c`
and its calculus (`HeightLe.of_mul_le`, `mono`, `rpow_mul`, `inv_const`, `mul`, `prod`, `pow`) are
Tau Ceti's. `HeightLe y c` says: for some multiplier `H ≠ 0` and some `h l ≥ 0`, the conjugates of
`H` are bounded by `exp α`, the numbers `H * y ι` are bounded `l`-adically by `l ^ h l`, and
`α + ∑ h l * log l ≤ c` over every finite set of primes. This file adds two results.

* `TauCeti.PrimePadicIso.HeightLe.of_le`: a height bound from `l`-adic bounds alone.
* `TauCeti.PrimePadicIso.HeightLe.nonneg_of_one`: the constant family `1` has height at least `0`,
  by the product formula (`New.log_product_formula`) for the norm of `H`.

## Relation to the literature

The multiplier H, and so the bound at infinity, does not depend on ι, while y ι may; so each prime
may use its own twist. Related work: Gaudron, Pentes des fibrés vectoriels adéliques sur un corps
global, 2006; Bombieri–Gubler, Heights in Diophantine Geometry, ch. 1, 2006.
-/

@[expose] public section

open Algebra Module Real Finset Filter IntermediateField AdjoinSimple Padic PadicAlgCl

namespace New

export TauCeti (PrimePadicIso)
export TauCeti.PrimePadicIso (HeightLe)

/-- The product formula for `ℚ`, in logarithms: `log |q| + ∑ log |q|_p = 0` (`log q` is `log |q|`
and `log 0 = 0`), the sum taken over the primes below any bound `M` that exceeds the absolute value
of the numerator of `q` and the denominator of `q`. -/
lemma log_product_formula {M : ℕ} {q : ℚ} (h_num_lt : q.num.natAbs < M) (h_den_lt : q.den < M) :
    log q + ∑ p ∈ range M with p.Prime, log (padicNorm p q) = 0 := by
  -- Factor the numerator and the denominator into primes and take logarithms; the term of `p`
  -- in `log |q|` is `v_p(q) * log p`, which cancels `log |q|_p = -v_p(q) * log p`.
  obtain rfl | hq := eq_or_ne q 0
  · simp
  have log_nat {n : ℕ} (hn : n ≠ 0) (hnM : n < M) :
      log n = ∑ p ∈ range M with p.Prime, padicValNat p n * log p := by
    conv_lhs => rw [← Nat.prod_pow_prime_multiplicity n hn M hnM]
    simp +contextual [log_prod, Nat.Prime.ne_zero, Nat.padicValNat_def]
  have log_q : log q = log q.num.natAbs - log q.den := by simp [q.cast_def, log_div, hq]
  have log_norm (p : ℕ) :
      log (padicNorm p q) = (padicValNat p q.den - padicValNat p q.num.natAbs) * log p := by
    simp [padicNorm.eq_zpow_of_ne_zero hq, padicValRat, padicValInt, Nat.padicValNat_def]
  rw [log_q, log_nat (by simpa using hq) h_num_lt, log_nat q.den_nz h_den_lt]
  simp [log_norm, sub_mul]

variable {c : ℝ} {y : PrimePadicIso → ℂ}

/-- If reals `e l` have sum at most `c` over every finite set of primes, and `y ι` has `l`-adic norm
at most `exp (e l)` under `ι.iso` for every pair `ι` of a prime `l = ι.prime` and an isomorphism
`ι.iso : ℂ ≃+* ℚ̄_l`, then the family `y` has height at most `c`. The `e l` may have any sign. -/
lemma _root_.TauCeti.PrimePadicIso.HeightLe.of_le {e : ℕ → ℝ}
    (h_sum : ∀ T : Finset ℕ, (∀ l ∈ T, l.Prime) → ∑ l ∈ T, e l ≤ c)
    (h_norm : ∀ ι : PrimePadicIso, ‖ι.iso (y ι)‖ ≤ exp (e ι.prime)) : HeightLe y c :=
  .of_mul_le (α := 0) one_ne_zero (by simp) e (by simpa using h_norm) (by simpa using h_sum)

/-- Let `H` be an algebraic number of degree `n` and `F` an algebraically closed normed field of
characteristic zero with the cardinality of `ℂ`. If `‖ι H‖ ≤ exp b` for all isomorphisms
`ι : ℂ ≃+* F`, then the norm of `H` from `ℚ(H)` to `ℚ` has size at most `exp (n * b)` in `F`. -/
lemma norm_algebraMap_norm_gen_le {F : Type} [NormedField F] [CharZero F] [IsAlgClosed F]
    (hF : Cardinal.mk ℂ = Cardinal.mk F) {H : ℂ} (h_alg : IsAlgebraic ℚ H) {b : ℝ}
    (hb : ∀ ι : ℂ ≃+* F, ‖ι H‖ ≤ exp b) :
    ‖algebraMap ℚ F (Algebra.norm ℚ (AdjoinSimple.gen ℚ H))‖ ≤ exp (finrank ℚ ℚ⟮H⟯ * b) := by
  have : NumberField ℚ⟮H⟯ := { to_finiteDimensional := adjoin.finiteDimensional h_alg.isIntegral }
  -- Each conjugate of `H` in `F` is `ι H` for some isomorphism `ι`.
  have conj_le (σ : ℚ⟮H⟯ →ₐ[ℚ] F) : ‖σ (gen ℚ H)‖ ≤ exp b := by
    obtain ⟨ι, hι⟩ : ∃ ι : ℂ ≃+* F, ∀ a : ℚ⟮H⟯, ι a = σ a :=
      exists_ringEquiv_extend hF ℚ⟮H⟯.val.toRingHom σ Subtype.val_injective σ.injective
    simpa [← hι] using hb ι
  calc _ = ∏ σ : ℚ⟮H⟯ →ₐ[ℚ] F, ‖σ (gen ℚ H)‖ := by rw [norm_eq_prod_embeddings, norm_prod]
    _ ≤ ∏ _σ : ℚ⟮H⟯ →ₐ[ℚ] F, exp b := prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun σ _ ↦ conj_le σ
    _ = exp (finrank ℚ ℚ⟮H⟯ * b) := by simp [exp_natCast_mul]

/-- If the constant family `1` has height at most `c`, then `0 ≤ c`. This is a form of the product
formula. -/
lemma _root_.TauCeti.PrimePadicIso.HeightLe.nonneg_of_one (h_one : HeightLe 1 c) : 0 ≤ c := by
  -- Let `q` be the norm of `H` from `ℚ(H)` to `ℚ` and `n` the degree. At every place `q` is a
  -- product of `n` conjugates of `H`, so `log |q| ≤ n α` and `log |q|_l ≤ n (e l) log l`.
  -- The product formula for `q` then gives `0 ≤ n * c`.
  obtain ⟨H, hH, α, e, -, hα, he, h_sum⟩ := TauCeti.PrimePadicIso.heightLe_iff.1 h_one
  have h_padic (l : ℕ) [hl : Fact l.Prime] (ι : ℂ ≃+* PadicAlgCl l) :
      ‖ι H‖ ≤ exp (e l * log l) := by
    simpa [rpow_def_of_pos, hl.out.pos, mul_comm] using he ⟨l, ι⟩
  -- `H` is algebraic, because its `2`-adic size is bounded uniformly in `ι`.
  have h_alg : IsAlgebraic ℚ H := isAlgebraic_of_norm_complexToCp_le (by simpa using h_padic 2)
  have : FiniteDimensional ℚ ℚ⟮H⟯ := adjoin.finiteDimensional h_alg.isIntegral
  let q : ℚ := Algebra.norm ℚ (gen ℚ H)
  let n : ℕ := finrank ℚ ℚ⟮H⟯
  have hq : q ≠ 0 := norm_ne_zero_iff.2 (by simpa [Subtype.ext_iff] using hH)
  have h_inf : log q ≤ n * α := by
    rw [← log_abs, log_le_iff_le_exp (by simpa using hq)]
    simpa using norm_algebraMap_norm_gen_le rfl h_alg hα
  have h_fin (l : ℕ) (hl : l.Prime) : log (padicNorm l q) ≤ n * (e l * log l) := by
    have : Fact l.Prime := ⟨hl⟩
    rw [← Padic.eq_padicNorm, log_le_iff_le_exp (norm_pos_iff.2 (Rat.cast_ne_zero.2 hq)),
      ← PadicAlgCl.norm_extends]
    exact norm_algebraMap_norm_gen_le mk_complex_eq_mk_padicAlgCl h_alg (h_padic l)
  -- Sum over the primes below a number `N` that exceeds the numerator and the denominator.
  let N : ℕ := q.num.natAbs + q.den + 1
  refine nonneg_of_mul_nonneg_right ?_ (Nat.cast_pos.2 (finrank_pos : 0 < n))
  calc 0 = log q + ∑ l ∈ range N with l.Prime, log (padicNorm l q) :=
      (log_product_formula (by omega) (by omega)).symm
    _ ≤ n * α + ∑ l ∈ range N with l.Prime, n * (e l * log l) :=
      add_le_add h_inf (sum_le_sum fun l hl ↦ h_fin l (mem_filter.1 hl).2)
    _ = n * (α + ∑ l ∈ range N with l.Prime, e l * log l) := by rw [mul_add, mul_sum]
    _ ≤ n * c := mul_le_mul_of_nonneg_left (h_sum _ fun l hl ↦ (mem_filter.1 hl).2) n.cast_nonneg

end New
