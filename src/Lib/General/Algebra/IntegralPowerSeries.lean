module

import TauCeti.NumberTheory.Padics.Factorial
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import TauCeti.RingTheory.MvPowerSeries.Derivative
public import Lib.GLn.SchurModule.Basic
public import Lib.General.Algebra.AdicCompletion

/-!
# Integral power series over ℂ_p: jets, the chain rule and the exponential

A power series over `ℂ_[p]` is called integral if it comes, through `New.seriesToCp`, from a series
with coefficients in the ring of integers of `ℂ_[p]`.

## Main definitions and results

* `New.mem_range_seriesToCp`: a series in one variable is integral iff all its coefficients have
  norm at most one.
* `New.jet_subst_linearSeries`: for a linear substitution `M`, the jet `P(∂) (F ∘ M) (0)` is the jet
  of `F` along the polynomial `New.linSubst M P` obtained from `P` by the transposed substitution.
* `New.expSubst`: the exponential `exp a` of a power series `a` in several variables without
  constant term; it turns finite sums into products (`New.expSubst_add`, `New.expSubst_sum`).
* `New.padicValNat_factorial_mem_Icc`: `n / (p - 1) - v_p(n!)` lies in `[0, K]` for `n < p ^ K`.

Notions from other files:
* `New.jet`: the bilinear pairing `P(∂)F(0)` of a polynomial `P` with a power series `F`, the sum
  over exponents `d` of `d!` times the product of the `d`-th coefficients of `P` and `F`.
* `New.linearSeries`: the linear form `∑ c_i z_i`, as a power series in the variables `z_i`.
* `New.linSubst`: for a matrix `M` over `R`, the `R`-algebra map of polynomial rings that sends
  `X_b` to `∑_t M_(t b) X_t`.

## Relation to the literature

Known results: the chain rule and the functional equation of the exponential for formal power
series, and Legendre's formula for the valuation of a factorial.
-/

@[expose] public section

/-! ## The inclusion of integral power series -/

section PadicSeriesDefs

variable {p : ℕ} [Fact p.Prime] {σ : Type}

/-- The inclusion of power series over the integers `valRingCp p` into power series over `ℂ_[p]`, as
a ring homomorphism. -/
noncomputable abbrev New.seriesToCp : MvPowerSeries σ (valRingCp p) →+* MvPowerSeries σ ℂ_[p] :=
  MvPowerSeries.map (σ := σ) (valRingCp p).subtype

@[simp]
lemma New.seriesToCp_smul (k : valRingCp p) (f : MvPowerSeries σ (valRingCp p)) :
    seriesToCp (p := p) (σ := σ) (k • f) = (k : ℂ_[p]) • seriesToCp f :=
  rfl

end PadicSeriesDefs

/-! ## Integral series, units, partial derivatives and linear forms -/

section IntegralSeries

open MvPowerSeries PowerSeries

namespace New

/-- The linear form ∑ c_i z_i, as a power series in the variables z_i. -/
noncomputable def linearSeries {ι R : Type*} [Fintype ι] [CommSemiring R] (c : ι → R) :
    MvPowerSeries ι R :=
  ∑ i : ι, c i • MvPowerSeries.X i

/-- Scaling the coefficients of a linear form scales its power series by the same scalar. -/
lemma linearSeries_smul {ι R : Type*} [Fintype ι] [CommSemiring R] (a : R) (c : ι → R) :
    linearSeries (a • c) = a • linearSeries c := by
  simp [linearSeries, Finset.smul_sum, mul_smul]

/-- Summing the coefficients of finitely many linear forms sums their power series. -/
lemma linearSeries_sum {ι J R : Type*} [Fintype ι] [CommSemiring R] (s : Finset J) (c : J → ι → R) :
    linearSeries (∑ j ∈ s, c j) = ∑ j ∈ s, linearSeries (c j) := by
  simp only [linearSeries, Finset.sum_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

variable {σ : Type*} {R S : Type*} [CommRing R] [CommRing S] {p : ℕ} [Fact p.Prime]

/-- A power series `f` in one variable over `ℂ_[p]` comes from a series over the ring of integers
`valRingCp p` if and only if all its coefficients have norm at most one. -/
lemma mem_range_seriesToCp {f : ℂ_[p]⟦X⟧} :
    f ∈ seriesToCp.range ↔ ∀ n : ℕ, ‖f.coeff n‖ ≤ 1 := by
  constructor
  · rintro ⟨g, rfl⟩ n
    exact (g.coeff (Finsupp.single () n)).property
  · intro hf
    have h_mem (d : Unit →₀ ℕ) : f d ∈ valRingCp p := by
      rw [d.unique_single]
      exact hf (d ())
    exact ⟨fun d ↦ ⟨f d, h_mem d⟩, rfl⟩

lemma map_pderiv (Ψ : R →+* S) (i : σ) (f : MvPowerSeries σ R) :
    MvPowerSeries.map Ψ (pderiv i f) = pderiv i (MvPowerSeries.map Ψ f) := by
  ext
  simp [coeff_pderiv]

@[simp]
lemma isUnit_integer_iff_norm_eq_one {c : valRingCp p} : IsUnit c ↔ ‖(c : ℂ_[p])‖ = 1 :=
  Valued.integer.isUnit_iff_norm_eq_one

@[simp]
lemma constantCoeff_linearSeries [Fintype σ] (c : σ → R) :
    MvPowerSeries.constantCoeff (linearSeries c) = 0 := by
  simp [linearSeries]

end New

end IntegralSeries

/-! ## The chain rule and jets of linear substitutions -/

section JetChainRule

open MvPowerSeries Finset WithPiTopology


/-- Jets of a linear substitution. Let `M` be a matrix and substitute the linear forms
`(M z)_i = ∑_k M_(i k) z_k` into the series `F`. The jet `P(∂) F(M z) (0)` equals the jet of `F`
along `linSubst M P`, the polynomial `P(Mᵀ x)`. -/
lemma New.jet_subst_linearSeries {ι κ R : Type} [CommRing R] [Fintype ι] [Fintype κ]
    (M : Matrix ι κ R) (P : MvPolynomial κ R) :
    ∀ F : MvPowerSeries ι R,
      jet R P (subst (fun i : ι ↦ linearSeries (M i)) F) = jet R (linSubst M P) F := by
  classical
  have hM : HasSubst fun i : ι ↦ linearSeries (M i) :=
    hasSubst_of_constantCoeff_zero fun i ↦ constantCoeff_linearSeries (M i)
  induction P using MvPolynomial.induction_on with
  | C c =>
    intro F
    have h_const : constantCoeff (subst (fun i : ι ↦ linearSeries (M i)) F) = constantCoeff F := by
      rw [constantCoeff_subst hM, finsum_eq_single _ 0 fun d hd ↦ ?_]
      · simp
      obtain ⟨i, hi⟩ : ∃ i : ι, d i ≠ 0 := Finsupp.ne_iff.1 hd
      simp [Finsupp.prod_fintype, prod_eq_zero (mem_univ i), hi]
    simp [jet_eq_sum, h_const]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P k hP =>
    intro F
    -- A factor `X k` acts on the series as `∂_k`, and the chain rule moves the derivative inside.
    have h_chain : pderiv k (subst (fun i : ι ↦ linearSeries (M i)) F) =
        ∑ i : ι, M i k • subst (fun i : ι ↦ linearSeries (M i)) (pderiv i F) := by
      rw [pderiv_subst hM]
      simp [linearSeries, pderiv_X, Pi.single_apply]
    have h_lin : linSubst M (P * .X k) = ∑ i : ι, M i k • (linSubst M P * .X i) := by
      simp [linSubst, mul_sum]
    simp only [h_lin, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, jet_mul_X,
      h_chain, hP]

end JetChainRule

/-! ## The exponential of a series and p-adic norms of factorials -/

section PadicExp

open PowerSeries Nat List

namespace New

variable {p : ℕ} [hp : Fact p.Prime] {σ : Type*}

/-- The series `exp a`, obtained by substituting `a` into the exponential series over `ℂ_[p]`. It is
meaningful when `a` has no constant term. -/
noncomputable abbrev expSubst (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  (exp ℂ_[p]).subst a

/-- The functional equation `exp (a + b) = exp a * exp b` for series `a`, `b` without constant
term. -/
lemma expSubst_add (a : MvPowerSeries σ ℂ_[p]) {b : MvPowerSeries σ ℂ_[p]}
    (ha : a.constantCoeff = 0) (hb : b.constantCoeff = 0) :
    expSubst (a + b) = expSubst a * expSubst b := by
  -- The universal case in two variables: `exp (X 0 + X 1) = exp (X 0) * exp (X 1)`.
  have h_univ : expSubst (.X 0 + .X 1 : MvPowerSeries (Fin 2) ℂ_[p]) =
      expSubst (.X 0) * expSubst (.X 1) := by
    ext e
    -- The coefficients agree: `(m + n).choose m / (m + n)! = 1 / m! * (1 / n!)`.
    rw [coeff_subst_X_zero_add_X_one, coeff_subst_X_zero_subst_mul_X_one]
    simp [cast_add_choose]
    field [factorial_ne_zero]
  -- Substituting `a` for `X 0` and `b` for `X 1` commutes with the exponential.
  have hab : MvPowerSeries.HasSubst ![a, b] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by simp [ha, hb])
  have h_comm (F : MvPowerSeries (Fin 2) ℂ_[p]) (hF : F.constantCoeff = 0) :
      (expSubst F).subst ![a, b] = expSubst (F.subst ![a, b]) :=
    -- `PowerSeries.subst` is `MvPowerSeries.subst` for a family indexed by `Unit`
    MvPowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero hF).const hab _
  simpa [MvPowerSeries.subst_add hab, MvPowerSeries.subst_mul hab, h_comm,
    MvPowerSeries.subst_X hab] using congrArg (MvPowerSeries.subst ![a, b]) h_univ

/-- The exponential of a finite sum of series without constant term is the product of their
exponentials. -/
lemma expSubst_sum {I : Type*} {t : Finset I} {a : I → MvPowerSeries σ ℂ_[p]}
    (h_const : ∀ i : I, (a i).constantCoeff = 0) :
    expSubst (t.sum a) = ∏ i ∈ t, expSubst (a i) := by
  induction t using Finset.cons_induction with
  | empty => simp [subst_zero_eq_C_constantCoeff]
  | cons i t hi ih => simp [expSubst_add _ (h_const i), h_const, ih]

/-- The norm of a nonzero natural number `n` in `ℂ_[p]` is `p ^ (-v_p(n))`. -/
lemma norm_natCast_eq_inv_pow_padicValNat {n : ℕ} (hn : n ≠ 0) :
    ‖(n : ℂ_[p])‖ = (p : ℝ)⁻¹ ^ padicValNat p n := by
  simpa [Padic.norm_eq_zpow_neg_valuation, hn, Nat.padicValNat_def] using
    PadicComplex.norm_extends' p n

/-- The `p`-adic norm of a finite product of nonzero natural numbers. -/
lemma norm_prod_natCast_eq_rpow_neg_sum {X : Type*} [Fintype X] {n : X → ℕ}
    (hn : ∀ x, n x ≠ 0) :
    ‖∏ x, (n x : ℂ_[p])‖ = (p : ℝ) ^ (-∑ x, (padicValNat p (n x) : ℝ)) := by
  simp [norm_natCast_eq_inv_pow_padicValNat, hn, Real.rpow_neg p.cast_nonneg,
    ← Nat.cast_sum, Finset.prod_pow_eq_pow_sum]

/-- For `p` prime and `n < p ^ K` one has `n / (p - 1) - K ≤ v_p(n!) ≤ n / (p - 1)`, a consequence
of Legendre's formula. -/
lemma padicValNat_factorial_mem_Icc {n K : ℕ} (hn : n < p ^ K) :
    (padicValNat p n ! : ℝ) ∈ Set.Icc ((n : ℝ) / (p - 1) - K) (n / (p - 1)) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [Nat.padicValNat_def]
  rw [Set.mem_Icc, Nat.padicValNat_def]
  refine ⟨?_, TauCeti.multiplicity_factorial_le_div p n⟩
  have hlog : Nat.log p n + 1 ≤ K := Nat.succ_le_of_lt (Nat.log_lt_of_lt_pow hn0 hn)
  exact (sub_le_sub_left (by exact_mod_cast hlog) _).trans
    (TauCeti.div_sub_log_le_multiplicity_factorial p n)

/-- Substituting `a` into the rescaled series `f(c X)` is substituting `c • a` into `f`. -/
lemma subst_rescale_eq_subst_smul {c : ℂ_[p]} (a : MvPowerSeries σ ℂ_[p]) (ha : HasSubst a)
    (f : ℂ_[p]⟦X⟧) :
    (rescale c f).subst a = f.subst (c • a) := by
  rw [rescale_eq_subst, subst_comp_subst_apply (.smul_X' c) ha, subst_smul ha, subst_X ha]

end New

end PadicExp

/-! ## Renaming the variables of a jet -/

section JetRename

open MvPolynomial Finsupp

/-- The jet pairing `P(∂)F(0)` of a polynomial `P` with a power series `F` is unchanged when both
are renamed along an injective map `e` of variables; `Q` is the renamed polynomial. -/
lemma New.jet_rename {σ τ R : Type} (e : σ ↪ τ) [CommRing R] {P : MvPolynomial σ R}
    {Q : MvPolynomial τ R} (h : rename e P = Q) (F : MvPowerSeries σ R) :
    jet R Q (F.rename e) = jet R P F := by
  subst h
  induction P using MvPolynomial.induction_on' with
  | monomial d r => simp [rename_monomial, ← embDomain_eq_mapDomain, prod, jet_monomial]
  | add P Q hP hQ => simp [hP, hQ]

end JetRename
