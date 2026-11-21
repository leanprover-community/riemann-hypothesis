import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJLocalFECoeff
import GroundTheory.AutomorphicForms.WhittakerCriterion

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic MeasureTheory Measures GJMatrix Polynomial
open scoped NNReal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

variable (F) in

def IsGammaFactor (π : Representation ℂ (GL (Fin n) F) V) (μ : Measure (GL (Fin n) F))
    (ψ : AddChar F Circle) (γ : RatFunc ℂ) : Prop :=
  ∀ Φ : Matrix (Fin n) (Fin n) F → ℂ, IsSchwartzBruhat Φ → ∀ v : V,
    ∀ ℓ ∈ smoothVectors (Representation.dual π),
      RatFE F γ (zetaIntegral μ Φ (matrixCoeff π v ℓ))
        (fun s => zetaIntegral μ (localMatrixFourier ψ Φ) (fun g => matrixCoeff π v ℓ g⁻¹) (1 - s))

omit [BorelSpace (GL (Fin n) F)] in

theorem IsGammaFactor.smul_measure {μ : Measure (GL (Fin n) F)} {ψ : AddChar F Circle}
    {γ : RatFunc ℂ} (h : IsGammaFactor F π μ ψ γ) (c : ℝ≥0) : IsGammaFactor F π (c • μ) ψ γ := by
  intro Φ hΦ v ℓ hℓ
  refine ((h Φ hΦ v ℓ hℓ).const_mul ((c : ℝ) : ℂ)).congr ⟨0, fun s _ => ?_⟩ ⟨0, fun s _ => ?_⟩
  · rw [zetaIntegral, zetaIntegral, integral_smul_nnreal_measure, NNReal.smul_def,
      Complex.real_smul]
  · rw [zetaIntegral, zetaIntegral, integral_smul_nnreal_measure, NNReal.smul_def,
      Complex.real_smul]


theorem IsGammaFactor.unique [π.IsIrreducible] (hπ : IsAdmissible π) {μ : Measure (GL (Fin n) F)}
    [μ.IsHaarMeasure] {ψ : AddChar F Circle} {γ γ' : RatFunc ℂ} (h : IsGammaFactor F π μ ψ γ)
    (h' : IsGammaFactor F π μ ψ γ') : γ = γ' := by
  classical
  obtain ⟨v₀, hv₀⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have : Nontrivial V := ⟨⟨v₀, 0, hv₀⟩⟩
  have h1 := one_mem_zetaIdeal μ hπ.1 (π := π)
  obtain ⟨R, hR, hR0⟩ : ∃ R ∈ zetaSet π μ, R ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hbot : zetaIdeal π μ = ⊥ := Submodule.span_eq_bot.2 hcon
    rw [hbot, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  obtain ⟨Φ, v, ℓ, hΦ, hℓ, s₀, hZ⟩ := hR
  refine RatFE.unique (h Φ hΦ v ℓ hℓ) (h' Φ hΦ v ℓ hℓ) fun t => ?_
  by_contra hcon
  push Not at hcon
  apply hR0
  refine eq_of_eval_qs_eq_right (F := F) (s₁ := max t s₀) fun s hs => ?_
  rw [max_lt_iff] at hs
  rw [← hZ s hs.2, hcon s hs.1, RatFunc.eval_zero]

variable (F π) in

def gammaFactor (ψ : AddChar F Circle) : RatFunc ℂ := by
  classical
  exact if h : ∃ γ : RatFunc ℂ, IsGammaFactor F π (Measure.haar : Measure (GL (Fin n) F)) ψ γ
    then h.choose else 0





variable (F) in

abbrev qInv : ℂ := ((LocalField.residueCard F : ℂ))⁻¹

omit [MeasurableSpace F] [BorelSpace F] in
theorem qInv_ne_zero : qInv F ≠ 0 :=
  inv_ne_zero (Nat.cast_ne_zero.2 LocalField.residueCard_ne_zero)

omit [MeasurableSpace F] [BorelSpace F] in

theorem qs_one_sub (s : ℂ) : qs F (1 - s) = qInv F / qs F s := by
  have h1 : qs F (1 - s) * qs F s = qs F 1 := by rw [← qs_add, sub_add_cancel]
  have h2 : qs F 1 = qInv F := by rw [qs, Complex.cpow_neg_one]
  rw [eq_div_iff (qs_ne_zero s), h1, h2]

variable (F) in

def dualVar : RatFunc ℂ := RatFunc.C (qInv F) * RatFunc.X⁻¹

variable (F) in

def dualPoly (p : ℂ[X]) : ℂ[X] :=
  ∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i * qInv F ^ i) * X ^ (p.natDegree - i)

omit [MeasurableSpace F] [BorelSpace F] in
theorem eval_dualPoly (p : ℂ[X]) {x : ℂ} (hx : x ≠ 0) :
    (dualPoly F p).eval x = x ^ p.natDegree * p.eval (qInv F / x) := by
  rw [dualPoly, eval_finsetSum, eval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hpow : x ^ p.natDegree = x ^ (p.natDegree - i) * x ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  rw [eval_mul, eval_C, eval_pow, eval_X, hpow, div_pow]
  field_simp

omit [MeasurableSpace F] [BorelSpace F] in
theorem aeval_dualVar (p : ℂ[X]) :
    aeval (dualVar F) p = algebraMap ℂ[X] (RatFunc ℂ) (dualPoly F p) /
      algebraMap ℂ[X] (RatFunc ℂ) (X ^ p.natDegree) := by
  have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  rw [aeval_eq_sum_range, dualPoly, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hpow : (RatFunc.X : RatFunc ℂ) ^ p.natDegree =
      RatFunc.X ^ (p.natDegree - i) * RatFunc.X ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  rw [dualVar, map_mul, map_pow, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X, hpow,
    Algebra.smul_def, RatFunc.algebraMap_eq_C, map_mul, map_pow, mul_pow, inv_pow]
  field_simp

omit [MeasurableSpace F] [BorelSpace F] in
theorem aeval_dualVar_ne_zero {p : ℂ[X]} (hp : p ≠ 0) : aeval (dualVar F) p ≠ 0 := by
  rw [aeval_dualVar]
  refine div_ne_zero ?_ ?_
  · rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))]
    intro h0
    apply hp
    refine Polynomial.eq_zero_of_infinite_isRoot p
      ((Set.finite_singleton (0 : ℂ)).infinite_compl.mono fun y hy => ?_)
    have hy0 : y ≠ 0 := hy
    have hx : qInv F / y ≠ 0 := div_ne_zero (qInv_ne_zero) hy0
    have := eval_dualPoly (F := F) p hx
    rw [h0, eval_zero, div_div_cancel₀ (qInv_ne_zero)] at this
    exact (mul_eq_zero.1 this.symm).resolve_left (pow_ne_zero _ hx)
  · rw [map_pow, RatFunc.algebraMap_X]
    exact pow_ne_zero _ RatFunc.X_ne_zero

variable (F) in

def dualSubst : RatFunc ℂ →ₐ[ℂ] RatFunc ℂ :=
  RatFunc.liftAlgHom (aeval (dualVar F)) fun _ hp =>
    mem_nonZeroDivisors_of_ne_zero (aeval_dualVar_ne_zero (nonZeroDivisors.ne_zero hp))

omit [MeasurableSpace F] [BorelSpace F] in
theorem dualSubst_algebraMap (p : ℂ[X]) :
    dualSubst F (algebraMap ℂ[X] (RatFunc ℂ) p) = aeval (dualVar F) p := by
  have := RatFunc.liftAlgHom_apply_div (φ := aeval (dualVar F)) (hφ := fun _ hp =>
    mem_nonZeroDivisors_of_ne_zero (aeval_dualVar_ne_zero (nonZeroDivisors.ne_zero hp))) p 1
  rw [map_one, div_one, map_one, div_one] at this
  exact this

omit [MeasurableSpace F] [BorelSpace F] in
theorem dualSubst_apply (R : RatFunc ℂ) :
    dualSubst F R = aeval (dualVar F) R.num / aeval (dualVar F) R.denom :=
  RatFunc.liftAlgHom_apply _ _ R

omit [MeasurableSpace F] [BorelSpace F] in

theorem eval_dualSubst (R : RatFunc ℂ) {x : ℂ} (hx : x ≠ 0)
    (hR : R.denom.eval (qInv F / x) ≠ 0) :
    (dualSubst F R).eval (RingHom.id ℂ) x = R.eval (RingHom.id ℂ) (qInv F / x) := by
  have h1 : algebraMap ℂ[X] (RatFunc ℂ) (X ^ R.num.natDegree) ≠ 0 := by
    rw [map_pow, RatFunc.algebraMap_X]; exact pow_ne_zero _ RatFunc.X_ne_zero
  have h2 : algebraMap ℂ[X] (RatFunc ℂ) (X ^ R.denom.natDegree) ≠ 0 := by
    rw [map_pow, RatFunc.algebraMap_X]; exact pow_ne_zero _ RatFunc.X_ne_zero
  have h3 : algebraMap ℂ[X] (RatFunc ℂ) (dualPoly F R.denom) ≠ 0 := by
    have := aeval_dualVar_ne_zero (F := F) R.denom_ne_zero
    intro h
    apply this
    rw [aeval_dualVar, h, zero_div]
  have hθ : dualSubst F R = algebraMap ℂ[X] (RatFunc ℂ) (dualPoly F R.num * X ^ R.denom.natDegree) /
      algebraMap ℂ[X] (RatFunc ℂ) (dualPoly F R.denom * X ^ R.num.natDegree) := by
    rw [dualSubst_apply, aeval_dualVar, aeval_dualVar, map_mul, map_mul]
    field_simp
  have hden : (dualPoly F R.denom * X ^ R.num.natDegree).eval x ≠ 0 := by
    rw [eval_mul, eval_pow, eval_X, eval_dualPoly _ hx]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hx) hR) (pow_ne_zero _ hx)
  rw [hθ, eval_div_algebraMap _ _ hden, eval_mul, eval_mul, eval_pow, eval_pow, eval_X,
    eval_dualPoly _ hx, eval_dualPoly _ hx]
  simp only [RatFunc.eval, eval₂_id]
  field_simp

omit [MeasurableSpace F] [BorelSpace F] in

theorem dualSubst_mem_laurentSubalgebra {L : RatFunc ℂ} (hL : L ∈ laurentSubalgebra) :
    dualSubst F L ∈ laurentSubalgebra := by
  have hX : dualSubst F RatFunc.X = dualVar F := by
    rw [← RatFunc.algebraMap_X, dualSubst_algebraMap, aeval_X]
  have hle : laurentSubalgebra ≤ (laurentSubalgebra).comap (dualSubst F) := by
    rw [laurentSubalgebra, Algebra.adjoin_le_iff]
    rintro y (rfl | rfl)
    · rw [SetLike.mem_coe, Subalgebra.mem_comap, hX, dualVar]
      exact mul_mem (C_mem_laurentSubalgebra _) X_inv_mem_laurentSubalgebra
    · rw [SetLike.mem_coe, Subalgebra.mem_comap, map_inv₀, hX, dualVar, mul_inv, inv_inv,
        ← map_inv₀]
      exact mul_mem (C_mem_laurentSubalgebra _) X_mem_laurentSubalgebra
  exact hle hL

omit [MeasurableSpace F] [BorelSpace F] in

theorem exists_eq_C_mul_X_pow_of_mem {ε : RatFunc ℂ} (h : ε ∈ laurentSubalgebra)
    (h' : ε⁻¹ ∈ laurentSubalgebra) (hε : ε ≠ 0) :
    ∃ (r : ℂ) (i a : ℕ), r ≠ 0 ∧
      ε = algebraMap ℂ[X] (RatFunc ℂ) (C r * X ^ i) / algebraMap ℂ[X] (RatFunc ℂ) (X ^ a) := by
  obtain ⟨P₁, a, h1⟩ := mem_laurentSubalgebra_iff.1 h
  obtain ⟨P₂, b, h2⟩ := mem_laurentSubalgebra_iff.1 h'
  have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have e1 : algebraMap ℂ[X] (RatFunc ℂ) P₁ = ε * RatFunc.X ^ a := by
    rw [h1, div_mul_cancel₀ _ (pow_ne_zero _ hX)]
  have e2 : algebraMap ℂ[X] (RatFunc ℂ) P₂ = ε⁻¹ * RatFunc.X ^ b := by
    rw [h2, div_mul_cancel₀ _ (pow_ne_zero _ hX)]
  have hprod : P₁ * P₂ = X ^ (a + b) := by
    apply IsFractionRing.injective ℂ[X] (RatFunc ℂ)
    rw [map_mul, e1, e2, map_pow, RatFunc.algebraMap_X, pow_add]
    field_simp
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow Polynomial.prime_X (a + b)).1 ⟨P₂, hprod.symm⟩
  obtain ⟨u, hu⟩ := hi
  obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.1 (u⁻¹).isUnit
  have hP₁ : P₁ = C r * X ^ i := by
    rw [hru, ← hu, mul_comm P₁ (u : ℂ[X]), ← mul_assoc, Units.inv_mul, one_mul]
  exact ⟨r, i, a, hr.ne_zero, by rw [h1, hP₁, map_pow, RatFunc.algebraMap_X]⟩

section Contragredient

variable [π.IsIrreducible] (hπ : IsAdmissible π) {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]
  {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {γ : RatFunc ℂ}
  (hγ : IsGammaFactor F π μ ψ γ)
include hπ hψ hψ1 hγ





end Contragredient

variable (F π) in

def epsilonFactor (ψ : AddChar F Circle) : RatFunc ℂ :=
  gammaFactor F π ψ *
    dualSubst F (algebraMap ℂ[X] (RatFunc ℂ) (LPolynomial (contragredient π))) /
      algebraMap ℂ[X] (RatFunc ℂ) (LPolynomial π)


end GodementJacquet

end GroundTheory.Automorphic
