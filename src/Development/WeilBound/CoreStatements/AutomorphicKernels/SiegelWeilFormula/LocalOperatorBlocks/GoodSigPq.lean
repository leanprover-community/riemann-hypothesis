import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.ContinuousWeightFactorUnitary
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.EqZeroOfEvalReal
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.IsUnitDenominatorBasePoint
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.LocOpCont
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocOpMMLaw
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocalOperatorLongWeylIntegral

section
noncomputable section

open MeasureTheory Matrix PositivityTheory.Rg.Sw
open scoped Matrix ComplexConjugate

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

theorem gramX_tr_g (x : Fin m → Fin n → ℂ) (j i : Fin n) :
    gramX (fun _ : Fin m => true) x j i = ∑ a, star (x a j) * x a i := by
  simp [PositivityTheory.Rg.Sw.gramX, PositivityTheory.Rg.Sw.evX, PositivityTheory.Rg.Sw.Qp,
    PositivityTheory.Rg.Sw.Qb]

end PositivityTheory.SiegelWeilFormula.KLI

end
end

section
noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

private theorem star_mulVec_dotProduct_mulVec_conj (U M : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) :
    star (U *ᵥ y) ⬝ᵥ (M *ᵥ (U *ᵥ y)) = star y ⬝ᵥ ((star U * M * U) *ᵥ y) := by
  simp [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec,
    Matrix.star_eq_conjTranspose, Matrix.mul_assoc]

private theorem integral_comp_unitary_mulVec (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℂ) : ∫ y, f (U *ᵥ y) = ∫ v, f v := by
  have hn : Complex.normSq U.det = 1 := by
    have h := Matrix.det_of_mem_unitary hU
    have h2 : star U.det * U.det = 1 := Unitary.star_mul_self_of_mem h
    have h3 : ((Complex.normSq U.det : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      exact h2
    exact_mod_cast h3
  have hsU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hUs : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  let e : (Fin n → ℂ) ≃ᵐ (Fin n → ℂ) :=
    { toFun := fun y => U *ᵥ y
      invFun := fun v => star U *ᵥ v
      left_inv := fun y => by simp [Matrix.mulVec_mulVec, hsU]
      right_inv := fun v => by simp [Matrix.mulVec_mulVec, hUs]
      measurable_toFun := (Continuous.matrix_mulVec continuous_const continuous_id).measurable
      measurable_invFun := (Continuous.matrix_mulVec continuous_const continuous_id).measurable }
  let L : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := (Matrix.toLin' U).restrictScalars ℝ
  have hdet : LinearMap.det L = 1 := by
    simp only [L]
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hn]
  have hmap : MeasureTheory.Measure.map (⇑e) MeasureTheory.volume = MeasureTheory.volume := by
    have he : (⇑e) = ⇑L := by
      funext y
      rfl
    rw [he, MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar _
      (by rw [hdet]; exact one_ne_zero), hdet]
    simp
  have h := MeasureTheory.integral_map_equiv (μ := MeasureTheory.volume) e f
  rw [hmap] at h
  exact h.symm

private theorem star_dotProduct_diagonal_mulVec_eq_sum (d y : Fin n → ℂ) :
    star y ⬝ᵥ (Matrix.diagonal d *ᵥ y) = ∑ k, d k * ((‖y k‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp only [RCLike.star_def]
  ring

private theorem integral_cexp_diagonal_eq_prod_pi_div (d : Fin n → ℂ) (hd : ∀ k, 0 < (-d k).re) :
    ∫ y : Fin n → ℂ, Complex.exp (∑ k, d k * ((‖y k‖ ^ 2 : ℝ) : ℂ)) = ∏ k, (Real.pi : ℂ) / (-d k) := by
  simp_rw [Complex.exp_sum]
  rw [integral_fintype_prod_volume_eq_prod
    (f := fun k (z : ℂ) => Complex.exp (d k * ((‖z‖ ^ 2 : ℝ) : ℂ)))]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hf : (fun z : ℂ => Complex.exp (d k * ((‖z‖ ^ 2 : ℝ) : ℂ))) =
      fun z : ℂ => Complex.exp (-(-d k) * (‖z‖ : ℂ) ^ 2) := by
    funext z
    push_cast
    ring_nf
  rw [hf, GaussianFourier.integral_cexp_neg_mul_sq_norm (hd k)]
  simp

private theorem integral_cexp_quadratic_mul_det_neg_eq_pi_pow (M U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (d : Fin n → ℂ) (hd : ∀ k, 0 < (-d k).re) (hM : star U * M * U = Matrix.diagonal d) :
    (∫ v : Fin n → ℂ, Complex.exp (star v ⬝ᵥ (M *ᵥ v))) * (-M).det = (Real.pi : ℂ) ^ n := by
  rw [← integral_comp_unitary_mulVec U hU]
  simp only [star_mulVec_dotProduct_mulVec_conj, hM, star_dotProduct_diagonal_mulVec_eq_sum]
  rw [integral_cexp_diagonal_eq_prod_pi_div d hd]
  have hsU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hdet : (-M).det = ∏ k, (-d k) := by
    have h1 : (star U * (-M) * U).det = (-M).det := by
      rw [Matrix.det_mul, Matrix.det_mul, mul_comm (star U).det, mul_assoc, ← Matrix.det_mul, hsU,
        Matrix.det_one, mul_one]
    have h2 : -Matrix.diagonal d = Matrix.diagonal (fun k => -d k) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [Matrix.diagonal_apply_ne _ hij]
    rw [← h1, Matrix.mul_neg, Matrix.neg_mul, hM, h2, Matrix.det_diagonal]
  rw [hdet, ← Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl fun k _ => div_mul_cancel₀ (Real.pi : ℂ) (fun h => by
    have := hd k
    rw [h] at this
    simp at this)]
  simp

private theorem evX_one_mul_gs_mul_cexp_eq_prod (b : Matrix (Fin n) (Fin n) ℂ) (c t : ℝ) (x : Fin m → Fin n → ℂ) :
    evX (1 : PX m n) x * gs c x * Complex.exp (Complex.I * ↑t * (b * gramX (fun _ : Fin m => true) x).trace)
      = ∏ a, Complex.exp (star (x a) ⬝ᵥ
          ((-(c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (Complex.I * (t : ℂ)) • bᵀ) *ᵥ x a)) := by
  have hn : ∀ z : ℂ, (‖z‖ : ℂ) ^ 2 = star z * z := by
    intro z
    have := Complex.normSq_eq_norm_sq z
    rw [← Complex.ofReal_pow, ← this, Complex.normSq_eq_conj_mul_self]
    rfl
  rw [← Complex.exp_sum]
  simp only [evX, map_one, one_mul, gs]
  rw [← Complex.exp_add]
  congr 1
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_smul,
    Finset.sum_add_distrib, Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX_tr_g, dotProduct, Matrix.mulVec,
    Matrix.transpose_apply, Pi.star_apply, smul_eq_mul, Pi.smul_apply]
  push_cast
  simp only [hn, Finset.mul_sum, Finset.sum_neg_distrib, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.transpose_apply, smul_eq_mul, mul_add, add_mul, Finset.sum_add_distrib, ite_mul, mul_ite, zero_mul,
    mul_zero, mul_one, one_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · conv_lhs => enter [2, y]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring

private theorem F0_jG_mul_nG_eq (sg : ℤˣ) (e : ℤ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) :
    F0 (pOf sg m) (qOf sg m) e (jG n * nG b) =
      (JJ n).det ^ e * ((-(Complex.I * ((sg : ℤ) : ℂ))) ^ n *
        (1 - (Complex.I * ((sg : ℤ) : ℂ)) • b).det) ^ (-(m : ℤ)) := by
  have hmR : mR (jG n * nG b) = Matrix.fromBlocks 0 1 (-1) (-b) := by
    rw [mR_mul, mR_jG, mR_nG hb]
    simp [JJ, nU, Matrix.fromBlocks_multiply]
  have hD : (mR (jG n * nG b)).det = (JJ n).det := by
    rw [mR_mul, mR_jG, mR_nG hb, Matrix.det_mul]
    simp [nU, Matrix.det_fromBlocks_zero₂₁]
  simp only [F0, f0, u1, u2]
  rw [hD, hmR]
  simp only [Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  rcases Int.units_eq_one_or sg with rfl | rfl
  · simp only [pOf, qOf, if_true]
    have hM : Complex.I • (-1 : Matrix (Fin n) (Fin n) ℂ) + -b =
        (-(Complex.I * (((1 : ℤˣ) : ℤ) : ℂ))) • (1 - (Complex.I * (((1 : ℤˣ) : ℤ) : ℂ)) • b) := by
      ext i j
      simp [Matrix.one_apply]
      split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring
    rw [hM, Matrix.det_smul, Fintype.card_fin]
    simp
  · simp only [pOf, qOf]
    have hne : (-1 : ℤˣ) ≠ 1 := by decide
    simp only [hne, if_false]
    have hM : -(Complex.I • (-1 : Matrix (Fin n) (Fin n) ℂ)) + -b =
        (-(Complex.I * (((-1 : ℤˣ) : ℤ) : ℂ))) • (1 - (Complex.I * (((-1 : ℤˣ) : ℤ) : ℂ)) • b) := by
      ext i j
      simp [Matrix.one_apply]
      split_ifs <;> ring_nf <;> simp [Complex.I_sq] <;> ring
    rw [hM, Matrix.det_smul, Fintype.card_fin]
    simp

theorem gauss_cell (sg : ℤˣ) (e : ℤ) : ∃ κ : ℂ, κ ≠ 0 ∧ ∀ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b →
    F0 (pOf sg m) (qOf sg m) e (jG n * nG b) =
      κ * secN (fun _ : Fin m => true) (2 * Real.pi) (2 * Real.pi * ((sg : ℤ) : ℝ)) (1 : PX m n) b := by
  have hs : ((sg : ℤ) : ℂ) = 1 ∨ ((sg : ℤ) : ℂ) = -1 := by
    rcases Int.units_eq_one_or sg with h | h <;> simp [h]
  have hIs : Complex.I * ((sg : ℤ) : ℂ) ≠ 0 := by
    rcases hs with h | h <;> simp [h, Complex.I_ne_zero]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : (((2 * Real.pi : ℝ)) : ℂ) ≠ 0 := by
    push_cast
    exact mul_ne_zero two_ne_zero hpi
  refine ⟨(JJ n).det ^ e * ((-(Complex.I * ((sg : ℤ) : ℂ))) ^ n) ^ (-(m : ℤ)) *
      ((((2 * Real.pi : ℝ)) : ℂ) ^ n / (Real.pi : ℂ) ^ n) ^ m, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (zpow_ne_zero _ JJ_det_ne)
      (zpow_ne_zero _ (pow_ne_zero _ (neg_ne_zero.mpr hIs))))
      (pow_ne_zero _ (div_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ hpi)))
  · intro b hb
    have hA : bᵀ.IsHermitian := (show b.IsHermitian from hb).transpose
    have hU : (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ :=
      hA.eigenvectorUnitary.2
    have hsU : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
    have hspec : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * bᵀ *
        (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues) := by
      have := hA.conjStarAlgAut_star_eigenvectorUnitary
      simpa [Unitary.conjStarAlgAut_apply, mul_assoc] using this
    have hMd : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        (-(((2 * Real.pi : ℝ)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
          (Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ)) • bᵀ) *
        (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.diagonal (fun k => -(((2 * Real.pi : ℝ)) : ℂ) +
          Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ) * (hA.eigenvalues k : ℂ)) := by
      have e1 : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
          (-(((2 * Real.pi : ℝ)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
            (Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ)) • bᵀ) *
          (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
          -(((2 * Real.pi : ℝ)) : ℂ) • (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
            (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) +
          (Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ)) •
            (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * bᵀ *
              (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      rw [e1, hsU, hspec]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    have hd : ∀ k, 0 < (-(-(((2 * Real.pi : ℝ)) : ℂ) +
        Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ) * (hA.eigenvalues k : ℂ))).re := by
      intro k
      simp [Complex.mul_re]
      exact Real.pi_pos
    have hJ := integral_cexp_quadratic_mul_det_neg_eq_pi_pow _ _ hU _ hd hMd
    have hnegM : -(-(((2 * Real.pi : ℝ)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ)) • bᵀ) =
        (((2 * Real.pi : ℝ)) : ℂ) • (1 - (Complex.I * ((sg : ℤ) : ℂ)) • b)ᵀ := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
        ring
      · simp [Matrix.one_apply_ne hij]
        ring
    rw [hnegM, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin] at hJ
    have hsec : secN (fun _ : Fin m => true) (2 * Real.pi) (2 * Real.pi * ((sg : ℤ) : ℝ)) (1 : PX m n) b =
        (∫ v : Fin n → ℂ, Complex.exp (star v ⬝ᵥ
          ((-(((2 * Real.pi : ℝ)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
            (Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ)) • bᵀ) *ᵥ v))) ^ m := by
      simp only [secN]
      simp only [evX_one_mul_gs_mul_cexp_eq_prod]
      have hp := integral_fintype_prod_volume_eq_pow (ι := Fin m) (fun v : Fin n → ℂ =>
        Complex.exp (star v ⬝ᵥ ((-(((2 * Real.pi : ℝ)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
            (Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ)) • bᵀ) *ᵥ v)))
      rw [Fintype.card_fin] at hp
      exact hp
    rw [F0_jG_mul_nG_eq sg e b hb, hsec]
    generalize (∫ v : Fin n → ℂ, Complex.exp (star v ⬝ᵥ
          ((-(((2 * Real.pi : ℝ)) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
            (Complex.I * (((2 * Real.pi * ((sg : ℤ) : ℝ)) : ℝ) : ℂ)) • bᵀ) *ᵥ v))) = J at hJ ⊢
    generalize (1 - (Complex.I * ((sg : ℤ) : ℂ)) • b).det = Δ at hJ ⊢
    have hΔ : Δ ≠ 0 := by
      rintro rfl
      simp at hJ
      exact pow_ne_zero _ hpi hJ.symm
    have hJ' : J = (Real.pi : ℂ) ^ n / ((((2 * Real.pi : ℝ)) : ℂ) ^ n * Δ) :=
      eq_div_of_mul_eq (mul_ne_zero (pow_ne_zero _ h2) hΔ) hJ
    rw [hJ', mul_zpow, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    field_simp
    rw [mul_assoc, mul_assoc, ← mul_pow, ← mul_pow]
    have hx : Δ * ((((2 * Real.pi : ℝ)) : ℂ) ^ n / (Real.pi : ℂ) ^ n *
        ((Real.pi : ℂ) ^ n / ((((2 * Real.pi : ℝ)) : ℂ) ^ n * Δ))) = 1 := by
      field_simp
    rw [hx, one_pow, mul_one]

theorem vac_unique (sg : ℤˣ) (e : ℤ) (S : GR n → ℂ) (C : ℂ) (hS : Continuous S) (h1 : S 1 = 1)
    (hlaw : ∀ y g : GR n, (mR y).toBlocks₂₁ = 0 → S (y * g) = F0 (pOf sg m) (qOf sg m) e y * S g)
    (hcell : ∀ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b →
      S (jG n * nG b) = C * secN (fun _ : Fin m => true) (2 * Real.pi) (2 * Real.pi * ((sg : ℤ) : ℝ)) (1 : PX m n) b) :
    ∀ g, S g = F0 (pOf sg m) (qOf sg m) e g := by
  obtain ⟨κ, hκ, hF⟩ := gauss_cell (m := m) (n := n) sg e
  have hpar : ∀ (a b : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → bᴴ = b →
      (mR (mG a * nG b)).toBlocks₂₁ = 0 := by
    intro a b ha hb
    rw [mR_mul, mR_mG ha, mR_nG hb, lower_left_block_mul]
    simp [mLc, nU]
  have hbig : Set.EqOn S (fun g => (C / κ) * F0 (pOf sg m) (qOf sg m) e g)
      {g : GR n | IsUnit (Matrix.toBlocks₂₁ (mR g)).det} := by
    intro g hg
    obtain ⟨a, b, b', ha, hb, hb', rfl⟩ := big_eq g hg
    have hy := hpar a b ha hb
    have hassoc : mG a * nG b * jG n * nG b' = (mG a * nG b) * (jG n * nG b') := by
      simp only [mul_assoc]
    simp only
    rw [hassoc, hlaw _ _ hy, weight_factor_mul_parabolic _ _ _ _ _ hy, hcell b' hb', hF b' hb']
    field_simp
  have hall : S = fun g => (C / κ) * F0 (pOf sg m) (qOf sg m) e g :=
    Continuous.ext_on dense_big hS (continuous_const.mul (continuous_weight_factor_unitary _ _ _)) hbig
  have h1' := congrFun hall 1
  rw [h1, weight_factor_one, mul_one] at h1'
  intro g
  rw [hall, ← h1']
  simp

end PositivityTheory.SiegelWeilFormula.KLI

end
end

section
noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

variable {sg : ℤˣ} {L : LOp m n}

def nbM (c : Matrix (Fin n) (Fin n) ℂ) : M2 n := Matrix.fromBlocks 1 0 c 1

theorem inG_nbM {c : Matrix (Fin n) (Fin n) ℂ} (hc : cᴴ = c) : InG (nbM c) := by
  unfold InG nbM JJ
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hc]

theorem nbM_inv (c : Matrix (Fin n) (Fin n) ℂ) : (nbM c)⁻¹ = nbM (-c) := by
  apply Matrix.inv_eq_left_inv
  unfold nbM
  rw [Matrix.fromBlocks_multiply]
  simp

theorem nb_eq {c : Matrix (Fin n) (Fin n) ℂ} (hc : cᴴ = c) (hu : IsUnit c.det) :
    toGR (nbM c) (inG_nbM hc) = mG (-c⁻¹) * nG c * jG n * nG c⁻¹ := by
  have hci : (c⁻¹)ᴴ = c⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hc]
  have hnu : IsUnit (-c⁻¹).det := by
    rw [Matrix.det_neg]
    exact ((isUnit_one.neg).pow _).mul (Matrix.isUnit_nonsing_inv_det c hu)
  apply mR_injective
  rw [mR_toGR, mR_mul, mR_mul, mR_mul, mR_mG hnu, mR_nG hc, mR_jG, mR_nG hci]
  have h1 : c⁻¹ * c = 1 := Matrix.nonsing_inv_mul c hu
  have h2 : c * c⁻¹ = 1 := Matrix.mul_nonsing_inv c hu
  have h3 : ((-c⁻¹)ᴴ)⁻¹ = -c := by
    rw [Matrix.conjTranspose_neg, hci]
    exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, h2])
  unfold nbM mLc nU JJ
  rw [h3]
  simp only [Matrix.fromBlocks_multiply]
  simp [h1, h2, Matrix.neg_mul, Matrix.mul_neg]

def dT (i0 : Fin n) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => if i = i0 then (t : ℂ) else 1

theorem dT_herm (i0 : Fin n) (t : ℝ) : (dT i0 t)ᴴ = dT i0 t := by
  unfold dT
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : i = i0 <;> simp [h]

theorem dT_det (i0 : Fin n) (t : ℝ) : (dT i0 t).det = t := by
  simp [dT, Matrix.det_diagonal]

def pth (i0 : Fin n) (t : ℝ) : GR n :=
  toGR (nbM (-dT i0 t)) (inG_nbM (by rw [Matrix.conjTranspose_neg, dT_herm]))

theorem pth_cont (i0 : Fin n) : Continuous (pth i0) := by
  have hdT : Continuous fun t : ℝ => dT i0 t := by
    unfold dT
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    by_cases h : i = i0
    · simp only [h, if_true]
      exact Complex.continuous_ofReal
    · simp only [h, if_false]
      exact continuous_const
  have hnb : ∀ f : ℝ → Matrix (Fin n) (Fin n) ℂ, Continuous f → Continuous fun t => nbM (f t) := by
    intro f hf
    unfold nbM
    exact continuous_const.matrix_fromBlocks continuous_const hf continuous_const
  unfold pth toGR
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · show Continuous fun t => nbM (-dT i0 t)
    exact hnb _ hdT.neg
  · show Continuous fun t => (nbM (-dT i0 t))⁻¹
    simp only [nbM_inv, neg_neg]
    exact hnb _ hdT

theorem weight_factor_ne_zero (p q : ℕ) (e : ℤ) (g : GR n) : F0 p q e g ≠ 0 := by
  unfold F0 f0
  have h1 : Matrix.det (mR g) ≠ 0 := (det_ne_of_inG (M := mR g) g.2).ne_zero
  exact mul_ne_zero (zpow_ne_zero _ h1)
    (mul_ne_zero (zpow_ne_zero _ (automorphy_first_det_ne_zero g)) (zpow_ne_zero _ (automorphy_second_det_ne_zero g)))

theorem pq_sum (sg : ℤˣ) (m : ℕ) : ((pOf sg m : ℕ) : ℤ) + (qOf sg m : ℕ) = m := by
  unfold pOf qOf
  split_ifs <;> simp

theorem lower_left_block_levi_unipotent (a b : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) (hb : bᴴ = b) :
    (mR (mG a * nG b)).toBlocks₂₁ = 0 := by
  rw [mR_mul, mR_mG ha, mR_nG hb, lower_left_block_mul]
  simp [mLc, nU]

theorem S_law (h : LocHyp sg L) {k : ℤ}
    (hk : ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mLc a → ∀ f, IsSw f →
      L y f = fun u => (a.det / (‖a.det‖ : ℂ)) ^ k * (‖a.det‖ : ℂ) ^ m * f (Matrix.of u * a))
    (a b : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) (hb : bᴴ = b) (g : GR n) :
    L (mG a * nG b * g) (fP 1) 0 = (a.det / (‖a.det‖ : ℂ)) ^ k * (‖a.det‖ : ℂ) ^ m * L g (fP 1) 0 := by
  have hf := isSw_fP (1 : PX m n)
  have hz : ∀ F : (Fin m → Fin n → ℂ) → ℂ, F (Matrix.of (0 : Fin m → Fin n → ℂ) * a) = F 0 := by
    intro F
    congr 1
    exact Matrix.zero_mul a
  have e2 : L (nG b * g) (fP 1) (Matrix.of (0 : Fin m → Fin n → ℂ) * a) = L g (fP 1) 0 := by
    refine (hz _).trans ?_
    rw [h.mul _ _ _ hf, h.nU (nG b) b hb (mR_nG hb) _ (h.sw _ _ hf)]
    simp
  have e1 := congrFun (hk (mG a) a ha (mR_mG ha) _ (h.sw (nG b * g) _ hf)) 0
  rw [mul_assoc, h.mul _ _ _ hf, e1]
  show _ * _ * L (nG b * g) (fP 1) (Matrix.of (0 : Fin m → Fin n → ℂ) * a) = _
  rw [e2]

theorem S_cell (h : LocHyp sg L) {C : ℂ}
    (hJ : ∀ y : GR n, mR y = JJ n → ∀ f, IsSw f → L y f 0 = C * ∫ v, f v)
    (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) :
    L (jG n * nG b) (fP (1 : PX m n)) 0 =
      C * secN (fun _ : Fin m => true) (2 * Real.pi) (2 * Real.pi * ((sg : ℤ) : ℝ)) (1 : PX m n) b := by
  have hf := isSw_fP (1 : PX m n)
  rw [h.mul _ _ _ hf, hJ (jG n) mR_jG _ (h.sw _ _ hf), h.nU (nG b) b hb (mR_nG hb) _ hf]
  unfold secN fP
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only
  rw [gramX_true]
  have e : Complex.I * ((2 * Real.pi * (((sg : ℤ) : ℝ)) : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * (((sg : ℤ) : ℂ)) := by
    push_cast
    ring
  rw [e]
  ring

theorem even_im_hermitian_sub (h : LocHyp sg L) (hn : 0 < n) {k : ℤ}
    (hk : ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mLc a → ∀ f, IsSw f →
      L y f = fun u => (a.det / (‖a.det‖ : ℂ)) ^ k * (‖a.det‖ : ℂ) ^ m * f (Matrix.of u * a)) :
    Even (k - m) := by
  obtain i0 : Fin n := ⟨0, hn⟩
  obtain ⟨C, hC0, hJ⟩ := h.longWeylFunctional
  obtain ⟨κ, hκ0, hκ⟩ := gauss_cell (m := m) (n := n) sg 0
  have key : ∀ t : ℝ, t ≠ 0 →
      L (pth i0 t) (fP 1) 0 * κ * star ((t : ℂ)⁻¹) ^ (m : ℤ) =
        F0 (pOf sg m) (qOf sg m) 0 (pth i0 t) * C *
          (((t : ℂ)⁻¹ / (‖(t : ℂ)⁻¹‖ : ℂ)) ^ k * (‖(t : ℂ)⁻¹‖ : ℂ) ^ m) := by
    intro t ht
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    have hc : (-dT i0 t)ᴴ = -dT i0 t := by rw [Matrix.conjTranspose_neg, dT_herm]
    have hdc : (-dT i0 t).det = (-1) ^ n * (t : ℂ) := by
      rw [Matrix.det_neg, dT_det, Fintype.card_fin]
    have hu : IsUnit (-dT i0 t).det := by
      rw [hdc]
      exact isUnit_iff_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (by norm_num)) ht')
    have hci : ((-dT i0 t)⁻¹)ᴴ = (-dT i0 t)⁻¹ := by
      rw [Matrix.conjTranspose_nonsing_inv, hc]
    have hd : (-(-dT i0 t)⁻¹).det = (t : ℂ)⁻¹ := by
      rw [Matrix.det_neg, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hdc, Fintype.card_fin,
        mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num)), one_mul]
    have hnu : IsUnit (-(-dT i0 t)⁻¹).det := by
      rw [hd]
      exact isUnit_iff_ne_zero.2 (inv_ne_zero ht')
    have hp : pth i0 t = mG (-(-dT i0 t)⁻¹) * nG (-dT i0 t) * jG n * nG (-dT i0 t)⁻¹ :=
      nb_eq hc hu
    rw [hp, mul_assoc (mG _ * nG _) (jG n) _, S_law h hk _ _ hnu hc, S_cell h hJ _ hci,
      weight_factor_mul_parabolic _ _ _ _ _ (lower_left_block_levi_unipotent _ _ hnu hc), weight_factor_levi_unipotent _ _ _ _ _ hnu hc, hκ _ hci, hd, pq_sum]
    simp only [zpow_zero, one_mul, sub_zero]
    ring
  have hpos : ∀ t : ℝ, 0 < t →
      L (pth i0 t) (fP 1) 0 * κ = F0 (pOf sg m) (qOf sg m) 0 (pth i0 t) * C := by
    intro t ht
    have e := key t ht.ne'
    have hr : ((t : ℂ))⁻¹ = ((t⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    have hr0 : ((t⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast inv_ne_zero ht.ne'
    rw [hr, Complex.star_def, Complex.conj_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.2 ht.le), div_self hr0, one_zpow, one_mul, zpow_natCast] at e
    apply mul_right_cancel₀ (pow_ne_zero m hr0)
    rw [e]
  have hneg : ∀ t : ℝ, t < 0 →
      L (pth i0 t) (fP 1) 0 * κ = (-1) ^ k * (-1) ^ m * (F0 (pOf sg m) (qOf sg m) 0 (pth i0 t) * C) := by
    intro t ht
    have e := key t ht.ne
    have hr : ((t : ℂ))⁻¹ = ((t⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    have hr0 : ((t⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast inv_ne_zero ht.ne
    rw [hr, Complex.star_def, Complex.conj_ofReal, Complex.norm_real,
      Real.norm_of_nonpos (inv_nonpos.2 ht.le), Complex.ofReal_neg, div_neg, div_self hr0,
      neg_pow, zpow_natCast] at e
    apply mul_right_cancel₀ (pow_ne_zero m hr0)
    rw [e]
    ring
  have hφ : Continuous fun t : ℝ => L (pth i0 t) (fP 1) 0 * κ :=
    ((h.cont 1 0).comp (pth_cont i0)).mul continuous_const
  have hψ : Continuous fun t : ℝ => F0 (pOf sg m) (qOf sg m) 0 (pth i0 t) * C :=
    ((continuous_weight_factor_unitary _ _ _).comp (pth_cont i0)).mul continuous_const
  have hs : Filter.Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hs' : Filter.Tendsto (fun j : ℕ => -(1 / ((j : ℝ) + 1))) Filter.atTop (nhds 0) := by
    simpa using hs.neg
  have hpos' : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 1) := fun j => by positivity
  have e1 : L (pth i0 0) (fP 1) 0 * κ = F0 (pOf sg m) (qOf sg m) 0 (pth i0 0) * C := by
    have A := (hφ.tendsto 0).comp hs
    have B := (hψ.tendsto 0).comp hs
    refine tendsto_nhds_unique A ?_
    refine B.congr (fun j => ?_)
    exact (hpos _ (hpos' j)).symm
  have e2 : L (pth i0 0) (fP 1) 0 * κ =
      (-1) ^ k * (-1) ^ m * (F0 (pOf sg m) (qOf sg m) 0 (pth i0 0) * C) := by
    have A := (hφ.tendsto 0).comp hs'
    have B := ((hψ.tendsto 0).comp hs').const_mul ((-1 : ℂ) ^ k * (-1) ^ m)
    refine tendsto_nhds_unique A ?_
    refine B.congr (fun j => ?_)
    exact (hneg _ (neg_neg_of_pos (hpos' j))).symm
  have hψ0 : F0 (pOf sg m) (qOf sg m) 0 (pth i0 0) * C ≠ 0 := mul_ne_zero (weight_factor_ne_zero _ _ _ _) hC0
  have hε : ((-1 : ℂ)) ^ k * (-1) ^ m = 1 := by
    rw [e1] at e2
    have := mul_right_cancel₀ hψ0 (e2.symm.trans (one_mul _).symm)
    exact this
  rcases Int.even_or_odd (k - m) with he | ho
  · exact he
  · exfalso
    have h1 : ((-1 : ℂ)) ^ (k - m) = -1 := ho.neg_one_zpow
    have h2 : ((-1 : ℂ)) ^ k = (-1) ^ (k - m) * (-1) ^ m := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 1
      ring
    rw [h2, h1] at hε
    have h3 : ((-1 : ℂ)) ^ m * (-1) ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    have : (-1 : ℂ) = 1 := by linear_combination hε + h3
    norm_num at this

theorem LocHyp.mM' (h : LocHyp sg L) : ∃ e : ℤ, ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det →
    mR y = mLc a → ∀ f, IsSw f → L y f = fun u => a.det ^ e * (star a.det) ^ ((m : ℤ) - e) * f (Matrix.of u * a) := by
  obtain ⟨k, hk⟩ := h.mM
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    refine ⟨0, fun y a ha hy f hf => ?_⟩
    rw [hk y a ha hy f hf]
    simp [Matrix.det_isEmpty]
  · obtain ⟨j, hj⟩ := even_im_hermitian_sub h hn hk
    refine ⟨m + j, fun y a ha hy f hf => ?_⟩
    rw [hk y a ha hy f hf]
    funext u
    congr 1
    have hz : a.det ≠ 0 := ha.ne_zero
    have hr : (‖a.det‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
    have hs : star a.det = (‖a.det‖ : ℂ) * (‖a.det‖ : ℂ) * (a.det)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hz, mul_comm, Complex.star_def, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [hs, show k = (m : ℤ) + (j + j) by omega, show (m : ℤ) - (m + j) = -j by ring]
    have hzj := zpow_ne_zero j hz
    have hrj := zpow_ne_zero j hr
    rw [div_zpow, zpow_add₀ hz, zpow_add₀ hz, zpow_add₀ hr, zpow_add₀ hr, zpow_add₀ hz,
      zpow_natCast, zpow_natCast, zpow_neg, mul_zpow, mul_zpow, inv_zpow]
    field_simp

end PositivityTheory.SiegelWeilFormula.KLI

end
end

section
noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

variable {sg : ℤˣ} {L : LOp m n}

theorem L_fP_lin (h : LocHyp sg L) (y : GR n) (a : ℂ) (P Q : PX m n) :
    L y (fP (a • P + Q)) = a • L y (fP P) + L y (fP Q) := by
  rw [fP_add_smul]
  exact h.lin y a _ _ (isSw_fP P) (isSw_fP Q)

theorem L_fP_zero (h : LocHyp sg L) (y : GR n) : L y (fP (0 : PX m n)) = 0 := by
  have e := L_fP_lin h y 1 0 0
  simp only [one_smul, add_zero] at e
  have : L y (fP (0 : PX m n)) + L y (fP 0) - L y (fP 0) = L y (fP 0) := by abel
  rw [← e] at this
  simpa using this.symm

def sLOf (h : LocHyp sg L) : PX m n →ₗ[ℂ] (GR n → ℂ) where
  toFun P y := L y (fP P) 0
  map_add' P Q := by
    funext y
    have e := L_fP_lin h y 1 P Q
    simp only [one_smul] at e
    simp [e]
  map_smul' a P := by
    funext y
    have e := L_fP_lin h y a P 0
    simp only [add_zero, L_fP_zero h] at e
    simp [e]

open scoped Classical in

def rhoFun (h : LocHyp sg L) (k : GR n) (P : PX m n) : PX m n :=
  if hk : InK (mR k) then Classical.choose (k_poly h k hk P) else 0

open scoped Classical in
theorem rhoFun_spec (h : LocHyp sg L) {k : GR n} (hk : InK (mR k)) (P : PX m n) :
    (rhoFun h k P).totalDegree ≤ P.totalDegree ∧ L k (fP P) = fP (rhoFun h k P) := by
  simp only [rhoFun, dif_pos hk]
  exact Classical.choose_spec (k_poly h k hk P)

open scoped Classical in

def rhoOf (h : LocHyp sg L) (k : GR n) : PX m n →ₗ[ℂ] PX m n where
  toFun := rhoFun h k
  map_add' P Q := by
    by_cases hk : InK (mR k)
    · apply fP_injective
      rw [← (rhoFun_spec h hk _).2]
      have e := L_fP_lin h k 1 P Q
      simp only [one_smul] at e
      rw [e, (rhoFun_spec h hk P).2, (rhoFun_spec h hk Q).2]
      have e2 := fP_add_smul (1 : ℂ) (rhoFun h k P) (rhoFun h k Q)
      simp only [one_smul] at e2
      rw [e2]
    · simp [rhoFun, dif_neg hk]
  map_smul' a P := by
    by_cases hk : InK (mR k)
    · apply fP_injective
      rw [← (rhoFun_spec h hk _).2]
      have e := L_fP_lin h k a P 0
      simp only [add_zero, L_fP_zero h] at e
      rw [e, (rhoFun_spec h hk P).2]
      have e2 := fP_add_smul a (rhoFun h k P) 0
      simp only [add_zero, fP_zero] at e2
      simp [e2]
    · simp [rhoFun, dif_neg hk]

theorem cnt_true : cnt (fun _ : Fin m => true) true = m := by
  simp [cnt]

theorem cnt_false : cnt (fun _ : Fin m => true) false = 0 := by
  simp [cnt]

theorem pOf_add_qOf (sg : ℤˣ) (m : ℕ) : ((pOf sg m : ℕ) : ℤ) + (qOf sg m : ℕ) = m := by
  unfold pOf qOf
  split_ifs <;> simp

theorem locData_of (h : LocHyp sg L) :
    ∃ (sL : PX m n →ₗ[ℂ] (GR n → ℂ)) (ρ : GR n → PX m n →ₗ[ℂ] PX m n) (e : ℤ),
      LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((sg : ℤ) : ℝ)) (pOf sg m) (qOf sg m) e sL ρ ∧
      (∀ P y, sL P y = L y (fP P) 0) ∧ ∀ (k : GR n) P, InK (mR k) → L k (fP P) = fP (ρ k P) := by
  obtain ⟨e, he⟩ := h.mM'
  obtain ⟨C, hC, hJ⟩ := h.longWeylFunctional

  have hlaw : ∀ (P : PX m n) (y g : GR n), (mR y).toBlocks₂₁ = 0 →
      sLOf h P (y * g) = F0 (pOf sg m) (qOf sg m) e y * sLOf h P g := by
    intro P y g hy
    obtain ⟨a, b, ha, hb, rfl⟩ := par_eq y hy
    have hg := h.sw g _ (isSw_fP P)
    show L (mG a * nG b * g) (fP P) 0 = _ * L g (fP P) 0
    rw [h.mul _ _ _ (isSw_fP P), h.mul _ _ _ hg, he (mG a) a ha (mR_mG ha) _ (h.sw _ _ hg),
      h.nU (nG b) b hb (mR_nG hb) _ hg, weight_factor_levi_unipotent _ _ _ a b ha hb, pOf_add_qOf]
    have key : ∀ X : Fin m → Fin n → ℂ, X = 0 → Complex.exp (2 * Real.pi * Complex.I * ((sg : ℤ) : ℂ) *
        (b * ((Matrix.of X)ᴴ * Matrix.of X)).trace) * L g (fP P) X = L g (fP P) 0 := by
      rintro X rfl
      rw [show Matrix.of (0 : Fin m → Fin n → ℂ) = 0 from rfl]
      simp
    simp only []
    rw [key _ (by funext i j; exact congrFun (congrFun (Matrix.zero_mul a) i) j)]

  have hcell : ∀ (P : PX m n) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b →
      sLOf h P (jG n * nG b) = C * secN (fun _ : Fin m => true) (2 * Real.pi) (2 * Real.pi * ((sg : ℤ) : ℝ)) P b := by
    intro P b hb
    show L (jG n * nG b) (fP P) 0 = _
    rw [h.mul _ _ _ (isSw_fP P), hJ (jG n) mR_jG _ (h.sw _ _ (isSw_fP P)), h.nU (nG b) b hb (mR_nG hb) _ (isSw_fP P)]
    simp only [secN, gramX_true, fP]
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    push_cast
    ring_nf
  have hvac : ∀ g, sLOf h 1 g = F0 (pOf sg m) (qOf sg m) e g := by
    refine vac_unique sg e (sLOf h 1) C (h.cont 1 0) ?_ (hlaw 1) (hcell 1)
    show L 1 (fP 1) 0 = 1
    rw [h.one _ (isSw_fP 1), fP_one_zero]
  refine ⟨sLOf h, rhoOf h, e, ?_, fun P y => rfl, fun k P hk => (rhoFun_spec h hk P).2⟩
  refine
    { cpos := by positivity
      sign := ?_
      cont := fun P => h.cont P 0
      vac := hvac
      law := hlaw
      cell := ⟨C, hC, fun P g b hb hg => by rw [eq_jn g b hb hg]; exact hcell P b hb⟩
      kact := ?_
      kvac := ?_
      kfin := ?_ }
  · rcases Int.units_eq_one_or sg with rfl | rfl
    · left; simp [pOf, qOf, cnt_true, cnt_false]
    · right; simp [pOf, qOf, cnt_true, cnt_false]
  · intro P g k hk
    show L (g * k) (fP P) 0 = L g (fP (rhoFun h k P)) 0
    rw [h.mul _ _ _ (isSw_fP P), (rhoFun_spec h hk P).2]
  · intro k hk
    have hd := (rhoFun_spec h hk 1).1
    rw [MvPolynomial.totalDegree_one, Nat.le_zero, MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hd
    have h1 : sLOf h (rhoOf h k 1) 1 = sLOf h 1 (1 * k) := by
      show L 1 (fP (rhoFun h k 1)) 0 = L (1 * k) (fP 1) 0
      rw [h.mul _ _ _ (isSw_fP 1), ← (rhoFun_spec h hk 1).2]
    change sLOf h (rhoFun h k 1) 1 = _ at h1
    set c := MvPolynomial.coeff 0 (rhoFun h k 1) with hcdef
    have hc : (MvPolynomial.C c : PX m n) = c • (1 : PX m n) := by rw [MvPolynomial.smul_eq_C_mul, mul_one]
    rw [hd, hc, map_smul, Pi.smul_apply, one_mul, hvac, weight_factor_one, smul_eq_mul, mul_one] at h1
    show rhoFun h k 1 = _
    rw [hd, hc, h1, hvac]
  · intro P
    refine ⟨MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree, fin_deg _,
      (MvPolynomial.mem_restrictTotalDegree _ _ _).2 le_rfl, ?_, ?_⟩
    · intro k hk Q hQ
      rw [MvPolynomial.mem_restrictTotalDegree] at hQ ⊢
      exact ((rhoFun_spec h hk Q).1).trans hQ
    · intro Q hQ l'
      rw [MvPolynomial.mem_restrictTotalDegree] at hQ
      refine continuousOn_of_evX P.totalDegree (fun k => rhoOf h k Q)
        (fun k hk => ((rhoFun_spec h hk Q).1).trans hQ) (fun u => ?_) l'
      have hcts : ContinuousOn (fun k => L k (fP Q) u / gs (2 * Real.pi) u) {k | InK (mR k)} :=
        ((h.cont Q u).div_const _).continuousOn
      refine hcts.congr (fun k hk => ?_)
      show evX (rhoFun h k Q) u = L k (fP Q) u / gs (2 * Real.pi) u
      rw [(rhoFun_spec h hk Q).2, fP, mul_div_assoc, div_self (show gs (2 * Real.pi) u ≠ 0 from Complex.exp_ne_zero _), mul_one]

end PositivityTheory.SiegelWeilFormula.KLI

end
end

section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem goodSig_pq {n m : ℕ} (sg : ℤˣ) (h : n ≤ m) : GoodSig n (pOf sg m) (qOf sg m) := by
  unfold pOf qOf GoodSig
  split_ifs
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))

theorem locHyp_of (hT : TAll) (hA : AuxiliaryPrimeFunction) {d : SD σ} (R : RD d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ} (hL : R.IsLocOp w L) :
    LocHyp (R.sg w) L := by
  have hG : GoodAwayEx := KFock.goodAwayEx
  refine
    { sw := fun y f hf => (hL y f hf).1
      one := R.locOp_one hT hG hL
      mul := R.locOp_mul hT hG hL
      lin := R.locOp_lin hT hG hL
      nU := R.locOp_nU hT hG hL
      mM := ?_
      nbar := ?_
      longWeylFunctional := R.localOperator_longWeyl_integral hT hA hG hL
      cont := locOp_cont hT R hL }
  · obtain ⟨k, hk⟩ := R.locOp_mM_law w hT hG hL
    exact ⟨k, fun y a ha hy f hf => hk y a ha hy f hf⟩
  · obtain ⟨C, s, κ, ε, hs, hκ, h4, hf, -, hs2, hη⟩ := R.locOp_nbar hT hA hG hL
    exact ⟨C, s, κ, ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹, hs, hκ, hs2, hη, h4, fun y c hc hy f hf' => hf y c hc hy f hf'⟩

theorem locInst_of (hT : TAll) (hA : AuxiliaryPrimeFunction) (_hF : FockMem) (_hLi : LiftEx) : LocInst := by
  intro F E _ _ _ _ _ σ d R w L hL
  obtain ⟨sL, ρ, e, hD, h1, h2⟩ := locData_of (locHyp_of hT hA R hL)
  exact ⟨sL, ρ, pOf (R.sg w) d.m, qOf (R.sg w) d.m, e, fun hnm => goodSig_pq _ hnm, hD, h1, h2⟩

end PositivityTheory.SiegelWeilFormula.KLI

end
end
