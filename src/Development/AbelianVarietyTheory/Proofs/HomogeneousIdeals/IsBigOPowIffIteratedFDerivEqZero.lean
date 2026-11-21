import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemUnitaryGroupIffIsIsometry
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain

section
universe u_1

namespace GlobalTheory.ExpOfFrechetDerivative

theorem eq_exp_fderiv {E : Type u_1} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ}
    (hd : DifferentiableAt ℂ f (0 : E)) (h0 : f (0 : E) ≠ (0 : ℂ))
    (hmul : ∀ x y : E, f (x + y) = f x * f y) (z : E) :
    f z = Complex.exp ((fderiv ℂ f (0 : E) : E → ℂ) z) := by
  set L := fderiv ℂ f (0 : E) with hL

  have hf0 : f 0 = 1 := by
    have h00 := hmul 0 0
    rw [add_zero] at h00
    have hfac : f 0 * (f 0 - 1) = 0 := by rw [mul_sub, mul_one, ← h00, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h h0
    · exact sub_eq_zero.mp h

  have hD : ∀ x : E, HasFDerivAt f (f x • L) x := by
    intro x
    have h1 : HasFDerivAt f L (x - x) := by
      rw [sub_self]
      exact hd.hasFDerivAt
    have h2 : HasFDerivAt (fun y : E => f (y - x)) L x := by
      have h := h1.comp (f := fun y : E => y - x) x ((hasFDerivAt_id x).sub_const x)
      rw [ContinuousLinearMap.comp_id] at h
      exact h
    refine (h2.const_mul (f x)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    show f y = f x * f (y - x)
    rw [← hmul, add_sub_cancel]

  have hE : ∀ y : E, HasFDerivAt (fun y => f y * Complex.exp (-(L y)))
      (f y • (Complex.exp (-(L y)) • -L) + Complex.exp (-(L y)) • (f y • L)) y :=
    fun y => (hD y).mul (L.hasFDerivAt.neg.cexp)
  have hzero : ∀ y, fderiv ℂ (fun y => f y * Complex.exp (-(L y))) y = 0 := by
    intro y
    rw [(hE y).fderiv]
    ext v
    simp only [add_apply, smul_apply, neg_apply, zero_apply, smul_eq_mul]
    ring
  have hc := is_const_of_fderiv_eq_zero (fun y => (hE y).differentiableAt) hzero z 0
  simp only [map_zero, neg_zero, Complex.exp_zero, mul_one, hf0] at hc
  calc f z = f z * Complex.exp (-(L z)) * Complex.exp (L z) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = Complex.exp (L z) := by rw [hc, one_mul]

end GlobalTheory.ExpOfFrechetDerivative
end

section
open Filter Topology Asymptotics Complex
open scoped Real ComplexConjugate

namespace GlobalTheory.Doubling

noncomputable section

section Rigidity

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup G]
  [NormedSpace ℂ G]

end Rigidity

section Series

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup G]
  [NormedSpace ℂ G]

def quadPart (h : E → G) (z : E) : G := (2 : ℂ)⁻¹ • iteratedFDeriv ℂ 2 h 0 fun _ => z

def doublingSeries (p : FormalMultilinearSeries ℂ E G) : FormalMultilinearSeries ℂ E G :=
  fun n => if n ≤ 2 then 0 else (-((2 : ℂ) ^ n - 4)⁻¹) • p n

end Series

section Character

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eq_cexp_fderiv_of_map_add {f : E → ℂ} (hf : DifferentiableAt ℂ f 0) (h0 : f 0 ≠ 0)
    (hm : ∀ x y, f (x + y) = f x * f y) (z : E) : f z = cexp (fderiv ℂ f 0 z) := by
  first
  | exact @_root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv
  | exact _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv
  | (apply _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv ..)

end Character

section Alternating

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem alt_I_smul_I_smul {B : V → V → ℂ} (hB : ∀ z u, B (I • z) u = I * B z u)
    (hE : ∀ u v, (B v u - B u v).im = 0) (u v : V) :
    B (I • v) (I • u) - B (I • u) (I • v) = B v u - B u v := by
  have h1 := hE (I • u) (I • v)
  have h2 := hE (I • u) v
  have h3 := hE u (I • v)
  have h4 := hE u v
  simp only [hB, sub_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_add] at h1 h2 h3 h4 ⊢
  apply Complex.ext <;> simp <;> linarith

def altHerm (l : V →ₗ[ℝ] V →ₗ[ℂ] ℂ) (hE : ∀ u v, (l u v - l v u).im = 0) : HermForm ℂ V :=
  HermForm.ofFun (fun u v => (l (I • u) v - l v (I • u)) + I * (l u v - l v u))
    (fun x y z => by simp; ring)
    (fun a x y => by
      have h := alt_I_smul_I_smul (B := fun z u => l u z) (by simp) hE x (I • y)
      have ha : ∀ w : V, a • w = a.re • w + a.im • (I • w) := fun w => by
        conv_lhs => rw [← re_add_im a, add_smul, mul_smul]
        rfl
      have hII : ∀ w : V, I • I • w = -w := fun w => by simp [smul_smul]
      rw [smul_comm I a x, ha x, ha (I • x), hII]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, map_neg,
        LinearMap.neg_apply, LinearMap.map_smul_of_tower, real_smul, smul_eq_mul]
      conv_rhs => rw [← re_add_im a]
      linear_combination (-(a.im : ℂ) * (l x y - l y x)) * I_sq)
    (fun x y => by
      have h := alt_I_smul_I_smul (B := fun z u => l u z) (by simp) hE x (I • y)
      have hII : ∀ w : V, I • I • w = -w := fun w => by simp [smul_smul]
      have h1 := conj_eq_iff_im.2 (hE (I • x) y)
      have h2 := conj_eq_iff_im.2 (hE x y)
      rw [star_add, star_mul', Complex.star_def, h1, h2, conj_I]
      simp only [hII, map_neg, LinearMap.neg_apply] at h
      linear_combination -h)

end Alternating

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]

end Lattice

example (z : ℂ) : quadPart (fun z : ℂ => z ^ 2 + z ^ 4) z = z ^ 2 := by
  have h1 : deriv (fun z : ℂ => z ^ 2 + z ^ 4) = fun z => 2 * z + 4 * z ^ 3 := by
    funext z; simp
  have h2 : deriv (fun z : ℂ => 2 * z + 4 * z ^ 3) 0 = 2 := by
    have := (((hasDerivAt_id (0 : ℂ)).const_mul 2).fun_add ((hasDerivAt_pow 3 0).const_mul 4)).deriv
    simpa using this
  rw [quadPart, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_succ,
    iteratedDeriv_one, h1, h2]
  simp [sq]
  ring

example (z : ℂ) : cexp (π * (z + I) ^ 2 / 2) * jacobiTheta₂ (z + I) I =
    1 * cexp (π * (z * conj I) + π * (I * conj I) / 2) * (cexp (π * z ^ 2 / 2) * jacobiTheta₂ z I) := by
  rw [jacobiTheta₂_add_left', ← mul_assoc, ← mul_assoc, one_mul, ← exp_add, ← exp_add, conj_I]
  congr 2
  linear_combination ((π : ℂ) / 2 - π + π / 2) * I_sq

end

end GlobalTheory.Doubling
end
