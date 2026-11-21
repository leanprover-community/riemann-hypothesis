import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealWeilThetaRealization
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitMeasureFiniteCompactSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedCoefficientMeasurableBounded
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetFinAtMemIntegralGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LFunctionEquationGlobal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnstatedLocalWeilLemma
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RWConstMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NsgDivNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilSmoothnessHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionTorusEquivariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitSmoothnessHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedLocalThetaBoundedIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousTwistedLocalThetaInTorus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedThetaValueIndicator

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th ComplexConjugate
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.RealTh.GForm

def pol (n : ℤ) (u : ℂ) : ℂ := if 0 ≤ n then conj u ^ n.natAbs else u ^ n.natAbs

theorem pol_mul (n : ℤ) (x y : ℂ) : pol n (x * y) = pol n x * pol n y := by
  unfold pol
  split_ifs
  · rw [map_mul, mul_pow]
  · rw [mul_pow]

theorem pol_ofReal (n : ℤ) (r : ℝ) : pol n (r : ℂ) = (r : ℂ) ^ n.natAbs := by
  unfold pol
  split_ifs <;> simp

theorem phiInf_eq (n : ℤ) (z : ℂ) :
    PhiInf n z = pol n z * Complex.exp (-2 * Real.pi * ((Complex.normSq z : ℝ) : ℂ)) := rfl

theorem exp_mul_exp_eq_exp_mul_gE (a d c r ρ : ℝ) (hc : c ≠ 0) (v : ℂ) :
    Complex.exp (2 * Real.pi * Complex.I *
        (((a * ρ ^ 2 + d * Complex.normSq v - 2 * (ρ * v.re)) / c : ℝ) : ℂ)) *
      Complex.exp (-2 * Real.pi * ((Complex.normSq (v * r) : ℝ) : ℂ)) =
    Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (ρ : ℂ) ^ 2 / c)) *
      gE (gA c d r) (Complex.I * ((-(2 * Real.pi * ρ) / c : ℝ) : ℂ)) v := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  rw [gE, ← Complex.exp_add, ← Complex.exp_add, Complex.mul_conj, Complex.add_conj, gA]
  congr 1
  simp only [map_mul, Complex.normSq_ofReal]
  push_cast
  field_simp
  ring

theorem int_rotate (ω : Circle) (F : ℂ → ℂ) : ∫ u, F u = ∫ v, F ((ω : ℂ) * v) := by
  have h := ((rotation ω).measurePreserving).integral_comp
    (rotation ω).toHomeomorph.measurableEmbedding F
  simpa [rotation_apply] using h.symm

theorem int_rot (n : ℤ) (a d c r ρ : ℝ) (hc : c ≠ 0) (ω : Circle) :
    ∫ u, Complex.exp (2 * Real.pi * Complex.I *
        (((a * Complex.normSq ((ρ : ℂ) * ω) + d * Complex.normSq u -
          2 * (conj ((ρ : ℂ) * ω) * u).re) / c : ℝ) : ℂ)) * PhiInf n (u * r) ∂volC =
    2 * (Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (ρ : ℂ) ^ 2 / c)) *
      (r : ℂ) ^ n.natAbs * pol n ω * gJ (gA c d r) (-(2 * Real.pi * ρ) / c) n.natAbs) := by
  have hωω : conj (ω : ℂ) * ω = 1 := by
    rw [mul_comm, Complex.mul_conj, Circle.normSq_coe]
    simp
  have hs : Complex.normSq ((ρ : ℂ) * ω) = ρ ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, Circle.normSq_coe]
    ring
  have e : ∀ v : ℂ, Complex.exp (2 * Real.pi * Complex.I *
        (((a * Complex.normSq ((ρ : ℂ) * ω) + d * Complex.normSq (((ω : ℂ) * v)) -
          2 * (conj ((ρ : ℂ) * ω) * ((ω : ℂ) * v)).re) / c : ℝ) : ℂ)) *
        PhiInf n (((ω : ℂ) * v) * r) =
      Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (ρ : ℂ) ^ 2 / c)) *
        (r : ℂ) ^ n.natAbs * pol n ω *
        (pol n v * gE (gA c d r) (Complex.I * ((-(2 * Real.pi * ρ) / c : ℝ) : ℂ)) v) := by
    intro v
    have h := exp_mul_exp_eq_exp_mul_gE a d c r ρ hc v
    have h1 : Complex.normSq (((ω : ℂ) * v)) = Complex.normSq v := by
      rw [Complex.normSq_mul, Circle.normSq_coe, one_mul]
    have h2 : conj ((ρ : ℂ) * ω) * ((ω : ℂ) * v) = (ρ : ℂ) * v := by
      rw [map_mul, Complex.conj_ofReal]
      linear_combination ((ρ : ℂ) * v) * hωω
    have h3 : ((ρ : ℂ) * v).re = ρ * v.re := by simp
    have h4 : Complex.normSq (((ω : ℂ) * v) * r) = Complex.normSq (v * r) := by
      rw [Complex.normSq_mul, h1, Complex.normSq_mul]
    rw [hs, h1, h2, h3, phiInf_eq, h4, pol_mul, pol_mul, pol_ofReal]
    generalize Complex.exp (2 * Real.pi * Complex.I *
        (((a * ρ ^ 2 + d * Complex.normSq v - 2 * (ρ * v.re)) / c : ℝ) : ℂ)) = E₁ at h ⊢
    generalize Complex.exp (-2 * Real.pi * ((Complex.normSq (v * r) : ℝ) : ℂ)) = E₂ at h ⊢
    linear_combination ((r : ℂ) ^ n.natAbs * pol n ω * pol n v) * h
  rw [volC, integral_smul_measure, int_rotate ω]
  simp only [e]
  rw [integral_const_mul]
  have hint : ∫ u : ℂ, pol n u *
      gE (gA c d r) (Complex.I * ((-(2 * Real.pi * ρ) / c : ℝ) : ℂ)) u =
      gJ (gA c d r) (-(2 * Real.pi * ρ) / c) n.natAbs := by
    unfold pol
    split_ifs
    · rfl
    · exact gJ_conj _ _ _
  rw [hint]
  simp

theorem gform_zero (n : ℤ) (a b c d r : ℝ) (hc : c = 0) (hdet : a * d - b * c = 1) (z : ℂ) :
    rWR a b c d (fun y => PhiInf n (y * r)) z =
      (r : ℂ) ^ n.natAbs * ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2)) ^ (-((n.natAbs + 1 : ℕ) : ℤ)) *
        pol n z *
        Complex.exp (2 * Real.pi * Complex.I * (((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) /
          ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2))) * ((Complex.normSq z : ℝ) : ℂ)) := by
  subst hc
  have had : a * d = 1 := by linarith
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one had
  have hd : d ≠ 0 := right_ne_zero_of_mul_eq_one had
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  have hadC : (a : ℂ) * d = 1 := by exact_mod_cast had
  have hdi : (d : ℂ) = (a : ℂ)⁻¹ := eq_inv_of_mul_eq_one_right hadC
  simp only [rWR, if_true, Complex.ofReal_zero, zero_mul, mul_zero, add_zero]
  have hsg : sgR a * ((|a| : ℝ) : ℂ) = a := sgR_mul_abs a ha
  rw [mul_assoc (Complex.exp _) (sgR a), hsg]
  have e1 : (d : ℂ) ^ (-((n.natAbs + 1 : ℕ) : ℤ)) = (a : ℂ) ^ (n.natAbs + 1) := by
    rw [hdi, _root_.zpow_neg, _root_.inv_zpow, inv_inv, zpow_natCast]
  rw [e1]
  have hphi : PhiInf n ((a : ℂ) * z * (r : ℂ)) =
      (a : ℂ) ^ n.natAbs * (r : ℂ) ^ n.natAbs * pol n z *
        Complex.exp (-2 * Real.pi * (((a * r) ^ 2 * Complex.normSq z : ℝ) : ℂ)) := by
    have h : Complex.normSq ((a : ℂ) * z * (r : ℂ)) = (a * r) ^ 2 * Complex.normSq z := by
      simp only [Complex.normSq_mul, Complex.normSq_ofReal]
      ring
    have h' : (a : ℂ) * z * (r : ℂ) = (a : ℂ) * (r : ℂ) * z := by ring
    rw [phiInf_eq, h, h', pol_mul, pol_mul, pol_ofReal, pol_ofReal]
  rw [hphi]
  have e2 : Complex.exp (2 * Real.pi * Complex.I * (((a * b * Complex.normSq z : ℝ) : ℂ))) *
      Complex.exp (-2 * Real.pi * (((a * r) ^ 2 * Complex.normSq z : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) / d) *
        ((Complex.normSq z : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [hdi]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [← e2]
  generalize Complex.exp (2 * Real.pi * Complex.I * (((a * b * Complex.normSq z : ℝ) : ℂ))) = E₁
  generalize Complex.exp (-2 * Real.pi * (((a * r) ^ 2 * Complex.normSq z : ℝ) : ℂ)) = E₂
  ring

theorem gform_ne_polar (n : ℤ) (a b c d r ρ : ℝ) (hr : 0 < r) (hc : c ≠ 0)
    (hdet : a * d - b * c = 1) (ω : Circle) :
    rWR a b c d (fun y => PhiInf n (y * r)) ((ρ : ℂ) * ω) =
      (r : ℂ) ^ n.natAbs * ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2)) ^ (-((n.natAbs + 1 : ℕ) : ℤ)) *
        ((ρ : ℂ) ^ n.natAbs * pol n ω) *
        Complex.exp (2 * Real.pi * Complex.I * (((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) /
          ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2))) * (ρ : ℂ) ^ 2) := by
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hAre := gA_re c d r hr
  have hA0 : gA c d r ≠ 0 := fun h0 => by simp [h0] at hAre
  set w : ℂ := (d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2) with hw
  have hAw : gA c d r = -(2 * Real.pi * Complex.I * w) / c := by
    rw [gA, hw]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have hw0 : w ≠ 0 := by
    intro h0
    rw [hAw, h0] at hA0
    simp at hA0
  have hdetC : (a : ℂ) * d - b * c = 1 := by exact_mod_cast hdet
  have h1 : (Real.pi : ℂ) / gA c d r = Complex.I * c / (2 * w) := by
    rw [hAw]
    field_simp
    ring_nf
    rw [Complex.I_sq]
  have h2 : Complex.I * ((-(2 * Real.pi * ρ) / c : ℝ) : ℂ) / gA c d r = (ρ : ℂ) / w := by
    rw [hAw]
    push_cast
    field_simp
  have h3 : (Complex.I * ((-(2 * Real.pi * ρ) / c : ℝ) : ℂ)) ^ 2 / gA c d r =
      -(2 * Real.pi * Complex.I * (ρ : ℂ) ^ 2) / (c * w) := by
    rw [sq, mul_div_assoc, h2]
    push_cast
    field_simp
  have h4 : Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (ρ : ℂ) ^ 2 / c)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (ρ : ℂ) ^ 2) / (c * w)) =
      Complex.exp (2 * Real.pi * Complex.I * (((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) / w) *
        (ρ : ℂ) ^ 2) := by
    rw [← Complex.exp_add]
    congr 1
    have e : (a : ℂ) * w - 1 = c * ((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) := by
      rw [hw]
      linear_combination hdetC
    have e' : ((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) / w = ((a : ℂ) * w - 1) / (c * w) := by
      rw [e]
      field_simp
    rw [e']
    field_simp
    ring
  have hgJ := gJ_eq (gA c d r) hAre (-(2 * Real.pi * ρ) / c) n.natAbs
  rw [h1, h2, h3] at hgJ
  simp only [rWR, if_neg hc]
  rw [int_rot n a d c r ρ hc ω, hgJ, ← h4, _root_.zpow_neg, zpow_natCast,
    mul_assoc Complex.I (sgR (-c)), sgR_neg_mul c hc]
  generalize Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (ρ : ℂ) ^ 2 / c)) = e₁
  generalize Complex.exp (-(2 * Real.pi * Complex.I * (ρ : ℂ) ^ 2) / (c * w)) = e₂
  rw [div_pow]
  field_simp
  rw [Complex.I_sq]
  ring

theorem gform (n : ℤ) (a b c d r : ℝ) (hr : 0 < r) (hdet : a * d - b * c = 1) (z : ℂ) :
    rWR a b c d (fun y => PhiInf n (y * r)) z =
      (r : ℂ) ^ n.natAbs * ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2)) ^ (-((n.natAbs + 1 : ℕ) : ℤ)) *
        (if 0 ≤ n then (starRingEnd ℂ) z ^ n.natAbs else z ^ n.natAbs) *
        Complex.exp (2 * Real.pi * Complex.I * (((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) /
          ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2))) * ((Complex.normSq z : ℝ) : ℂ)) := by
  change _ = _ * _ * pol n z * _
  by_cases hc : c = 0
  · exact gform_zero n a b c d r hc hdet z
  · have hz : z = ((‖z‖ : ℝ) : ℂ) * (Circle.exp (Complex.arg z) : ℂ) := by
      rw [Circle.coe_exp, Complex.norm_mul_exp_arg_mul_I]
    have hs : ((Complex.normSq z : ℝ) : ℂ) = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    have hp : pol n z = ((‖z‖ : ℝ) : ℂ) ^ n.natAbs * pol n (Circle.exp (Complex.arg z) : ℂ) := by
      conv_lhs => rw [hz, pol_mul, pol_ofReal]
    rw [hs, hp]
    conv_lhs => rw [hz]
    exact gform_ne_polar n a b c d r ‖z‖ hr hc hdet _

end GlobalTheory.CompanionTheory.RealTh.GForm
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_theta_kernel_formula : ∀ (n : ℤ) (a b c d r : ℝ), 0 < r → a * d - b * c = 1 → ∀ z : ℂ,
  rWR a b c d (fun y => PhiInf n (y * r)) z =
    (r : ℂ) ^ n.natAbs * ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2)) ^ (-((n.natAbs + 1 : ℕ) : ℤ)) *
      (if 0 ≤ n then (starRingEnd ℂ) z ^ n.natAbs else z ^ n.natAbs) *
      Complex.exp (2 * Real.pi * Complex.I * (((b : ℂ) + Complex.I * ((a : ℂ) * (r : ℂ) ^ 2)) /
        ((d : ℂ) + Complex.I * ((c : ℂ) * (r : ℂ) ^ 2))) * ((Complex.normSq z : ℝ) : ℂ)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RealTh.GForm.gform
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.ArchDecay

def wG (g : GL (Fin 2) ℝ) : ℂ := (g.val 1 1 : ℂ) + Complex.I * (g.val 1 0 : ℂ)

def tauG (g : GL (Fin 2) ℝ) : ℂ := ((g.val 0 1 : ℂ) + Complex.I * (g.val 0 0 : ℂ)) / wG g

def preG (n : ℤ) (t : ℝ) (g : GL (Fin 2) ℝ) : ℂ :=
  (((g.val).det : ℝ) : ℂ) ^ (Complex.I * t) * ((Real.sqrt (g.val).det : ℝ) : ℂ) *
    ((Real.sqrt (g.val).det : ℝ) : ℂ) ^ n.natAbs * wG g ^ (-((n.natAbs + 1 : ℕ) : ℤ))

def monoX (n : ℤ) (x : ℂ) : ℂ :=
  if 0 ≤ n then (starRingEnd ℂ) x ^ n.natAbs else x ^ n.natAbs

theorem norm_monoX (n : ℤ) (x : ℂ) : ‖monoX n x‖ = ‖x‖ ^ n.natAbs := by
  unfold monoX
  split_ifs <;> simp [norm_pow, Complex.norm_conj]

theorem piRc_eq (n : ℤ) (t : ℝ) (g : GL (Fin 2) ℝ) (h : 0 < (g.val).det) (x : ℂ) :
    piRc (chC n (Complex.I * t)) g (PhiInf n) x = preG n t g * monoX n x *
      Complex.exp (2 * Real.pi * Complex.I * tauG g * ((Complex.normSq x : ℝ) : ℂ)) := by
  unfold piRc preG monoX tauG wG
  rw [dif_pos h]
  set D : ℝ := (g.val).det with hD
  have hr : 0 < Real.sqrt D := Real.sqrt_pos.mpr h
  have hrD : Real.sqrt D ^ 2 = D := Real.sq_sqrt h.le
  have hrC : ((Real.sqrt D : ℝ) : ℂ) ^ 2 = (D : ℂ) := by exact_mod_cast hrD
  have hDC : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h.ne'
  have hdet : g.val 0 0 / D * g.val 1 1 - g.val 0 1 * (g.val 1 0 / D) = 1 := by
    have : D = g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 := by
      rw [hD, Matrix.det_fin_two]
    field_simp
    linarith
  have hk := GlobalTheory.T.real_theta_kernel_formula n (g.val 0 0 / D) (g.val 0 1) (g.val 1 0 / D) (g.val 1 1)
    (Real.sqrt D) hr hdet x
  have e1 : (((g.val 1 0 / D : ℝ) : ℂ)) * ((Real.sqrt D : ℝ) : ℂ) ^ 2 = (g.val 1 0 : ℂ) := by
    rw [hrC]
    push_cast
    field_simp
  have e2 : (((g.val 0 0 / D : ℝ) : ℂ)) * ((Real.sqrt D : ℝ) : ℂ) ^ 2 = (g.val 0 0 : ℂ) := by
    rw [hrC]
    push_cast
    field_simp
  rw [e1, e2] at hk
  rw [GlobalTheory.CompanionTheory.RealTh.chC_pos n _ _ hr, hrD, hk]
  ring

theorem wG_ne (g : GL (Fin 2) ℝ) (h : 0 < (g.val).det) : wG g ≠ 0 := by
  intro hw
  have h1 : g.val 1 1 = 0 := by simpa [wG] using congrArg Complex.re hw
  have h2 : g.val 1 0 = 0 := by simpa [wG] using congrArg Complex.im hw
  rw [Matrix.det_fin_two, h1, h2] at h
  simp at h

theorem tauG_im_pos (g : GL (Fin 2) ℝ) (h : 0 < (g.val).det) : 0 < (tauG g).im := by
  have hn : 0 < Complex.normSq (wG g) := Complex.normSq_pos.mpr (wG_ne g h)
  have : (tauG g).im = (g.val).det / Complex.normSq (wG g) := by
    rw [tauG, Complex.div_im, Matrix.det_fin_two]
    simp only [wG, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [this]
  exact div_pos h hn

theorem continuous_entry' (i j : Fin 2) : Continuous fun g : GL (Fin 2) ℝ => g.val i j :=
  Units.continuous_val.matrix_elem i j

theorem continuous_detG : Continuous fun g : GL (Fin 2) ℝ => (g.val).det :=
  Units.continuous_val.matrix_det

theorem continuous_wG : Continuous wG := by
  unfold wG
  have h1 := Complex.continuous_ofReal.comp (continuous_entry' 1 1)
  have h2 := Complex.continuous_ofReal.comp (continuous_entry' 1 0)
  exact h1.add (continuous_const.mul h2)

theorem continuousAt_tauG (g₀ : GL (Fin 2) ℝ) (h : 0 < (g₀.val).det) : ContinuousAt tauG g₀ := by
  unfold tauG
  have h1 := Complex.continuous_ofReal.comp (continuous_entry' 0 1)
  have h2 := Complex.continuous_ofReal.comp (continuous_entry' 0 0)
  exact (h1.add (continuous_const.mul h2)).continuousAt.div continuous_wG.continuousAt (wG_ne g₀ h)

theorem continuousAt_preG (n : ℤ) (t : ℝ) (g₀ : GL (Fin 2) ℝ) (h : 0 < (g₀.val).det) :
    ContinuousAt (preG n t) g₀ := by
  unfold preG
  have hD : Continuous fun g : GL (Fin 2) ℝ => (((g.val).det : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp continuous_detG
  have hS : Continuous fun g : GL (Fin 2) ℝ => ((Real.sqrt (g.val).det : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_detG)
  have hc : ContinuousAt (fun g : GL (Fin 2) ℝ => (((g.val).det : ℝ) : ℂ) ^ (Complex.I * t)) g₀ :=
    hD.continuousAt.cpow continuousAt_const (Complex.ofReal_mem_slitPlane.mpr h)
  have hz : ContinuousAt (fun g : GL (Fin 2) ℝ => wG g ^ (-((n.natAbs + 1 : ℕ) : ℤ))) g₀ :=
    continuous_wG.continuousAt.zpow₀ _ (Or.inl (wG_ne g₀ h))
  exact ((hc.mul hS.continuousAt).mul (hS.pow _).continuousAt).mul hz

theorem decay (N : ℕ) (α : ℝ) (hα : 0 < α) :
    ∃ B : ℝ, ∀ s : ℝ, 0 ≤ s → s ^ N * (1 + s) ^ 4 * Real.exp (-α * s ^ 2) ≤ B := by
  refine ⟨2 ^ (N + 4) * ((N + 4).factorial / α ^ (N + 4)) * Real.exp α, fun s hs => ?_⟩
  set k := N + 4 with hk
  have hαk : 0 < α ^ k := pow_pos hα k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h1 : s ^ N * (1 + s) ^ 4 ≤ (1 + s) ^ k := by
    rw [hk, pow_add]
    gcongr
    linarith
  have h2 : (1 + s) ^ k ≤ (2 * (1 + s ^ 2)) ^ k := by
    apply pow_le_pow_left₀ (by linarith)
    nlinarith [sq_nonneg (s - 1), sq_nonneg s]
  have h3 : (α * (1 + s ^ 2)) ^ k / k.factorial ≤ Real.exp (α * (1 + s ^ 2)) :=
    Real.pow_div_factorial_le_exp _ (by positivity) k
  have h4 : (1 + s ^ 2) ^ k ≤ k.factorial / α ^ k * Real.exp (α * (1 + s ^ 2)) := by
    rw [mul_pow, div_le_iff₀ hf] at h3
    rw [div_mul_eq_mul_div, le_div_iff₀ hαk]
    nlinarith
  have h5 : Real.exp (α * (1 + s ^ 2)) * Real.exp (-α * s ^ 2) = Real.exp α := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE : 0 < Real.exp (-α * s ^ 2) := Real.exp_pos _
  calc s ^ N * (1 + s) ^ 4 * Real.exp (-α * s ^ 2)
      ≤ (2 ^ k * (k.factorial / α ^ k * Real.exp (α * (1 + s ^ 2)))) * Real.exp (-α * s ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hE.le
        calc s ^ N * (1 + s) ^ 4 ≤ (2 * (1 + s ^ 2)) ^ k := h1.trans h2
          _ = 2 ^ k * (1 + s ^ 2) ^ k := mul_pow _ _ _
          _ ≤ _ := by gcongr
    _ = 2 ^ k * (k.factorial / α ^ k) * (Real.exp (α * (1 + s ^ 2)) * Real.exp (-α * s ^ 2)) := by
        ring
    _ = _ := by rw [h5]

theorem norm_exp_tau (τ : ℂ) (x : ℂ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * τ * ((Complex.normSq x : ℝ) : ℂ))‖ =
      Real.exp (-(2 * Real.pi * τ.im) * ‖x‖ ^ 2) := by
  rw [Complex.norm_exp, Complex.normSq_eq_norm_sq]
  congr 1
  generalize ‖x‖ ^ 2 = s
  simp [Complex.mul_re, Complex.mul_im]

theorem piRc_decay : ∀ (n : ℤ) (t : ℝ) (g₀ : GL (Fin 2) ℝ), 0 < (g₀.val).det → ∃ W ∈ nhds g₀, ∃ A : ℝ,
    (∀ g ∈ W, ∀ x : ℂ, ‖piRc (chC n (Complex.I * t)) g (PhiInf n) x‖ ≤ A * ((1 + ‖x‖) ^ 4)⁻¹) ∧
    ∀ x : ℂ, ContinuousAt (fun g => piRc (chC n (Complex.I * t)) g (PhiInf n) x) g₀ := by
  intro n t g₀ h₀
  have hτ := tauG_im_pos g₀ h₀
  set ε : ℝ := (tauG g₀).im / 2 with hε
  have hε0 : 0 < ε := by positivity
  set P : ℝ := ‖preG n t g₀‖ + 1 with hP
  have hP0 : 0 < P := by positivity
  obtain ⟨B, hB⟩ := decay n.natAbs (2 * Real.pi * ε) (by positivity)
  have hcτ := continuousAt_tauG g₀ h₀
  have hcp := continuousAt_preG n t g₀ h₀
  have e1 : ∀ᶠ g in nhds g₀, 0 < ((g : GL (Fin 2) ℝ).val).det :=
    continuous_detG.continuousAt.eventually (lt_mem_nhds h₀)
  have e2 : ∀ᶠ g in nhds g₀, ‖preG n t g‖ < P :=
    hcp.norm.eventually (gt_mem_nhds (by rw [hP]; linarith))
  have e3 : ∀ᶠ g in nhds g₀, ε < (tauG g).im :=
    (Complex.continuous_im.continuousAt.comp hcτ).eventually (lt_mem_nhds (by simp only [Function.comp]; rw [hε]; linarith))
  refine ⟨_, e1.and (e2.and e3), P * B, ?_, fun x => ?_⟩
  · rintro g ⟨h1, h2, h3⟩ x
    have h1' : 0 < (g.val).det := h1
    have h2' : ‖preG n t g‖ < P := h2
    have h3' : ε < (tauG g).im := h3
    have hx : 0 ≤ ‖x‖ := norm_nonneg x
    rw [piRc_eq n t g h1' x, norm_mul, norm_mul, norm_monoX, norm_exp_tau]
    have hexp : Real.exp (-(2 * Real.pi * (tauG g).im) * ‖x‖ ^ 2) ≤
        Real.exp (-(2 * Real.pi * ε) * ‖x‖ ^ 2) := by
      apply Real.exp_le_exp.mpr
      have : (2 * Real.pi * ε) * ‖x‖ ^ 2 ≤ (2 * Real.pi * (tauG g).im) * ‖x‖ ^ 2 := by
        gcongr
      linarith
    have hq : (0 : ℝ) < (1 + ‖x‖) ^ 4 := by positivity
    have hb : ‖x‖ ^ n.natAbs * Real.exp (-(2 * Real.pi * ε) * ‖x‖ ^ 2) ≤ B * ((1 + ‖x‖) ^ 4)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hq]
      have := hB ‖x‖ hx
      linarith
    calc ‖preG n t g‖ * ‖x‖ ^ n.natAbs * Real.exp (-(2 * Real.pi * (tauG g).im) * ‖x‖ ^ 2)
        ≤ P * (‖x‖ ^ n.natAbs * Real.exp (-(2 * Real.pi * ε) * ‖x‖ ^ 2)) := by
          rw [mul_assoc]
          gcongr
      _ ≤ P * (B * ((1 + ‖x‖) ^ 4)⁻¹) := by gcongr
      _ = P * B * ((1 + ‖x‖) ^ 4)⁻¹ := by ring
  · have hF : ContinuousAt (fun g : GL (Fin 2) ℝ => preG n t g * monoX n x *
        Complex.exp (2 * Real.pi * Complex.I * tauG g * ((Complex.normSq x : ℝ) : ℂ))) g₀ := by
      refine (hcp.mul continuousAt_const).mul (Complex.continuous_exp.continuousAt.comp ?_)
      exact (continuousAt_const.mul hcτ).mul continuousAt_const
    exact hF.congr (e1.mono fun g hg => (piRc_eq n t g hg x).symm)

end GlobalTheory.CompanionTheory.ArchDecay
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_weil_action_local_bound_continuous : ∀ (n : ℤ) (t : ℝ) (g₀ : GL (Fin 2) ℝ), 0 < (g₀.val).det → ∃ W ∈ nhds g₀, ∃ A : ℝ,
  (∀ g ∈ W, ∀ x : ℂ, ‖piRc (chC n (Complex.I * t)) g (PhiInf n) x‖ ≤ A * ((1 + ‖x‖) ^ 4)⁻¹) ∧
  ∀ x : ℂ, ContinuousAt (fun g => piRc (chC n (Complex.I * t)) g (PhiInf n) x) g₀ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ArchDecay.piRc_decay
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.LatticeSum

open NumberField.mixedEmbedding
open scoped Classical

theorem infinitePlace_eq (K : Type) [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2)
    (hc : IsTotallyComplex K) (w w' : InfinitePlace K) : w = w' := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
  have h3 := IsTotallyComplex.nrRealPlaces_eq_zero K
  have h4 : Fintype.card (InfinitePlace K) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, h3]
    omega
  exact Fintype.card_le_one_iff.1 h4.le w w'

theorem norm_mixedEmbedding (K : Type) [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2)
    (hc : IsTotallyComplex K) (x : K) : ‖mixedEmbedding K x‖ = ‖embC K x‖ := by
  rw [norm_eq_sup'_normAtPlace]
  unfold embC
  rw [InfinitePlace.norm_embedding_eq]
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun w _ => ?_
    rw [normAtPlace_apply, infinitePlace_eq K h2 hc w (Classical.arbitrary _)]
  · refine le_trans (le_of_eq (normAtPlace_apply _ x).symm) ?_
    exact Finset.le_sup' (fun w => normAtPlace w (mixedEmbedding K x)) (Finset.mem_univ _)

theorem finrank_span_latticeBasis (K : Type) [Field K] [NumberField K] :
    Module.finrank ℤ (Submodule.span ℤ (Set.range (latticeBasis K))) = Module.finrank ℚ K := by
  rw [finrank_span_eq_card ((latticeBasis K).linearIndependent.restrict_scalars (R := ℤ)
    (by simpa using Int.cast_injective))]
  rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]

theorem summable_inv_one_add_norm_pow_four :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ N : ℕ, N ≠ 0 →
  Summable (fun ξ : {ξ : K // ∃ a : 𝓞 K, (N : K) * ξ = a} => ((1 + ‖embC K ξ.1‖) ^ 4)⁻¹) := by
  intro K _ _ h2 hc N hN
  have hrank : Module.finrank ℤ (Submodule.span ℤ (Set.range (latticeBasis K))) < 4 := by
    rw [finrank_span_latticeBasis, h2]
    omega
  have hs := ZLattice.summable_norm_pow_inv (Submodule.span ℤ (Set.range (latticeBasis K))) 4 hrank
  have hmem : ∀ ξ : {ξ : K // ∃ a : 𝓞 K, (N : K) * ξ = a},
      mixedEmbedding K ((N : K) * ξ.1) ∈ Submodule.span ℤ (Set.range (latticeBasis K)) := by
    rintro ⟨ξ, a, ha⟩
    rw [ha]
    exact (mem_span_latticeBasis K).mpr ⟨a, rfl⟩
  let f : {ξ : K // ∃ a : 𝓞 K, (N : K) * ξ = a} →
      Submodule.span ℤ (Set.range (latticeBasis K)) := fun ξ => ⟨_, hmem ξ⟩
  have hN' : (N : K) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hinj : Function.Injective f := by
    intro ξ η h
    have h1 : mixedEmbedding K ((N : K) * ξ.1) = mixedEmbedding K ((N : K) * η.1) :=
      congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel₀ hN' (mixedEmbedding_injective K h1))
  have h0 : Summable fun z : Submodule.span ℤ (Set.range (latticeBasis K)) =>
      (if z = 0 then (1 : ℝ) else 0) := (hasSum_ite_eq _ (1 : ℝ)).summable
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun ξ => ?_)
    (((hs.mul_left ((N : ℝ) ^ 4)).add h0).comp_injective hinj)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hnorm : ‖f ξ‖ = N * ‖embC K ξ.1‖ := by
    change ‖mixedEmbedding K ((N : K) * ξ.1)‖ = _
    rw [norm_mixedEmbedding K h2 hc]
    unfold embC
    simp
  simp only [Function.comp_apply]
  by_cases hz : f ξ = 0
  · rw [if_pos hz]
    have h1 : ((1 + ‖embC K ξ.1‖) ^ 4)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg (embC K ξ.1)]))
    have h3 : 0 ≤ (N : ℝ) ^ 4 * ‖f ξ‖⁻¹ ^ 4 := by positivity
    linarith
  · rw [if_neg hz, add_zero, hnorm]
    have ht : 0 < ‖embC K ξ.1‖ := by
      have : 0 < ‖f ξ‖ := norm_pos_iff.mpr hz
      rw [hnorm] at this
      exact (mul_pos_iff_of_pos_left hNpos).mp this
    have he : (N : ℝ) ^ 4 * ((N : ℝ) * ‖embC K ξ.1‖)⁻¹ ^ 4 = (‖embC K ξ.1‖ ^ 4)⁻¹ := by
      field_simp
    rw [he]
    gcongr
    linarith

end GlobalTheory.CompanionTheory.LatticeSum
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_inverse_quartic_over_lattice : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ N : ℕ, N ≠ 0 →
  Summable (fun ξ : {ξ : K // ∃ a : 𝓞 K, (N : K) * ξ = a} => ((1 + ‖embC K ξ.1‖) ^ 4)⁻¹) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LatticeSum.summable_inv_one_add_norm_pow_four
end

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_measure_finite_compact_support : ∀ Sv : Finset Pl, IsFiniteMeasure (muU Sv) ∧ (∀ᵐ u ∂(muU Sv), ∀ v : Sv, u v ∈ unQ v.1) ∧ ∀ v : Pl, IsCompact (unQ v) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaUnits.muU_finite_units | exact GlobalTheory.CompanionTheory.ThetaUnits.muU_finite_units | (intros; apply GlobalTheory.CompanionTheory.ThetaUnits.muU_finite_units <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_coefficient_measurable_bounded : ∀ (K : Type) [Field K] [NumberField K] (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v) (Sv : Finset Pl) (m : Pl →₀ ℤ),
  Measurable (fun u => ctM M Sv m u) ∧ ∀ u, ‖ctM M Sv m u‖ ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.CtMeas.measurable_ctM_norm_le | exact GlobalTheory.CompanionTheory.CtMeas.measurable_ctM_norm_le | (intros; apply GlobalTheory.CompanionTheory.CtMeas.measurable_ctM_norm_le <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.AdelicIntegral

theorem eventually_finAt_mem_and_integralGL :
    ∀ (S : Finset Pl) (g₀ : G2) (U : ∀ v : Pl, Set (GL (Fin 2) (Qv v))), (∀ v ∈ S, U v ∈ nhds (finAt v g₀)) →
  (∀ v ∉ S, finAt v g₀ ∈ integralGL (Qv v) 2) →
  ∀ᶠ g in nhds g₀, (∀ v ∈ S, finAt v g ∈ U v) ∧ ∀ v ∉ S, finAt v g ∈ integralGL (Qv v) 2 := by
  intro S g₀ U hU hint
  have h₁ : ∀ᶠ g in nhds g₀, ∀ v ∈ S, finAt v g ∈ U v :=
    (Filter.eventually_all_finset S).2 fun v hv =>
      (GroundTheory.Automorphic.Reduction.continuous_finAt v).continuousAt.eventually_mem (hU v hv)
  have h₂ : ∀ᶠ g in nhds g₀, ∀ v ∉ S, finAt v g ∈ integralGL (Qv v) 2 :=
    (GroundTheory.Automorphic.Reduction.isOpen_setOf_forall_not_mem_imp S).mem_nhds hint
  exact h₁.and h₂

end GlobalTheory.CompanionTheory.AdelicIntegral
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open scoped Topology
open Filter Matrix Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.WeilSmooth GlobalTheory.CompanionTheory.WeilPiRep

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilLocConst

theorem piE_mul : GL2LocalData.ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η =>
    ∀ c : Eˣ →* ℂˣ, ∀ Φ ∈ GL2LocalData.SBc F E c, ∀ g h : GL (Fin 2) F,
      (∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det) →
      (∃ t : Eˣ, Algebra.norm F (t : E) = (h.val).det) →
      GL2LocalData.piE E χ σ η c (g * h) Φ = GL2LocalData.piE E χ σ η c g (GL2LocalData.piE E χ σ η c h Φ) := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη c Φ hΦ g h hg hh
  have wdg := GlobalTheory.CompanionTheory.WeilDilation.wDiagT F χ hχ hχ1 E hfr hcont σ hσ η hη
  have wsb := GlobalTheory.CompanionTheory.WeilSB.wsb F χ hχ hχ1 E hfr hcont σ hσ η hη
  have wrp := GlobalTheory.T.weil_representation_hypothesis F χ hχ hχ1 E hfr hcont σ hσ η hη
  beta_reduce at wdg wsb wrp
  have hdet : ∀ x : GL (Fin 2) F, (x.val).det ≠ 0 := fun x =>
    ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).ne_zero
  obtain ⟨tg, htg⟩ := hg
  obtain ⟨t, hnt⟩ := hh
  have hiso := hΦ.2.2
  have hpi : piE E χ σ η c h Φ = fun x => (((c t : ℂˣ) : ℂ) * (((modulus (h.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
      rWE E χ σ η (red h.val) (fun y => Φ (y * (t : E))) x :=
    funext fun x => piG_choice χ σ (muE E χ) (lamE E χ η) c hiso h t hnt x
  set k : ℂ := ((c t : ℂˣ) : ℂ) * (((modulus (h.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) with hk
  set Ψ : E → ℂ := fun y => Φ (y * (t : E)) with hΨdef
  have hΨ : Ψ ∈ SBc F E c := dil_mem hΦ t
  have hΨE : Ψ ∈ SBE E := ⟨hΨ.1, hΨ.2.1⟩
  have hd1 : (red h.val).det = 1 := det_red (hdet h)
  have hmem : piE E χ σ η c h Φ ∈ SBc F E c := by
    rw [hpi]
    exact const_mul_mem ((wsb _ hd1 Ψ hΨE).2 c hΨ) k
  have hdg := hdet g
  have hgh : Algebra.norm F ((tg * t : Eˣ) : E) = ((g * h).val).det := by
    rw [Units.val_mul, map_mul, htg, hnt, Units.val_mul, Matrix.det_mul]
  funext x
  have lhs := piG_choice χ σ (muE E χ) (lamE E χ η) c hiso (g * h) (tg * t) hgh x
  have rhs := piG_choice χ σ (muE E χ) (lamE E χ η) c hmem.2.2 g tg htg x
  refine lhs.trans (Eq.trans ?_ rhs.symm)
  set f : E → ℂ := fun y => Ψ (y * (tg : E)) with hfdef
  have hfE : f ∈ SBE E := by
    have := dil_mem hΨ tg
    exact ⟨this.1, this.2.1⟩
  have hcj : (cjA (g.val).det (red h.val)).det = 1 := by rw [det_cjA hdg, hd1]
  have hgd : (red g.val).det = 1 := det_red hdg
  have hL : (fun y => Φ (y * ((tg * t : Eˣ) : E))) = f := by
    funext y
    simp only [hfdef, hΨdef, Units.val_mul, mul_assoc]
  have hR : (fun y => piE E χ σ η c h Φ (y * (tg : E))) =
      fun y => k * rWE E χ σ η (cjA (g.val).det (red h.val)) f y := by
    funext y
    have := congrFun (wdg (red h.val) hd1 tg Ψ hΨE) y
    rw [htg] at this
    rw [hpi]
    simp only []
    rw [this]
  have e1 : rW χ σ (muE E χ) (lamE E χ η) (((g * h).val) 0 0 / ((g * h).val).det) (((g * h).val) 0 1)
      (((g * h).val) 1 0 / ((g * h).val).det) (((g * h).val) 1 1) f x =
      rWE E χ σ η (red (g * h).val) f x := rfl
  have e2 : rW χ σ (muE E χ) (lamE E χ η) ((g.val) 0 0 / (g.val).det) ((g.val) 0 1)
      ((g.val) 1 0 / (g.val).det) ((g.val) 1 1)
      (fun y => k * rWE E χ σ η (cjA (g.val).det (red h.val)) f y) x =
      k * rWE E χ σ η (red g.val) (rWE E χ σ η (cjA (g.val).det (red h.val)) f) x :=
    GlobalTheory.CompanionTheory.WeilChoice.rW_const_mul _ _ _ _ _ _ _ _ _ _ _
  rw [hL, hR, e1, e2, Units.val_mul, red_mul hdg (hdet h), wrp _ _ hgd hcj f hfE]
  have e3 : (((modulus ((g.val * h.val).det) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) =
      (((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) * (((modulus (h.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) := by
    rw [Matrix.det_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
  rw [e3, map_mul, Units.val_mul, hk]
  ring

theorem piE_locConst : GL2LocalData.ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η =>
  ∀ c : Eˣ →* ℂˣ, IsUnit1 c → ∀ Φ ∈ GL2LocalData.SBc F E c, ∀ g₀ : GL (Fin 2) F,
    (∃ t : Eˣ, Algebra.norm F (t : E) = (g₀.val).det) →
    ∃ U ∈ nhds g₀, ∀ g ∈ U, GL2LocalData.piE E χ σ η c g Φ = GL2LocalData.piE E χ σ η c g₀ Φ := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη c hc Φ hΦ g₀ hg₀
  haveI : Fact (Module.finrank F E = 2) := ⟨hfr⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : ValuativeExtension F E := GlobalTheory.CompanionTheory.WeilSB.valuativeExtension_of_continuous hcont
  haveI : Algebra.IsSeparable F E := inferInstance
  have hNc := GlobalTheory.CompanionTheory.WeilSB.continuous_norm_of (F := F) (E := E) hcont
  have hlc := GlobalTheory.CompanionTheory.WeilSB.isLocallyConstant_char hχ hχ1
  have hSB : Φ ∈ SBE E := ⟨hΦ.1, hΦ.2.1⟩
  have hiso := hΦ.2.2
  have hmul : ∀ g h : GL (Fin 2) F, (∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det) →
      (∃ t : Eˣ, Algebra.norm F (t : E) = (h.val).det) →
      piE E χ σ η c (g * h) Φ = piE E χ σ η c g (piE E χ σ η c h Φ) :=
    piE_mul F χ hχ hχ1 E hfr hcont σ hσ η hη c Φ hΦ
  have hrep : ∀ g h : Matrix (Fin 2) (Fin 2) F, g.det = 1 → h.det = 1 → ∀ Ψ ∈ SBE E,
      rWE E χ σ η (g * h) Ψ = rWE E χ σ η g (rWE E χ σ η h Ψ) :=
    GlobalTheory.T.weil_representation_hypothesis F χ hχ hχ1 E hfr hcont σ hσ η hη
  have hsb : ∀ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 → ∀ Ψ ∈ SBE E, rWE E χ σ η g Ψ ∈ SBE E :=
    fun g hg Ψ hΨ => (GlobalTheory.CompanionTheory.WeilSB.wsb F χ hχ hχ1 E hfr hcont σ hσ η hη g hg Ψ hΨ).1
  have hone : piE E χ σ η c 1 Φ = Φ :=
    (piG_det_one χ σ (muE E χ) (lamE E χ η) c hiso 1 (by simp)).trans
      (rWm_one χ σ (muE E χ) (lamE E χ η) Φ)
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (GL (Fin 2) F), ∀ h, h ∈ H ↔
      (∃ t : Eˣ, Algebra.norm F (t : E) = (h.val).det) ∧ piE E χ σ η c h Φ = Φ := by
    refine ⟨{ carrier := {h | (∃ t : Eˣ, Algebra.norm F (t : E) = (h.val).det) ∧ piE E χ σ η c h Φ = Φ}
              mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun h => Iff.rfl⟩
    · rintro a b ⟨⟨s, hs⟩, ha⟩ ⟨⟨t, ht⟩, hb⟩
      refine ⟨⟨s * t, ?_⟩, ?_⟩
      · rw [Units.val_mul, map_mul, hs, ht, Units.val_mul, Matrix.det_mul]
      · rw [hmul a b ⟨s, hs⟩ ⟨t, ht⟩, hb, ha]
    · exact ⟨⟨1, by simp⟩, hone⟩
    · rintro a ⟨⟨t, ht⟩, ha⟩
      have h1 : ((a⁻¹ : GL (Fin 2) F).val).det * (a.val).det = 1 := by
        rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel]
        simp
      have h2 : Algebra.norm F ((t⁻¹ : Eˣ) : E) * (a.val).det = 1 := by
        rw [← ht, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
      have hd : Algebra.norm F ((t⁻¹ : Eˣ) : E) = ((a⁻¹ : GL (Fin 2) F).val).det :=
        mul_right_cancel₀ (show (a.val).det ≠ 0 from fun h0 => by simp [h0] at h1) (h2.trans h1.symm)
      refine ⟨⟨t⁻¹, hd⟩, ?_⟩
      have := hmul a⁻¹ a ⟨t⁻¹, hd⟩ ⟨t, ht⟩
      rw [inv_mul_cancel, hone, ha] at this
      exact this.symm
  have key : ∀ h : GL (Fin 2) F, (∃ t : Eˣ, Algebra.norm F (t : E) = (h.val).det) →
      piE E χ σ η c h Φ = Φ → h ∈ H := fun h hx he => (hH h).2 ⟨hx, he⟩
  have hdet1 : ∀ h : GL (Fin 2) F, (h.val).det = 1 → rWE E χ σ η h.val Φ = Φ → h ∈ H := by
    intro h hd he
    refine key h ⟨1, by simp [hd]⟩ ?_
    exact (piG_det_one χ σ (muE E χ) (lamE E χ η) c hiso h hd).trans he
  have hUp : ∀ᶠ x in 𝓝 (0 : F), uni2 x ∈ H := by
    filter_upwards [ev_chirp hlc hNc hΦ.2.1] with x hx
    refine hdet1 _ (by simp [uni2, Matrix.det_fin_two]) ?_
    funext z
    exact (rWm_upper χ σ (muE E χ) (lamE E χ η) x Φ z).trans (hx z)
  have hLow : ∀ᶠ y in 𝓝 (0 : F), low y ∈ H := by
    have hwm : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by simp [Matrix.det_fin_two]
    have hwi : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by simp [Matrix.det_fin_two]
    have hΦ' := hsb _ hwi Φ hSB
    have ht : Tendsto (fun y : F => -y) (𝓝 0) (𝓝 0) := by
      have : ContinuousAt (fun y : F => -y) 0 := continuous_neg.continuousAt
      simpa [ContinuousAt] using this
    filter_upwards [ht.eventually (ev_chirp hlc hNc hΦ'.2)] with y hy
    have hnd : (!![1, -y; 0, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by simp [Matrix.det_fin_two]
    have hn : rWE E χ σ η !![1, -y; 0, 1] (rWE E χ σ η !![0, -1; 1, 0] Φ) = rWE E χ σ η !![0, -1; 1, 0] Φ :=
      funext fun z => (rWm_upper χ σ (muE E χ) (lamE E χ η) (-y) _ z).trans (hy z)
    have e : (low y).val = !![0, 1; -1, 0] * (!![1, -y; 0, 1] * !![0, -1; 1, 0]) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [low, Matrix.mul_apply, Fin.sum_univ_two]
    have e1 : (!![0, 1; -1, 0] * !![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    refine hdet1 _ (by simp [low, Matrix.det_fin_two]) ?_
    rw [e, hrep _ _ hwm (by rw [Matrix.det_mul, hnd, hwi, one_mul]) Φ hSB, hrep _ _ hnd hwi Φ hSB, hn,
      ← hrep _ _ hwm hwi Φ hSB, e1]
    exact rWm_one χ σ (muE E χ) (lamE E χ η) Φ
  have tE : Tendsto (algebraMap F E) (𝓝 1) (𝓝 1) := by
    have := hcont.tendsto 1
    rwa [map_one] at this
  have hGood : ∀ᶠ r in 𝓝 (1 : F), r ≠ 0 ∧ GroundTheory.LocalField.modulus r = 1 ∧
      (∀ x, Φ (x * algebraMap F E r) = Φ x) ∧ ∀ u : Eˣ, (u : E) = algebraMap F E r → c u = 1 := by
    filter_upwards [eventually_ne_nhds (one_ne_zero (α := F)), ev_modulus, tE.eventually (ev_dil hSB),
      tE.eventually (ev_char c hc.1)] with r h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hS := ev_sq hGood
  have hD : ∀ᶠ a in 𝓝 (1 : F), ∀ s : Fˣ, (s : F) = a → dg2 s 1 ∈ H := by
    filter_upwards [hS] with a ha s hs
    obtain ⟨r, ⟨hr0, hrm, hrd, hrc⟩, hra⟩ := ha
    let t : Eˣ := Units.mk0 (algebraMap F E r) ((map_ne_zero _).2 hr0)
    have hNt : Algebra.norm F (t : E) = a := by
      simp [t, Algebra.norm_algebraMap, hfr, sq, hra]
    have hdet : ((dg2 s 1 : GL (Fin 2) F).val).det = a := by
      simp [dg2, Matrix.det_fin_two, hs]
    have ha0 : a ≠ 0 := hs ▸ s.ne_zero
    have hma : GroundTheory.LocalField.modulus a = 1 := by
      rw [← hra, GroundTheory.LocalField.modulus_mul, hrm, one_mul]
    refine key _ ⟨t, by rw [hNt, hdet]⟩ ?_
    funext x
    have e00 : (dg2 s 1 : GL (Fin 2) F).val 0 0 = a := by simp [dg2, hs]
    have e01 : (dg2 s 1 : GL (Fin 2) F).val 0 1 = 0 := by simp [dg2]
    have e10 : (dg2 s 1 : GL (Fin 2) F).val 1 0 = 0 := by simp [dg2]
    have e11 : (dg2 s 1 : GL (Fin 2) F).val 1 1 = 1 := by simp [dg2]
    refine (piG_choice χ σ (muE E χ) (lamE E χ η) c hiso _ t (by rw [hNt, hdet]) x).trans ?_
    rw [hdet, e00, e01, e10, e11, div_self ha0, zero_div, rW_zero, hrc t rfl, hma]
    simp [nsg_one, t, hrd]
  have hM : ∀ᶠ a in 𝓝 (1 : F), ∀ s : Fˣ, (s : F) = a → dg2 s s⁻¹ ∈ H := by
    filter_upwards [hS] with a ha s hs
    obtain ⟨r, ⟨hr0, hrm, hrd, hrc⟩, hra⟩ := ha
    let t : Eˣ := Units.mk0 (algebraMap F E r) ((map_ne_zero _).2 hr0)
    have hNt : Algebra.norm F (t : E) = a := by
      simp [t, Algebra.norm_algebraMap, hfr, sq, hra]
    have hma : GroundTheory.LocalField.modulus a = 1 := by
      rw [← hra, GroundTheory.LocalField.modulus_mul, hrm, one_mul]
    refine hdet1 _ (by simp [dg2, Matrix.det_fin_two]) ?_
    funext z
    show rW χ σ (muE E χ) (lamE E χ η) ((dg2 s s⁻¹ : GL (Fin 2) F).val 0 0) ((dg2 s s⁻¹ : GL (Fin 2) F).val 0 1)
      ((dg2 s s⁻¹ : GL (Fin 2) F).val 1 0) ((dg2 s s⁻¹ : GL (Fin 2) F).val 1 1) Φ z = Φ z
    have e00 : (dg2 s s⁻¹ : GL (Fin 2) F).val 0 0 = a := by simp [dg2, hs]
    have e01 : (dg2 s s⁻¹ : GL (Fin 2) F).val 0 1 = 0 := by simp [dg2]
    have e10 : (dg2 s s⁻¹ : GL (Fin 2) F).val 1 0 = 0 := by simp [dg2]
    rw [e00, e01, e10, rW_zero, hma, ← hNt, nsg_norm, hNt]
    have : Φ (algebraMap F E a * z) = Φ z := by
      rw [← hra, map_mul, mul_comm, ← mul_assoc, hrd, hrd]
    simp [this]
  have hmem := mem_nhds_of_factors H hUp hLow hD hM
  have hcont' : ContinuousAt (fun g : GL (Fin 2) F => g₀⁻¹ * g) g₀ :=
    (continuous_const.mul continuous_id).continuousAt
  refine ⟨(fun g : GL (Fin 2) F => g₀⁻¹ * g) ⁻¹' (H : Set (GL (Fin 2) F)),
    hcont'.preimage_mem_nhds (by simpa using hmem), fun g hg => ?_⟩
  obtain ⟨hx, he⟩ := (hH _).1 hg
  calc piE E χ σ η c g Φ = piE E χ σ η c (g₀ * (g₀⁻¹ * g)) Φ := by rw [mul_inv_cancel_left]
    _ = piE E χ σ η c g₀ (piE E χ σ η c (g₀⁻¹ * g) Φ) := hmul _ _ hg₀ hx
    _ = piE E χ σ η c g₀ Φ := by rw [he]

end GlobalTheory.CompanionTheory.WeilLocConst
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.field_weil_action_locally_constant : GL2LocalData.ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η =>
  ∀ c : Eˣ →* ℂˣ, IsUnit1 c → ∀ Φ ∈ GL2LocalData.SBc F E c, ∀ g₀ : GL (Fin 2) F,
    (∃ t : Eˣ, Algebra.norm F (t : E) = (g₀.val).det) →
    ∃ U ∈ nhds g₀, ∀ g ∈ U, GL2LocalData.piE E χ σ η c g Φ = GL2LocalData.piE E χ σ η c g₀ Φ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.WeilLocConst.piE_locConst
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.SplitContG

theorem piS_locConst : GL2LocalData.ForES fun F _ _ _ _ _ _ _ χ => ∀ c₁ : Fˣ →* ℂˣ, IsUnit1 c₁ → ∀ Φ ∈ GL2LocalData.SBE (F × F), ∀ g₀ : GL (Fin 2) F,
    ∃ U ∈ nhds g₀, ∀ g ∈ U, GL2LocalData.piS χ c₁ g Φ = GL2LocalData.piS χ c₁ g₀ Φ := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 c₁ h₁ Φ hΦ g₀
  have hH := GlobalTheory.CompanionTheory.SplitSmooth.stab_near hχ hχ1 h₁.1 hΦ
  have hU : (fun g => g₀⁻¹ * g) ⁻¹' {u : GL (Fin 2) F | GL2LocalData.piS χ c₁ u Φ = Φ} ∈ nhds g₀ := by
    have hc : ContinuousAt (fun g : GL (Fin 2) F => g₀⁻¹ * g) g₀ := (continuous_const.mul continuous_id).continuousAt
    have h1 : {u : GL (Fin 2) F | GL2LocalData.piS χ c₁ u Φ = Φ} ∈ nhds (g₀⁻¹ * g₀) := by
      rw [inv_mul_cancel]
      exact hH
    exact hc h1
  refine ⟨_, hU, fun g hg => ?_⟩
  have hg' : GL2LocalData.piS χ c₁ (g₀⁻¹ * g) Φ = Φ := hg
  have e : g = g₀ * (g₀⁻¹ * g) := by group
  rw [e, GlobalTheory.CompanionTheory.SplitPi.piS_mul hχ hχ1 c₁ hΦ, hg']

end GlobalTheory.CompanionTheory.SplitContG
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_weil_action_locally_constant : GL2LocalData.ForES fun F _ _ _ _ _ _ _ χ => ∀ c₁ : Fˣ →* ℂˣ, IsUnit1 c₁ → ∀ Φ ∈ GL2LocalData.SBE (F × F), ∀ g₀ : GL (Fin 2) F,
  ∃ U ∈ nhds g₀, ∀ g ∈ U, GL2LocalData.piS χ c₁ g Φ = GL2LocalData.piS χ c₁ g₀ Φ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SplitContG.piS_locConst
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver

namespace GlobalTheory.CompanionTheory.ThetaStab

theorem val_stab : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ∀ g₀ : GL (Fin 2) (Qv v), L.plus g₀ → ∃ U ∈ nhds g₀, ∀ g ∈ U, ∀ (τ : (Qv v)ˣ) (ξ : K),
    (L.tw τ).val g ξ = (L.tw τ).val g₀ ξ := by
  intro K _ _ h2 c v L hok g₀ hp
  have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.RankinQ.isStd_local v
  have hψ := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.continuous_charInv (GP.psiF v) hstd.1
  have hψ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.2 hstd.2.1
  cases L with
  | @sp w₁ w₂ h₁ h₂ Φ =>
    obtain ⟨_, hl, hc⟩ := hok
    obtain ⟨U, hU, hUe⟩ := GlobalTheory.T.split_weil_action_locally_constant (Qv v) (GP.psiF v)⁻¹ hψ hψ1 (cAt c v w₁)
      (GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.isUnit1_cAt c v w₁) Φ ⟨hl, hc⟩ g₀
    refine ⟨U, hU, fun g hg τ ξ => ?_⟩
    have e := fun h : GL (Fin 2) (Qv v) => GlobalTheory.T.split_weil_action_torus_equivariant (Qv v) (GP.psiF v)⁻¹ hψ hψ1 (cAt c v w₁) h Φ τ
      (dg1 v w₁ ξ, dg1 v w₂ ξ)
    simp only [LM.tw, LM.val]
    rw [e g, e g₀, hUe g hg]
  | @ns w h σ η Φ =>
    obtain ⟨hu, hσ, hη, hΦ⟩ := hok
    obtain ⟨U, hU, hUe⟩ := GlobalTheory.T.field_weil_action_locally_constant (Qv v) (GP.psiF v)⁻¹ hψ hψ1 (Kv K w)
      (GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.places_nonsplit h2 v w hu) (_root_.continuous_algebraMap (Qv v) (Kv K w)) σ hσ η hη
      (localChar c w) (GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.isUnit1_localCharK c w) Φ hΦ g₀ hp
    refine ⟨U, hU, fun g hg τ ξ => ?_⟩
    exact congrFun (hUe g hg) _

end GlobalTheory.CompanionTheory.ThetaStab
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_local_theta_locally_constant : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ∀ g₀ : GL (Fin 2) (Qv v), L.plus g₀ → ∃ U ∈ nhds g₀, ∀ g ∈ U, ∀ (τ : (Qv v)ˣ) (ξ : K),
    (L.tw τ).val g ξ = (L.tw τ).val g₀ ξ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ThetaStab.val_stab
end

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_local_theta_bounded_integral : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ∀ g₀ : GL (Fin 2) (Qv v), L.plus g₀ → ∀ T : Set (Qv v)ˣ, IsCompact T → ∃ (B : ℝ) (N : ℕ), N ≠ 0 ∧
    ∀ τ ∈ T, ∀ ξ : K, ‖(L.tw τ).val g₀ ξ‖ ≤ B ∧ ((L.tw τ).val g₀ ξ ≠ 0 →
      ∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w) ((N : K) * ξ) ∈ 𝒪[Kv K w]) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaBound.bound | exact GlobalTheory.CompanionTheory.ThetaBound.bound | (intros; apply GlobalTheory.CompanionTheory.ThetaBound.bound <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_twisted_local_theta_in_torus : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ∀ g₀ : GL (Fin 2) (Qv v), L.plus g₀ → ∀ ξ : K, Continuous (fun τ : (Qv v)ˣ => (L.tw τ).val g₀ ξ) := by
  first | exact @GlobalTheory.CompanionTheory.TwistCont.val_tw_continuous | exact GlobalTheory.CompanionTheory.TwistCont.val_tw_continuous | (intros; apply GlobalTheory.CompanionTheory.TwistCont.val_tw_continuous <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_theta_value_indicator : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → L.std → Unr c v → ∀ k ∈ integralGL (Qv v) 2, ∀ ξ : K,
    ((∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w) ξ ∈ 𝒪[Kv K w]) → L.val k ξ = 1) ∧
    (¬ (∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w) ξ ∈ 𝒪[Kv K w]) → L.val k ξ = 0) := by
  first | exact @GlobalTheory.CompanionTheory.StdSphVal.val_std | exact GlobalTheory.CompanionTheory.StdSphVal.val_std | (intros; apply GlobalTheory.CompanionTheory.StdSphVal.val_std <;> assumption)
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.ThetaFin

variable {K : Type} [Field K] [NumberField K]

theorem tw_one {c : HeckeCharacter K} {v : Pl} (L : LM c v) : L.tw 1 = L := by
  cases L with
  | sp w₁ w₂ Φ =>
    have h : (fun x : Qv v × Qv v => Φ (x * (1, 1))) = Φ := by
      funext x
      exact congrArg Φ (mul_one x)
    simp [LM.tw, h]
  | ns w σ η Φ => simp [LM.tw]

theorem integral_iff (w : PlK K) (x : K) :
    algebraMap K (Kv K w) x ∈ 𝒪[Kv K w] ↔ w.valuation K x ≤ 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [Valuation.mem_integer_iff, ← map_one (ValuativeRel.valuation _), ← Valuation.vle_iff_le,
    Valuation.vle_iff_le Valued.v, map_one]
  have h : Valued.v (algebraMap K (w.adicCompletion K) x) = w.valuation K x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  rw [h]

theorem lies_under (w : PlK K) : w.asIdeal.LiesOver (w.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩

theorem tu_off (Sv : Finset Pl) (m : Pl →₀ ℤ) (u : ∀ v : Sv, (Qv v.1)ˣ) {v : Pl}
    (h1 : v ∉ Sv) (h2 : v ∉ m.support) : tu Sv m u v = 1 := by
  have : m v = 0 := by simpa using h2
  simp [tu, h1, this]

theorem tu_mem (Sv : Finset Pl) (m : Pl →₀ ℤ) (u : ∀ v : Sv, (Qv v.1)ˣ) (hu : ∀ v : Sv, u v ∈ unQ v.1) (v : Pl) :
    tu Sv m u v ∈ (fun x => unifUnit (Qv v) ^ (m v) * x) '' (unQ v ∪ {1}) := by
  by_cases h : v ∈ Sv
  · exact ⟨u ⟨v, h⟩, Or.inl (hu ⟨v, h⟩), by simp [tu, h]⟩
  · exact ⟨1, Or.inr rfl, by simp [tu, h]⟩

theorem compact_alt (m : Pl →₀ ℤ) (v : Pl) :
    IsCompact ((fun x => unifUnit (Qv v) ^ (m v) * x) '' (unQ v ∪ {1})) :=
  ((GlobalTheory.CompanionTheory.ThetaUnits.isCompact_unQ v).union isCompact_singleton).image (by fun_prop)

theorem measurable_tu (Sv : Finset Pl) (m : Pl →₀ ℤ) (v : Pl) {f : (Qv v)ˣ → ℂ} (hf : Continuous f) :
    Measurable (fun u : ∀ v : Sv, (Qv v.1)ˣ => f (tu Sv m u v)) := by
  by_cases h : v ∈ Sv
  · have hc : Continuous (fun x : (Qv v)ˣ => f (unifUnit (Qv v) ^ (m v) * x)) := by fun_prop
    have : (fun u : ∀ v : Sv, (Qv v.1)ˣ => f (tu Sv m u v)) =
        (fun x : (Qv v)ˣ => f (unifUnit (Qv v) ^ (m v) * x)) ∘ (fun u => u ⟨v, h⟩) := by
      funext u; simp [tu, h]
    rw [this]
    exact hc.measurable.comp (measurable_pi_apply _)
  · have : (fun u : ∀ v : Sv, (Qv v.1)ˣ => f (tu Sv m u v)) = fun _ => f (unifUnit (Qv v) ^ (m v)) := by
      funext u; simp [tu, h]
    rw [this]
    exact measurable_const

theorem exists_finset_integral (ξ : K) : ∃ T : Finset Pl, ∀ v ∉ T, ∀ w : PlK K,
    w.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w) ξ ∈ 𝒪[Kv K w] := by
  classical
  refine ⟨(HeightOneSpectrum.Support.finite (𝓞 K) ξ).toFinset.image (fun w => w.under (𝓞 ℚ)), ?_⟩
  intro v hv w hw
  rw [integral_iff]
  by_contra hlt
  apply hv
  refine Finset.mem_image.2 ⟨w, ?_, HeightOneSpectrum.ext hw.over.symm⟩
  simpa [HeightOneSpectrum.Support] using hlt

theorem valuation_natCast_le_one (w : PlK K) (n : ℕ) : w.valuation K (n : K) ≤ 1 := by
  have h := w.valuation_le_one (K := K) (n : 𝓞 K)
  simpa using h

theorem finitePart : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v), AdmM M →
  ∀ (Sv : Finset Pl) (m : Pl →₀ ℤ) (g₀ : G2), g₀ ∈ Gp M → ∃ (W : Set G2) (N : ℕ) (B : ℝ), W ∈ nhds g₀ ∧ N ≠ 0 ∧
    (∀ g ∈ W, g ∈ Gp M → ∀ u (ξ : K), ∏ᶠ v, (twM M Sv m u v).val (finAt v g) ξ = ∏ᶠ v, (twM M Sv m u v).val (finAt v g₀) ξ) ∧
    (∀ u, (∀ v : Sv, u v ∈ unQ v.1) → ∀ ξ : K, ‖∏ᶠ v, (twM M Sv m u v).val (finAt v g₀) ξ‖ ≤ B ∧
      (∏ᶠ v, (twM M Sv m u v).val (finAt v g₀) ξ ≠ 0 → ∃ a : 𝓞 K, (N : K) * ξ = a)) ∧
    ∀ ξ : K, Measurable (fun u => ∏ᶠ v, (twM M Sv m u v).val (finAt v g₀) ξ) := by
  classical
  intro K _ _ hK c M hM Sv m g₀ hg
  obtain ⟨hok, S0, hS0⟩ := hM
  obtain ⟨S1, hS1⟩ := GlobalTheory.CompanionTheory.AdelicIntegral.exists_finset_finAt_mem_integralGL g₀
  obtain ⟨S, hS⟩ : ∃ S : Finset Pl, S = S0 ∪ m.support ∪ Sv ∪ S1 := ⟨_, rfl⟩
  have hmem : ∀ v ∉ S, v ∉ S0 ∧ v ∉ m.support ∧ v ∉ Sv ∧ v ∉ S1 := by
    intro v hv
    subst hS
    simp only [Finset.mem_union, not_or] at hv
    exact ⟨hv.1.1.1, hv.1.1.2, hv.1.2, hv.2⟩
  have hplus : ∀ v, (M v).plus (finAt v g₀) := hg.1
  have hoff : ∀ v ∉ S, ∀ u, twM M Sv m u v = M v := by
    intro v hv u
    obtain ⟨-, h2, h3, -⟩ := hmem v hv
    simp only [twM]
    rw [tu_off Sv m u h3 h2, tw_one]
  have hint0 : ∀ v ∉ S, finAt v g₀ ∈ integralGL (Qv v) 2 := fun v hv => hS1 v (hmem v hv).2.2.2
  have hsph : ∀ v ∉ S, ∀ k ∈ integralGL (Qv v) 2, ∀ ξ : K,
      ((∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w) ξ ∈ 𝒪[Kv K w]) → (M v).val k ξ = 1) ∧
      (¬ (∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w) ξ ∈ 𝒪[Kv K w]) → (M v).val k ξ = 0) :=
    fun v hv k hk ξ => GlobalTheory.T.unramified_theta_value_indicator K hK c v (M v) (hok v) (hS0 v (hmem v hv).1).2 (hS0 v (hmem v hv).1).1 k hk ξ
  choose U hU hUc using fun v => GlobalTheory.T.twisted_local_theta_locally_constant K hK c v (M v) (hok v) (finAt v g₀) (hplus v)
  choose Bf Nf hNf hBN using fun v =>
    GlobalTheory.T.twisted_local_theta_bounded_integral K hK c v (M v) (hok v) (finAt v g₀) (hplus v) _ (compact_alt m v)
  have hW := GlobalTheory.CompanionTheory.AdelicIntegral.eventually_finAt_mem_and_integralGL S g₀ U (fun v _ => hU v) hint0
  have key : ∀ ξ : K, ∃ T : Finset Pl,
      (∀ u, ∀ v ∉ S ∪ T, (twM M Sv m u v).val (finAt v g₀) ξ = 1) ∧
      ∀ u, ∏ᶠ v, (twM M Sv m u v).val (finAt v g₀) ξ = ∏ v ∈ S ∪ T, (twM M Sv m u v).val (finAt v g₀) ξ := by
    intro ξ
    obtain ⟨T, hT⟩ := exists_finset_integral ξ
    have hone : ∀ u, ∀ v ∉ S ∪ T, (twM M Sv m u v).val (finAt v g₀) ξ = 1 := by
      intro u v hv
      simp only [Finset.mem_union, not_or] at hv
      rw [hoff v hv.1 u]
      exact (hsph v hv.1 _ (hint0 v hv.1) ξ).1 (hT v hv.2)
    refine ⟨T, hone, fun u => finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_⟩
    by_contra h
    exact hv (hone u v (by simpa using h))
  refine ⟨_, ∏ v ∈ S, Nf v, ∏ v ∈ S, max (Bf v) 1, hW, Finset.prod_ne_zero_iff.2 fun v _ => hNf v, ?_, ?_, ?_⟩
  · intro g hgW _ u ξ
    refine finprod_congr fun v => ?_
    by_cases hv : v ∈ S
    · exact hUc v _ (hgW.1 v hv) _ ξ
    · rw [hoff v hv u]
      have a := hsph v hv _ (hgW.2 v hv) ξ
      have b := hsph v hv _ (hint0 v hv) ξ
      by_cases hi : ∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w) ξ ∈ 𝒪[Kv K w]
      · rw [a.1 hi, b.1 hi]
      · rw [a.2 hi, b.2 hi]
  · intro u hu ξ
    obtain ⟨T, hone, hfp⟩ := key ξ
    have hloc := fun v => hBN v (tu Sv m u v) (tu_mem Sv m u hu v) ξ
    rw [hfp u]
    constructor
    · rw [norm_prod]
      calc ∏ v ∈ S ∪ T, ‖(twM M Sv m u v).val (finAt v g₀) ξ‖
          ≤ ∏ v ∈ S ∪ T, (if v ∈ S then max (Bf v) 1 else 1) := by
            refine Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => ?_
            by_cases hv : v ∈ S
            · rw [if_pos hv]
              exact (hloc v).1.trans (le_max_left _ _)
            · rw [if_neg hv, hoff v hv u]
              have b := hsph v hv _ (hint0 v hv) ξ
              by_cases hi : ∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → algebraMap K (Kv K w) ξ ∈ 𝒪[Kv K w]
              · rw [b.1 hi]; simp
              · rw [b.2 hi]; simp
        _ = ∏ v ∈ S, (if v ∈ S then max (Bf v) 1 else 1) :=
            (Finset.prod_subset Finset.subset_union_left fun v _ hv => if_neg hv).symm
        _ = ∏ v ∈ S, max (Bf v) 1 := Finset.prod_congr rfl fun v hv => if_pos hv
    · intro hne
      have hfv : ∀ v, (twM M Sv m u v).val (finAt v g₀) ξ ≠ 0 := by
        intro v
        by_cases hv : v ∈ S ∪ T
        · exact Finset.prod_ne_zero_iff.1 hne v hv
        · rw [hone u v hv]; exact one_ne_zero
      have hall : ∀ w : PlK K, w.valuation K (((∏ v ∈ S, Nf v : ℕ) : K) * ξ) ≤ 1 := by
        intro w
        have hl := lies_under w
        by_cases hv : w.under (𝓞 ℚ) ∈ S
        · have h1 := (integral_iff w _).1 ((hloc _).2 (hfv _) w hl)
          have h2 : ((∏ v ∈ S, Nf v : ℕ) : K) * ξ =
              ((∏ v ∈ S.erase (w.under (𝓞 ℚ)), Nf v : ℕ) : K) * ((Nf (w.under (𝓞 ℚ)) : K) * ξ) := by
            rw [← Finset.mul_prod_erase S Nf hv]
            push_cast
            ring
          rw [h2, map_mul]
          exact mul_le_one' (valuation_natCast_le_one w _) h1
        · have hi : ∀ w' : PlK K, w'.asIdeal.LiesOver (w.under (𝓞 ℚ)).asIdeal →
              algebraMap K (Kv K w') ξ ∈ 𝒪[Kv K w'] := by
            by_contra hi
            have := (hsph _ hv _ (hint0 _ hv) ξ).2 hi
            apply hfv (w.under (𝓞 ℚ))
            rw [hoff _ hv u]
            exact this
          rw [map_mul]
          exact mul_le_one' (valuation_natCast_le_one w _) ((integral_iff w _).1 (hi w hl))
      obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K _ hall
      exact ⟨r, hr.symm⟩
  · intro ξ
    obtain ⟨T, -, hfp⟩ := key ξ
    have h : (fun u => ∏ᶠ v, (twM M Sv m u v).val (finAt v g₀) ξ) =
        fun u => ∏ v ∈ S ∪ T, (twM M Sv m u v).val (finAt v g₀) ξ := funext hfp
    rw [h]
    exact Finset.measurable_fun_prod _ fun v _ =>
      measurable_tu Sv m v (GlobalTheory.T.continuous_twisted_local_theta_in_torus K hK c v (M v) (hok v) _ (hplus v) ξ)

end GlobalTheory.CompanionTheory.ThetaFin
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_theta_locally_constant_bounded : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v), AdmM M →
  ∀ (Sv : Finset Pl) (m : Pl →₀ ℤ) (g₀ : G2), g₀ ∈ Gp M → ∃ (W : Set G2) (N : ℕ) (B : ℝ), W ∈ nhds g₀ ∧ N ≠ 0 ∧
    (∀ g ∈ W, g ∈ Gp M → ∀ u (ξ : K), ∏ᶠ v, (twM M Sv m u v).val (finAt v g) ξ = ∏ᶠ v, (twM M Sv m u v).val (finAt v g₀) ξ) ∧
    (∀ u, (∀ v : Sv, u v ∈ unQ v.1) → ∀ ξ : K, ‖∏ᶠ v, (twM M Sv m u v).val (finAt v g₀) ξ‖ ≤ B ∧
      (∏ᶠ v, (twM M Sv m u v).val (finAt v g₀) ξ ≠ 0 → ∃ a : 𝓞 K, (N : K) * ξ = a)) ∧
    ∀ ξ : K, Measurable (fun u => ∏ᶠ v, (twM M Sv m u v).val (finAt v g₀) ξ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ThetaFin.finitePart
end

section
section
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.FexTheta

theorem hasSum_aT : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
    ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M →
    ∀ (Sv : Finset Pl) (m : Pl →₀ ℤ), ∀ g ∈ Gp M,
    HasSum (fun ξ : K => aT n t M Sv g m ξ) (∫ u, ctM M Sv m u * thP n t (twM M Sv m u) g ∂muU Sv) := by
  intro K _ _ h2 hC c n t M hM Sv m g hg
  obtain ⟨hfinμ, hae, -⟩ := GlobalTheory.T.unit_measure_finite_compact_support Sv
  haveI := hfinμ
  haveI : Countable K := (Module.finBasis ℚ K).equivFun.toEquiv.injective.countable
  obtain ⟨-, N, B, -, hN, -, hbd, hmeas⟩ := GlobalTheory.T.product_theta_locally_constant_bounded K h2 c M hM Sv m g hg
  obtain ⟨Wa, hWa, A, hAb, -⟩ := GlobalTheory.T.real_weil_action_local_bound_continuous n t (GL2Classical.realPart g) hg.2
  obtain ⟨hctm, hct1⟩ := GlobalTheory.T.twisted_coefficient_measurable_bounded K c M Sv m
  have hmem : GL2Classical.realPart g ∈ Wa := mem_of_mem_nhds hWa
  set L : Set K := {ξ : K | ∃ a : 𝓞 K, (N : K) * ξ = a} with hL
  set b : K → ℝ := L.indicator (fun ξ => |A| * |B| * ((1 + ‖embC K ξ‖) ^ 4)⁻¹) with hb
  have hbsum : Summable b := by
    rw [hb, ← summable_subtype_iff_indicator]
    exact (GlobalTheory.T.summable_inverse_quartic_over_lattice K h2 hC N hN).mul_left _
  set F : K → (∀ v : Sv, (Qv v.1)ˣ) → ℂ := fun ξ u => ctM M Sv m u * thT n t (twM M Sv m u) g ξ with hF
  have hFm : ∀ ξ, Measurable (F ξ) := fun ξ => by
    simp only [hF, thT]
    exact hctm.mul ((hmeas ξ).const_mul _)
  have hFb : ∀ ξ, ∀ᵐ u ∂muU Sv, ‖F ξ u‖ ≤ b ξ := fun ξ => by
    filter_upwards [hae] with u hu
    obtain ⟨h1, h3⟩ := hbd u hu ξ
    have hp : 0 ≤ ((1 + ‖embC K ξ‖) ^ 4)⁻¹ := by positivity
    have ha : ‖piRc (chC n (Complex.I * t)) (GL2Classical.realPart g) (PhiInf n) (embC K ξ)‖ ≤
        |A| * ((1 + ‖embC K ξ‖) ^ 4)⁻¹ :=
      (hAb _ hmem _).trans (mul_le_mul_of_nonneg_right (le_abs_self A) hp)
    by_cases h0 : ∏ᶠ v, (twM M Sv m u v).val (finAt v g) ξ = 0
    · have : F ξ u = 0 := by simp only [hF, thT, h0, mul_zero]
      rw [this, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => by positivity) _
    · have hξ : ξ ∈ L := h3 h0
      have hbξ : b ξ = |A| * |B| * ((1 + ‖embC K ξ‖) ^ 4)⁻¹ := Set.indicator_of_mem hξ _
      rw [hbξ]
      simp only [hF, thT, norm_mul]
      calc ‖ctM M Sv m u‖ * (‖piRc (chC n (Complex.I * t)) (GL2Classical.realPart g) (PhiInf n) (embC K ξ)‖ *
            ‖∏ᶠ v, (twM M Sv m u v).val (finAt v g) ξ‖)
          ≤ 1 * ((|A| * ((1 + ‖embC K ξ‖) ^ 4)⁻¹) * |B|) := by
            gcongr
            · exact hct1 u
            · exact h1.trans (le_abs_self B)
        _ = |A| * |B| * ((1 + ‖embC K ξ‖) ^ 4)⁻¹ := by ring
  have hFi : ∀ ξ, Integrable (F ξ) (muU Sv) := fun ξ =>
    Integrable.of_bound (hFm ξ).aestronglyMeasurable (b ξ) (hFb ξ)
  have hsum : Summable fun ξ => ∫ u, ‖F ξ u‖ ∂muU Sv := by
    refine Summable.of_nonneg_of_le (fun ξ => integral_nonneg fun _ => norm_nonneg _) (fun ξ => ?_)
      (hbsum.mul_right ((muU Sv).real Set.univ))
    have := norm_integral_le_of_norm_le_const (μ := muU Sv) (f := fun u => ‖F ξ u‖) (C := b ξ)
      (by filter_upwards [hFb ξ] with u hu; simpa using hu)
    exact (le_abs_self _).trans (by simpa using this)
  have key := hasSum_integral_of_summable_integral_norm hFi hsum
  have hint : (∫ u, ∑' ξ, F ξ u ∂muU Sv) = ∫ u, ctM M Sv m u * thP n t (twM M Sv m u) g ∂muU Sv := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hF, thP, tsum_mul_left]
  rw [hint] at key
  exact key

end GlobalTheory.CompanionTheory.FexTheta
end
end

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_fourier_coefficient_hasSum : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (c : HeckeCharacter K)
  (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M → ∀ (Sv : Finset Pl) (m : Pl →₀ ℤ), ∀ g ∈ Gp M,
    HasSum (fun ξ : K => aT n t M Sv g m ξ) (∫ u, ctM M Sv m u * thP n t (twM M Sv m u) g ∂muU Sv) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FexTheta.hasSum_aT
end
