module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireTheta
public import GroundTheory.AutomorphicForms.ReductionMeasure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormSmoothSpanNormLeShortRationalVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerMapFlatSemiabelian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.lintegral_theta_above_det_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (π' : CuspSub E (m + 1)), π'.IsUnitary →
    ∀ φ' ∈ GlobalTheory.JSW.mspanR π', ∀ G ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → ∀ x : ℝ,
      ∫⁻ g in 𝓕 ∩ {g | 1 ≤ GlobalTheory.RSnm.detAbs g}, ‖φ' g‖ₑ ^ 2 * (∑' ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0}, ‖G (Matrix.vecMul (fun j => algebraMap E (Ad E) (ξ.1 j)) g.val)‖ₑ) * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ x) ∂μ ≠ ⊤ := by
  intro E _ _ _ m π' hπ' φ' hφ' G hG μ _ 𝓕 h𝓕 x
  have hd := GlobalTheory.MSpanDecay.Good.decays
    (GlobalTheory.MSpanDecay.mspanR_le_goodSub hπ' hφ')
  obtain ⟨C, hC⟩ := (GlobalTheory.SBThetaUpper.isSmallKernel_sq_mul hd hG).tsum_le
    (N := ⌈x⌉₊ + 1) (by omega)
  have hI := ((GlobalTheory.RSTheta.integrableOn_absDet_rpow_neg (Nat.succ_pos m) μ h𝓕
    (s := (⌈x⌉₊ + 1 : ℕ) - x) (by push_cast; linarith [Nat.le_ceil x])).const_mul C).lintegral_lt_top
  refine ne_top_of_le_ne_top hI.ne (lintegral_mono fun g => ?_)
  obtain ⟨hs, hle⟩ := hC g
  have h0 := GlobalTheory.RSnm.detAbs_pos g
  change _ ≤ C * GlobalTheory.RSnm.detAbs g ^ _ at hle
  change _ ≤ ENNReal.ofReal (C * GlobalTheory.RSnm.detAbs g ^ _)
  rw [← ENNReal.tsum_mul_left]
  simp only [← eNorm_pow, ← eNorm_mul]
  simp only [← ofReal_norm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs,
    ← ENNReal.ofReal_mul (tsum_nonneg fun _ => norm_nonneg _), neg_sub, sub_eq_neg_add,
    Real.rpow_add h0, ← mul_assoc]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle (by positivity))
