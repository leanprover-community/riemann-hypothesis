module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireTheta
public import GroundTheory.AutomorphicForms.ReductionMeasure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnAbsDetRpowLeOneFundamentalDomainStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieModelFiniteBaseChange
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_theta_below_det_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (π' : CuspSub E (m + 1)), π'.IsUnitary →
    ∀ φ' ∈ GlobalTheory.JSW.mspanR π', ∀ G ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → ∀ x : ℝ, 1 < x →
      ∫⁻ g in 𝓕 ∩ {g | GlobalTheory.RSnm.detAbs g ≤ 1}, ‖φ' g‖ₑ ^ 2 * (∑' ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0}, ‖G (Matrix.vecMul (fun j => algebraMap E (Ad E) (ξ.1 j)) g.val)‖ₑ) * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ x) ∂μ ≠ ⊤ := by
  intro E _ _ _ m π' hπ φ' hφ G hG μ _ 𝓕 h𝓕 x hx
  have hbound := GlobalTheory.ThetaSqLow.exists_bound hπ hφ hG
  obtain ⟨C, hC⟩ := hbound
  have hi : IntegrableOn (fun g : GA E (m + 1) => GlobalTheory.RSnm.detAbs g ^ (x - 1))
      (𝓕 ∩ {g | GlobalTheory.RSnm.detAbs g ≤ 1}) μ :=
    GlobalTheory.T.integrableOn_absDet_rpow_le_one_fundamentalDomain
      E (m + 1) m.succ_pos μ 𝓕 h𝓕 (x - 1) (by linarith)
  refine ne_top_of_le_ne_top (hi.const_mul C).2.ne (lintegral_mono fun g => ?_)
  have hδ := GlobalTheory.RSnm.detAbs_pos g
  refine (mul_le_mul_left (hC g) _).trans ?_
  rw [mul_comm, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), Real.eNorm_eq_ofReal_abs]
  refine ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) (le_abs_self _))
  beta_reduce
  rw [Real.rpow_sub_one hδ.ne']
  ring
