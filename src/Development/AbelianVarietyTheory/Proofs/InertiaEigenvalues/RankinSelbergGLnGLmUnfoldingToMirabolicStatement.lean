module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import GroundTheory.AutomorphicForms.ReductionMeasure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergGLnGLmUnfoldingToMirabolic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.rankinSelbergGLnGLm_unfolding_to_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure],
    ∃ c : ℝ, 0 < c ∧ ∀ (π : CuspSub E (m + r + 1 + 1)) (π' : CuspSub E (m + 1)), π.IsUnitary → π'.IsUnitary →
    ∀ (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ), φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
    ∀ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)), ∀ 𝓕 𝓕₀ : Set (GA E (m + 1)),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∀ x : ℝ, ∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ (x - ((r : ℝ) + 1))) ∂μ ≠ ⊤ → ∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ' h‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ x) ∂μ ≠ ⊤ →
      IntegrableOn (GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x) 𝓕₀ μ ∧
      ∫ h in 𝓕, GlobalTheory.RSnm.rsIntegrand (m + 1) (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' (x : ℂ) h ∂μ =
        (c : ℂ) * ∫ h in 𝓕₀, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x h ∂μ := by
  first | (exact @GlobalTheory.RSnmUnfold.rs_unfold) | (exact GlobalTheory.RSnmUnfold.rs_unfold) | (intros; apply GlobalTheory.RSnmUnfold.rs_unfold  <;> assumption)
