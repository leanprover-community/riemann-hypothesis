module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralSmoothSpanEqToRealLint
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

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors

theorem _root_.GlobalTheory.T.rankinSelbergThetaIntegral_smoothSpan_eq_toReal_lintegral : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (π : CuspSub E a)
    (F : GA E a → ℂ), F ∈ GlobalTheory.JSW.mspanR π → Continuous F →
    ∀ (Φ : (Fin a → Cinf E) → ℂ), Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)),
    IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ x : ℝ,
    ∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ ≠ ⊤ →
    GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ F F Φ J η x = (((∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ).toReal : ℝ) : ℂ) := by
  first | exact @GlobalTheory.RSPoleToc.thetaZ_eq_toReal_lintegral | exact GlobalTheory.RSPoleToc.thetaZ_eq_toReal_lintegral | (intros; apply GlobalTheory.RSPoleToc.thetaZ_eq_toReal_lintegral <;> assumption)
