module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import GroundTheory.AutomorphicForms.ReductionMeasure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulPartialRankinSelbergL
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.RSJ Filter Topology Formalism.UG

theorem _root_.GlobalTheory.T.unfoldedThetaIntegral_eq_mul_partialRankinSelbergL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (σ σ' : CG E a), 1 ≤ a → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∈ T, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal = Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ T) → (∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → UnrOutside T σ → UnrOutside T σ' → ∃ (N : ℕ) (Φ : (Fin a → Cinf E) → ℂ) (π π' : CuspSub E a) (φ φ' : GA E a → ℂ), CG.mk π = σ ∧ CG.mk π' = σ' ∧ φ ∈ GlobalTheory.JSW.mspanR π ∧ φ' ∈ GlobalTheory.JSW.mspanR π' ∧ φ ≠ 0 ∧ φ' ≠ 0 ∧ 0 < N ∧ ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ (∀ ℓ : Fin a, (ℓ : ℕ) + 1 = a → tsupport Φ ⊆ {u | ∀ w, u ℓ w ≠ 0}) ∧ ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ (∀ x : ℝ, 0 < (H x).re ∧ (H x).im = 0) ∧ ∀ x : ℝ, 1 < x → GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) ∧ GlobalTheory.RSJ.Zint μ 𝓕 φ φ Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) ∧ GlobalTheory.RSJ.Zint μ 𝓕 φ' φ' Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ' w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) := by
  first
  | exact @GlobalTheory.ZEul.Smooth.zint_eq_mul_partialL_smooth
  | exact GlobalTheory.ZEul.Smooth.zint_eq_mul_partialL_smooth
  | (intros; apply GlobalTheory.ZEul.Smooth.zint_eq_mul_partialL_smooth <;> assumption)
