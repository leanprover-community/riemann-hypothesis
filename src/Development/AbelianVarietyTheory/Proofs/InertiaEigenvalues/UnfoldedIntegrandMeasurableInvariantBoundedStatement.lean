module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import GroundTheory.AutomorphicForms.ReductionMeasure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedIntegrandMeasurableInvariantBounded
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

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

theorem _root_.GlobalTheory.T.unfoldedIntegrand_measurable_invariant_bounded : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (φ φ' : GA E (m + 1) → ℂ)
    (Φ : (Fin (m + 1) → Cinf E) → ℂ) (N : ℕ) (x : ℝ),
    Continuous (GlobalTheory.JSW.whit φ) → Continuous (GlobalTheory.JSW.whit φ') →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    Continuous Φ → (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    Measurable (GlobalTheory.ZEul.uInt φ φ' Φ N x) ∧
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, GlobalTheory.ZEul.uInt φ φ' Φ N x (u * g) = GlobalTheory.ZEul.uInt φ φ' Φ N x g) ∧
    ∀ g, ‖GlobalTheory.ZEul.uInt φ φ' Φ N x g‖ ≤ (‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ + ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖) / 2 := by
  first | exact @GlobalTheory.ZEulProps.uInt_props | exact GlobalTheory.ZEulProps.uInt_props | (intros; apply GlobalTheory.ZEulProps.uInt_props <;> assumption)
