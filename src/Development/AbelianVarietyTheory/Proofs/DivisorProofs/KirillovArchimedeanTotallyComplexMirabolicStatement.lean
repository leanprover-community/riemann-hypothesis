module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Definitions.Divisors.MirSet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovArchimedeanTotallyComplexMirabolic
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

@[expose] public section

open NumberField GlobalTheory.CuspRep MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.kirillov_archimedean_totallyComplex_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (β f : GL (Fin (m + 1)) (Cinf E) → ℂ), (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin (m + 1)), ∀ y, β (u * y) = (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) * β y) → (∃ B : Lie E (m + 1) → ℂ, ContDiffOn ℝ ∞ B (invSet E (m + 1)) ∧ ∀ y : GL (Fin (m + 1)) (Cinf E), B (toL y.val) = β y) → (∃ C : Set (GL (Fin (m + 1)) (Cinf E)), IsCompact C ∧ ∀ y ∈ GlobalTheory.JSW.mirSet (Cinf E) m, β y ≠ 0 → ∃ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin (m + 1)), u⁻¹ * y ∈ C) → (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin (m + 1)), ∀ y, f (u * y) = (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) * f y) → Continuous f → (∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * height y ^ N) → f 1 ≠ 0 → ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ ∧ ∀ y ∈ GlobalTheory.JSW.mirSet (Cinf E) m, ∫ x, k x * f (y * γ x) ∂ν = β y := by
  first | exact @GlobalTheory.JSW.MirCinf.kirillov_cinf | exact GlobalTheory.JSW.MirCinf.kirillov_cinf | (intros; apply GlobalTheory.JSW.MirCinf.kirillov_cinf <;> assumption)
