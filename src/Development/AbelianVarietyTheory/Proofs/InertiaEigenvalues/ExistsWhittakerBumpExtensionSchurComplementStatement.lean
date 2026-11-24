module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Definitions.Divisors.MirSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWhittakerBumpExtensionSchurComplement
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

theorem _root_.GlobalTheory.T.exists_whittaker_bump_extension_schur_complement : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (β : GA E (m + 1) → ℂ),
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, β (u * g) = GlobalTheory.JSW.psiN u * β g) →
    (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) →
    (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
      ∀ u ∈ U, ∀ g, β (g * finGL E (m + 1) u) = β g) →
    (∀ g, ContDiffOn ℝ ∞ (chart β g) (invSet E (m + 1))) →
    ∃ b : GA E (m + r + 1 + 1) → ℂ,
      (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧
      (∃ C : Set (GA E (m + r + 1 + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := (m + r + 1) + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) (m + r + 1)), b p ≠ 0 →
        ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + r + 1 + 1)), u⁻¹ * p ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + r + 1 + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + r + 1 + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ g, b (g * finGL E (m + r + 1 + 1) u) = b g) ∧
      (∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + r + 1 + 1))) ∧
      ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, b (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) = β h := by
  first | (exact @GlobalTheory.SchurExt.exists_ext) | (exact GlobalTheory.SchurExt.exists_ext) | (intros; apply GlobalTheory.SchurExt.exists_ext <;> assumption)
