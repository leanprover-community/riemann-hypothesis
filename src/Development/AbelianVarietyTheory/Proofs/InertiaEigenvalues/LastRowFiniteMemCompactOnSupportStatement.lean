module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowFiniteMemCompactOnSupport
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

theorem _root_.GlobalTheory.T.lastRow_finite_mem_compact_on_support : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → ∃ K : Set (Fin (m + 1) → Af E), IsCompact K ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → (fun j => pFin E ((h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j)) ∈ K := by
  first
  | exact @GlobalTheory.JSW.lastRow_finite_compact
  | exact GlobalTheory.JSW.lastRow_finite_compact
  | (intros; apply GlobalTheory.JSW.lastRow_finite_compact <;> assumption)
