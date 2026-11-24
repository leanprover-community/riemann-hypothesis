module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothWhittakerBumpAdelicGL
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

theorem _root_.GlobalTheory.T.exists_smooth_whittakerBump_adelicGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ b : GA E (a + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (a + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (a + 1)), IsCompact C ∧ ∀ p, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (a + 1)), u⁻¹ * p ∈ C) ∧ (∃ U : Subgroup (GL (Fin (a + 1)) (Af E)), IsOpen (U : Set (GL (Fin (a + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (a + 1) u) = b g) ∧ ∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (a + 1)) := by
  first | (exact @GlobalTheory.WhitBump.exists_bump_glob) | (exact GlobalTheory.WhitBump.exists_bump_glob) | (intros; apply GlobalTheory.WhitBump.exists_bump_glob  <;> assumption)
