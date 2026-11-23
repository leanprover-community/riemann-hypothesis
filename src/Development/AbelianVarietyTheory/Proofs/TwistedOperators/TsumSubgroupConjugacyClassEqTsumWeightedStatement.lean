module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TsumSubgroupConjugacyClassEqTsumWeighted
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

theorem _root_.GlobalTheory.T.tsum_subgroupConjugacyClass_eq_tsum_weighted : ∀ (H : Type) [Group H] (Γ : Subgroup H) (γ : H), γ ∈ Γ → ∀ (α : H → ℝ≥0∞), (∀ y, ∑' h : Γ.subgroupOf (cent γ), α (((h : cent γ) : H) * y) = 1) → ∀ (G : H → ℝ≥0∞) (x : H), ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, G (x⁻¹ * δ * x) = ∑' g : Γ, α ((g : H) * x) * G (((g : H) * x)⁻¹ * γ * ((g : H) * x)) := by
  first | exact @GlobalTheory.Twist.ClassSumReindex.tsum_ratClass_eq_tsum_weighted | exact GlobalTheory.Twist.ClassSumReindex.tsum_ratClass_eq_tsum_weighted | (intros; apply GlobalTheory.Twist.ClassSumReindex.tsum_ratClass_eq_tsum_weighted <;> assumption)
