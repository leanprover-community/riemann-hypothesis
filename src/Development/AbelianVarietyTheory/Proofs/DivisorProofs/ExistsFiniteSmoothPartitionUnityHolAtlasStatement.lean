module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSmoothPartitionUnityHolAtlas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.exists_finite_smooth_partition_unity_holAtlas : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n), ∃ (N : ℕ) (c : Fin N → A.ι) (χ : Fin N → M → ℝ), (∀ j, A.SmoothOn univ fun y => (χ j y : ℂ)) ∧ (∀ j, tsupport (χ j) ⊆ (A.e (c j)).source) ∧ ∀ y, ∑ j, χ j y = 1 := by
  first | exact @GlobalTheory.exists_finite_smooth_partition_holAtlas | exact GlobalTheory.exists_finite_smooth_partition_holAtlas | (intros; apply GlobalTheory.exists_finite_smooth_partition_holAtlas <;> assumption)
