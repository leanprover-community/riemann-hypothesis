module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsQuotientMeasureOfBruhatFunction
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

open MeasureTheory Topology GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_isQuotientMeasure_of_bruhat : ∀ (T T' : Type) [Group T] [MeasurableSpace T] [MeasurableMul₂ T] [Group T'] [MeasurableSpace T'] [MeasurableMul T'] [MeasurableInv T'] (j : T' →* T), Measurable j → ∀ (m : Measure T) [SFinite m] [m.IsMulLeftInvariant] (m' : Measure T') [SFinite m'] [m'.IsMulRightInvariant] [m'.IsInvInvariant] (b : T → ℝ≥0∞), Measurable b → (∀ t, ∫⁻ s, b (j s * t) ∂m' = 1) → ∃ ν, IsQuotientMeasure j m' m ν := by
  first | exact @GlobalTheory.exists_isQuotientMeasure_of_bruhatFunction | exact GlobalTheory.exists_isQuotientMeasure_of_bruhatFunction | (intros; apply GlobalTheory.exists_isQuotientMeasure_of_bruhatFunction <;> assumption)
