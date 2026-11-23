module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Polish
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetIwasawaSliceOfTransversal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.measurableSet_iwasawa_slice_of_transversal : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G] (N M K : Subgroup G) (σ : G → G), MeasurableSet (N : Set G) → MeasurableSet (M : Set G) → MeasurableSet (K : Set G) → Measurable σ → (∀ x, σ x * x⁻¹ ∈ K ⊓ M) → (∀ l ∈ K ⊓ M, ∀ x, σ (l * x) = σ x) → (∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N) → (∀ u ∈ N, ∀ m ∈ M, u * m ∈ K → u = 1) → ∀ DN DM : Set G, MeasurableSet DN → MeasurableSet DM → ∃ D : Set G, MeasurableSet D ∧ ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, (u * m * k ∈ D ↔ u ∈ DN ∧ m * (k * (σ k)⁻¹) ∈ DM) := by
  exact @GlobalTheory.exists_measurableSet_slice_of_transversal
