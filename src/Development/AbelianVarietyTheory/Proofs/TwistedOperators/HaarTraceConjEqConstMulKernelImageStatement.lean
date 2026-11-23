module

public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarTraceConjEqConstMulKernelImage
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.haar_trace_conj_eq_const_mul_kernel_image : ∀ {X Y : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X] [BorelSpace X]
    [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [MeasurableSpace Y] [BorelSpace Y]
    (R N K : Subgroup X) (π : R →* Y) (σ : Y →* R),
    IsClosed (R : Set X) → IsClosed (N : Set X) → N ≤ R → IsOpen (K : Set X) → IsCompact (K : Set X) →
    Continuous π → Continuous σ → (∀ y, π (σ y) = y) → (∀ r : R, π r = 1 ↔ r.1 ∈ N) →
    ∀ ρ : Measure R, ρ.IsHaarMeasure →
    ∃ (κ : ℝ) (la : Measure N) (ν : Measure Y), 0 < κ ∧ la.IsHaarMeasure ∧ ν.IsHaarMeasure ∧ ∀ b : X,
      ρ.real {r : R | b⁻¹ * r.1 * b ∈ K} = κ * la.real {n : N | b⁻¹ * n.1 * b ∈ K} * ν.real (π '' {r : R | b⁻¹ * r.1 * b ∈ K}) := by
  first | exact @GlobalTheory.RowFubini.haar_trace_conj_eq | exact GlobalTheory.RowFubini.haar_trace_conj_eq | (intros; apply GlobalTheory.RowFubini.haar_trace_conj_eq <;> assumption)
