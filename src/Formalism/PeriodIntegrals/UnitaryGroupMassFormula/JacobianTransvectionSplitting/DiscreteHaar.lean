module

public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
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

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace PI.NglqJacSplitW


open Classical in
def modF (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    [LocallyCompactSpace F] (a : F) : ℝ≥0∞ := by
  classical
  exact if h : a = 0 then 0 else ((distribHaarChar F (Units.mk0 a h) : ℝ≥0) : ℝ≥0∞)

def LinModulus : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
    [LocallyCompactSpace F] [SecondCountableTopology F] (ι : Type) [Fintype ι] [DecidableEq ι]
    [MeasurableSpace (ι → F)] [BorelSpace (ι → F)] (M : Matrix ι ι F), M.det ≠ 0 →
    ∀ ν : Measure (ι → F), ν.IsAddHaarMeasure → ∀ S : Set (ι → F), MeasurableSet S →
      ν ((fun x => M *ᵥ x) '' S) = modF F M.det * ν S

def LinModulusV : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
    [LocallyCompactSpace F] [SecondCountableTopology F]
    (V : Type) [AddCommGroup V] [Module F V] [TopologicalSpace V] [MeasurableSpace V]
    [BorelSpace V] (ι : Type) [Fintype ι] [DecidableEq ι], Nonempty (V ≃L[F] (ι → F)) →
    ∀ f : V →ₗ[F] V, LinearMap.det f ≠ 0 →
    ∀ ν : Measure V, ν.IsAddHaarMeasure → ∀ S : Set V, MeasurableSet S →
      ν (f '' S) = modF F (LinearMap.det f) * ν S

def DiagOne : Prop :=
  ∀ (F : Type) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
    [LocallyCompactSpace F] [SecondCountableTopology F] (ι : Type) [Fintype ι] [DecidableEq ι]
    [MeasurableSpace (ι → F)] [BorelSpace (ι → F)] (i : ι) (a : F), a ≠ 0 →
    ∀ ν : Measure (ι → F), ν.IsAddHaarMeasure → ∀ S : Set (ι → F), MeasurableSet S →
      ν ((fun x => Function.update x i (a * x i)) '' S) = modF F a * ν S

end PI.NglqJacSplitW
