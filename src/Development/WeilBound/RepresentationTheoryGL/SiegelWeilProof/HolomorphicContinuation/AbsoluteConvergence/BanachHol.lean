module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
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

open MeasureTheory Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

def BanachHol : Prop := ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] (U : Set ℂ) (F : ℂ → X → ℂ), IsOpen U →
  ContinuousOn (fun y : ℂ × X => F y.1 y.2) (U ×ˢ univ) → (∀ x, DifferentiableOn ℂ (fun z => F z x) U) →
  ∃ Φ : ℂ → C(X, ℂ), DifferentiableOn ℂ Φ U ∧ ∀ z ∈ U, ∀ x, Φ z x = F z x

def DslopeFam : Prop := ∀ (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] (U : Set ℂ) (s₀ : ℂ) (F : ℂ → X → ℂ),
  IsOpen U → s₀ ∈ U → ContinuousOn (fun y : ℂ × X => F y.1 y.2) (U ×ˢ univ) → (∀ x, DifferentiableOn ℂ (fun z => F z x) U) →
  (∀ x, F s₀ x = 0) →
  ContinuousOn (fun y : ℂ × X => dslope (fun z => F z y.2) s₀ y.1) (U ×ˢ univ) ∧
    ∀ x, DifferentiableOn ℂ (fun z => dslope (fun z => F z x) s₀ z) U

def FactorL : Prop := ∀ (G : Type) [TopologicalSpace G] (S : Submodule ℂ (G → ℂ)) (l : (G → ℂ) → ℂ) (C : Set G),
  IsCompact C → (∀ F ∈ S, Continuous F) → (∀ (a : ℂ), ∀ F ∈ S, ∀ F' ∈ S, l (a • F + F') = a * l F + l F') →
  (∀ F ∈ S, ∀ M : ℝ, (∀ x ∈ C, ‖F x‖ ≤ M) → ‖l F‖ ≤ M) →
  ∃ L : C(C, ℂ) →L[ℂ] ℂ, ∀ F ∈ S, ∀ (hF : Continuous F), l F = L ⟨fun x => F x, hF.comp continuous_subtype_val⟩

def KRCpt : Prop := ∀ n : ℕ, CompactSpace (KR n)

end PositivityTheory.Rg.Sw.AbsSt
