module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousDensitiesEqOfIntegralsOnCompacts
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.continuous_densities_eq_of_integrals_on_compacts : ∀ (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (B : Set X), IsOpen B → ∀ D D' : X → ℝ≥0∞, ContinuousOn D B → ContinuousOn D' B → (∀ S : Set X, IsCompact S → S ⊆ B → ∫⁻ b in S, D b ∂ν = ∫⁻ b in S, D' b ∂ν) → ∀ b ∈ B, D b = D' b := by
  first | exact @GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq | exact GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq | (intros; apply GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq <;> assumption)
