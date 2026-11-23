module

public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2ConvolutionLocallyCompactMem
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace

theorem _root_.GlobalTheory.T.l2_convolution_locally_compact_mem : ∀ {G L : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [SecondCountableTopology L] [T2Space L] [LocallyCompactSpace L] [MeasurableSpace L] [BorelSpace L] (ν : Measure L) [IsFiniteMeasureOnCompacts ν] (j : L →* G), Continuous j → ∀ D : L → ℂ, Continuous D → HasCompactSupport D → ∀ φ ψ : G → ℂ, Continuous φ → ∀ h : MemL2Quotient Γ μ φ, (∀ g, ψ g = ∫ y, φ (g * j y) * D y ∂ν) → ∃ h' : MemL2Quotient Γ μ ψ, ∀ W : Submodule ℂ (L2 Γ μ), IsSubrep (R Γ μ) W → h.toL2 ∈ W → h'.toL2 ∈ W := by
  first | exact @GlobalTheory.CompanionTheory.AutomorphicL2Convolution.memL2_convolution_mem | exact GlobalTheory.CompanionTheory.AutomorphicL2Convolution.memL2_convolution_mem | (intros; apply GlobalTheory.CompanionTheory.AutomorphicL2Convolution.memL2_convolution_mem <;> assumption)
