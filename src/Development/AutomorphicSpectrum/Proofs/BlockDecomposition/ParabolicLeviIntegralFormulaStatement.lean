module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitHomeoApply
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLeviIntegralFormula
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

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

theorem _root_.GlobalTheory.T.parabolic_levi_integral_formula : ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (ν : Measure π.ker) [ν.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (D : Set π.ker) (𝓕₁ : Set G₁), MeasurableSet D → NullMeasurableSet 𝓕₁ μ₁ → NullMeasurableSet (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)) (Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) ∧ ∀ f : P → ℝ≥0∞, Measurable f → ∫⁻ p in (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)), f p ∂(Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) = ∫⁻ u in 𝓕₁, ∫⁻ m in D, f ((m : P) * ι u) ∂ν ∂μ₁ := by
  exact @GlobalTheory.CompanionTheory.SplitExtLat.setLIntegral_splitHomeo_image_prod
