module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEigenfunctionBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape

@[expose] public section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

theorem _root_.GlobalTheory.T.kernel_eigenfunction_bound : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (α : GA E N → ℂ) (δ : ℝ) (F : Set (GA E N)), Continuous α → HasCompactSupport α → 0 < δ →
  IsFundamentalDomain (latticeGL E N) F μ → ∃ C₀ : ℝ, ∀ ψ : GA E N → ℂ, Continuous ψ → (∀ γ ∈ latticeGL E N, ∀ g, ψ (γ * g) = ψ g) →
  (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) → (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 →
  ∀ (x : GA E N) (k : ℕ), {γ : GA E N | γ ∈ latticeGL E N ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k →
    ‖ψ x‖ ^ 2 ≤ C₀ * k := by
  intro E _ _ _ N _ _ μ _ α δ F hα hc hδ hF
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  exact GlobalTheory.CompanionTheory.Conc.BesselPt.pointwise μ (latticeGL E N) hα hc hδ hF
