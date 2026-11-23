module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaZeroDivisorJetBound
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl


theorem _root_.GlobalTheory.T.theta_zero_divisor_jet_bound : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (θ : (Fin g → ℂ) → ℂ)
    (L : (Fin g ⊕ Fin g → ℝ) ≃ₗ[ℝ] (Fin g → ℂ)) (i₀ : Fin g ⊕ Fin g) (c₀ : ℝ),
    Differentiable ℂ θ → (∃ w, θ w ≠ 0) →
    (∀ p, L p ∈ Λ ↔ ∃ k : Fin g ⊕ Fin g → ℤ, p = fun α => (k α : ℝ)) →
    (∀ l ∈ Λ, ∀ w, θ (w + l) = 0 ↔ θ w = 0) →
    (∃ k : ℤ, c₀ = k / 2) →
    ∀ᶠ m : ℕ in Filter.atTop, ∀ (Ix : Type) [Fintype Ix] (r : Ix → Fin g → ℂ),
      (∀ i, (m : ℂ) • r i ∈ Λ ∧ θ (r i) ≠ 0) →
      (∀ w : Fin g → ℂ, (m : ℂ) • w ∈ Λ → θ w ≠ 0 → ∃! i, w - r i ∈ Λ) →
      Nonempty Ix ∧ Fintype.card Ix ≤
        3 * {i | (1 / 4 : ℝ) ≤ Metric.infDist (L.symm (r i) i₀ + c₀) (Set.range ((↑) : ℤ → ℝ))}.ncard := by
  first | exact @GlobalTheory.CompanionTheory.TorsOff.torsion_off_zeros | exact GlobalTheory.CompanionTheory.TorsOff.torsion_off_zeros | (intros; apply GlobalTheory.CompanionTheory.TorsOff.torsion_off_zeros <;> assumption)
