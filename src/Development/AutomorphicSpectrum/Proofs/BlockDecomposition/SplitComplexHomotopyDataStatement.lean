module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitComplexHomotopyData
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

theorem _root_.GlobalTheory.T.split_complex_homotopy_data : ∀ (R P₀ P₁ P₂ : Type) [CommRing R] [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂] (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (t : P₁ →ₗ[R] P₀) (s : P₂ →ₗ[R] P₁), a₁ ∘ₗ a₀ = 0 → a₀ ∘ₗ t ∘ₗ a₀ = a₀ → a₁ ∘ₗ s ∘ₗ a₁ = a₁ → ∃ (j : Hc a₀ a₁ →ₗ[R] P₁) (π : P₁ →ₗ[R] Hc a₀ a₁) (h : P₁ →ₗ[R] P₀) (h' : P₂ →ₗ[R] P₁), π ∘ₗ j = LinearMap.id ∧ a₁ ∘ₗ j = 0 ∧ π ∘ₗ a₀ = 0 ∧ j ∘ₗ π + a₀ ∘ₗ h + h' ∘ₗ a₁ = LinearMap.id := by
  exact @GlobalTheory.CompanionTheory.PerfVB.exists_contraction_onto_homology
