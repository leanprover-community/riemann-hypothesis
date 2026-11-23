module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
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
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.log_period_limit : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ), ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ (ws : ℕ → Fin n → ℂ) (W : Submodule ℤ Λ) (per : W →+ (Fin g → ℂ)), (∀ m, ws m ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le) ∧ Tendsto (fun m => GroundTheory.Heights₂.Heights.Regular.expCover a (ws m)) atTop (𝓝 z) ∧ (∀ x : W, Tendsto (fun m => L.P (ws m) x) atTop (𝓝 (per x))) ∧ (∀ (x : ℕ → Λ) (p : Fin g → ℂ), Tendsto (fun m => L.P (ws m) (x m)) atTop (𝓝 p) → ∃ x₀ : W, p = per x₀ ∧ ∀ᶠ m in atTop, x m = x₀) ∧ (∀ φ : W →+ ℤ, (∀ x : W, (∀ x' : W, L.E x x' = 0) → φ x = 0) → ∃ x₀ : W, ∀ x : W, φ x = L.E x₀ x) ∧ ∀ Hb : Matrix (Fin g) (Fin g) ℂ, Hb.IsHermitian → (∀ x x' : W, (per x ⬝ᵥ Hb *ᵥ star (per x')).im = L.E x x') → (∀ x : W, (∀ x' : W, L.E x x' = 0) → Hb *ᵥ star (per x) = 0) → ∀ v : Fin g → ℂ, 0 ≤ (v ⬝ᵥ Hb *ᵥ star v).re ∧ (v ⬝ᵥ Hb *ᵥ star v).re ≤ C * ∑ i, ‖v i‖ ^ 2 ∧ ((v ⬝ᵥ Hb *ᵥ star v).re = 0 → v ∈ Submodule.span ℂ {p | ∃ x : W, (∀ x' : W, L.E x x' = 0) ∧ p = per x}) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RiemannLimit.bounded_on_limit_lattice | exact GlobalTheory.CompanionTheory.Ar.RiemannLimit.bounded_on_limit_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.RiemannLimit.bounded_on_limit_lattice <;> assumption)
