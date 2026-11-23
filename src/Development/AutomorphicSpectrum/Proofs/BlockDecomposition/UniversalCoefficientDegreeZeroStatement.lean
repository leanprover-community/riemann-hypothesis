module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniversalCoefficientDegreeZero
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

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

theorem _root_.GlobalTheory.T.universal_coefficient_degree_zero : ∀ (R A₀ A₁ P₀ P₁ : Type) [CommRing R] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁] (d₀ : A₀ →ₗ[R] A₁) (a₀ : P₀ →ₗ[R] P₁) (ψ₀ : P₀ →ₗ[R] A₀) (ψ₁ : P₁ →ₗ[R] A₁) (e : A₀), ψ₁ ∘ₗ a₀ = d₀ ∘ₗ ψ₀ → d₀ e = 0 → (∀ (M : Type) [AddCommGroup M] [Module R M], QIsoAt (0 : R →ₗ[R] M ⊗[R] P₀) (a₀.lTensor M) (0 : R →ₗ[R] M ⊗[R] A₀) (d₀.lTensor M) (ψ₀.lTensor M)) → (∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (fun m : M ↦ m ⊗ₜ[R] e) ∧ ∀ x : M ⊗[R] A₀, d₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] e = x) → ∃ u : P₀, a₀ u = 0 ∧ ∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (fun m : M ↦ m ⊗ₜ[R] u) ∧ ∀ x : M ⊗[R] P₀, a₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] u = x := by
  exact @GlobalTheory.CompanionTheory.PerfUnit.exists_unit_on_model
