module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasiIsomorphismDegreeOneKernel
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

theorem _root_.GlobalTheory.T.quasi_isomorphism_degree_one_kernel : ∀ (R A₀ A₁ A₂ P₀ P₁ P₂ : Type) [CommRing R] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup A₂] [Module R A₂] [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] (d₀ : A₀ →ₗ[R] A₁) (d₁ : A₁ →ₗ[R] A₂) (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] A₀) (ψ₁ : P₁ →ₗ[R] A₁) (ψ₂ : P₂ →ₗ[R] A₂) (r : P₂ →ₗ[R] P₁) (Z : Submodule R A₁) (dZ : A₀ →ₗ[R] Z), (∀ z, z ∈ Z ↔ d₁ z = 0) → (∀ y, (dZ y : A₁) = d₀ y) → a₁ ∘ₗ a₀ = 0 → ψ₁ ∘ₗ a₀ = d₀ ∘ₗ ψ₀ → ψ₂ ∘ₗ a₁ = d₁ ∘ₗ ψ₁ → a₁ ∘ₗ r ∘ₗ a₁ = a₁ → (∀ (M : Type) [AddCommGroup M] [Module R M], QIsoAt (a₀.lTensor M) (a₁.lTensor M) (d₀.lTensor M) (d₁.lTensor M) (ψ₁.lTensor M)) → ∀ (M : Type) [AddCommGroup M] [Module R M], (∀ x : M ⊗[R] A₁, d₁.lTensor M x = 0 → ∃ (t : M ⊗[R] Z) (y : M ⊗[R] A₀), Z.subtype.lTensor M t + d₀.lTensor M y = x) ∧ (∀ (t : M ⊗[R] Z) (y : M ⊗[R] A₀), Z.subtype.lTensor M t = d₀.lTensor M y → ∃ y' : M ⊗[R] A₀, dZ.lTensor M y' = t) := by
  exact @GlobalTheory.CompanionTheory.PerfectFirstCohomologyUniversal.univ_coeff
