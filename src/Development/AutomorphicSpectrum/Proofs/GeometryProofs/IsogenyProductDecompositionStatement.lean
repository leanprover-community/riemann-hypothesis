module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsogenyProductDecomposition
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.isogeny_product_decomposition : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (n N : ℕ) (C : Fin n → Out.PolAV (Sp (𝓞 K))) (B : Out.PolAV (Sp (𝓞 K))) (ψ : ∀ k, (C k).A ⟶ B.A), (∀ k, IsMonHom (ψ k)) → 0 < N → (∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ B.A, ∃ x : ∀ k, Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ (C k).A, y = (List.ofFn fun k => x k ≫ ψ k).prod) → (∀ x : ∀ k, Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ (C k).A, (List.ofFn fun k => x k ≫ ψ k).prod = 1 → ∀ k, x k ^ N = 1) → ∃ χ : ∀ k, B.A ⟶ (C k).A, (∀ k, IsMonHom (χ k)) ∧ (∀ k, ψ k ≫ χ k = 𝟙 (C k).A ^ N) ∧ ∀ k k', k ≠ k' → ψ k ≫ χ k' = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.isogeny_product_decomposition | exact GlobalTheory.CompanionTheory.Relay.isogeny_product_decomposition | (intros; apply GlobalTheory.CompanionTheory.Relay.isogeny_product_decomposition <;> assumption)
