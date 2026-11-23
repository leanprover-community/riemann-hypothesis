module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportConvolutionTriple
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.finite_support_convolution_triple : ∀ (G₁ G₂ V : Type) [Group G₁] [Group G₂] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G₁ × G₂) V) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (f₁ f₁' f₁'' : G₁ → ℂ) (f₂ f₂' f₂'' : G₂ → ℂ), (∀ f ∈ ({f₁, f₁', f₁''} : Set (G₁ → ℂ)), (Function.support fun q : G₁ ⧸ K₁ => f q.out).Finite ∧ ∀ k ∈ K₁, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → (∀ f ∈ ({f₂, f₂', f₂''} : Set (G₂ → ℂ)), (Function.support fun q : G₂ ⧸ K₂ => f q.out).Finite ∧ ∀ k ∈ K₂, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → (∀ v : V, (∀ k ∈ K₁, ρ (k, 1) v = v) → ∑ᶠ q : G₁ ⧸ K₁, f₁'' q.out • ρ (q.out, 1) v = ∑ᶠ q : G₁ ⧸ K₁, f₁ q.out • ρ (q.out, 1) (∑ᶠ q' : G₁ ⧸ K₁, f₁' q'.out • ρ (q'.out, 1) v)) → (∀ v : V, (∀ k ∈ K₂, ρ (1, k) v = v) → ∑ᶠ q : G₂ ⧸ K₂, f₂'' q.out • ρ (1, q.out) v = ∑ᶠ q : G₂ ⧸ K₂, f₂ q.out • ρ (1, q.out) (∑ᶠ q' : G₂ ⧸ K₂, f₂' q'.out • ρ (1, q'.out) v)) → ∀ v : V, (∀ k ∈ K₁.prod K₂, ρ k v = v) → ∑ᶠ q : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁'' q.out.1 * f₂'' q.out.2) • ρ q.out v = ∑ᶠ q : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁ q.out.1 * f₂ q.out.2) • ρ q.out (∑ᶠ q' : (G₁ × G₂) ⧸ K₁.prod K₂, (f₁' q'.out.1 * f₂' q'.out.2) • ρ q'.out v) := by
  exact @GlobalTheory.CompanionTheory.HeckeProduct.product_operators_mul
