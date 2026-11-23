module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenDecompositionExactSequence
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

@[expose] public section

open NumberField GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.eigen_decomposition_exact_sequence : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (V₁ V₂ V₃ : Type) [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃] (ρ₁ : 𝓞 E →+* Module.End k V₁) (ρ₂ : 𝓞 E →+* Module.End k V₂) (ρ₃ : 𝓞 E →+* Module.End k V₃) (f : V₁ →ₗ[k] V₂) (g : V₂ →ₗ[k] V₃), Function.Injective f → Function.Surjective g → LinearMap.range f = LinearMap.ker g → (∀ a x, f (ρ₁ a x) = ρ₂ a (f x)) → (∀ a x, g (ρ₂ a x) = ρ₃ a (g x)) → ∀ (τ : 𝓞 E →+* k) (r n : ℕ) (b₁ : Fin r → V₁) (b₂ : Fin n → V₂), LinearIndependent k b₁ → Submodule.span k (Set.range b₁) = eigSp ρ₁ τ → LinearIndependent k b₂ → Submodule.span k (Set.range b₂) = eigSp ρ₂ τ → r ≤ n ∧ ∃ b₃ : Fin (n - r) → V₃, LinearIndependent k b₃ ∧ Submodule.span k (Set.range b₃) = eigSp ρ₃ τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EigExact.exists_basis_eigSp_quot | exact GlobalTheory.CompanionTheory.Ar.EigExact.exists_basis_eigSp_quot | (intros; apply GlobalTheory.CompanionTheory.Ar.EigExact.exists_basis_eigSp_quot <;> assumption)
