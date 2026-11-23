module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FiniteDetectStatement
public import Mathlib.NumberTheory.NumberField.Basic
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

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct

def KerCoreStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Submodule K V)
    (Fam : ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁], (V →ₗ[K] K₁) → Prop),
    (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁] (f : V →ₗ[K] K₁), Fam K₁ f →
      W ≤ LinearMap.ker f) →
    (∀ v : V, (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁] (f : V →ₗ[K] K₁),
      Fam K₁ f → f v = 0) → v ∈ W) →
    (∀ (K' K₁ : Type) [Field K'] [NumberField K'] [Algebra K K'] [Field K₁] [NumberField K₁]
      [Algebra K K₁] (e : K' →ₐ[K] K₁) (f : V →ₗ[K] K'), Fam K' f →
      ∃ f₁ : V →ₗ[K] K₁, Fam K₁ f₁ ∧ ∀ v, f₁ v = e (f v)) →
    ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra K K₁) (ρ : ℕ)
      (g : Fin ρ → (V →ₗ[K] K₁)) (cfL : Fin ρ → Module.Dual K₁ (K₁ ⊗[K] V)),
      (∀ i, Fam K₁ (g i)) ∧ (∀ i v, cfL i ((1 : K₁) ⊗ₜ[K] v) = g i v) ∧
      (∀ x : K₁ ⊗[K] V, (∀ i, cfL i x = 0) ↔ x ∈ baseSpan K₁ W) ∧
      Module.finrank K W + ρ = Module.finrank K V

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
