module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FiniteDetectStatement
public import Mathlib.FieldTheory.Galois.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct

section Defs

variable {K K₂ : Type*} [Field K] [Field K₂] [Algebra K K₂] {V : Type*} [AddCommGroup V]
  [Module K V]

noncomputable def galAct (σ : K₂ ≃ₐ[K] K₂) : K₂ ⊗[K] V →ₗ[K] K₂ ⊗[K] V :=
  LinearMap.rTensor V σ.toLinearMap

def kPoints (W : Submodule K₂ (K₂ ⊗[K] V)) : Submodule K V :=
  (W.restrictScalars K).comap (TensorProduct.mk K K₂ V 1)

end Defs

def GaloisDescentStatement : Prop :=
  ∀ (K K₂ V : Type) [Field K] [Field K₂] [Algebra K K₂] [FiniteDimensional K K₂] [IsGalois K K₂]
    [AddCommGroup V] [Module K V] (W : Submodule K₂ (K₂ ⊗[K] V)),
    (∀ σ : K₂ ≃ₐ[K] K₂, ∀ x ∈ W, galAct σ x ∈ W) →
    W = baseSpan K₂ (kPoints W)

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
