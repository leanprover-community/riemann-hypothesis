module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.RingTheory.Norm.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix LinearMap Module

noncomputable section

namespace Formalism.E

def sgram {R M ι : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid M] [Module R M]
    (B : M →ₗ⋆[R] M →ₗ[R] R) (v : ι → M) : Matrix ι ι R :=
  Matrix.of fun i j => B (v i) (v j)

def orthSum {R M₁ M₂ : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] (B₁ : M₁ →ₗ⋆[R] M₁ →ₗ[R] R) (B₂ : M₂ →ₗ⋆[R] M₂ →ₗ[R] R) :
    (M₁ × M₂) →ₗ⋆[R] (M₁ × M₂) →ₗ[R] R :=
  (B₁.comp (LinearMap.fst R M₁ M₂)).compl₂ (LinearMap.fst R M₁ M₂) +
    (B₂.comp (LinearMap.snd R M₁ M₂)).compl₂ (LinearMap.snd R M₁ M₂)

def SubIndexNorm : Prop :=
  ∀ (S M ι : Type) [CommRing S] [AddCommGroup M] [Module S M]
    [Module.Free ℤ S] [Module.Finite ℤ S] [Fintype ι] [DecidableEq ι]
    (b : Basis ι S M) (N : Submodule S M) (bN : Basis ι S N),
    Nat.card (M ⧸ N) = (Algebra.norm ℤ (b.det fun i => (bN i : M))).natAbs

def CovolGram : Prop :=
  ∀ (E ι : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E),
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) = Real.sqrt (Matrix.gram ℝ b).det

end Formalism.E
