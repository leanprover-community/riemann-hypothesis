module

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

def hdual {S K V : Type*} [CommRing S] [Field K] [StarRing K] [Algebra S K] [AddCommGroup V]
    [Module K V] [Module S V] [IsScalarTower S K V] (B : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule S V) : Submodule S V :=
  ⨅ y ∈ L, (1 : Submodule S K).comap ((B y).restrictScalars S)

def HermDual : Prop :=
  ∀ (S K V ι : Type) [CommRing S] [Field K] [StarRing K] [Algebra S K]
    [AddCommGroup V] [Module K V] [Module S V] [IsScalarTower S K V] [Fintype ι] [DecidableEq ι]
    (B : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis ι K V),
    Function.Injective (algebraMap S K) →
    (∀ s : S, star (algebraMap S K s) ∈ Set.range (algebraMap S K)) →
    (Submodule.span S (Set.range b) ≤ hdual B (Submodule.span S (Set.range b)) ↔
      ∀ i j, B (b i) (b j) ∈ Set.range (algebraMap S K)) ∧
    ∀ [Module.Free ℤ S] [Module.Finite ℤ S] (GS : Matrix ι ι S),
      (∀ i j, B (b i) (b j) = algebraMap S K (GS i j)) → GS.det ≠ 0 →
      (Submodule.span S (Set.range b)).toAddSubgroup.relIndex
          (hdual B (Submodule.span S (Set.range b))).toAddSubgroup =
        (Algebra.norm ℤ GS.det).natAbs ∧
      (hdual B (Submodule.span S (Set.range b)) = Submodule.span S (Set.range b) ↔
        IsUnit GS.det)

end Formalism.E
