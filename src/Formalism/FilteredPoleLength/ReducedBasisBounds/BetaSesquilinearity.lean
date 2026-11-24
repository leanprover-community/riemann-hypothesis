module

public import Formalism.LogFactorialIndices.StatementIdx
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.IsTensorProduct
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

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

def IsLatticeSpanImage : Prop :=
  ∀ (O O' K K' V V₁ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁), IsBaseChange K' j →
    ∀ M : Submodule O V, Formalism.LatticeIndexTer.IsLat O K V M →
      Formalism.LatticeIndexTer.IsLat O' K' V₁ (Submodule.span O' (j '' (M : Set V)))

def FinrankSpanImage : Prop :=
  ∀ (O O' K K' V V₁ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁), IsBaseChange K' j →
    ∀ V' : Submodule K V, finrank K' (Submodule.span K' (j '' (V' : Set V))) = finrank K V'

def SpanImageInf : Prop :=
  ∀ (O O' K K' V V₁ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁), IsBaseChange K' j →
    ∀ (M : Submodule O V) (V' : Submodule K V), Formalism.LatticeIndexTer.IsLat O K V M →
      Submodule.span O' (j '' (M : Set V)) ⊓
          (Submodule.span K' (j '' (V' : Set V))).restrictScalars O' =
        Submodule.span O' (j '' ((M ⊓ V'.restrictScalars O : Submodule O V) : Set V))

def RelIndexSpanImage : Prop :=
  ∀ (O O' K K' V V₁ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁), IsBaseChange K' j →
    ∀ ϖ : O, Irreducible ϖ → Irreducible (algebraMap O O' ϖ) →
    ∀ A B : Submodule O V, A.FG → B.FG →
      Submodule.span K (A : Set V) = Submodule.span K (B : Set V) →
      Formalism.LatticeIndexTer.idx O' V₁ (Submodule.span O' (j '' (A : Set V)))
                (Submodule.span O' (j '' (B : Set V))) =
        Formalism.LatticeIndexTer.idx O V A B

def LocalStepDescent : Prop :=
  ∀ (O O' K K' V V₁ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    [Field K] [Algebra O K] [IsFractionRing O K] [Field K'] [Algebra O' K'] [IsFractionRing O' K']
    [Algebra K K'] [Algebra O K'] [IsScalarTower O K K'] [IsScalarTower O O' K']
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    [AddCommGroup V₁] [Module K' V₁] [Module O' V₁] [IsScalarTower O' K' V₁]
    [Module K V₁] [IsScalarTower K K' V₁] (j : V →ₗ[K] V₁), IsBaseChange K' j →
    ∀ ϖ : O, Irreducible ϖ → Irreducible (algebraMap O O' ϖ) →
    ∀ (M Θ : Submodule O V) (V' : Submodule K V), Formalism.LatticeIndexTer.IsLat O K V M →
      Formalism.LatticeIndexTer.IsLat O K V Θ → ∀ (d Y Z : ℝ) (e : ℕ),
      d * (Formalism.LatticeIndexTer.idx O' V₁
            (Submodule.span O' (j '' (M : Set V)) ⊓
              (Submodule.span K' (j '' (V' : Set V))).restrictScalars O')
            (Submodule.span O' (j '' (Θ : Set V)) ⊓
              (Submodule.span K' (j '' (V' : Set V))).restrictScalars O') : ℝ) ≤
          d * ((e : ℝ) * (finrank K' (Submodule.span K' (j '' (V' : Set V))) : ℝ) + Y) + Z →
        d * (Formalism.LatticeIndexTer.idx O V (M ⊓ V'.restrictScalars O) (Θ ⊓ V'.restrictScalars O) : ℝ) ≤
          d * ((e : ℝ) * (finrank K V' : ℝ) + Y) + Z

end Formalism.LatticeBaseChangeAlt
