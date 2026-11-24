module

public import Formalism.HarderNarasimhan.StatementPl
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

open Module NumberField

noncomputable section

namespace Formalism.HN

def placePart {P ι : Type*} [Fintype P] [Fintype ι] (v : P) :
    Submodule ℝ (EuclideanSpace ℝ (P × ι × Fin 2)) :=
  ⨅ (p : P × ι × Fin 2) (_ : p.1 ≠ v), LinearMap.ker (EuclideanSpace.proj p : EuclideanSpace ℝ (P × ι × Fin 2) →L[ℝ] ℝ).toLinearMap

def PlaceSplit : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ N : Submodule (𝓞 K) V, N.FG →
      Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) =
        (⨆ v, Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N : Set _) ⊓ placePart v) ∧
      ∀ v, Module.finrank ℝ
        (Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓
          placePart v : Submodule ℝ _) = 2 * rkK N

def GramBlock : Prop :=
  ∀ (P E E' ι : Type) [Fintype P] [DecidableEq P] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    (Ev : P → Submodule ℝ E) (Ev' : P → Submodule ℝ E') (T : E →ₗ[ℝ] E') (c : P → ℝ)
    (W : Submodule ℝ E) (u : ι → E),
    (∀ v w, v ≠ w → ∀ x ∈ Ev v, ∀ y ∈ Ev w, inner ℝ x y = 0) →
    (∀ v w, v ≠ w → ∀ x ∈ Ev' v, ∀ y ∈ Ev' w, inner ℝ x y = 0) →
    (∀ v, 0 ≤ c v) → (∀ v, ∀ x ∈ Ev v, T x ∈ Ev' v ∧ ‖T x‖ ≤ c v * ‖x‖) →
    W = (⨆ v, W ⊓ Ev v) → LinearIndependent ℝ u → Submodule.span ℝ (Set.range u) = W →
    (Matrix.gram ℝ (fun i => T (u i))).det ≤
        (∏ v, c v ^ (2 * Module.finrank ℝ (W ⊓ Ev v : Submodule ℝ E))) * (Matrix.gram ℝ u).det ∧
      ((∀ v, ∀ x ∈ Ev v, ∀ y ∈ Ev v, inner ℝ (T x) (T y) = c v ^ 2 * inner ℝ x y) →
        (Matrix.gram ℝ (fun i => T (u i))).det =
          (∏ v, c v ^ (2 * Module.finrank ℝ (W ⊓ Ev v : Submodule ℝ E))) * (Matrix.gram ℝ u).det)

end Formalism.HN
