module

public import Formalism.HermitianLattices.StatementLat
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
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

open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

def zmap {V W : Type*} [AddCommGroup V] [AddCommGroup W] {R : Type*} [Ring R] [Module R V]
    (ι : V →+ W) (M : Submodule R V) : Submodule ℤ W :=
  (M.toAddSubgroup.map ι).toIntSubmodule

def TraceReal : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∃ (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)),
      (∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ)) ∧
      (∀ a : K, ∃ C : ℝ, ∀ x : V, ‖ι (a • x)‖ ≤ C * ‖ι x‖) ∧
      (∀ M : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsFullLattice K M →
        ∃ _ : DiscreteTopology (zmap ι M), IsZLattice ℝ (zmap ι M))

def GenusCovol : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)),
      (∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ)) →
    ∀ L M : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L → M ∈ genus h L →
    ∀ [DiscreteTopology (zmap ι L)] [IsZLattice ℝ (zmap ι L)]
      [DiscreteTopology (zmap ι M)] [IsZLattice ℝ (zmap ι M)],
      ZLattice.covolume (zmap ι M) = ZLattice.covolume (zmap ι L)

def ShortVectors : Prop :=
  ∀ (N : ℕ) (c C : ℝ), 0 < c → ∃ B : ℝ, ∀ (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin N)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ],
    (∀ v ∈ Λ, v ≠ 0 → c ≤ ‖v‖) → ZLattice.covolume Λ ≤ C →
    ∃ v : Fin N → EuclideanSpace ℝ (Fin N), (∀ i, v i ∈ Λ) ∧ LinearIndependent ℝ v ∧
      ∀ i, ‖v i‖ ≤ B

def GenusScale : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    ∀ L : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L →
    ∃ d : ℕ, 0 < d ∧ ∀ M ∈ genus h L, ∀ x ∈ M, ∀ y ∈ M,
      (d : K) * h x y ∈ (1 : Submodule (NumberField.RingOfIntegers K) K)

def FinIntermediate : Prop :=
  ∀ (W : Type) [AddCommGroup W] (P Q : AddSubgroup W), P ≤ Q → Finite (Q ⧸ P.addSubgroupOf Q) →
    Set.Finite {M : AddSubgroup W | P ≤ M ∧ M ≤ Q}

def IsomOfTrace : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (g : V ≃ₗ[K] V),
    (∀ x y : V, Algebra.trace ℚ K (h (g x) (g y)) = Algebra.trace ℚ K (h x y)) → g ∈ isom h

end Formalism.HermitianLatticesTheory
