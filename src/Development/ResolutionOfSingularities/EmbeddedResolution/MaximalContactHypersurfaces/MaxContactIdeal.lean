module

public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
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

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]

def IsDerivBalanced (I : X.IdealSheafData) (m : ℕ) : Prop :=
  ∀ i < m, derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i)

theorem isDerivBalanced_iff (I : X.IdealSheafData) (m : ℕ) :
    IsDerivBalanced k p I m ↔ ∀ i < m, derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i) :=
  Iff.rfl

theorem IsDerivBalanced.derivIdealSheafIterate_pow_le {I : X.IdealSheafData} {m : ℕ} (h : IsDerivBalanced k p I m)
    {i : ℕ} (hi : i < m) : derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i) :=
  h i hi

theorem isDerivBalanced_of_pow_le {I : X.IdealSheafData} {m : ℕ}
    (h : ∀ i < m, derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i)) : IsDerivBalanced k p I m :=
  h

theorem isDerivBalanced_one (I : X.IdealSheafData) : IsDerivBalanced k p I 1 := by
  intro i hi
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  have h : derivIdealSheafIterate k p 0 I = I := derivIdealSheafIterate_zero k p I
  exact le_of_eq (by rw [h, Nat.sub_zero])

noncomputable def maxContactIdeal (I : X.IdealSheafData) (m : ℕ) : X.IdealSheafData :=
  derivIdealSheafIterate k p (m - 1) I

@[simp] theorem maxContactIdeal_eq_derivIdealSheafIterate (I : X.IdealSheafData) (m : ℕ) :
    maxContactIdeal k p I m = derivIdealSheafIterate k p (m - 1) I :=
  rfl

theorem maxContactIdeal_one (I : X.IdealSheafData) : maxContactIdeal k p I 1 = I :=
  rfl

theorem maxContactIdeal_ideal (I : X.IdealSheafData) (m : ℕ) (U : X.affineOpens) :
    (maxContactIdeal k p I m).ideal U =
      @derivIdealIterate k _ _ _ (sectionsAlgebra k p U.1) (m - 1) (I.ideal U) :=
  derivIdealSheafIterate_ideal k p (m - 1) I U

def IsMaxContactInvariant (I : X.IdealSheafData) (m : ℕ) : Prop :=
  maxContactIdeal k p I m * derivIdealSheaf k p I ≤ I

theorem isMaxContactInvariant_of_mul_le {I : X.IdealSheafData} {m : ℕ}
    (h : maxContactIdeal k p I m * derivIdealSheaf k p I ≤ I) : IsMaxContactInvariant k p I m :=
  h

end FunctorialResolution.EmbeddedResolution
