module

public import Formalism.ThetaLiftIndependence.Statement
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
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

open NumberField

noncomputable section

namespace Formalism.HermitianLatticesTheory

def mass {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (RingOfIntegers K) V) :
    ℝ := by
  classical
  exact if hs : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s then
    ∑ M ∈ hs.choose, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ else 0

def IsOrthoLattice {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [Module (RingOfIntegers K) V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule (RingOfIntegers K) V) (n : ℕ) : Prop :=
  ∃ e : Fin n → V, LinearIndependent K e ∧ Submodule.span K (Set.range e) = ⊤ ∧
    L = Submodule.span (RingOfIntegers K) (Set.range e) ∧
    ∀ i j, h (e i) (e j) = if i = j then 1 else 0

def fDeg (K : Type*) [Field K] [NumberField K] : ℕ := Fintype.card (InfinitePlace K)

def vInv (K : Type*) [Field K] [NumberField K] : ℝ :=
  |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * fDeg K)) / 2

def eulerFac (K : Type*) [Field K] [NumberField K] [StarRing K] (M : ℕ)
    (P : Ideal (RingOfIntegers K)) : ℝ :=
  if conjIdeal (K := K) P = P then
    (1 - (-1 : ℝ) ^ M * (Real.sqrt (Ideal.absNorm P : ℝ)) ^ (-(M : ℤ)))⁻¹
  else
    (1 - (Ideal.absNorm P : ℝ) ^ (-(M : ℤ))) ^ (-(1 : ℝ) / 2)

def lValEta (K : Type*) [Field K] [NumberField K] [StarRing K] (M : ℕ) : ℝ :=
  ∏' P : {P : Ideal (RingOfIntegers K) // P.IsMaximal}, eulerFac K M P.1

def massRatioRightSide (K : Type*) [Field K] [NumberField K] [StarRing K] (M : ℕ) : ℝ :=
  (((Nat.factorial (M - 1) : ℕ) : ℝ) * (vInv K / Real.pi) ^ M) ^ fDeg K /
    Real.sqrt ((2 * vInv K) ^ fDeg K) * lValEta K M

def IsCMUnram (K : Type*) [Field K] [NumberField K] [StarRing K] : Prop :=
  IsTotallyComplex K ∧ (∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) ∧
    ∀ P : Ideal (RingOfIntegers K), P.IsMaximal →
      ∃ θ t : RingOfIntegers K, algebraMap (RingOfIntegers K) K t =
        star (algebraMap (RingOfIntegers K) K θ) ∧ θ - t ∉ P

end Formalism.HermitianLatticesTheory

namespace Formalism.HermitianLatticesTheory

open NumberField

def MassBasic : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ L : Submodule (RingOfIntegers K) V, Submodule.IsFullLattice K L →
      (∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s) ∧
      (∀ s, Formalism.ThetaLiftIndependence.IsClassReps h L s →
        mass h L = ∑ M ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹) ∧
      0 < mass h L

def SiegelMassRatio : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], IsCMUnram K →
    ∀ (M : ℕ), 3 ≤ M →
    ∀ (V V' : Type) [AddCommGroup V] [Module K V] [Module (RingOfIntegers K) V]
      [IsScalarTower (RingOfIntegers K) K V] [AddCommGroup V'] [Module K V']
      [Module (RingOfIntegers K) V'] [IsScalarTower (RingOfIntegers K) K V']
      (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K)
      (L : Submodule (RingOfIntegers K) V) (L' : Submodule (RingOfIntegers K) V'),
      h.IsSymm → h'.IsSymm → IsOrthoLattice h L M → IsOrthoLattice h' L' (M - 1) →
      mass h L / mass h' L' = massRatioRightSide K M

end Formalism.HermitianLatticesTheory
