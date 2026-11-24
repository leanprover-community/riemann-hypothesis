module

public import Formalism.SatakeDualWeyl.Statement
public import Formalism.HermitianLattices.StatementLat
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

open Matrix

namespace Formalism.UG

variable {K : Type} [Field K] [StarRing K] {n : Type} [Fintype n] [DecidableEq n]

def gram (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K) : Matrix n n K :=
  fun i j => h (Pi.single i 1) (Pi.single j 1)

def glEquiv (g : GL n K) : (n → K) ≃ₗ[K] (n → K) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K) (Matrix.GeneralLinearGroup.toLin g)

def GlEquivApply : Prop :=
  ∀ (K : Type) [Field K] (n : Type) [Fintype n] [DecidableEq n] (g : GL n K) (x : n → K),
    glEquiv g x = (g : Matrix n n K) *ᵥ x

def HformGram : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : Type) [Fintype n] [DecidableEq n]
    (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K) (x y : n → K),
    h x y = hform (starRingEnd K) (gram h) x y

def HermBridge : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : Type) [Fintype n] [DecidableEq n]
    (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K) (g : GL n K),
    g ∈ UJ (starRingEnd K) (gram h) ↔ glEquiv g ∈ Formalism.HermitianLatticesTheory.isom h

def HermBridgeSurj : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : Type) [Fintype n] [DecidableEq n]
    (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K), ∀ u ∈ Formalism.HermitianLatticesTheory.isom h, ∃ g : GL n K, glEquiv g = u

end Formalism.UG
