module

public import Formalism.CharacterColumnKernels.StatementN
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
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

open Finset Classical Polynomial

noncomputable section

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

universe u v w

open Formalism.NG

section Det

variable {O K X G : Type*} [CommRing O] [CommRing K] [Algebra O K] [Monoid G]
  {n : Type} [Fintype n] [DecidableEq n]

def tSpan (T : Subalgebra O (X → O)) (r : G →* (X → Matrix n n K)) : Set (X → Matrix n n K) :=
  {F | ∃ (s : Finset G) (c : G → X → O), (∀ g, c g ∈ T) ∧
    F = ∑ g ∈ s, fun x => algebraMap O K (c g x) • r g x}

def FromT (T : Subalgebra O (X → O)) (f : X → K) : Prop :=
  ∃ t ∈ T, ∀ x, algebraMap O K (t x) = f x

end Det

def LemmaDetPoly : Prop :=
  ∀ (O K X G : Type*) [CommRing O] [CommRing K] [Algebra O K] [Monoid G]
    (n : Type) [Fintype n] [DecidableEq n] (T : Subalgebra O (X → O))
    (r : G →* (X → Matrix n n K)),
    (∀ (g : G) (k : ℕ), FromT T (fun x => (Matrix.charpolyRev (r g x)).coeff k)) →
    ∀ (m : ℕ) (a : Fin m → X → Matrix n n K), (∀ i, a i ∈ tSpan T r) →
    ∀ s : Fin m →₀ ℕ, FromT T (fun x => AddMonoidAlgebra.coeff (Matrix.det (∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) K) • (a i x).map MvPolynomial.C))
      s)

def LemmaDetSub : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] (X' G : Type*) [Monoid G] (T' : Subalgebra O (X' → O))
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    (r : G →* (X' → Matrix d d (FractionRing O))),
    (∀ (g : G) (k : ℕ), FromT T' (fun x => (Matrix.charpolyRev (r g x)).coeff k)) →
    (∀ a ∈ R', a ∈ tSpan T' r) →
    ∀ (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R'), ∃ f ∈ T', ∀ x',
      algebraMap O (FractionRing O) (f x') =
        (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det

def BridgeDet : Prop :=
  LemmaDetPoly.{u, u, v, w} → StatBlockDet.{u, v} → LemmaDetSub.{u, v, w}

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
