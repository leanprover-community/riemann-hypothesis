module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Ideal.Height
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

open Polynomial

def PolynomialPrimeOverZeroHeight.Statement : Prop :=
  ∀ (D : Type u) [CommRing D] [IsDomain D] (Q : Ideal D[X]) [Q.IsPrime],
    Q.comap (C : D →+* D[X]) = ⊥ → Q.height ≤ 1

def QuotientHeightAddOne.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (I : Ideal R), I ≠ ⊥ →
    ∀ (P : Ideal (R ⧸ I)) [P.IsPrime], P.height + 1 ≤ (P.comap (Ideal.Quotient.mk I)).height

def PolynomialDimensionInequality.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (P : Ideal A[X]) [P.IsPrime],
    Cardinal.ofENat P.height + Algebra.trdeg (A ⧸ P.under A) (A[X] ⧸ P) ≤
      Cardinal.ofENat (P.under A).height + 1

def DimensionInequalityOneGenerator.Statement : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B] [IsDomain B]
    [Algebra A B] (x : B), Algebra.adjoin A {x} = ⊤ → Function.Injective (algebraMap A B) →
    ∀ (P : Ideal B) [P.IsPrime],
      Cardinal.ofENat P.height + Algebra.trdeg (A ⧸ P.under A) (B ⧸ P) ≤
        Cardinal.ofENat (P.under A).height + Algebra.trdeg A B

end GroundTheory.Heights₂.Heights.NumbersDVR
