module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Localization.FractionRing
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

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

variable {ι ζ : Type*} {n : ℕ}

abbrev LVar (ι ζ : Type*) (n : ℕ) := (ι × Fin n) ⊕ ζ

def diagS (A : Type*) [CommRing A] (n : ℕ) (last : Bool) (e : ℤ) :
    Matrix (Fin n) (Fin n) (LaurentPolynomial A) :=
  Matrix.diagonal fun a =>
    if (if last then a.val + 1 = n else a.val = 0) then LaurentPolynomial.T e else 1

def conjS {L : Type*} [CommRing L] (τ : Type*) (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (e : ℤ) :
    Matrix (Fin n) (Fin n) (LaurentPolynomial (MvPolynomial τ L)) :=
  g.map (fun c => LaurentPolynomial.C (C c)) * diagS (MvPolynomial τ L) n last e *
    gi.map (fun c => LaurentPolynomial.C (C c))

def conjAct {k L : Type*} [CommRing k] [CommRing L] (φ : k →+* L) (isVec : ι → Bool) (S : Set ι)
    [DecidablePred (· ∈ S)] (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) :
    MvPolynomial (LVar ι ζ n) k →+* LaurentPolynomial (MvPolynomial (LVar ι ζ n) L) :=
  eval₂Hom ((LaurentPolynomial.C).comp ((C).comp φ)) fun x =>
    match x with
    | Sum.inl (i, a) =>
      if i ∈ S then
        (if isVec i then
          Matrix.vecMul (fun b => LaurentPolynomial.C (X (Sum.inl (i, b)))) (conjS _ g gi last 1) a
        else
          Matrix.vecMul (fun b => LaurentPolynomial.C (X (Sum.inl (i, b))))
            (conjS _ g gi last (-1)).transpose a)
      else LaurentPolynomial.C (X (Sum.inl (i, a)))
    | Sum.inr z => LaurentPolynomial.C (X (Sum.inr z))

abbrev GenField (k : Type*) [Field k] (n : ℕ) := FractionRing (MvPolynomial (Fin n × Fin n) k)

def genMat (k : Type*) [Field k] (n : ℕ) : Matrix (Fin n) (Fin n) (GenField k n) :=
  Matrix.of fun a b => algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n) (X (a, b))

def genAct (k : Type*) [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)] (last : Bool) :
    MvPolynomial (LVar ι ζ n) k →+* LaurentPolynomial (MvPolynomial (LVar ι ζ n) (GenField k n)) :=
  conjAct ((algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)).comp C) isVec S
    (genMat k n) (genMat k n)⁻¹ last

def valS {k : Type*} [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G : MvPolynomial (LVar ι ζ n) k) : WithTop ℤ :=
  (genAct k isVec S true G).coeff.support.min

def lam1S {k : Type*} [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
    (G : MvPolynomial (LVar ι ζ n) k) : WithBot ℤ :=
  (genAct k isVec S false G).coeff.support.max

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
