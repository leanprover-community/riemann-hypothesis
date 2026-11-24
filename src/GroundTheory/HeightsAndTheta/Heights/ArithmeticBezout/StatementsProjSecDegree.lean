module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def projVar (e : ℕ) (i : Fin (e + 1)) : FractionRing (MvPolynomial (Fin (e + 1)) ℂ) :=
  algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (X i)

def projPar {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) :
    Vertical.Par e n → FractionRing (MvPolynomial (Fin (e + 1)) ℂ)
  | .inl (i, j) =>
      projVar e i.succ * algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (A 0 j) -
        projVar e 0 * algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (A i.succ j)
  | .inr j => algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (A 0 j) / projVar e 0

def ProjSecDegree.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    ComplexSets.projDegree J A =
      Module.finrank (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
        (Vertical.SecAlg
          (J.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
          (projPar A))

end

end GroundTheory.Heights₂.Heights
