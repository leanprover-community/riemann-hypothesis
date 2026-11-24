module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
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

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

variable {n d : ℕ}

def leadForm (f : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  homogeneousComponent f.totalDegree f

def leadIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (leadForm '' (J : Set (MvPolynomial (Fin n) ℂ)))

def originIdeal (n : ℕ) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (Set.range X)

def linIdeal (A : Matrix (Fin d) (Fin n) ℂ) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (Set.range (linPoly A))

def ConeAvoids (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (N : ℕ) : Prop :=
  originIdeal n ^ N ≤ leadIdeal J ⊔ linIdeal A

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.ComplexSets
