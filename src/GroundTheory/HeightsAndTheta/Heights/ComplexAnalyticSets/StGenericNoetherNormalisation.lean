module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
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

universe u

def GenericNoetherNormalisation.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] (n : ℕ) (q : Ideal (MvPolynomial (Fin (n + 1)) A)),
    q.IsPrime → q ≠ ⊥ → q.comap (C : A →+* MvPolynomial (Fin (n + 1)) A) = ⊥ →
    ∃ a : A, a ≠ 0 ∧ ∃ (z : Fin n → MvPolynomial (Fin (n + 1)) A ⧸ q)
      (s : Finset (MvPolynomial (Fin (n + 1)) A ⧸ q)),
      ∀ d : MvPolynomial (Fin (n + 1)) A ⧸ q, ∃ (k : ℕ) (c : MvPolynomial (Fin (n + 1)) A ⧸ q → MvPolynomial (Fin n) A),
        a ^ k • d = ∑ t ∈ s, aeval z (c t) * t

end GroundTheory.Heights₂.Heights
