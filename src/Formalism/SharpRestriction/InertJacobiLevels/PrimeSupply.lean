module

public import Formalism.FrobeniusOrbits.Statement
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.LocalRingCardinality.SpanPowerMembership.Primes

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField

def dlogQ (d : ℕ) (hd : d.Prime) : ℝ :=
  haveI : Fact d.Prime := ⟨hd⟩
  haveI : NeZero d := ⟨hd.ne_zero⟩
  (deriv (DirichletCharacter.LFunction
      ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ d)) 1 /
    DirichletCharacter.LFunction
      ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ d) 1).re

structure QDGood (x eps : ℝ) (q d : ℕ) : Prop where
  hyp : HostHyp q d
  q_lo : Real.exp (x ^ (eps / 5) / 2) < q
  q_hi : (q : ℝ) ≤ Real.exp (x ^ (eps / 5))
  d_lo : Real.exp (x ^ (eps / 5) * Real.log x ^ 2 / 2) < d
  d_hi : (d : ℝ) ≤ Real.exp (x ^ (eps / 5) * Real.log x ^ 2)
  split : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ x ^ (eps / 5) → jacobiSym (-(d : ℤ)) p = 1
  dlog : |dlogQ d hyp.2.1| ≤ x ^ eps

end Formalism.MainNotions.Inhab

end
