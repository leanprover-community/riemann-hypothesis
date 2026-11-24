module

public import ReciprocityTheory.DualLattices.CotangentSurjective
public import Mathlib.FieldTheory.IsAlgClosed.Basic
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

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def PrimeHopfOrderStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → v (p : C) < 1 →
    ∀ AA : HopfOrder (C := C) R (ZMod p),
    ∃ (x ω : ZMod p → C) (δ : R),
      x ∈ AA.carrier ∧ x 0 = 0 ∧ (∀ a, ω a ^ p = ω a) ∧ (∀ a, v (ω a - (a.val : C)) < 1) ∧
      (∀ a, x a = ω a * x 1) ∧ x ^ p = (fun a => algebraMap R C δ * x a) ∧
      v (algebraMap R C δ) = v (x 1) ^ (p - 1) ∧
      AA.carrier = Submodule.span R (Set.range fun j : Fin p => x ^ (j : ℕ)) ∧
      augIdeal AA.carrier = Submodule.span R {y | ∃ j : ℕ, 1 ≤ j ∧ j < p ∧ y = x ^ j} ∧
      sqIdeal (augIdeal AA.carrier) = Submodule.span R
        ({fun a => algebraMap R C δ * x a} ∪ {y | ∃ j : ℕ, 2 ≤ j ∧ j < p ∧ y = x ^ j}) ∧
      HasColen R v AA.carrier (v (x 1) ^ (p * (p - 1) / 2))

end ReciprocityTheory.PGsh.Up
