module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegKrull

@[expose] public section

open scoped BigOperators Matrix ComplexConjugate
open Polynomial

namespace GlobalTheory

theorem integral_of_forall_height_one :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
      (t : FractionRing R),
      (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → ∃ a b : R, b ∉ p ∧
        t * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a) →
      ∃ a : R, algebraMap R (FractionRing R) a = t := by
  intro R _ _ _ _ t h
  exact ReciprocityTheory.ChartRestriction.G.T0.mem_of_mem_heightOne_localizations (K := FractionRing R) t
    (fun p hp h1 => @h p hp h1)

end GlobalTheory
