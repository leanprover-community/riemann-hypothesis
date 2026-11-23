module

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Quotient
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.LocalField

section Completion

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

def openFiniteIndex : Set (Subgroup G) :=
  {H | IsOpen (H : Set G) ∧ H.FiniteIndex}


variable {G} in
def quotientMapOfLE {H H' : Subgroup G} (h : H ≤ H') : G ⧸ H →* G ⧸ H' :=
  QuotientGroup.map H H' (MonoidHom.id G) h


def openCompletion : Subgroup (∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) where
  carrier := {a | ∀ (H H' : openFiniteIndex G) (h : (H : Subgroup G) ≤ H'), quotientMapOfLE h (a H) = a H'}
  one_mem' := fun H H' h => by simp
  mul_mem' := fun ha hb H H' h => by simp [map_mul, ha H H' h, hb H H' h]
  inv_mem' := fun ha H H' h => by simp [map_inv, ha H H' h]

namespace openCompletion

variable {G}






theorem discreteTopology_quotient (H : openFiniteIndex G) : DiscreteTopology (G ⧸ (H : Subgroup G)) :=
  QuotientGroup.discreteTopology H.2.1

end openCompletion

end Completion

end GroundTheory.LocalField
