module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Regular.RegularSequence
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

open IsLocalRing CategoryTheory RingTheory.Sequence

universe u

def AuslanderBuchsbaumProjDimUpper.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (n d : ℕ) (ms : List R),
    HasProjectiveDimensionLE (ModuleCat.of R M) n →
    (∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d) →
    (∀ r ∈ ms, r ∈ maximalIdeal R) → IsWeaklyRegular M ms →
      HasProjectiveDimensionLE (ModuleCat.of R M) (d - ms.length)

end GroundTheory.Heights₂.Heights
