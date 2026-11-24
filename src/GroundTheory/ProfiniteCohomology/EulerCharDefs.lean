module

public import GroundTheory.ProfiniteCohomology.ContinuousCochains
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

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]




variable [IsTopologicalGroup G]


variable (k G) in
def HasFiniteCohomology (P : ℕ → Prop) : Prop :=
  ∀ (A : Rep.{u} k G) [IsDiscreteRep A], Finite A → P (Nat.card A) →
    (∀ q : ℕ, Finite (cohomology A q)) ∧ ∀ q : ℕ, 3 ≤ q → Subsingleton (cohomology A q)

noncomputable def eulerChar (A : Rep.{u} k G) [IsDiscreteRep A] : ℚ :=
  ∏ q ∈ Finset.range 3, (Nat.card (cohomology A q) : ℚ) ^ ((-1 : ℤ) ^ q)

end GroundTheory.ProfCoh
