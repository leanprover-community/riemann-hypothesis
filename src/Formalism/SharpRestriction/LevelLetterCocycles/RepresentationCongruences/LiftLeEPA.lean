module

public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.FinalStep0
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

theorem lift_le_ePA (l : ℕ) [Fact l.Prime] (hl : 11 ≤ l) (h η H M : ℕ) (h1 : 1 ≤ h) (hη : 20 * η ≤ h)
    (hH : H ≤ h + η) (hM : M ≤ h) (jumps : Finset ℤ)
    (hj : ∀ u ∈ jumps, -(M : ℤ) ≤ u ∧ u ≤ h) :
    (Formalism.MainNotions.LiftingTheory.ePA l M H jumps : ℝ) ≤
      71 / 10 * (h : ℝ) / l + 71 / 10 + 2 * Real.logb l (2 * (h : ℝ)) := by
  unfold Formalism.MainNotions.LiftingTheory.ePA Formalism.MainNotions.LiftingTheory.eUA Formalism.MainNotions.LiftingTheory.eWA Formalism.MainNotions.LiftingTheory.aA Formalism.MainNotions.LiftingTheory.JSet
  exact lift_le l hl h η H M h1 hη hH hM jumps hj

end Formalism.MainNotions.N.FrobeniusPowerSeries
