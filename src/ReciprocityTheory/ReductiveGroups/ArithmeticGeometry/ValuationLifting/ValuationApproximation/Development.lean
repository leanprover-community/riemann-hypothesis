module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.LiftSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ValuationLifting.ValuationApproximation.LargeSmall
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

namespace ReciprocityTheory.ChartRestriction.G.Lift.VA

theorem valApprox_of (hP : PairSep) (hL : LargeSmall) (hN : NearOne) (hA : Assembly) :
    ReciprocityTheory.ChartRestriction.G.Lift.ApproxStatement := by
  intro Ω _ ι _ v h1 hne n
  have h1' : ∀ i, ∃ x, v i x = WithZero.exp (1 : ℤ) := h1
  have hgt : ∀ i, ∃ x, 1 < v i x := fun i => by
    obtain ⟨x, hx⟩ := h1' i
    refine ⟨x, ?_⟩
    rw [hx]
    first
    | exact WithZero.one_lt_exp_of_pos zero_lt_one
    | (rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; exact zero_lt_one)
    | exact WithZero.coe_lt_coe.2 (by decide)
  obtain ⟨x, hx⟩ := hA Ω ι v h1' (hN Ω ι v (hL Ω ι v hgt (hP Ω ι v h1' hne))) n
  exact ⟨x, hx⟩

end ReciprocityTheory.ChartRestriction.G.Lift.VA
