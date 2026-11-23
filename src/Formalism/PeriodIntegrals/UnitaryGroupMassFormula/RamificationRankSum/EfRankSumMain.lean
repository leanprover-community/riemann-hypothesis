module

public import Formalism.PeriodIntegrals.EfRankSum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RamificationRankSum.Lattice
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RamificationRankSum.Points
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
public import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PI.UnitaryGroupMassFormula.EfRankSum

open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing

theorem sum_ef (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] [Module.Finite O ↥(As O A)] [Module.Flat O ↥(As O A)]
    {ϖ : O} (hϖ : Irreducible ϖ) :
    (∑ᶠ ζ : Pts O A, ep ϖ ζ * fdeg ζ) = Module.finrank O ↥(As O A) := by
  classical
  have : Finite (Pts O A) := finite_pts O A
  let : Fintype (Pts O A) := Fintype.ofFinite _
  let : Fintype ((maximalIdeal O).primesOver ↥(As O A)) := Fintype.ofEquiv _ (ptsEquiv O A)
  rw [finsum_eq_sum_of_fintype, ← Ideal.sum_ramification_inertia_eq_finrank (maximalIdeal O),
    ← (ptsEquiv O A).sum_comp]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [ptsEquiv_apply, ep_eq_ramificationIdx hϖ, fdeg_eq_inertiaDeg]

theorem efRankSum_main : PI.EfRankSum := by
  intro O _ _ _ K _ _ _ A _ _ _ _ _ _ ϖ hϖ hfin _
  haveI : Module.Free O ↥(As O A) := free_as O K A
  exact ⟨finite_pts O A, by rw [sum_ef O A hϖ, finrank_as O K A]⟩

end PI.UnitaryGroupMassFormula.EfRankSum
