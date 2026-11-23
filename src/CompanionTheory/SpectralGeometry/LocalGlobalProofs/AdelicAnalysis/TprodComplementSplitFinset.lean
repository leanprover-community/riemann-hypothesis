module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Real

@[expose] public section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TailCut

theorem tprod_tail_cut : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (S S' : Finset ι),
    Summable (fun v => |a v - 1|) → S ⊆ S' →
      ∏' v : {v // v ∉ S}, a v.1 = (∏ v ∈ S' \ S, a v) * ∏' v : {v // v ∉ S'}, a v.1 := by
  intro ι _ a S S' hsum hSS'
  have hmul : ∀ T : Set ι, Multipliable (T.mulIndicator a) := by
    intro T
    have hs : Summable fun v => ‖T.mulIndicator a v - 1‖ := by
      refine Summable.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_) hsum
      by_cases hv : v ∈ T
      · simp [Set.mulIndicator_of_mem hv, Real.norm_eq_abs]
      · simp [Set.mulIndicator_of_notMem hv]
    have h := multipliable_one_add_of_summable hs
    simpa using h
  have e1 : (∏' v : {v // v ∉ S}, a v.1) = ∏' v, Set.mulIndicator {v | v ∉ S} a v :=
    tprod_subtype {v | v ∉ S} a
  have e2 : (∏' v : {v // v ∉ S'}, a v.1) = ∏' v, Set.mulIndicator {v | v ∉ S'} a v :=
    tprod_subtype {v | v ∉ S'} a
  have hsplit : (∏' v, Set.mulIndicator {v | v ∉ S} a v) =
      ∏' v, (Set.mulIndicator (↑(S' \ S) : Set ι) a v * Set.mulIndicator {v | v ∉ S'} a v) := by
    refine tprod_congr fun v => ?_
    by_cases h1 : v ∈ S
    · have h2 : v ∈ S' := hSS' h1
      simp [Set.mulIndicator, h1, h2]
    · by_cases h2 : v ∈ S'
      · simp [Set.mulIndicator, h1, h2]
      · simp [Set.mulIndicator, h1, h2]
  have hfin : (∏' v, Set.mulIndicator (↑(S' \ S) : Set ι) a v) = ∏ v ∈ S' \ S, a v := by
    rw [tprod_eq_prod (s := S' \ S)]
    · exact Finset.prod_congr rfl fun v hv => Set.mulIndicator_of_mem (Finset.mem_coe.mpr hv) a
    · intro v hv
      exact Set.mulIndicator_of_notMem (by rwa [Finset.mem_coe]) a
  rw [e1, e2, hsplit, Multipliable.tprod_mul (hmul _) (hmul _), hfin]

end GlobalTheory.CompanionTheory.SW.TailCut
