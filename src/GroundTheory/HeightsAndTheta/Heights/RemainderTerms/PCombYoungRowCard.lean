module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
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

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem CombYoungRowCard.proof : CombYoungRowCard.Statement := by
  intro m lam i
  rw [← Finset.card_range (lam i)]
  refine Finset.card_bij (fun p _ => p.1.2) ?_ ?_ ?_
  · intro p hp
    have hp' : p.1.1 = i := (mem_filter.1 hp).2
    have hc : p.1.2 < lam p.1.1 := (mem_filter.1 p.2).2
    rw [hp'] at hc
    exact mem_range.2 hc
  · intro p hp q hq h
    have hp' : p.1.1 = i := (mem_filter.1 hp).2
    have hq' : q.1.1 = i := (mem_filter.1 hq).2
    exact Subtype.ext (Prod.ext (hp'.trans hq'.symm) h)
  · intro c hc
    have hc' : c < lam i := mem_range.1 hc
    have hmem : ((i, c) : Fin m × ℕ) ∈ youngCells lam := by
      unfold youngCells
      refine mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, mem_range.2 ?_⟩, hc'⟩
      exact lt_of_lt_of_le hc'
        (Finset.single_le_sum (fun j _ => Nat.zero_le (lam j)) (mem_univ i))
    exact ⟨⟨(i, c), hmem⟩, mem_filter.2 ⟨mem_univ _, rfl⟩, rfl⟩

end GroundTheory.Heights₂.Heights.RestTerms
