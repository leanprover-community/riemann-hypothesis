module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeltaCupProduct
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

set_option autoImplicit false

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem Dtot_cup : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E)
    (Φ : E →+ (Finset ι → E)) (c : Finset ι → E), (∀ x, Φ x ∅ = 0) → c ∅ = 0 →
    (∀ s, Dtot d (Φ (c s)) = 0) → Dtot d (cup Φ c) = cup Φ (delta c) := by
  intro ι _ E _ d Φ c hΦ hc hD
  funext u
  have key := delta_cup_eq Φ c hΦ hc u
  suffices hS : (∑ j ∈ u, ((-1 : ℤ) ^ ({x ∈ u | x < j}).card) • delta (Φ (c ({x ∈ u | x ≤ j}))) ({x ∈ u | j ≤ x}))
      + ((-1 : ℤ) ^ u.card) • d (cup Φ c u) = 0 by
    simp only [Dtot]
    rw [key, add_assoc, hS, add_zero]

  simp only [cup, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j hj => ?_
  have h := congrFun (hD ({x ∈ u | x ≤ j})) ({x ∈ u | j ≤ x})
  simp only [Dtot, Pi.zero_apply] at h
  rw [eq_neg_of_add_eq_zero_left h]
  have hcard : ({x ∈ u | x < j}).card + ({x ∈ u | j ≤ x}).card = u.card := by
    have := Finset.card_filter_add_card_filter_not (s := u) (fun x => x < j)
    simpa only [not_lt] using this
  rw [smul_neg, smul_smul, ← pow_add, hcard, neg_add_cancel]

end GlobalTheory.DI
