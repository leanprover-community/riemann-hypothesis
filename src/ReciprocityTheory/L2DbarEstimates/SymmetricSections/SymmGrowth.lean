module

public import ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

theorem symmGrowth : symmGrowthStatement.{u} := by
  intro n M z u R δ hR hdeg k w
  have hfin : (z ⁻¹' {w}).Finite := Set.finite_of_encard_le_coe (hdeg w)
  have hcard : hfin.toFinset.card ≤ δ := by
    have := hdeg w
    rw [← hfin.coe_toFinset, Set.encard_coe_eq_coe_finsetCard] at this
    exact_mod_cast this
  unfold fiberSymm fiberVals
  rw [dite_eq_left hfin, Finset.esymm_map_val]
  have hB : 0 ≤ max (R w) 0 := le_max_right _ _
  have hu : ∀ y ∈ hfin.toFinset, ‖u y‖ ≤ max (R w) 0 := by
    intro y hy
    rw [Set.Finite.mem_toFinset] at hy
    have hy' : z y = w := hy
    calc ‖u y‖ ≤ R (z y) := hR y
      _ = R w := by rw [hy']
      _ ≤ max (R w) 0 := le_max_left _ _
  calc ‖∑ t ∈ hfin.toFinset.powersetCard k, t.prod u‖
      ≤ ∑ t ∈ hfin.toFinset.powersetCard k, ‖t.prod u‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ hfin.toFinset.powersetCard k, (max (R w) 0) ^ k := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Finset.mem_powersetCard] at ht
        rw [norm_prod]
        calc ∏ y ∈ t, ‖u y‖ ≤ ∏ _y ∈ t, max (R w) 0 :=
              Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun y hy => hu y (ht.1 hy))
          _ = (max (R w) 0) ^ k := by rw [Finset.prod_const, ht.2]
    _ = ((hfin.toFinset.powersetCard k).card : ℝ) * (max (R w) 0) ^ k := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ δ * (max (R w) 0) ^ k := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hB k)
        rw [Finset.card_powersetCard]
        have h1 := Nat.choose_le_two_pow hfin.toFinset.card k
        have h2 : 2 ^ hfin.toFinset.card ≤ 2 ^ δ := Nat.pow_le_pow_right (by norm_num) hcard
        exact_mod_cast h1.trans h2

end ReciprocityTheory.L2DbarEstimates.Norm
