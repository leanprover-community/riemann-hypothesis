module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RankCount
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up CategoryTheory

theorem UpperTheory.V.ZK.Up.fibCount : UpperTheory.V.ZK.Up.FibCount := by
  intro Y T B _ _ _ _ β g c hc S hS
  classical
  choose! y hy using hS
  have := Fintype.ofFinite T
  calc S.card ≤ c * (S.image (fun s => β (y s))).card := by
        apply Finset.card_le_mul_card_image
        intro t _
        rcases (S.filter (fun s => β (y s) = t)).eq_empty_or_nonempty with hF | ⟨s₀, hs₀⟩
        · rw [hF]
          simp
        · rw [← Finset.card_image_of_injective _ (sub_left_injective (b := s₀))]
          apply hc
          intro u hu
          obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hu
          have hs' := Finset.mem_filter.1 hs
          have hs₀' := Finset.mem_filter.1 hs₀
          refine ⟨y s - y s₀, by rw [map_sub, hs'.2, hs₀'.2, sub_self], ?_⟩
          rw [map_sub, ← hy s hs'.1, ← hy s₀ hs₀'.1]
    _ ≤ c * Nat.card T := by
        apply Nat.mul_le_mul_left
        rw [Nat.card_eq_fintype_card]
        exact Finset.card_le_univ _
