module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CthFac
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

noncomputable section

namespace GlobalTheory.Sieg.CthMult

end GlobalTheory.Sieg.CthMult


open scoped UpperHalfPlane MatrixGroups Manifold in
theorem _root_.GlobalTheory.Sieg.cthFac_multipliable : ∀ (c : ℕ) (q t : ℂ), ‖q‖ < 1 → t ≠ 0 →
    Multipliable (fun m : ℕ => _root_.GlobalTheory.Sieg.cthFac c q t (m + 1)) := by
  intro c q t hq _
  set g : ℂ → ℂ := fun u => (1 - u * t) ^ c ^ 2 * (1 - u * t⁻¹) ^ c ^ 2 /
    ((1 - u * t ^ c) * (1 - u * (t ^ c)⁻¹)) with hg
  have hgd : DifferentiableAt ℂ g 0 := by
    apply DifferentiableAt.div (by fun_prop) (by fun_prop)
    simp
  have hg0 : g 0 = 1 := by simp [hg]
  have hbig : (fun m : ℕ => g (q ^ (m + 1)) - 1) =O[Filter.atTop] (fun m : ℕ => q ^ (m + 1)) := by
    have h := hgd.isBigO_sub
    rw [hg0] at h
    simp only [sub_zero] at h
    have ht : Filter.Tendsto (fun m : ℕ => q ^ (m + 1)) Filter.atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).comp (Filter.tendsto_add_atTop_nat 1)
    exact h.comp_tendsto ht
  have hsum : Summable (fun m : ℕ => ‖g (q ^ (m + 1)) - 1‖) := by
    refine summable_of_isBigO_nat (g := fun m : ℕ => ‖q‖ ^ (m + 1)) ?_ ?_
    · exact (summable_geometric_of_lt_one (norm_nonneg _) hq).comp_injective (add_left_injective 1)
    · simpa [norm_pow] using hbig.norm_left.norm_right
  have hmul := multipliable_one_add_of_summable hsum
  simpa [hg, _root_.GlobalTheory.Sieg.cthFac] using hmul
