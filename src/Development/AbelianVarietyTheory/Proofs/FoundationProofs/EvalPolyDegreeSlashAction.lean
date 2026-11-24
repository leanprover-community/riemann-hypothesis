module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem eval_polySlash : ∀ (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) (z : ℂ), p ∈ degreeLT ℂ (w + 1) → ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ≠ 0 → (slP w g p).eval z = ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ w * p.eval (((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / ((g 1 0 : ℂ) * z + (g 1 1 : ℂ))) := by
  intro w g p z hp hz
  have hn : p.natDegree < w + 1 := by
    rcases eq_or_ne p 0 with rfl | h
    · simp
    · exact (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hp)
  have hs : slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i •
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
    simp [slP, LinearMap.sum_apply, LinearMap.toSpanSingleton_apply]
  rw [hs, eval_finsetSum, eval_eq_sum_range' hn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  simp only [eval_smul, eval_mul, eval_pow, eval_add, eval_C, eval_X, smul_eq_mul]
  rw [div_pow, ← Nat.sub_add_cancel hi', pow_add]
  rw [Nat.sub_add_cancel hi']
  have hD : ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ i ≠ 0 := pow_ne_zero _ hz
  have e := mul_inv_cancel₀ hD
  linear_combination (-(p.coeff i * ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) ^ i *
    ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ (w - i))) * e

end GlobalTheory.HeckeFamilyMatrices
