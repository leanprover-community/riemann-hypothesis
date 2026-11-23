module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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

open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

theorem norm_pow_le_const_mul_one_add_sum_abs_coord_pow :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : Type) [Fintype ι] (b : Module.Basis ι ℝ E) (i : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : E, ‖x‖ ^ i ≤ K * (1 + ∑ c, |b.coord c x| ^ i) := by
  intro E _ _ ι _ b i
  have hB1 : 1 ≤ 1 + ∑ c, ‖b c‖ := by
    have : 0 ≤ ∑ c, ‖b c‖ := Finset.sum_nonneg (fun c _ => norm_nonneg _)
    linarith
  refine ⟨(1 + ∑ c, ‖b c‖) ^ i, by positivity, fun x => ?_⟩
  have hS : 0 ≤ ∑ c, |b.coord c x| ^ i := Finset.sum_nonneg (fun c _ => by positivity)
  have hx : ‖x‖ ≤ ∑ c, |b.coord c x| * ‖b c‖ := by
    conv_lhs => rw [← b.sum_repr x]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, Module.Basis.coord_apply]
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h0 : ‖x‖ = 0 := by
      have : ∑ c, |b.coord c x| * ‖b c‖ = 0 := by simp
      linarith [norm_nonneg x]
    rw [h0]
    have hp : 1 ≤ (1 + ∑ c, ‖b c‖) ^ i := one_le_pow₀ hB1
    calc (0:ℝ) ^ i ≤ 1 := pow_le_one₀ le_rfl zero_le_one
      _ ≤ (1 + ∑ c, ‖b c‖) ^ i * (1 + ∑ c, |b.coord c x| ^ i) := by nlinarith
  · obtain ⟨c0, -, hc0⟩ := Finset.exists_max_image Finset.univ (fun c => |b.coord c x|)
      Finset.univ_nonempty
    have h1 : ‖x‖ ≤ |b.coord c0 x| * (1 + ∑ c, ‖b c‖) := by
      calc ‖x‖ ≤ ∑ c, |b.coord c x| * ‖b c‖ := hx
        _ ≤ ∑ c, |b.coord c0 x| * ‖b c‖ := Finset.sum_le_sum (fun c _ =>
            mul_le_mul_of_nonneg_right (hc0 c (Finset.mem_univ _)) (norm_nonneg _))
        _ = |b.coord c0 x| * ∑ c, ‖b c‖ := by rw [Finset.mul_sum]
        _ ≤ |b.coord c0 x| * (1 + ∑ c, ‖b c‖) :=
            mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have h2 : |b.coord c0 x| ^ i ≤ ∑ c, |b.coord c x| ^ i :=
      Finset.single_le_sum (f := fun c => |b.coord c x| ^ i) (fun c _ => by positivity)
        (Finset.mem_univ c0)
    calc ‖x‖ ^ i ≤ (|b.coord c0 x| * (1 + ∑ c, ‖b c‖)) ^ i :=
          pow_le_pow_left₀ (norm_nonneg _) h1 i
      _ = (1 + ∑ c, ‖b c‖) ^ i * |b.coord c0 x| ^ i := by rw [mul_pow, mul_comm]
      _ ≤ (1 + ∑ c, ‖b c‖) ^ i * (1 + ∑ c, |b.coord c x| ^ i) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith

end GlobalTheory
