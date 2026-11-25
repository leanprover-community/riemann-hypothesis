module

public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem finrank_real_V {n : ℕ} : Module.finrank ℝ (V n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (V n), Complex.finrank_real_complex, finrank_euclideanSpace_fin]

theorem mvPow : MVPowStatement := by
  intro n s hn
  haveI : Nontrivial (V n) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_real_V]; omega)
  have hind : (ball (0 : V n) 1).indicator (fun z : V n => ‖z‖ ^ (-2 * s)) =
      fun z => (Iio (1 : ℝ)).indicator (fun y : ℝ => y ^ (-2 * s)) ‖z‖ := by
    funext z
    by_cases h : ‖z‖ < 1 <;> simp [Set.indicator, h]
  rw [← integrable_indicator_iff measurableSet_ball, hind, integrable_fun_norm_addHaar,
    finrank_real_V]
  have hfun : (fun y : ℝ => y ^ (2 * n - 1) • (Iio (1 : ℝ)).indicator (fun y : ℝ => y ^ (-2 * s)) y) =
      (Iio (1 : ℝ)).indicator (fun y : ℝ => y ^ (2 * n - 1) * y ^ (-2 * s)) := by
    funext y
    simp only [indicator_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hfun, IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
    Measure.restrict_restrict measurableSet_Iio, Set.inter_comm, Set.Ioi_inter_Iio, ← IntegrableOn]
  have hcongr : EqOn (fun y : ℝ => y ^ (2 * n - 1) * y ^ (-2 * s))
      (fun y : ℝ => y ^ ((2 * n : ℝ) - 1 - 2 * s)) (Ioo 0 1) := by
    intro y hy
    have hy0 : 0 < y := hy.1
    simp only
    rw [← Real.rpow_natCast, ← Real.rpow_add hy0]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
    push_cast
    ring
  rw [integrableOn_congr_fun hcongr measurableSet_Ioo,
    intervalIntegral.integrableOn_Ioo_rpow_iff one_pos]
  constructor <;> intro h <;> linarith

end ReciprocityTheory.L2DbarEstimates.C
