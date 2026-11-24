module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Complex.Liouville

@[expose] public section

universe u_1 u_2

namespace Bl.general_b_fact_second_bis_form

theorem goal1 :
  ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Complex E]
  [inst_2 : NormedAddCommGroup.{u_2} F] [inst_3 : NormedSpace.{0, u_2} Complex F] {f : E → F} {y : E} {δ M : Real},
  LT.lt.{0} 0 δ →
    DifferentiableOn.{0, u_1, u_2} Complex f (Metric.ball.{u_1} y δ) →
      (∀ (z : E), Membership.mem.{u_1, u_1} (Metric.ball.{u_1} y δ) z → LE.le.{0} (Norm.norm.{u_2} (f z)) M) →
        LE.le.{0} (Norm.norm.{max u_2 u_1} (fderiv.{0, u_1, u_2} Complex f y)) (HDiv.hDiv.{0, 0, 0} M δ) := by
  intro E F _ _ _ _ f y δ M hδ hf hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y (Metric.mem_ball_self hδ))
  have hdy : DifferentiableAt ℂ f y :=
    hf.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM0 hδ.le) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hline : ∀ t : ℂ, HasDerivAt (fun t : ℂ => y + t • v) v t :=
    fun t => by simpa using ((hasDerivAt_id t).smul_const v).const_add y
  have hmaps : ∀ t : ℂ, ‖t‖ * ‖v‖ < δ → y + t • v ∈ Metric.ball y δ :=
    fun t ht => by simpa [Metric.mem_ball, dist_eq_norm, norm_smul] using ht
  have hr : ∀ r : ℝ, 0 < r → r < δ → ‖fderiv ℂ f y v‖ * r ≤ M * ‖v‖ := by
    intro r hr0 hrδ
    have hgd : DifferentiableOn ℂ (fun t : ℂ => f (y + t • v)) (Metric.ball 0 (δ / ‖v‖)) :=
      hf.comp (by fun_prop) fun t ht => hmaps t (by
        rwa [Metric.mem_ball, dist_zero_right, lt_div_iff₀ hvpos] at ht)
    have hcl : DiffContOnCl ℂ (fun t : ℂ => f (y + t • v)) (Metric.ball 0 (r / ‖v‖)) :=
      hgd.diffContOnCl_ball
        (Metric.closedBall_subset_ball ((div_lt_div_iff_of_pos_right hvpos).2 hrδ))
    have hderiv : deriv (fun t : ℂ => f (y + t • v)) 0 = fderiv ℂ f y v :=
      (hdy.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) (hline 0) (by simp)).deriv
    have hb : ∀ z ∈ Metric.sphere (0 : ℂ) (r / ‖v‖), ‖f (y + z • v)‖ ≤ M := by
      intro z hz
      rw [mem_sphere_zero_iff_norm] at hz
      exact hM _ (hmaps z (by rw [hz, div_mul_cancel₀ _ hvpos.ne']; exact hrδ))
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (div_pos hr0 hvpos) hcl hb
    rwa [hderiv, div_div_eq_mul_div, le_div_iff₀ hr0] at h
  have ht : Filter.Tendsto (fun r : ℝ => ‖fderiv ℂ f y v‖ * r) (nhdsWithin δ (Set.Iio δ))
      (nhds (‖fderiv ℂ f y v‖ * δ)) :=
    ((continuous_const.mul continuous_id).tendsto δ).mono_left nhdsWithin_le_nhds
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
  refine le_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT hδ] with r h1 using hr r h1.1 h1.2

end Bl.general_b_fact_second_bis_form
