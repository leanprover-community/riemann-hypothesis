module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.Schwarz
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

universe u_1

namespace Bl.general_b_fact_version

theorem goal1 :
  ∀ {Y : Type u_1} [inst : NormedAddCommGroup.{u_1} Y] [inst_1 : NormedSpace.{0, u_1} Complex Y] {g : Y → Complex} {y : Y}
  {R M : Real},
  LT.lt.{0} 0 R →
    DifferentiableOn.{0, u_1, 0} Complex g (Metric.ball.{u_1} y (HMul.hMul.{0, 0, 0} 2 R)) →
      (∀ (v : Y),
          Membership.mem.{u_1, u_1} (Metric.ball.{u_1} y (HMul.hMul.{0, 0, 0} 2 R)) v →
            LE.le.{0} (Norm.norm.{0} (g v)) M) →
        LE.le.{0} (Norm.norm.{u_1} (fderiv.{0, u_1, 0} Complex g y)) (HDiv.hDiv.{0, 0, 0} M R) := by
  intro Y _ _ g y R M hR hd hM
  have hy : y ∈ Metric.ball y (2 * R) := Metric.mem_ball_self (by positivity)
  have hmaps : Set.MapsTo g (Metric.ball y (2 * R)) (Metric.closedBall (g y) (2 * M)) := by
    intro v hv
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖g v - g y‖ ≤ ‖g v‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hM v hv) (hM y hy)
      _ = 2 * M := by ring
  have h := Complex.norm_fderiv_le_div_of_mapsTo_ball hd hmaps (by positivity)
  calc ‖fderiv ℂ g y‖ ≤ 2 * M / (2 * R) := h
    _ = M / R := by rw [mul_div_mul_left _ _ (two_ne_zero)]

end Bl.general_b_fact_version
