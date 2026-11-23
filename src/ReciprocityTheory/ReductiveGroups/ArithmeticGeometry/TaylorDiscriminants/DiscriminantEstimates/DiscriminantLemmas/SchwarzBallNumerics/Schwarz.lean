module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ScaledBoundInequalityHypothesesOne
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

namespace PI.UnitaryGroupMassFormula.TBNum

open ComplexConjugate

theorem schwarzBall : ReciprocityTheory.ChartRestriction.G.TB.SchwarzBallSt := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.SchwarzBallSt
  intro E _ _ u ρ M hρ hu hM z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hzρ : ‖z‖ < ρ := mem_ball_zero_iff.mp hz
  have hmaps : Set.MapsTo (fun w : ℂ => w • z) (Metric.ball 0 (ρ / ‖z‖)) (Metric.ball (0 : E) ρ) := by
    intro w hw
    rw [mem_ball_zero_iff] at hw ⊢
    rw [norm_smul]
    rw [lt_div_iff₀ hzpos] at hw
    exact hw
  have hg : DifferentiableOn ℂ (fun w : ℂ => u (w • z)) (Metric.ball 0 (ρ / ‖z‖)) :=
    hu.comp (differentiable_id.smul_const z).differentiableOn hmaps
  have h1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) (ρ / ‖z‖) := by
    rw [mem_ball_zero_iff, norm_one, lt_div_iff₀ hzpos, one_mul]
    exact hzρ
  have hmap2 : Set.MapsTo (fun w : ℂ => u (w • z)) (Metric.ball 0 (ρ / ‖z‖))
      (Metric.closedBall (u ((0 : ℂ) • z)) M) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm, zero_smul]
    exact hM _ (hmaps hw)
  have hS := Complex.dist_le_div_mul_dist_of_mapsTo_ball hg hmap2 h1
  simp only [one_smul, zero_smul, dist_eq_norm, sub_zero, norm_one, mul_one] at hS
  rw [div_div_eq_mul_div] at hS
  exact hS

end PI.UnitaryGroupMassFormula.TBNum
