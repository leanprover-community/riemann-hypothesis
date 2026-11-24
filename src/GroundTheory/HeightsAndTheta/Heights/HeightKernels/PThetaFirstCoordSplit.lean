module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsTheta
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordFirst
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ThetaGauss
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

namespace KThetaFirstCoordSplit

theorem term_le {g : ℕ} [NeZero g] (Y : Matrix (Fin g) (Fin g) ℝ) (ρ : ℝ) (a u₁ : Fin g → ℝ)
    (hY : Y.PosDef) (hρ : 0 < ρ) (hρY : Y⁻¹ 0 0 = ρ ^ 2) (k : Fin g → ℤ) :
    exp (-π * qf Y (intVec k + a + u₁)) ≤
      exp (-(π / (2 * ρ ^ 2)) * Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) ^ 2) *
        exp (-(π / 2) * qf Y (intVec k + (a + u₁))) := by
  set v := intVec k + (a + u₁) with hv
  have hassoc : intVec k + a + u₁ = v := add_assoc _ _ _
  rw [hassoc]
  set δ := Metric.infDist (u₁ 0 + a 0) (Set.range ((↑) : ℤ → ℝ)) with hδ
  have hδ0 : 0 ≤ δ := Metric.infDist_nonneg
  have hv0 : v 0 = (k 0 : ℝ) + (a 0 + u₁ 0) := by simp [hv, intVec]
  have hδle : δ ≤ |v 0| := by
    have h := Metric.infDist_le_dist_of_mem (x := u₁ 0 + a 0)
      (Set.mem_range_self (f := ((↑) : ℤ → ℝ)) (-(k 0)))
    refine h.trans (le_of_eq ?_)
    rw [Real.dist_eq, hv0]
    congr 1
    push_cast
    ring
  have hδsq : δ ^ 2 ≤ v 0 ^ 2 := by
    rw [← sq_abs (v 0)]
    exact pow_le_pow_left₀ hδ0 hδle 2
  have hcoord : v 0 ^ 2 ≤ ρ ^ 2 * qf Y v := by
    have := KCoord.sq_coord_le Y hY 0 v
    rwa [hρY] at this
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hkey : δ ^ 2 / ρ ^ 2 ≤ qf Y v := by
    rw [div_le_iff₀ hρ2]
    linarith [mul_comm (ρ ^ 2) (qf Y v)]
  have hexp : exp (-(π / 2) * qf Y v) ≤ exp (-(π / (2 * ρ ^ 2)) * δ ^ 2) := by
    apply exp_le_exp.2
    have h1 : (π / (2 * ρ ^ 2)) * δ ^ 2 = (π / 2) * (δ ^ 2 / ρ ^ 2) := by
      field_simp
    have h2 : (π / 2) * (δ ^ 2 / ρ ^ 2) ≤ (π / 2) * qf Y v :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    linarith
  have hsplit : exp (-π * qf Y v) = exp (-(π / 2) * qf Y v) * exp (-(π / 2) * qf Y v) := by
    rw [← exp_add]
    ring_nf
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hexp (exp_pos _).le

end KThetaFirstCoordSplit

theorem ThetaFirstCoordSplit.proof : ThetaFirstCoordSplit.Statement := by
  intro g _ Y ρ a u₁ hY hρ hρY
  have hs1 : Summable fun k : Fin g → ℤ => exp (-π * qf Y (intVec k + a + u₁)) := by
    have := KTheta.summable_exp_qf Y hY π pi_pos (a + u₁)
    simpa only [add_assoc] using this
  have hs2 : Summable fun k : Fin g → ℤ => exp (-(π / 2) * qf Y (intVec k + (a + u₁))) :=
    KTheta.summable_exp_qf Y hY (π / 2) (by positivity) (a + u₁)
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum
    (fun k => KThetaFirstCoordSplit.term_le Y ρ a u₁ hY hρ hρY k) hs1 (hs2.mul_left _)

end GroundTheory.Heights₂.Heights
