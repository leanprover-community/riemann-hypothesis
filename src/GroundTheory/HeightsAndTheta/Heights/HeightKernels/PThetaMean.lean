module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsTheta
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory

namespace KThetaMean

variable {g : ℕ}

theorem continuous_exp_qf_add (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ) (a : Fin g → ℝ) :
    Continuous fun x : Fin g → ℝ => exp (-c * qf Y (x + a)) := by
  have h1 : Continuous fun x : Fin g → ℝ => x + a := continuous_id.add continuous_const
  have h2 : Continuous fun x : Fin g → ℝ => qf Y (x + a) := by
    unfold qf
    exact h1.dotProduct (continuous_const.matrix_mulVec h1)
  exact (continuous_const.mul h2).rexp

end KThetaMean

theorem ThetaMean.proof (h : ThetaInnerMean.Statement) : ThetaMean.Statement := by
  intro g X Y a b hY
  set F : (Fin g → ℝ) → ℝ := fun x => exp (-(2 * π) * qf Y (x + a)) with hF
  have hinner : ∀ u₁ : Fin g → ℝ,
      ∫ u₂ in Set.Icc (0 : Fin g → ℝ) 1, thetaNorm X Y a b u₁ u₂ ^ 2 =
        ∑' k : Fin g → ℤ, F (intVec k + u₁) := by
    intro u₁
    rw [h g X Y a b u₁ hY]
    congr 1
    simp [hF, add_assoc, add_comm, add_left_comm]
  simp_rw [hinner]
  have hs : ∀ u : Fin g → ℝ, Summable fun k : Fin g → ℤ => F (intVec k + u) := by
    intro u
    simp only [hF, add_assoc]
    exact KTheta.summable_exp_qf Y hY (2 * π) (by positivity) (u + a)
  rw [KTheta.integral_cube_tsum F (fun x => (exp_pos _).le)
    (KThetaMean.continuous_exp_qf_add Y (2 * π) a) hs]
  rw [hF, integral_add_right_eq_self (fun x : Fin g → ℝ => exp (-(2 * π) * qf Y x)) a]
  exact KTheta.integral_exp_two_pi_qf Y hY

end GroundTheory.Heights₂.Heights
