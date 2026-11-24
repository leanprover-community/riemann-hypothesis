module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace PGaussDetFactor

lemma rpow_neg_half_sq {d : ℝ} (hd : 0 < d) : (d ^ (-(1 / 2 : ℝ))) ^ 2 = d⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
  norm_num
  exact Real.rpow_neg_one d

end PGaussDetFactor


open PGaussDetFactor in
theorem GaussDetFactor.proof : GaussDetFactor.Statement := by
  intro g Y B hY hBY
  have hd : 0 < Y.det := hY.det_pos
  have hsq : B.det ^ 2 = (1 / 2 : ℝ) ^ g * Y.det := by
    have := congrArg Matrix.det hBY
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin] at this
    rw [sq]; exact this
  have hB0 : 0 < |B.det| := by
    have : B.det ^ 2 ≠ 0 := by rw [hsq]; positivity
    exact abs_pos.mpr (fun h => this (by rw [h]; ring))
  have hL : 0 ≤ |B.det|⁻¹ := (inv_pos.mpr hB0).le
  have hR : 0 ≤ √2 ^ g * Y.det ^ (-(1 / 2 : ℝ)) := by positivity
  refine (pow_left_inj₀ hL hR (two_ne_zero)).mp ?_
  rw [inv_pow, sq_abs, hsq, mul_pow, rpow_neg_half_sq hd, ← pow_mul, mul_comm g 2, pow_mul,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [mul_inv, one_div, inv_pow, inv_inv]

end GroundTheory.Heights₂.Heights
