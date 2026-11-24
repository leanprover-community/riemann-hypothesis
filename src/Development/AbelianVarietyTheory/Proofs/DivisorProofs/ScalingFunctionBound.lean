module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

noncomputable section

open Filter Asymptotics

namespace GlobalTheory.BigTop.Fun

theorem exists_log_le_two_rpow {eps : ℝ} (he : 0 < eps) : ∃ x0 : ℝ, ∀ y, x0 ≤ y → Real.log y ≤ 2 * y ^ eps := by
  have hev : ∀ᶠ y in atTop, Real.log y ≤ 2 * y ^ eps := by
    have h := (isLittleO_log_rpow_atTop he).bound (by norm_num : (0 : ℝ) < 2)
    filter_upwards [h, eventually_gt_atTop 0] with y hy hy0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy0 _)] at hy
    exact (le_abs_self _).trans hy
  exact eventually_atTop.1 hev

end GlobalTheory.BigTop.Fun

end
