module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Group.Measure
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities

theorem scale_int {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {r : ℝ}
    (hr : (Module.finrank ℝ E : ℝ) < r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, 0 < a → 0 < b →
      ∫⁻ x, ENNReal.ofReal ((a + b * ‖x‖) ^ (-r)) ∂μ ≤
        ENNReal.ofReal (K * a ^ (-r) * (a / b) ^ (Module.finrank ℝ E : ℝ)) := by
  have hg := integrable_one_add_norm (μ := μ) hr
  refine ⟨∫ x, (1 + ‖x‖) ^ (-r) ∂μ, integral_nonneg fun x => by positivity, fun a b ha hb => ?_⟩
  have ht : 0 < a / b := div_pos ha hb
  have ha' := ha.ne'
  have hb' := hb.ne'
  have hpt : ∀ x : E, (a + b * ‖x‖) ^ (-r) = a ^ (-r) * (1 + ‖(a / b)⁻¹ • x‖) ^ (-r) := by
    intro x
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le),
      ← Real.mul_rpow ha.le (by positivity : (0 : ℝ) ≤ 1 + (a / b)⁻¹ * ‖x‖)]
    congr 1
    first | (field_simp; done) | (field_simp; ring)
  have hF : Integrable (fun x => a ^ (-r) * (1 + ‖(a / b)⁻¹ • x‖) ^ (-r)) μ :=
    (hg.comp_smul (inv_ne_zero ht.ne')).const_mul (a ^ (-r))
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hF (Filter.Eventually.of_forall fun x =>
    mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg (by positivity) _))]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_const_mul, Measure.integral_comp_smul (μ := μ) (f := fun y => (1 + ‖y‖) ^ (-r)) (R := (a / b)⁻¹),
    smul_eq_mul, inv_pow, inv_inv, abs_of_pos (pow_pos ht _), Real.rpow_natCast]
  exact le_of_eq (by ring)

end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
