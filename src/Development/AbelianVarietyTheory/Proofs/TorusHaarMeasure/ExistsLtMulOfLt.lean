module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EqZeroOfLePolyExp
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EventuallyComparable
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FjNormMulExpLeSupFlow
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsomOfGramEq
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneAddInvFirstMinimumLeOfMajorants
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ClosedModes

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_lt_mul_of_lt {s a : ℝ} (ha : 0 ≤ a) (hs : s < a) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ s < θ * a := by
  rcases ha.eq_or_lt with h | h
  · subst h
    exact ⟨1 / 2, by norm_num, by norm_num, by simpa using hs⟩
  · have hm : max s 0 < a := max_lt hs h
    have h0 : 0 ≤ max s 0 := le_max_right _ _
    have h1 : s ≤ max s 0 := le_max_left _ _
    refine ⟨(max s 0 + a) / (2 * a), by positivity, ?_, ?_⟩
    · rw [div_lt_one (by positivity)]
      linarith
    · have : (max s 0 + a) / (2 * a) * a = (max s 0 + a) / 2 := by field_simp
      rw [this]
      linarith

theorem modeHalf_closed : (∀ (r : ℕ) (X : Data E r), ModeHalfStatement X) := by
  intro r X la F ps a hF hps ha hmean ξ hξ ν hν x hx
  obtain ⟨θ, hθ0, hθ1, hνθ⟩ := exists_lt_mul_of_lt ha hν
  exact ModeDecay.fj_eq_zero_of_decay fj_norm_mul_exp_le_sup_flow
    ClosedDiscontinuity.propDisc_and_la1GG.2 r X la F (θ * a) hF
    (pnorm_le_exp_neg_tt_near_cusp
      (MajNear.maj_near_orth MajorantContinuity.majorant_continuity.1) maj_lact_rmul
      NormFactor.nfac_transform r X la F ps a hF hps ha hmean θ (θ * a) hθ0 hθ1 rfl)
    ξ hξ ν hνθ x hx

end GlobalTheory.ClosedModes
