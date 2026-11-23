module

public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
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

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

theorem fubiniStudy_first_term_nonneg {q : ℝ} (hq : 0 ≤ q) : 0 ≤ fubiniStudyProfile q := by
  exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))

theorem projectiveLine_section_self_infty : projectiveLinePairSection (OnePoint.infty : OnePoint ℂ) (OnePoint.infty : OnePoint ℂ) = 0 := by
  rw [projLineSection_infty, infiniteCoord_infty]

theorem projectiveLine_section_self_coe (z : ℂ) : projectiveLinePairSection (z : OnePoint ℂ) z = 1 := by
  rw [projLineSection_coe]

theorem logNormSec_coe (z : ℂ) : logNormSec fsPot projectiveLinePairSection z = -fubiniStudyProfile (‖z‖ ^ 2) := by
  simp only [logNormSec, projectiveLine_section_self_coe, fsPot_φ_coe, finiteCoord_coe, norm_one, one_mul, Real.log_exp,
    fubiniStudyProfile]

theorem logNormSec_infty : logNormSec fsPot projectiveLinePairSection (OnePoint.infty : OnePoint ℂ) = 0 := by
  simp [logNormSec, projectiveLine_section_self_infty]

theorem rW_coe (z : ℂ) : rW fsPot projectiveLinePairSection z = Real.exp 1 + 2 * fubiniStudyProfile (‖z‖ ^ 2) := by
  simp only [rW, logNormSec_coe]
  ring

theorem rW_infty : rW fsPot projectiveLinePairSection (OnePoint.infty : OnePoint ℂ) = Real.exp 1 := by
  simp [rW, logNormSec_infty]

theorem projectiveLine_weight_ge_exp_one (y : OnePoint ℂ) : Real.exp 1 ≤ rW fsPot projectiveLinePairSection y := by
  induction y using OnePoint.rec with
  | infty => rw [rW_infty]
  | coe z =>
    rw [rW_coe]
    have h := fubiniStudy_first_term_nonneg (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 2)
    linarith

theorem one_le_log_rW (y : OnePoint ℂ) : 1 ≤ Real.log (rW fsPot projectiveLinePairSection y) := by
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (rW fsPot projectiveLinePairSection y) := Real.log_le_log (Real.exp_pos 1) (projectiveLine_weight_ge_exp_one y)

end

end ReciprocityTheory.AnForm.P
