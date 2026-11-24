module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMatrixCoefficientStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixCoeffDecayFirstPartStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixCoeffDecaySecondPartStatement
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

open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory
namespace MatrixCoeff

theorem norm_le_max_parts (n : ℕ) (w : Fin n ⊕ Fin n → ℝ) : ‖w‖ ≤ max ‖pPart w‖ ‖qPart w‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rcases i with j | j
  · exact le_max_of_le_left (by
      have := PiLp.norm_apply_le (pPart w) j
      simpa [pPart] using this)
  · exact le_max_of_le_right (by
      have := PiLp.norm_apply_le (qPart w) j
      simpa [qPart] using this)

theorem one_add_norm_pow_le_parts (n N : ℕ) (w : Fin n ⊕ Fin n → ℝ) :
    (1 + ‖w‖) ^ N ≤ (1 + ‖pPart w‖) ^ N + (1 + ‖qPart w‖) ^ N := by
  have h := norm_le_max_parts n w
  rcases le_total ‖pPart w‖ ‖qPart w‖ with h' | h'
  · rw [max_eq_right h'] at h
    have : (1 + ‖w‖) ^ N ≤ (1 + ‖qPart w‖) ^ N := by gcongr
    linarith [pow_nonneg (by positivity : (0:ℝ) ≤ 1 + ‖pPart w‖) N]
  · rw [max_eq_left h'] at h
    have : (1 + ‖w‖) ^ N ≤ (1 + ‖pPart w‖) ^ N := by gcongr
    linarith [pow_nonneg (by positivity : (0:ℝ) ≤ 1 + ‖qPart w‖) N]

end MatrixCoeff

open MatrixCoeff

theorem matrixCoeff_continuous_rapidDecay : ∀ (n : ℕ) (g g' : Sch (Fin n)),
    Continuous (fun w : Fin n ⊕ Fin n → ℝ => ∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)) ∧
    ∀ N : ℕ, ∃ C : ℝ, ∀ w : Fin n ⊕ Fin n → ℝ, ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖w‖) ^ N ≤ C := by
  intro n g g'
  refine ⟨GlobalTheory.T.continuous_matrix_coefficient n g g', fun N => ?_⟩
  obtain ⟨C1, h1⟩ := GlobalTheory.T.matrix_coeff_decay_first_part n g g' N
  obtain ⟨C2, h2⟩ := GlobalTheory.T.matrix_coeff_decay_second_part n g g' N
  refine ⟨C1 + C2, fun w => ?_⟩
  have := one_add_norm_pow_le_parts n N w
  have hn : 0 ≤ ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ := norm_nonneg _
  calc _ ≤ ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * ((1 + ‖pPart w‖) ^ N + (1 + ‖qPart w‖) ^ N) :=
        mul_le_mul_of_nonneg_left this hn
    _ ≤ C1 + C2 := by rw [mul_add]; exact add_le_add (h1 w) (h2 w)

end GlobalTheory
