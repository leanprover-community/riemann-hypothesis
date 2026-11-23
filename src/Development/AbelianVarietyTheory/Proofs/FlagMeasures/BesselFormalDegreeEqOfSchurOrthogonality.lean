module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem fdegH_eq_of_schurH (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)) (d : ℝ) (w : H)
    (hS : SchurH μG σ d) (hw : w ≠ 0) : fdegH μG σ w = d := by
  obtain ⟨hd, hrel⟩ := hS
  obtain ⟨-, hint⟩ := hrel w w w w
  have hpt : ∀ g : Mt k r, coef σ w w (Matrix.of g) * star (coef σ w w (Matrix.of g))
      = ((‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    simp only [coef]
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [hpt] at hint
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at hint
  have hreal : ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG = ‖w‖ ^ 4 / d := by
    apply Complex.ofReal_injective
    rw [hint]
    push_cast
    rw [← pow_add]
    rfl
  have hn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  unfold fdegH
  rw [hreal]
  have h4 : (‖w‖ ^ 4 : ℝ) ≠ 0 := by positivity
  field_simp

end GlobalTheory.SgInf
