module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralLeOfExpanding
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

open MeasureTheory

theorem _root_.GlobalTheory.T.setIntegral_le_pow_mul_setIntegral_of_expanding : ∀ (N : ℕ) (A Q : Set (Fin N → ℝ)) (K : ℝ) (f : (Fin N → ℝ) → (Fin N → ℝ)) (h₁ h₂ : (Fin N → ℝ) → ℝ), IsCompact A → IsCompact Q → 0 ≤ K → Continuous h₁ → Continuous h₂ → (∀ t, 0 ≤ h₁ t) → (∀ t, 0 ≤ h₂ t) → (∀ t ∈ A, f t ∈ Q ∧ h₁ t ≤ h₂ (f t)) → (∀ t ∈ A, ∀ t' ∈ A, ‖t - t'‖ ≤ K * ‖f t - f t'‖) → ∫ t in A, h₁ t ≤ K ^ N * ∫ t in Q, h₂ t := by
  first | exact @GlobalTheory.setIntegral_le_of_expanding | exact GlobalTheory.setIntegral_le_of_expanding | (intros; apply GlobalTheory.setIntegral_le_of_expanding <;> assumption)
