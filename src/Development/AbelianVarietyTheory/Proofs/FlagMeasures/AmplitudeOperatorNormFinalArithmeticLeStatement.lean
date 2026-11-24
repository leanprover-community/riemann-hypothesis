module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOperatorNormFinalArithmeticLe
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

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.amplitudeOperatorNorm_finalArithmetic_le : ∀ (k r : ℕ) (H₁ De D : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → 1 ≤ H₁ → 1 ≤ De → 0 < D → ((4 * r : ℝ) ^ (11 * r ^ 2) * De ^ (12 * r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * 4 ^ (k - 2 - r) * ((r + 1) * 4 ^ (24 * r ^ 3 + 1))) * 24 * (r : ℝ) ^ (2 * r) * H₁ ^ (24 * r ^ 3) * De ^ (2 * r) * (2 ^ r / D) ^ (k - 2 - r) ≤ absBd k r H₁ De D := by
  first | exact @GlobalTheory.Amp.absArith | exact GlobalTheory.Amp.absArith | (intros; apply GlobalTheory.Amp.absArith <;> assumption)
