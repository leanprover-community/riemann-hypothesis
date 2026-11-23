module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DyadicSummationWithDecay
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.dyadic_summation_with_decay : ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (A B S S' Y Y' : X → ℝ) (r j kk e q : ℕ) (H₁ De D K K' sg : ℝ), Measurable A → Measurable B → Measurable S → Measurable S' → Measurable Y → Measurable Y' → 1 ≤ r → 1 ≤ kk → e + 4 * r + 2 ≤ q → 1 ≤ H₁ → 1 ≤ De → 0 < D → 0 < K → 0 < K' → 1 ≤ sg → (∀ᵐ x ∂ν, 0 ≤ A x ∧ 0 ≤ B x ∧ 1 ≤ S x ∧ 1 ≤ S' x ∧ 0 < Y x ∧ 0 < Y' x ∧ Y x * Y' x * D ≤ 2 ^ j ∧ D ≤ (S x * S' x) ^ r ∧ Y x ≤ max (S x) (S' x) ^ r * De ∧ Y' x ≤ max (S x) (S' x) ^ r * De ∧ sg ≤ max 1 ((S x * S' x) ^ r / (2 * H₁) ^ (2 * r))) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S x ≤ 2 ^ (i + 1) * H₁ ∧ (i = 0 ∨ 2 ^ i * H₁ < S x) ∧ S' x ≤ 2 ^ (i' + 1) * H₁ ∧ y < Y x ∧ Y x ≤ 2 * y}, ENNReal.ofReal (A x ^ 2) ∂ν ≤ ENNReal.ofReal (K * (2 ^ (i + i' + 1) * H₁) ^ e * y ^ (2 * kk) * (((2 : ℝ) ^ i) ^ (2 * q))⁻¹)) → (∀ (i i' : ℕ) (y : ℝ), 0 < y → ∫⁻ x in {x | S' x ≤ 2 ^ (i' + 1) * H₁ ∧ (i' = 0 ∨ 2 ^ i' * H₁ < S' x) ∧ S x ≤ 2 ^ (i + 1) * H₁ ∧ y < Y' x ∧ Y' x ≤ 2 * y}, ENNReal.ofReal (B x ^ 2) ∂ν ≤ ENNReal.ofReal (K' * (2 ^ (i + i' + 1) * H₁) ^ e * y ^ (2 * kk) * (((2 : ℝ) ^ i') ^ (2 * q))⁻¹)) → ∫⁻ x, ENNReal.ofReal (A x * B x) ∂ν ≤ ENNReal.ofReal (16 * Real.sqrt (K * K') * (2 * H₁) ^ (e + 4 * r) * De ^ 2 * (2 ^ j / D) ^ kk * sg ^ (-(((q : ℝ) - e - 4 * r - 1) / r))) := by
  first | exact @GlobalTheory.Amp.dyadic_summation | exact GlobalTheory.Amp.dyadic_summation | (intros; apply GlobalTheory.Amp.dyadic_summation <;> assumption)
