module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProductWeightsLeOfSeparatedGeometricMean
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open GlobalTheory.SepPer

theorem _root_.GlobalTheory.T.sum_productWeights_le_of_separated_geometricMean : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ la : ℝ, 0 < la → la ≤ 1 → ∀ S : Finset (ι → Matrix (Fin n) (Fin n) ℂ), (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → la ^ Fintype.card ι ≤ ∏ v, hsn (s v - s' v)) → ∑ s ∈ S, ∏ v, ((1 + hsn (s v)) ^ (2 * n ^ 2 + 1))⁻¹ ≤ C * la⁻¹ ^ (2 * n ^ 2 * Fintype.card ι) := by
  first | exact @GlobalTheory.SepSum.sum_weights_le_of_separated | exact GlobalTheory.SepSum.sum_weights_le_of_separated | (intros; apply GlobalTheory.SepSum.sum_weights_le_of_separated <;> assumption)
