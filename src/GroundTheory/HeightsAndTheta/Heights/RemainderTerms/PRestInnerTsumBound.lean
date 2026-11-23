module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsElem
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Elementary
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
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

theorem RestInnerTsumBound.proof : RestInnerTsumBound.Statement := by
  intro p k c M hp hk hc
  obtain ⟨hsum, hle⟩ := GeometricTail.intersectionNumber_baseChange p k hp hk
  have hM : 0 ≤ M := (abs_nonneg (c 0)).trans (hc 0)
  have hnn : ∀ n : ℕ, 0 ≤ (p ^ ((n + 1) * k))⁻¹ := fun n => by
    have : (0 : ℝ) ≤ p := by linarith
    positivity
  have hbound : ∀ n : ℕ, ‖(p ^ ((n + 1) * k))⁻¹ * c n‖ ≤ (p ^ ((n + 1) * k))⁻¹ * M := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn n)]
    exact mul_le_mul_of_nonneg_left (hc n) (hnn n)
  have hsumM : Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹ * M) := hsum.mul_right M
  have hS : Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹ * c n) :=
    Summable.of_norm_bounded hsumM hbound
  refine ⟨hS, ?_⟩
  calc |∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * c n|
      = ‖∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * c n‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖(p ^ ((n + 1) * k))⁻¹ * c n‖ := norm_tsum_le_tsum_norm hS.norm
    _ ≤ ∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * M := hS.norm.tsum_le_tsum hbound hsumM
    _ = (∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹) * M := tsum_mul_right
    _ ≤ (2 * (p ^ k)⁻¹) * M := mul_le_mul_of_nonneg_right hle hM
    _ = M * (2 * (p ^ k)⁻¹) := mul_comm _ _

end RestTerms

end GroundTheory.Heights₂.Heights
