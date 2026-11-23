module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory

theorem translate_modifiedSigma_add_mul_sub_at_zero :
    ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P Q : ℂ, P ∉ Λ → Q ∉ Λ →
      U1 Λ (P + Q) (sgStar Λ) 0 * U1 Λ (P - Q) (sgStar Λ) 0 =
        (wpF Λ Q - wpF Λ P) * U1 Λ P (sgStar Λ) 0 ^ 2 * U1 Λ Q (sgStar Λ) 0 ^ 2 := by
  intro Λ hΛ P Q hP hQ
  have hlaw := (GlobalTheory.OddTheta.sgStar_laws Λ hΛ).2.2.2.1 P Q hP hQ
  have hσ : sgStar Λ (P + Q) * sgStar Λ (P - Q) =
      (wpF Λ Q - wpF Λ P) * sgStar Λ P ^ 2 * sgStar Λ Q ^ 2 := by
    linear_combination hlaw
  simp only [U1, zero_add, mul_zero, zero_mul, zero_div, zero_sub]
  have hexp : ∀ x : ℂ, Complex.exp x ^ 2 = Complex.exp (2 * x) := by
    intro x; rw [← Complex.exp_nat_mul]; norm_num
  have key : Complex.exp (-(↑Real.pi * (P + Q) * (starRingEnd ℂ) (P + Q) / (2 * ↑(area Λ)))) *
      Complex.exp (-(↑Real.pi * (P - Q) * (starRingEnd ℂ) (P - Q) / (2 * ↑(area Λ)))) =
      Complex.exp (-(↑Real.pi * P * (starRingEnd ℂ) P / (2 * ↑(area Λ)))) ^ 2 *
      Complex.exp (-(↑Real.pi * Q * (starRingEnd ℂ) Q / (2 * ↑(area Λ)))) ^ 2 := by
    rw [hexp, hexp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [map_add (f := _), map_sub]
    ring
  calc _ = (sgStar Λ (P + Q) * sgStar Λ (P - Q)) *
      (Complex.exp (-(↑Real.pi * (P + Q) * (starRingEnd ℂ) (P + Q) / (2 * ↑(area Λ)))) *
      Complex.exp (-(↑Real.pi * (P - Q) * (starRingEnd ℂ) (P - Q) / (2 * ↑(area Λ))))) := by ring
    _ = _ := by rw [hσ, key]; ring

end GlobalTheory
