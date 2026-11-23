module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
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
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

theorem GaussianSum.proof (hPD : GaussPoissonDual.Statement) (hSS : GaussShellSum.Statement)
    (hC : GaussConstant.Statement) : GaussianSum.Statement := by
  refine ⟨72 * Real.exp 4, by positivity, ?_⟩
  intro g Y ρ hY hρ hmin u
  obtain ⟨hsum, Λ, hΛ, hle⟩ := hPD g Y ρ hY hρ hmin u
  refine ⟨hsum, ?_⟩
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · have hq : ∀ k : Fin 0 → ℤ, qf Y (intVec k + u) = 0 := fun k => by simp [qf]
    simp only [hq, mul_zero, Real.exp_zero, tsum_const, Nat.card_unique, one_smul,
      Nat.cast_zero, zero_div, Real.rpow_zero, Matrix.det_isEmpty, Real.one_rpow, pow_zero,
      mul_one, le_refl]
  · have hdet : 0 < Y.det := hY.det_pos
    have hd : 0 ≤ Y.det ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hdet.le _
    have hS := (hSS g hg Λ ρ hρ hΛ).2
    have hc := hC g hg
    have hr : 0 ≤ (1 + 1 / ρ) ^ g := by positivity
    calc ∑' k : Fin g → ℤ, Real.exp (-(π / 2) * qf Y (intVec k + u))
        ≤ √2 ^ g * Y.det ^ (-(1 / 2 : ℝ)) *
            ∑' μ : Λ, Real.exp (-π * ‖(μ : EuclideanSpace ℝ (Fin g))‖ ^ 2) := hle
      _ ≤ √2 ^ g * Y.det ^ (-(1 / 2 : ℝ)) * (2 * gaussShellConst g * (1 + 1 / ρ) ^ g) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = √2 ^ g * (2 * gaussShellConst g) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g := by ring
      _ ≤ (72 * Real.exp 4 * g) ^ ((g : ℝ) / 2) * Y.det ^ (-(1 / 2 : ℝ)) * (1 + 1 / ρ) ^ g :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hd) hr

end GroundTheory.Heights₂.Heights
