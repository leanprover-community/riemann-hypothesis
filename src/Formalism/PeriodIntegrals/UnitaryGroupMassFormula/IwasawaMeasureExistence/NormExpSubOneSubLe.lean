module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

noncomputable section

namespace PI.IwaMeasEx.Gauge.ZetaZeros

open Filter Topology Formalism.MainNotions.S

section Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

theorem norm_exp_sub_partial_le (x : 𝔸) (m : ℕ) :
    ‖NormedSpace.exp x - ∑ i ∈ Finset.range m, ((i.factorial : ℝ)⁻¹) • x ^ i‖ ≤
      Real.exp ‖x‖ - ∑ i ∈ Finset.range m, ((i.factorial : ℝ)⁻¹) * ‖x‖ ^ i := by
  have h1 : HasSum (fun i : ℕ => ((i.factorial : ℝ)⁻¹) • x ^ i) (NormedSpace.exp x) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x
  have h2 : HasSum (fun i : ℕ => ((i.factorial : ℝ)⁻¹) • ‖x‖ ^ i) (Real.exp ‖x‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖
  have h1' := (hasSum_nat_add_iff' m).mpr h1
  have h2' := (hasSum_nat_add_iff' m).mpr h2
  simp only [smul_eq_mul] at h2'
  refine h1'.norm_le_of_bounded h2' (fun i => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le x _) (by positivity)

theorem norm_exp_le' (x : 𝔸) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  simpa using norm_exp_sub_partial_le x 0

end Trotter

section Mat

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

end Mat

end PI.IwaMeasEx.Gauge.ZetaZeros

end
