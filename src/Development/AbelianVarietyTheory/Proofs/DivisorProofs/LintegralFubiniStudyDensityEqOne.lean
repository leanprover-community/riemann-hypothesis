module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvPowAddNormSqComplexSpaceStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory

theorem lintegral_fubiniStudy_density_eq_one : ∀ n : ℕ, ∫⁻ v : ReciprocityTheory.L2DbarEstimates.V n,
    ENNReal.ofReal (n.factorial / Real.pi ^ n * ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) = 1 := by
  intro n
  have hc : (0 : ℝ) ≤ n.factorial / Real.pi ^ n := by positivity
  have hmeas : Measurable fun v : ReciprocityTheory.L2DbarEstimates.V n =>
      ENNReal.ofReal (((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) := by fun_prop
  have hsplit : ∀ v : ReciprocityTheory.L2DbarEstimates.V n,
      ENNReal.ofReal (n.factorial / Real.pi ^ n * ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) =
        ENNReal.ofReal (n.factorial / Real.pi ^ n) *
          ENNReal.ofReal (((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) := fun v => ENNReal.ofReal_mul hc
  simp_rw [hsplit]
  rw [lintegral_const_mul _ hmeas]
  have hV : ∫⁻ v : ReciprocityTheory.L2DbarEstimates.V n, ENNReal.ofReal (((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) =
      ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (((1 + ∑ i, ‖z i‖ ^ 2) ^ (n + 0 + 1))⁻¹) := by
    rw [← (FinChart.measurePreserving_toV (D := n)).lintegral_comp hmeas]
    congr 1
    funext z
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  rw [hV, GlobalTheory.T.lintegral_inv_pow_add_normSq_complexSpace n 0 1 one_pos, ← ENNReal.ofReal_mul hc]
  have hpi : Real.pi ^ n ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [show (n.factorial : ℝ) / Real.pi ^ n * (Real.pi ^ n * (Nat.factorial 0 : ℝ) /
      (((n + 0).factorial : ℝ) * 1 ^ (0 + 1))) = 1 by
    simp only [Nat.factorial_zero, Nat.cast_one, add_zero, one_pow, mul_one]
    field_simp]
  exact ENNReal.ofReal_one

end GlobalTheory
