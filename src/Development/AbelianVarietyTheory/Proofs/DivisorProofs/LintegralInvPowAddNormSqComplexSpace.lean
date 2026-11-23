module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralComplexInvPowAddNormSqStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
namespace GlobalTheory.ComplexSpaceIntegral

theorem lintegral_inv_pow_add_sum_norm_sq :
    ∀ (n m : ℕ) (a : ℝ), 0 < a → ∫⁻ v : Fin n → ℂ, ENNReal.ofReal (((a + ∑ i, ‖v i‖ ^ 2) ^ (n + m + 1))⁻¹)
      = ENNReal.ofReal (Real.pi ^ n * m.factorial / ((n + m).factorial * a ^ (m + 1))) := by
  intro n
  induction n with
  | zero =>
    intro m a ha
    rw [lintegral_unique]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add, pow_zero, one_mul]
    have : (volume : Measure (Fin 0 → ℂ)) univ = 1 := by
      rw [MeasureTheory.volume_pi, Measure.pi_univ]; simp
    rw [this, mul_one]
    congr 1
    have hf : (m.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  | succ n ih =>
    intro m a ha
    have e := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0
    rw [← (e.symm).lintegral_comp_emb (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).symm.measurableEmbedding]
    rw [MeasureTheory.Measure.volume_eq_prod]
    rw [lintegral_prod]
    swap
    · apply Measurable.aemeasurable
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.inv
      apply Measurable.pow_const
      apply Measurable.add measurable_const
      apply Finset.measurable_sum
      intro i _
      apply Measurable.pow_const
      apply Measurable.norm
      exact (measurable_pi_apply i).comp (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).symm.measurable
    have inner : ∀ z : ℂ, ∫⁻ w : Fin n → ℂ, ENNReal.ofReal (((a + ∑ i, ‖(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).symm (z, w) i‖ ^ 2) ^ (n + 1 + m + 1))⁻¹)
        = ENNReal.ofReal (Real.pi ^ n * (m+1).factorial / (n + (m+1)).factorial) * ENNReal.ofReal (((a + ‖z‖ ^ 2) ^ (m + 2))⁻¹) := by
      intro z
      have hz : 0 < a + ‖z‖ ^ 2 := by positivity
      have key := ih (m+1) (a + ‖z‖ ^ 2) hz
      have hsum : ∀ w : Fin n → ℂ, a + ∑ i, ‖(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).symm (z, w) i‖ ^ 2
          = a + ‖z‖ ^ 2 + ∑ i, ‖w i‖ ^ 2 := by
        intro w
        rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.sum_univ_succ]
        simp [Fin.insertNthEquiv, add_assoc]
      simp_rw [hsum]
      have hexp : n + 1 + m + 1 = n + (m + 1) + 1 := by ring
      rw [hexp, key, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show m + 1 + 1 = m + 2 by ring]
      have hf : ((n + (m+1)).factorial : ℝ) ≠ 0 := by positivity
      have hp : (a + ‖z‖ ^ 2) ^ (m + 2) ≠ 0 := by positivity
      field_simp
    simp_rw [inner]
    rw [lintegral_const_mul _ (by
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.inv
      apply Measurable.pow_const
      exact measurable_const.add (measurable_norm.pow_const 2))]
    rw [GlobalTheory.T.lintegral_complex_inv_pow_add_norm_sq m a ha, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have h1 : ((n + (m+1)).factorial : ℝ) ≠ 0 := by positivity
    have h2 : ((n + 1 + m).factorial : ℝ) ≠ 0 := by positivity
    have h3 : (n + (m+1)) = n + 1 + m := by ring
    rw [h3, Nat.factorial_succ m]
    push_cast
    have ha' : a ^ (m+1) ≠ 0 := by positivity
    field_simp
    ring

end GlobalTheory.ComplexSpaceIntegral
