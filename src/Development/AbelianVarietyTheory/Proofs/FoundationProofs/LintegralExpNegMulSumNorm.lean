module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.Pi
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

namespace GlobalTheory.CartanInt

theorem integral_exp_neg_mul_norm_complex (b : ℝ) (hb : 0 < b) :
    ∫ z : ℂ, Real.exp (-(b * ‖z‖)) = 2 * Real.pi / b ^ 2 := by
  have h := Complex.integral_exp_neg_mul_rpow (p := 1) (b := b) le_rfl hb
  simp only [Real.rpow_one, neg_mul, div_one] at h
  rw [h]
  have h3 : Real.Gamma (2 + 1) = 2 := by
    have := Real.Gamma_nat_eq_factorial 2
    simpa [Nat.factorial] using this
  rw [h3, Real.rpow_neg hb.le, Real.rpow_two]
  field_simp

theorem lintegral_exp_neg_mul_sum_norm (p q : ℕ) (b : ℝ) (hb : 0 < b) :
    ∫⁻ B : Fin p → Fin q → ℂ, ENNReal.ofReal (Real.exp (-(b * ∑ i, ∑ j, ‖B i j‖))) =
      ENNReal.ofReal ((2 * Real.pi / b ^ 2) ^ (p * q)) := by
  have h1 := integral_exp_neg_mul_norm_complex b hb
  have hne : (2 * Real.pi / b ^ 2) ≠ 0 := by positivity
  have hi : Integrable (fun z : ℂ => Real.exp (-(b * ‖z‖))) :=
    Integrable.of_integral_ne_zero (by rw [h1]; exact hne)
  have hprod : ∀ B : Fin p → Fin q → ℂ, Real.exp (-(b * ∑ i, ∑ j, ‖B i j‖)) =
      ∏ i, ∏ j, Real.exp (-(b * ‖B i j‖)) := by
    intro B
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  have hrow : Integrable (fun v : Fin q → ℂ => ∏ j, Real.exp (-(b * ‖v j‖))) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun _ (z : ℂ) => Real.exp (-(b * ‖z‖))) (fun _ => hi)
  have hall : Integrable (fun B : Fin p → Fin q → ℂ => ∏ i, ∏ j, Real.exp (-(b * ‖B i j‖))) := by
    rw [volume_pi]
    exact Integrable.fintype_prod
      (f := fun _ (v : Fin q → ℂ) => ∏ j, Real.exp (-(b * ‖v j‖))) (fun _ => hrow)
  have hrowv : ∫ v : Fin q → ℂ, ∏ j, Real.exp (-(b * ‖v j‖)) = (2 * Real.pi / b ^ 2) ^ q := by
    rw [volume_pi, integral_fintype_prod_eq_prod (f := fun _ (z : ℂ) => Real.exp (-(b * ‖z‖)))]
    simp only [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hallv : ∫ B : Fin p → Fin q → ℂ, ∏ i, ∏ j, Real.exp (-(b * ‖B i j‖)) =
      (2 * Real.pi / b ^ 2) ^ (p * q) := by
    rw [volume_pi, integral_fintype_prod_eq_prod
      (f := fun _ (v : Fin q → ℂ) => ∏ j, Real.exp (-(b * ‖v j‖)))]
    simp only [hrowv, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul, mul_comm q p]
  simp only [hprod]
  rw [← hallv, ofReal_integral_eq_lintegral_ofReal hall]
  exact Filter.Eventually.of_forall fun B => by positivity

end GlobalTheory.CartanInt
