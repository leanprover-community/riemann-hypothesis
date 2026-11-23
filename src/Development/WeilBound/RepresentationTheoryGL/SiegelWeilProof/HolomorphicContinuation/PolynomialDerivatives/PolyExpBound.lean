module

import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousEvX
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.NullSec
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SquareNormBound
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.HasFDerivAtEvX
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

@[expose] public section

noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC.NullS

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

def Sg (c : ℝ) : PX m n := C (-(c : ℂ)) * ∑ a, ∑ i, X (a, i, true) * X (a, i, false)

theorem gs_eq (c : ℝ) (x : Fin m → Fin n → ℂ) : gs c x = Complex.exp (evX (Sg c) x) := by
  unfold gs
  congr 1

  simp only [Sg, evX_eq, map_mul, map_sum, eval_C, eval_X, crd_apply, if_true, Bool.false_eq_true, if_false,
  Complex.star_def, Complex.conj_mul']
  push_cast
  ring

theorem continuous_evX (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x :=
  continuous_iff_continuousAt.2 fun x => (hasFDerivAt_evX P x).continuousAt

theorem evX_bound (P : PX m n) : ∃ K : ℝ, ∃ d : ℕ, 0 ≤ K ∧ ∀ x, ‖evX P x‖ ≤ K * (1 + ‖x‖) ^ d := by
  apply PositivityTheory.Rg.Sw.AbsSt.DF.poly_bound <;> assumption

theorem sq_norm_le (x : Fin m → Fin n → ℂ) : ‖x‖ ^ 2 ≤ ∑ a, ∑ i, ‖x a i‖ ^ 2 :=
  _root_.UpperTheory.Reformulated.B.SquareNormBound.sq_norm_le x

theorem norm_gs_le (c : ℝ) (hc : 0 < c) (x : Fin m → Fin n → ℂ) : ‖gs c x‖ ≤ Real.exp (-(c * ‖x‖ ^ 2)) := by
  unfold gs
  rw [show (-(↑(c * ∑ a, ∑ i, ‖x a i‖ ^ 2) : ℂ)) = ↑(-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) by push_cast; ring,
    Complex.norm_exp_ofReal]
  apply Real.exp_le_exp.2
  have := sq_norm_le x
  nlinarith

theorem poly_exp_bound (c : ℝ) (hc : 0 < c) (N : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ N * Real.exp (-(c * t ^ 2)) ≤ Real.exp (3 * c) * ((N.factorial : ℝ) / (2 * c) ^ N) := by
  set y := 2 * c * (1 + t) with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 : Real.exp (-(c * t ^ 2)) ≤ Real.exp (3 * c) * Real.exp (-y) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith [sq_nonneg (t - 1)]
  have h2 : (1 + t) ^ N * Real.exp (-y) ≤ (N.factorial : ℝ) / (2 * c) ^ N := by
    have := Real.pow_div_factorial_le_exp y hy0 N
    rw [div_le_iff₀ (by positivity)] at this
    rw [le_div_iff₀ (by positivity)]
    have hyN : y ^ N = (2 * c) ^ N * (1 + t) ^ N := by rw [hy, mul_pow]
    calc (1 + t) ^ N * Real.exp (-y) * (2 * c) ^ N = y ^ N * Real.exp (-y) := by rw [hyN]; ring
      _ ≤ (Real.exp y * N.factorial) * Real.exp (-y) := mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = N.factorial := by rw [mul_comm (Real.exp y), mul_assoc, ← Real.exp_add]; simp
  calc (1 + t) ^ N * Real.exp (-(c * t ^ 2)) ≤ (1 + t) ^ N * (Real.exp (3 * c) * Real.exp (-y)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Real.exp (3 * c) * ((1 + t) ^ N * Real.exp (-y)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le

instance instHaarX : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure :=
  MeasureTheory.Measure.pi.isAddHaarMeasure _

theorem continuous_gs (c : ℝ) : Continuous fun x : Fin m → Fin n → ℂ => gs c x := by
  simp_rw [gs_eq]; exact Complex.continuous_exp.comp (continuous_evX _)

theorem integrable_pg (c : ℝ) (hc : 0 < c) (P : PX m n) :
    Integrable (fun x : Fin m → Fin n → ℂ => evX P x * gs c x) := by
  obtain ⟨K, d, hK, hb⟩ := evX_bound P
  set R : ℕ := Module.finrank ℝ (Fin m → Fin n → ℂ) + 1 with hR
  set M := Real.exp (3 * c) * (((d + R).factorial : ℝ) / (2 * c) ^ (d + R)) with hM
  have hcont : Continuous (fun x : Fin m → Fin n → ℂ => evX P x * gs c x) := (continuous_evX P).mul (continuous_gs c)
  refine ((integrable_one_add_norm (E := Fin m → Fin n → ℂ) (μ := volume) (r := (R : ℝ)) (by simp [hR])).const_mul
    (K * M)).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have ht : 0 ≤ ‖x‖ := norm_nonneg x
  have hpos : 0 < (1 + ‖x‖) ^ R := by positivity
  have key := poly_exp_bound c hc (d + R) ‖x‖ ht
  rw [norm_mul, Real.rpow_neg (by positivity), Real.rpow_natCast]
  calc ‖evX P x‖ * ‖gs c x‖ ≤ (K * (1 + ‖x‖) ^ d) * Real.exp (-(c * ‖x‖ ^ 2)) :=
        mul_le_mul (hb x) (norm_gs_le c hc x) (norm_nonneg _) (by positivity)
    _ = K * ((1 + ‖x‖) ^ (d + R) * Real.exp (-(c * ‖x‖ ^ 2))) / (1 + ‖x‖) ^ R := by
        rw [pow_add]; field_simp
    _ ≤ K * M / (1 + ‖x‖) ^ R := by
        apply div_le_div_of_nonneg_right _ hpos.le
        exact mul_le_mul_of_nonneg_left key hK
    _ = K * M * ((1 + ‖x‖) ^ R)⁻¹ := by rw [div_eq_mul_inv]

end PositivityTheory.Rg.Sw.LC.NullS
