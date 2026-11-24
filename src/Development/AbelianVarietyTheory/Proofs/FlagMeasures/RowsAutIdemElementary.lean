module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

@[expose] public section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory

theorem rowsAut_idem_elementary : ∀ B : RowsAut,
    (B.e 1).im = 0 ∧ 0 ≤ (B.e 1).re ∧ (∀ y, ‖B.e y‖ ≤ (B.e 1).re) ∧ Continuous B.e := by
  intro B
  obtain ⟨hlc, -, hstar, hpos, -⟩ := B.e_adm

  have him : (B.e 1).im = 0 := by
    have h := congrArg Complex.im (hstar 1)
    rw [inv_one, Complex.star_def, Complex.conj_im] at h
    linarith

  have hre : 0 ≤ (B.e 1).re := by
    have h := hpos 1 (fun _ => 1) (fun _ => 1)
    simp only [Fin.sum_univ_one, star_one, one_mul, inv_one] at h
    exact (Complex.nonneg_iff.mp h).1
  refine ⟨him, hre, ?_, hlc.continuous⟩
  intro y
  set a := (B.e 1).re with ha
  have h1 : B.e 1 = (a : ℂ) := Complex.ext (by simp [ha]) (by simp [him])
  set b := B.e y with hb
  have hyi : B.e y⁻¹ = star b := hstar y
  have key : star b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  have hs : star ((‖b‖ : ℝ) : ℂ) = ((‖b‖ : ℝ) : ℂ) := Complex.conj_ofReal _

  have h := hpos 2 ![1, y] ![b, -((‖b‖ : ℝ) : ℂ)]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    inv_one, one_mul, mul_one, inv_mul_cancel, hyi, h1, star_neg, hs] at h
  have hE : star b * b * (a : ℂ) + star b * -((‖b‖ : ℝ) : ℂ) * b +
      (-((‖b‖ : ℝ) : ℂ) * b * star b + -((‖b‖ : ℝ) : ℂ) * -((‖b‖ : ℝ) : ℂ) * (a : ℂ)) =
      ((2 * ‖b‖ ^ 2 * (a - ‖b‖) : ℝ) : ℂ) := by
    push_cast at key ⊢
    linear_combination ((a : ℂ) - 2 * ((‖b‖ : ℝ) : ℂ)) * key
  rw [hE, Complex.zero_le_real] at h
  refine le_of_not_gt fun hlt => ?_
  have hb0 : 0 < ‖b‖ := lt_of_le_of_lt hre hlt
  have hneg : 2 * ‖b‖ ^ 2 * (a - ‖b‖) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
  linarith

end GlobalTheory
