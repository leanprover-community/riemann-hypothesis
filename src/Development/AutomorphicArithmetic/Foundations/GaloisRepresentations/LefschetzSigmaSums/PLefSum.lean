module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open Matrix Polynomial
open UpperTheory.Gal.W2 (lefTerm)

namespace UpperTheory.Gal.LocalSmoothExtension

theorem lefSum_of : LefSum := by
  intro d A y
  set p : ℂ[X] := (1 + (X : ℂ[X]) • A.map (C : ℂ →+* ℂ[X])).det with hp
  have hdeg : p.natDegree < d + 1 := by
    have h1 : (1 + (X : ℂ[X]) • A.map (C : ℂ →+* ℂ[X]) : Matrix (Fin d) (Fin d) ℂ[X]) =
        (X : ℂ[X]) • A.map C + (1 : Matrix (Fin d) (Fin d) ℂ).map C := by
      rw [Matrix.map_one C (map_zero _) (map_one _), add_comm]
    have hle := natDegree_det_X_add_C_le A 1
    rw [← h1, Fintype.card_fin] at hle
    exact Nat.lt_succ_of_le hle
  have hev : p.eval (-y) = (1 - y • A).det := by
    rw [hp, ← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.one_apply, coe_evalRingHom, smul_eq_mul]
    split_ifs <;> simp <;> ring
  unfold lefTerm
  rw [← hev, eval_eq_sum_range' hdeg, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end UpperTheory.Gal.LocalSmoothExtension
