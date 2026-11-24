module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ProdSubLtEqFactorial
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Residue
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem sCoef_lamT (lam : Fin n → ℝ) (t : ℕ) {i : ℕ} (hi : i + 1 < n) :
    sCoef (lamT lam t) i = sCoef lam i + t := by
  simp only [sCoef, dif_pos hi, lamT, Dvec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem sCoef_zero_of (i : ℕ) (hi : i + 1 < n) : sCoef (0 : Fin n → ℝ) i = 1 := by
  simp [sCoef, dif_pos hi]

theorem ph_lamT (lam : Fin n → ℝ) (t : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Ph (lamT lam t) X = Ph lam X + (t : ℝ) * Ph (0 : Fin n → ℝ) X := by
  simp only [Ph, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i + 1 < n := by simp at hi; omega
  rw [sCoef_lamT lam t hi', sCoef_zero_of i hi']
  ring

theorem lamT_apply (lam : Fin n → ℝ) (t : ℕ) (a : Fin n) :
    lamT lam t a = lam a + (t : ℝ) * ((n : ℝ) - 1 - ((a : ℕ) : ℝ)) := by
  simp [lamT, Dvec]

theorem lamT_sub (lam : Fin n → ℝ) (t : ℕ) (a b : Fin n) :
    lamT lam t a - lamT lam t b = (lam a - lam b) + (t : ℝ) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  rw [lamT_apply, lamT_apply]; ring

theorem strictAnti_lamT {lam : Fin n → ℝ} (hlam : StrictAnti lam) (t : ℕ) : StrictAnti (lamT lam t) := by
  intro a b hab
  have h1 := hlam hab
  have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  have h3 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have := lamT_sub lam t b a
  nlinarith

theorem vand_pos {lam : Fin n → ℝ} (hlam : StrictAnti lam) : 0 < Vand lam := by
  unfold Vand
  refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact sub_pos.2 (hlam hb)

theorem prod_pairs_eq_factorial (n : ℕ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ i ∈ range n, (i.factorial : ℝ) := by
  rw [Finset.prod_comm' (t' := univ) (s' := fun b => univ.filter (fun a : Fin n => a < b))
    (fun x y => by simp)]
  simp_rw [prod_sub_lt_eq_factorial]
  exact Fin.prod_univ_eq_prod_range (fun i => (i.factorial : ℝ)) n

theorem dimVlam_eq_vand {lam : Fin n → ℝ} (hlam : StrictAnti lam) :
    dimVlam lam = Vand lam / ∏ i ∈ range n, (i.factorial : ℝ) := by
  unfold dimVlam Vand
  rw [prod_pairs_eq_factorial]
  congr 1
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact abs_of_pos (sub_pos.2 (hlam hb))

end ReciprocityTheory.ChartRestriction.DS.G2
