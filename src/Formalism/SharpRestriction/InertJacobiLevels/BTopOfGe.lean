module

public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField

theorem bTopOf_ge {D : D7} (L : SizeData₂ D) (h : L.sc.x ^ L.sc.eps ≤ L.LaG) :
    L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ (2 * L.sc.eps) * L.sc.b' / (D.R.k : ℝ) ≤ bTopOf L := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb : 0 ≤ L.sc.b' := by
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity
  have hd : 0 ≤ L.sc.delta1 := by
    unfold Scale.delta1
    positivity
  have e4 : L.sc.x ^ (2 * L.sc.eps) = L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps := by rw [two_mul, Real.rpow_add hx]
  have hp : 0 ≤ L.sc.x ^ L.sc.eps := Real.rpow_nonneg hx.le _
  unfold bTopOf
  rw [e4]
  have h1 : L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps ≤ L.sc.x ^ L.sc.eps * L.LaG := mul_le_mul_of_nonneg_left h hp
  have h2 : 2 * (D.R.n : ℝ) * L.sc.delta1 * (L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps) * L.sc.b' / (D.R.k : ℝ) ≤
      2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / (D.R.k : ℝ) := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_right _ hb
    rw [mul_assoc (2 * (D.R.n : ℝ) * L.sc.delta1) (L.sc.x ^ L.sc.eps) L.LaG]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

end Formalism.MainNotions.Inhab

end
