module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullbackValuationInvarianceOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR.QuadraticAlgebraValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm

theorem qAl_of (hLaws : Laws) : QAlStatement := by
  unfold QAlStatement
  intro V _ _ _ ϖ hϖ D Q hQ O _ _ _ oa a N h1 _ χ

  have hb : bOf D.toPre Q (star a • χ) (star a • χ) = bOf D.toPre Q χ ((N : O) • χ) := by
    rw [bOf_balance hϖ D hLaws oa hQ (star a) χ (star a • χ), star_star, smul_smul, h1]
  have hN : ((N : O) • χ) = N • χ := Nat.cast_smul_eq_nsmul O N χ

  have hlin (n : ℕ) : bOf D.toPre Q χ (n • χ) = n * bOf D.toPre Q χ χ := by
    rw [bOf_comm D (Q := Q) χ (n • χ)]
    induction n with
    | zero =>
      have h := bOf_add_left hϖ D hQ (0 : D.toPre.X) 0 χ
      simp only [zero_add] at h
      simpa using (show bOf D.toPre Q 0 χ = 0 by linarith)
    | succ n ih =>
      rw [succ_nsmul, bOf_add_left hϖ D hQ, ih, Nat.cast_succ, add_mul, one_mul]
  have e1 := two_Q_eq hϖ D hQ (star a • χ)
  have e2 := two_Q_eq hϖ D hQ χ
  rw [hb, hN, hlin N, ← e2] at e1
  linarith

end ReciprocityTheory.ChartRestriction.G.DVR.QuadraticAlgebraValuation
