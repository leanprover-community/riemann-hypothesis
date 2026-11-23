module

public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

open Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.LoopBTheta

theorem normWin_one {D : D7} (large₂ : SizeData₂ D) {C1 : ℝ} (hC1 : 0 ≤ C1) : normWin D large₂ C1 1 := by
  have hL : 0 ≤ large₂.sc.L := by
    show 0 ≤ large₂.sc.x ^ large₂.sc.eps
    exact le_of_lt (Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _)
  have hb : (1 : ℝ) ≤ large₂.sc.b := by
    show (1 : ℝ) ≤ Real.exp large₂.sc.L
    exact Real.one_le_exp hL
  have hc : 0 ≤ C1 * (D.R.m : ℝ) ^ 2 := mul_nonneg hC1 (sq_nonneg _)
  refine ⟨?_, ?_⟩
  · exact Real.rpow_le_one_of_one_le_of_nonpos hb (neg_nonpos.mpr hc)
  · exact Real.one_le_rpow hb hc

end Formalism.L2.SG.Pf.LoopBTheta
