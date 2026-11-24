module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnGramDeterminantUnitLowerThree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

theorem _root_.GlobalTheory.T.columnGramDeterminant_unitLower_three : ∀ M : Matrix (Fin 3) (Fin 3) ℂ, (∀ i, M i i = 1) → (∀ i j : Fin 3, i < j → M i j = 0) → colGram M 1 = 1 + ‖M 1 0‖ ^ 2 + ‖M 2 0‖ ^ 2 ∧ colGram M 2 = 1 + ‖M 2 1‖ ^ 2 + ‖M 1 0 * M 2 1 - M 2 0‖ ^ 2 := by
  first | exact @GlobalTheory.IntBall.colGram_three_unitLower | exact GlobalTheory.IntBall.colGram_three_unitLower | (intros; apply GlobalTheory.IntBall.colGram_three_unitLower <;> assumption)
