module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowTOPPLeB
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_TOv_mul_PP_le_b_and_sqrt_b : SzRow (fun C D L => (((TOv L.sc : ℕ) : ℝ) * (C.T.CP * zBase L ^ C.T.eP) * L.sc.x ^ C.T.Cb ≤ L.sc.b) ∧ (((TOv L.sc : ℕ) : ℝ) * (C.T.CP * zBase L ^ C.T.eP) ≤ L.sc.b ^ (1 / 2 : ℝ)) ∧ ((C.T.CP * zBase L ^ C.T.eP) ^ 3 * ((TOv L.sc : ℕ) : ℝ) ^ 2 * L.sc.x ^ C.T.Cb ≤ L.sc.b) ∧ ((C.T.CP * zBase L ^ C.T.eP) ^ 3 * ((TOv L.sc : ℕ) : ℝ) ^ 2 ≤ L.sc.b ^ (1 / 2 : ℝ))) := by
  first | exact @GlobalTheory.EX.szRow_TO_PP_le_b | exact GlobalTheory.EX.szRow_TO_PP_le_b | (intros; apply GlobalTheory.EX.szRow_TO_PP_le_b <;> assumption)
