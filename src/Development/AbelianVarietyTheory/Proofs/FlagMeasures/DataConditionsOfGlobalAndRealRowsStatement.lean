module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DataConditionsOfGlobalAndRealRows
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG

theorem _root_.GlobalTheory.T.dataConditions_of_global_and_real_rows : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (Cg C0 : ℝ), Glob0 D x eps CD Cg → Nodes D x eps → ArithmeticConditionsOfDatum D → DuWin D C0 → StandingNumericalData D C0 := by
  first | exact @GlobalTheory.Diag.PG.data_of_rows | exact GlobalTheory.Diag.PG.data_of_rows | (intros; apply GlobalTheory.Diag.PG.data_of_rows <;> assumption)
