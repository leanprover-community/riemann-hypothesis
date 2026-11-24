module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowFormsMatchPeriodMapOfFurtherProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

theorem _root_.GlobalTheory.T.rowFormsMatchPeriodMap_of_furtherProperties : ∀ (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0), RX K B f T w Z Wt p0 t → ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a := by
  first | exact @GlobalTheory.AtG.RX.rowPin_of_rx | exact GlobalTheory.AtG.RX.rowPin_of_rx | (intros; apply GlobalTheory.AtG.RX.rowPin_of_rx <;> assumption)
