module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ReferenceChainEvaluationAtBundlePoints
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSymmetricColumnFormsStepZeroFiniteCharacteStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PropertyAtConstructedPointsOfTrueColumnsViewStatement
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.PeriodEntriesOverColumns

def TiePt (D : D7) (_ : Obj D) : Prop :=
  Formalism.L2.Theta.RealTied D ∧ ∃ C : Formalism.L2.Forms.ColsTiedSym D, ∀ u, Formalism.MainNotions.RT.ChiFin0 (C.forms u)

theorem row_tie_of_overCols : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), PeriodEntriesOverColumns.Row_tie Q Lk := by
  intro Q hQ Bd Lk
  have hpt : ∀ (K : Ctx) (β : BPt K), β.Is HasCols → TiePt β.D β.O :=
    GlobalTheory.T.property_at_constructedPoints_of_trueColumnsView TiePt fun B f T w Z O nch _ _ hR =>
      ⟨hR, GlobalTheory.T.exists_symmetricColumnForms_stepZeroFiniteCharacter w.I w.ok w.pins w.l Z⟩
  have h0 : Row0 Q (EvC TiePt) :=
    validForConstructedPointClasses_eventuallyWorkingClass (Q := Q) (EvP.of_all fun _ K _ β hq => hpt K β (hQ K β.X β.f β.T β.c hq))
  refine Row0.row (Row.imp h0 fun 𝒜 _ _ h => ?_) Lk
  refine Closed.imp h fun Fm _ _ H => ?_
  obtain ⟨x0, hx0⟩ := H
  refine ⟨max x0 (Fm.x1 + 1), fun x hx i => ?_⟩
  have e0 : x0 ≤ x := le_trans (le_max_left _ _) hx
  have e1 : Fm.x1 < x := by have := le_trans (le_max_right x0 (Fm.x1 + 1)) hx; linarith
  exact hx0 x e0 e1 i

end GlobalTheory.Fc.PeriodEntriesOverColumns
