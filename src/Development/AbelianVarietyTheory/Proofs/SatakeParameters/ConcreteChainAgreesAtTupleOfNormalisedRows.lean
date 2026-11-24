module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodRelationsTrueColumnsAtTupleStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowPinSetDivZ
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain



theorem GlobalTheory.Svd.tiesAt_of_rowPin : ∀ (K : Ctx) (β : BPt K), β.Is (positionOf (HasPartAnd fun _ _ _ _ w Z => ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a)) → ∀ μ, GlobalTheory.AtG.TiesAt β.D β.O.ex.errX β.O.X μ := by
  intro K β hβ μ
  have key := positionOf_ind (R := fun K X f T c => ∀ O : Obj X.toD7, ofObj O = c.O → ∀ N h μ,
      GlobalTheory.AtG.TiesAt (setDiv X.toD7 N h) (O.tr N h).ex.errX (O.tr N h).X μ) ?_ hβ
  · exact key (β.Y.obj β.p) ((show ofObj (β.Y.obj β.p) = layObj β.Y from rfl).trans β.hY) (nPrime β.p.L) β.p.ht μ
  · intro K B f T w Z c hc O hO N h μ
    obtain ⟨⟨P⟩, hrow⟩ := hc
    have hpart : Part w Z (ofObj O) := hO ▸ P
    obtain ⟨_, hpiG, hpiT, hqp, _⟩ := Part.kerTie B f T w Z O hpart
    exact GlobalTheory.T.periodRelations_trueColumns_at_tuple w.I w.ok w.l (GlobalTheory.Mem.Db.setDivZ Z N h) w.l0 P.pin.jets _ _ μ hpiG hpiT hqp
      (GlobalTheory.AtG.rowPin_setDivZ w.I w.ok w.l Z N h μ (hrow μ))
