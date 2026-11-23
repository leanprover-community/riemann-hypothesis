module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopShapeAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Hyps
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefiniteSideCondition
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc

theorem GlobalTheory.Fc.goal_of_shape_of_hyps (V NR : Prop) (N : FamClass → Prop) (G : Prop) (t : _root_.GlobalTheory.Fc.TopShapeAlt V NR N G) (hV : V) (hR : NR) (h : _root_.GlobalTheory.Fc.HypsAlt N _root_.GlobalTheory.Fc.DefiniteSideCondition) : G :=
  t h.𝒜 h.cT h.hEx (_root_.GlobalTheory.Fc.familySelection h.σ) h.hduty (_root_.GlobalTheory.Fc.spectralConditionOfRawSelection h.σ) (_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection h.σ) (_root_.GlobalTheory.Fc.definiteHeightOfRawSelection h.σ) (fun Fm hc x hx k i => (_root_.GlobalTheory.Fc.columnChoiceOfRawSelection h.σ Fm hc x hx k i).toS) (_root_.GlobalTheory.Fc.selectionBundleOfRawSelection h.σ) h.hRB h.hTw h.hPA h.hLamP
    (fun Fm hc x hx k i => (GlobalTheory.Cp.divRows3G_iff _).1 (h.hDivG Fm hc x hx k i)) h.hDcPtG h.hTu h.hn4 h.hLit hV h.hWu h.hRF h.hTF h.c30 h.hc30 h.sTy h.sNG h.sM h.sLp h.sO h.h30 h.hInstR h.selJ h.jOn h.hMt
    (h.rRows.imp fun Fm CH _ r hc => let ⟨C, h0, x0, r⟩ := r hc
      ⟨C, h0, x0, fun x hx k hx0 i => let ⟨a, d⟩ := r x hx k hx0 i
        ⟨⟨a.w1, a.covol, a.onto, a.lamLow, a.seeIso, a.miStar, a.fun0, a.pass, a.kap⟩, d⟩⟩)
    h.aPt0 h.aPtTw h.aPer0 h.aPerTw h.aP10 h.aAtG h.aC2 ((_root_.GlobalTheory.Cp.serv_t_iff_formalism_serv_t _ _).1 h.hServ) hR h.nRest h.cIc h.hcI h.irrC h.zL h.tie h.hU h.hG
theorem GlobalTheory.Fc.forall_goal_of_shape_of_hyps : ∀ (V NR : Prop) (N : FamClass → Prop) (G : Prop), _root_.GlobalTheory.Fc.TopShapeAlt V NR N G → V → NR → _root_.GlobalTheory.Fc.HypsAlt N _root_.GlobalTheory.Fc.DefiniteSideCondition → G :=
  fun V NR N G t hV hR h => _root_.GlobalTheory.Fc.goal_of_shape_of_hyps V NR N G t hV hR h
end
