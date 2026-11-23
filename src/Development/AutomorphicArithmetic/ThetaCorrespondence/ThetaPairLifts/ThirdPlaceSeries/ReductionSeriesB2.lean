module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridStaircaseLatticeFirstColumnTransportStages
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricHeckeLawsOfMultiplicityLowerBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Lb2OfThetaTwistStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedThTw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section
namespace GlobalTheory.HeightCounting.Up
private theorem listPin_of_stage_eq {B : Base} {C : Cols B} {a b : Late B C}
    {I : Type} {L : Formalism.IndefR.Links.LevCh a.D I}
    {L' : Formalism.IndefR.Links.LevCh b.D I} {c bound : ℝ}
    (e : a = b) (hL : HEq L L') (h : ListPin b.D L' c bound) :
    ListPin a.D L c bound := by
  subst b
  exact Eq.mpr (congrArg (fun M => ListPin a.D M c bound) (eq_of_heq hL)) h

open GlobalTheory.Mem.R3.Tr in
private theorem listPin_thetaTwist {K : Ctx} {B : Base} {f : Fr B.toPre}
    {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P)
    (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd
      (Dof x).ntw (Dof x).nexp)
    {I : Type} (L : Formalism.IndefR.Links.LevCh (Dof x) I) {c bound : ℝ}
    (h : ListPin (Dof x) L c bound) :
    ListPin (w.st (oTw x (thTw (Dof x) th)).Z).toD7
      (levCh (a := x.o.Z) (oTw x (thTw (Dof x) th)).Z L) c bound := by
  obtain ⟨G, hF, hTie⟩ := h
  let G' := GlobalTheory.Mem.GridMove.gdC (a := x.o.Z) (oTw x (thTw (Dof x) th)).Z G
  refine ⟨G', ⟨?_, ?_⟩, ?_⟩
  · with_unfolding_all exact hF.values
  · with_unfolding_all exact hF.roots
  · dsimp only [G', GlobalTheory.BigTop.Fun.lamOf, GlobalTheory.Mem.GridMove.gdC,
      GlobalTheory.Mem.GridMove.plC, GlobalTheory.Mem.GridMove.chC] at hTie ⊢
    exact hTie

open GlobalTheory.Mem.R3.Tr in
theorem points_step_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.ModuliPointsExistList' hL cDep := by
  intro hPr hSer hL cDep
  refine StepW.trans (_root_.GlobalTheory.T.geoLaws_iC_at_levelB1_of_serN hPr hSer hL) (StepW.of_all ?_)
  intro K B f T w _ _ hq P x l
  have hlaw := hq P x l
  let th := GlobalTheory.GeoTie.geoNTh hlaw
  obtain ⟨x', hl', ho, hLc⟩ :=
    _root_.GlobalTheory.T.exists_levelB2_twist_of_thetaTie hL x l th (GlobalTheory.GeoTie.geoTie hlaw)
  refine ⟨x', hl', fun hLs => ?_⟩
  exact listPin_of_stage_eq (a := x'.o.Z) (b := (oTw x (thTw (Dof x) th)).Z)
    (congrArg (fun o : P.q.Over => o.Z) ho) hLc
    (listPin_thetaTwist x th x.m.z.R.toRealDat.toLevCh (c := cDep) (bound := K.s.b) hLs)
end GlobalTheory.HeightCounting.Up
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.moduliPointsExistList_of_inputs_serN : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.ModuliPointsExistList' hL cDep := by
  exact _root_.GlobalTheory.HeightCounting.Up.points_step_alt_alt
end
end
