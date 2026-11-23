module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridStaircaseLatticeFirstColumnTransportStages
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StateB2OfRationalData
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedThTw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3.Tr in
theorem points_preserved_under_level_transfer_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ P x => ∀ D0 : D7, _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x →
    Carried D0 (Dof x) → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x') ∧ Carried D0 (Dof x') ∧ ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x' := by
  intro hPr hSer hL
  refine StepW.trans (_root_.GlobalTheory.T.geoLaws_iC_at_levelB1_of_serN hPr hSer hL) ?_
  refine StepW.of_all ?_
  intro K B f T w _ _ hq P x D0 l hC
  have hlaw := hq P x l
  obtain ⟨x', hl', ho, hLc⟩ := _root_.GlobalTheory.T.exists_levelB2_twist_of_thetaTie hL x l (GlobalTheory.GeoTie.geoNTh hlaw) (GlobalTheory.GeoTie.geoTie hlaw)
  obtain ⟨o', fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩ := x'
  dsimp only at ho
  subst ho
  refine ⟨⟨oTw x (thTw (Dof x) (GlobalTheory.GeoTie.geoNTh hlaw)), fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩, hl',
    carried_thTw D0 (Dof x) _ hC, fun cDep hLs => ?_⟩
  have hgen (D : D7) (th : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp)
      (Z : GlobalTheory.LamTie.LamDat D) : GlobalTheory.LamTie.IsLamTieFull D.ntw Z →
        GlobalTheory.LamTie.IsLamTieFull (thTw D th).toD7.ntw (lamTw (thTw D th) Z) := fun h => h
  have htrans (y : St P) (N : TwNew (Dof y))
      (hN : ∀ Z : GlobalTheory.LamTie.LamDat (Dof y), GlobalTheory.LamTie.IsLamTieFull (Dof y).ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z)
      (c b : ℝ) {I : Type} (Lc : Formalism.IndefR.Links.LevCh (Dof y) I)
      (h : ListPin (Dof y) Lc c b) :
      ListPin (w.st (oTw y N).Z).toD7 (levCh (a := y.o.Z) (oTw y N).Z Lc) c b := by
    obtain ⟨G, h1, h2⟩ := h
    exact ⟨(by with_unfolding_all exact ((GlobalTheory.Mem.GridMove.gdC (a := y.o.Z) (oTw y N).Z G) :)),
      ⟨(by with_unfolding_all exact (h1.values :)), (by with_unfolding_all exact (h1.roots :))⟩,
      (by with_unfolding_all exact ((hN _ h2) :))⟩
  have eL : m'.z.R.toRealDat.toLevCh =
      (by with_unfolding_all exact ((levCh (a := x.o.Z) (oTw x (thTw (Dof x) (GlobalTheory.GeoTie.geoNTh hlaw))).Z x.m.z.R.toRealDat.toLevCh) :)) := eq_of_heq hLc
  show ListPin _ m'.z.R.toRealDat.toLevCh cDep K.s.b
  rw [eL]
  exact htrans x _ (fun Z h => hgen _ _ Z h) _ _ _ hLs
end GlobalTheory.HeightCounting.Up
end
end
section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_levelB2_carried_of_levelB1 : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ P x => ∀ D0 : D7, _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x → Carried D0 (Dof x) → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x') ∧ Carried D0 (Dof x') ∧ ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x' := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.points_preserved_under_level_transfer_alt | exact _root_.GlobalTheory.HeightCounting.Up.points_preserved_under_level_transfer_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.points_preserved_under_level_transfer_alt <;> assumption)
end
end
