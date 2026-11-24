module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanLevelVolumeMulRelIndexStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosetsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvHaarVolumeToRealEqRelIndexIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinColTOfPinColL
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryChainStepIdentity
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelProdStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.Fam
namespace VolMid
end VolMid
open VolMid
theorem volLev_mul_wt_mid_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j, j + 2 ≤ B.R.m → ∃ v : ℂ, v ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α, (GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) : ℂ) * J.wt j α = v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT j hj
  obtain ⟨Up, hUpf, hUpc, hK⟩ := _root_.GlobalTheory.T.true_geometry_step_value_alt W hW u a ha haT j hj
  have step : ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α : J.Ch j,
      (GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) : ℂ) * J.wt j α = (GlobalTheory.SeeSaw.volLev (a.g.x j).vol Up : ℂ) ∧
        J.wt j α ≠ 0 ∧ GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) ≠ 0 := by
    intro t J hJ α
    obtain ⟨H, φ, hH, hφK, hφs, hU⟩ := hK t J hJ α
    have hidx := relIndex_eq_prod_of_pi φ Up (J.A.U j (J.ι j α)) (fun i => KO (J.G i).k _) H hφK hφs hU
    have hreps := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hW.tr.ok hW.tr.pins.some l Z u (W.P.I.tup t) J.Ch₀ J.A hJ.is j (by omega) (J.ι j α)).1
    have hvol := GlobalTheory.T.archimedeanLevelVolume_mul_relIndex (I.rec7 l Z) _ (a.g.x j).vol (J.A.U j (J.ι j α)) Up (fun g hg => ((hU g).1 hg).1) hUpf hUpc
      hreps.opn
    have hwt : J.wt j α = ((J.A.U j (J.ι j α)).relIndex Up : ℂ) := by
      rw [hidx, _root_.GlobalTheory.Fam.QuadraticExtensionData.wt]
      push_cast
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [(hH i).2.2.2]
      exact GlobalTheory.T.inv_haarVolume_toReal_eq_relIndex_integral (J.G i) _ (J.E i) j (H i) (hH i).1 (hH i).2.1 (hH i).2.2.1
    refine ⟨?_, ?_, GlobalTheory.AdForm.PinInhab.volLev_ne_zero hW.tr.ok haT.pinX.inf j _ _ hreps⟩
    · rw [hwt, ← hvol]; push_cast; ring
    · rw [hwt, hidx]; push_cast; exact Finset.prod_ne_zero_iff.2 fun i _ => by exact_mod_cast (hH i).2.2.1
  by_cases hex : ∃ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.Reads ∧ Nonempty (J.Ch j)
  · obtain ⟨t, J, hJ, ⟨α⟩⟩ := hex
    refine ⟨GlobalTheory.SeeSaw.volLev (a.g.x j).vol Up, ?_, fun t' J' hJ' α' => (step t' J' hJ' α').1⟩
    obtain ⟨h1, h2, h3⟩ := step t J hJ α
    rw [← h1]
    exact mul_ne_zero (by exact_mod_cast h3) h2
  · exact ⟨1, one_ne_zero, fun t J hJ α => absurd ⟨t, J, hJ, ⟨α⟩⟩ hex⟩
end GlobalTheory.Fam
end
end
