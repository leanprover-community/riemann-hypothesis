module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithOrigin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRowsDivisionTransportSpectralStageLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridStaircaseLatticeFirstColumnTransportStages
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Lv3StageMovesSpectral
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerUpStatement
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



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
namespace GlobalTheory.HeightCounting.Up
theorem org_of_kept_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cDep : ℝ} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
    {w : ColW B f T} {D D' : D7} {Wt : Set B.places.Pl} {nch : NChoice D} {nch' : NChoice D'}
    (h : _root_.GlobalTheory.HeightCounting.Up.OriginData hL cDep K w Wt nch) (hk : Kept nch nch') : _root_.GlobalTheory.HeightCounting.Up.OriginData hL cDep K w Wt nch' := by
  obtain ⟨P, x, l, h1, h2, h3⟩ := h
  exact ⟨P, x, l, h1, h2, kept_trans_layer h3 hk⟩

theorem lv3Mv_extensionWithOrigin_and_nEog : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (S : SExt) (Γ : GeoP), LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s ∧ LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.GeometricNormExtension hL cDep) S Γ).s := by
  intro hL cDep S Γ
  constructor
  · intro K B f T w Z l S' N h
    have htransport := _root_.GlobalTheory.T.adelicRowsDivision_transport_spectralStage_lattices K B f T w Z l.Wt l.p0 l.what₂ S' N h
    obtain ⟨p0', t', hs, hgeo, hpk, hrx⟩ := htransport
    have hchoice := _root_.GlobalTheory.T.exists_kept_choice_upper_lattice_alt hL K B f T w Z l.Wt S' N h l.nch l.xd
    obtain ⟨nch', xd', hk, -, hn, -, hnx⟩ := hchoice
    have hnnew := hn l.n
    obtain ⟨n'⟩ := hnnew
    have hrxnew := hrx ⟨l.rx⟩
    obtain ⟨rx'⟩ := hrxnew
    have hdata := l.nx
    obtain ⟨c, ⟨e, ⟨pin⟩⟩, ⟨org⟩⟩ := hdata
    have hnxnew := hnx l.p0 l.what₂ l.n p0' t' n' hs hgeo ⟨c, e⟩
    obtain ⟨⟨c', e'⟩⟩ := hnxnew
    have pin' := GlobalTheory.Mem.GridMove.listPin_rowsSame cDep K.s.b K B f T w Z l.Wt S' N h l.p0 l.what₂ p0' t' hs pin
    exact ⟨Lv3.mk ⟨l.g, l.coh, l.Wt, p0', t', rx'⟩ nch' n' xd'
      l.chiT ⟨c', ⟨e', ⟨pin'⟩⟩, ⟨_root_.GlobalTheory.HeightCounting.Up.org_of_kept_alt org hk⟩⟩, hpk⟩
  · intro K B f T w Z l S' N h
    have htransport := _root_.GlobalTheory.T.adelicRowsDivision_transport_spectralStage_lattices K B f T w Z l.Wt l.p0 l.what₂ S' N h
    obtain ⟨p0', t', hs, hgeo, hpk, hrx⟩ := htransport
    have hchoice := _root_.GlobalTheory.T.exists_kept_choice_upper_lattice_alt hL K B f T w Z l.Wt S' N h l.nch l.xd
    obtain ⟨nch', xd', hk, -, hn, hg, hnx⟩ := hchoice
    have hnnew := hn l.n
    obtain ⟨n'⟩ := hnnew
    have hrxnew := hrx ⟨l.rx⟩
    obtain ⟨rx'⟩ := hrxnew
    have hdata := l.nx
    obtain ⟨c, ⟨⟨e, ⟨pin⟩⟩, ⟨org⟩⟩, ⟨good⟩⟩ := hdata
    have hnxnew := hnx l.p0 l.what₂ l.n p0' t' n' hs hgeo ⟨c, e⟩
    obtain ⟨⟨c', e'⟩⟩ := hnxnew
    have pin' := GlobalTheory.Mem.GridMove.listPin_rowsSame cDep K.s.b K B f T w Z l.Wt S' N h l.p0 l.what₂ p0' t' hs pin
    exact ⟨Lv3.mk ⟨l.g, l.coh, l.Wt, p0', t', rx'⟩ nch' n' xd'
      l.chiT ⟨c', ⟨⟨e', ⟨pin'⟩⟩, ⟨_root_.GlobalTheory.HeightCounting.Up.org_of_kept_alt org hk⟩⟩, ⟨hg good⟩⟩, hpk⟩
end GlobalTheory.HeightCounting.Up
end
