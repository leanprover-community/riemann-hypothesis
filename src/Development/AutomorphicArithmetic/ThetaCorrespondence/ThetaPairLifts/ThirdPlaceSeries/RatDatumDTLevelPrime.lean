module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistFiniteDatumThetaAtLevelPrimeStatement
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem ratDatum_dT_levelPrime_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ eT, IsIdemSum eT ((B.primes X).vT u) → ∀ j (hj : j + 1 ≤ B.R.m) (α : J.Ch₀ j) (γ : J.Ch₀ (j + 1)), IsRatDatum (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ eT (fun z => B.embLL (Formalism.L2.Col.phiT B.fields.K (J.A.p0 j α).1.1.deco.1 (J.A.p0 (j + 1) γ).1.1.deco.1 (GlobalTheory.QTw.homOf I l Z j hj z))) (a.g.vac j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j)) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hAll u a ha hTr t J hJ eT heT j hj α γ
  letI : Field a.k := a.fld
  letI : ValuativeRel a.k := a.val
  letI : TopologicalSpace a.k := a.top
  letI : IsNonarchimedeanLocalField a.k := a.loc
  have hS := ha.shape
  have hP : (fun v => v ∈ a.v.tP) = (fun v => ∃ i, v = (a.o.p i).v) := funext fun x => propext (hS.pre.tP x)
  have hPl : GlobalTheory.FinPl.Places a.o.p a.o.I (fun v => ∃ i, v = (a.o.p i).v) :=
    ⟨hS.pre.nodup, hS.pre.all, hS.pre.inj, fun _ => Iff.rfl, fun i => (hS.pre.char i).2⟩
  have hR : GlobalTheory.FinPl.Reps (_root_.GlobalTheory.Fam.pk_z W).ψ (a.o.β j) (a.o.β (j + 1)) (a.g.x j).L (a.g.x (j + 1)).L
      (fun i => GlobalTheory.LatPair.phiOne (a.o.Q j i) (a.o.Q (j + 1) i)) a.o.I (fun v => ∃ i, v = (a.o.p i).v) (a.v.dT j) := by
    rw [← hP]; exact ⟨(ha.vis.atT j).1, hS.rep j hj⟩
  exact GlobalTheory.T.twistFiniteDatum_theta_at_levelPrime I hAll.tr.ok hAll.tr.pins.some l Z u (W.P.I.tup t) J.Ch₀ J.A hJ.is _ _ _ _ _ hTr.pinX a.k a.ι a.o.p a.o.β a.o.Q
    hTr.std a.o.I hPl j hj α γ (a.v.dT j) hR eT heT
end GlobalTheory.Fam
end
