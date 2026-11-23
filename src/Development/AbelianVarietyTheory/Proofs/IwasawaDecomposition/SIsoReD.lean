module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsoPairToTermSymm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeepPuVolAR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralRedivisionTermEquivKeepsTermDataStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe.IsoRe

variable {D : D7} (Z : New D) {X : HidaSetting D} {Y : Full X} (h : FinX Y) (h' : FinX (reY Z Y))

def eP (u u' : D.what₂.Word) : RP Y u u' ≃ RP (reY Z Y) (wd Z u) (wd Z u') :=
  (rp_iso_pair D Z X Y h h' u u').choose



def sIsoRe : SIso (sOf h) ((@sOf (reD D Z) (@reX D Z X) (@reY D Z X Y) h')) where
  cd := (by with_unfolding_all exact ((Eq.refl (Formalism.L2.SG.PairVal.cdScaleOf D)) :))
  del := (by with_unfolding_all exact ((Eq.refl D.s.Del) :))
  letter := (by with_unfolding_all exact ((Eq.refl D.s.letter) :))
  eHH := (by with_unfolding_all exact ((eHHre Z X) :))
  eCu := (by with_unfolding_all exact ((eCure Z h h') :))
  Pu_eq := (by with_unfolding_all exact ((keep_pu_vol_aR D Z X Y h h').1 :))
  volN := (by with_unfolding_all exact ((Eq.refl Y.volN) :))
  volH := (by with_unfolding_all exact ((Eq.refl Y.volH) :))
  eT := (by with_unfolding_all exact ((eRT Z Y) :))
  aTerm_eq := (by with_unfolding_all exact ((keep_pu_vol_aR D Z X Y h h').2.2 :))
  isId := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).1 :))
  inS := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.1 :))
  relevant := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.1 :))
  FeqF := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.1 :))
  Gterm := fun {u u'} t => Subtype.ext (a1 := (sOf h).Gterm t) (a2 := (by with_unfolding_all exact (((sOf h').Gterm (eRT Z Y u u' t)) :))) ((by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.2.1 :)))
  atP := fun p => (by with_unfolding_all exact ((Formalism.L2.S.LocIso.refl (Formalism.L2.S.locC D p)) :))
  ePl := (by with_unfolding_all exact ((Equiv.refl (Formalism.MainNotions.S.LocalSplitGroups.PlF D)) :))
  BBne := fun {u u'} t q => (by with_unfolding_all exact ((((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.2.2.1 q) :))
  generic := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.1 :))
  eP := (by with_unfolding_all exact ((eP Z h h') :))
  pfst := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).1) :))
  psnd := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).2.1) :))
  s0 := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).2.2.1) :))
  scalarPair := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).2.2.2.1) :))
  pval := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).2.2.2.2) :))
  ptOf := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.2.2.2.1 :))
  cTerm := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.2.2.2.2.2 :))
  massPair := fun {u u'} p => (by with_unfolding_all exact (((((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 ((p.1.1) : RT Y u u')).2.2.2.2.2.2.2.2.1).trans
      (congrArg Formalism.L2.SG.PairVal.massTerm ((rp_iso_pair D Z X Y h h' u u').choose_spec ((p) : RP Y u u')).1)) : _))
  meanCount := (by with_unfolding_all exact ((funext fun u => funext fun u' => funext fun w => (GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').2 w :
      (fun (u u' : D.what₂.Word) w => Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w) =
        fun (u u' : D.what₂.Word) w => Formalism.L2.SG.PairVal.meanCount (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) w) :))

end GlobalTheory.Mem.SRe.IsoRe

namespace GlobalTheory.Mem.SRe



theorem sIso_reD : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (h : FinX Y) (h' : FinX (reY Z Y)),
    ∃ e : SIso (sOf h) ((@sOf (reD D Z) (@reX D Z X) (@reY D Z X Y) h')), HEq e.eHH (eHHre Z X) ∧ ∀ u, HEq (e.eCu u) (eCure Z h h' u) :=
  fun _ Z X _ h h' => ⟨IsoRe.sIsoRe Z h h', (by with_unfolding_all exact ((HEq.refl (eHHre Z X)) :)),
    fun u => (by with_unfolding_all exact ((HEq.refl (eCure Z h h' u)) :))⟩

end GlobalTheory.Mem.SRe
