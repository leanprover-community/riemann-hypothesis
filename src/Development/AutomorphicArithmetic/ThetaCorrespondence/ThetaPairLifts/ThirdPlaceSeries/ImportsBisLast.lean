module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DownMemRecOfTies
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodLabelsRankPartParameterCuspidal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPartRecursion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParUpRecOfTies
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigAtStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisExtra
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisRestStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisTer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsLast
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointCondRho
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SEtaChi
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SEtaSig
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameGeneratorResidual
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeOrthOfPinStatement
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
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowsCClose
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), _root_.GlobalTheory.NPin.CharacterChoiceJoin P → _root_.GlobalTheory.NRows.RowsAAlt D →
    GlobalTheory.NRows.RowsB D → Formalism.MainNotions.SumRepresentations.adm1 D → Formalism.MainNotions.SumRepresentations.adm8 D → _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D →
    (∀ i, PairLift D.nd D.naut i ∧ SplitBC D.nd D.naut i ∧ RepOfLoc D.nd D.naut i) → GlobalTheory.NRows.RowsC D := by
  intro hL D P J hA hB a1 a8 p1 hi
  obtain ⟨p41, _, p42⟩ := p1
  obtain ⟨tl, lt, io, rb⟩ := _root_.GlobalTheory.TieLabAt.main_alt_alt hL D P
  have iface := _root_.GlobalTheory.AdmIface.main_alt_alt D
  have bc : ∀ i, BCEx D.nd D.naut i := iface.1 a1
  have lift : ∀ i, GlobalTheory.ThetaExh.LiftParam D.nd D.naut i := iface.2.2.1 p42
  have isot : Rows.IsotInternal D.what₂ := iface.2.2.2.2.2.mp a8
  have rho : GlobalDatumResidualRepCondition D :=
    _root_.GlobalTheory.ParamRep.jointCond_33_rho_of_signature_adm5 D hA.tie0 hA.a2 hB.a4 hA.a5 p41 (GlobalTheory.GoodCuspPoint.main D tl)
      (_root_.GlobalTheory.XiOver.main_alt_alt_alt D P.cf P.C P.tp P.chr P.val hA.tie0 hA.a2 hA.a5)
  have rp : _root_.UpperTheory.GalS.RowRepAtGN D :=
    _root_.GlobalTheory.RowRepOcc.repAtGN_of_point_split D hA.tie0 hA.a2 hA.a5 p42 rho hA.gsp (_root_.GlobalTheory.T.point_of_aux42_aux41 hL D P p42 p41)
  exact
    { c4b := _root_.GlobalTheory.RowTie.tameGenerator_residual_alt_alt D rb io lt rp
      rho := rho
      dz := _root_.GlobalTheory.GoodDepthZero.main_alt_alt D hA.tie0 hB.a4 p41 hA.gsp
      parUp := GlobalTheory.RowTie.parUpRec_of_ties D P.T hB.thetaOne (fun i => (hi i).1) bc (fun i => (hi i).2.1)
        (fun i => (hi i).2.2)
      downMem := GlobalTheory.RowTie.downMemRec_of_ties D P.T hB.thetaOne isot
        (fun i => _root_.GlobalTheory.PartOrthPin.main_alt_alt hL D P i ⟨J.rowM i⟩) (fun i => _root_.GlobalTheory.T.type_orthogonality_of_form' hL D P i (J.form i))
        (fun i => (hi i).1) bc (fun i => (hi i).2.1)
      goodPart := GlobalTheory.Proof.GoodComponentRecursion.goodPartRec_of_ties D P.T hB.thetaOne lift (fun i => _root_.GlobalTheory.T.ptLocal_theta_exhaustion hL D P i) bc
        (fun i => (hi i).2.1) }
end GlobalTheory.RowsCClose
end
