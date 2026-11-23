module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormDifferentEqProd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRankSumLeTwoMulTotalRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStrips
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatRepr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMemBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioConjugatesOfTransport
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfied
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralAndArchimedeanBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyLargeGrid
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridExistenceOfPieces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyFinitenessGlobal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormFieldSquareClass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceSquare
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CarrySecond
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CarryWeilUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsExOfSeparates
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIntegralOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KeyFinHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormCharacters
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormJets
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormPhase
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeAlgebraMapMono
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TrEasy
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TrJetOfTrFlip
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TrPhaseOfTrFlip
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransferBottom
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransferFlip
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwoLeMOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomFieldIsNumberField
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsWeilDeligneOfLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RowSumOfHyp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaPairLiftCuspidalOfHypotheses
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistRatioMemNumberField
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedBaseExistence
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedConstantExistence
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDictionaryEventuallyLarge
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedLinearBound
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
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.Mem.Top GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory.Mem.LiteralAutomorphy
theorem evaluation_grid_of_join : GlobalTheory.Published.HoweDualityReal → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Mem.LiteralAutomorphy.JoinOut → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → EvLgG (GridA CF) :=
  fun hw hm P hJ ht K WC LM TA FS =>
    GlobalTheory.Mem.LiteralAutomorphy.evLgG_gridA_of_exGrid
      (GlobalTheory.Mem.LiteralAutomorphy.exGrid_of (_root_.GlobalTheory.Mem.LiteralAutomorphy.exists_weilDeligne_of_localInputs P)
        (isEx_of_separates FS (_root_.GlobalTheory.RowEx.twisted_linear_bound P (_root_.GlobalTheory.PairLift.thetaPairLift_cuspidal_of_hypotheses P)) (_root_.GlobalTheory.RowEx.twisted_base_existence P (_root_.GlobalTheory.RowEx.twisted_constant_existence hw hm P K WC LM TA)))
        (nfAll_of GlobalTheory.RowEx.nfChars nfRoot (GlobalTheory.RowEx.nfPhase_of_sumOKK (_root_.GlobalTheory.RowClaim.rowSum_of_hypotheses_alt P))
          (GlobalTheory.NFJetProof.nfJet_holds (_root_.GlobalTheory.RowClaim.rowSum_of_hypotheses_alt P) GlobalTheory.NormSum.inp_all (_root_.GlobalTheory.DictFree.twisted_dictionary_eventually_large P GlobalTheory.NormSum.inp_all))
          (_root_.GlobalTheory.RowEx.RatioField.twistRatio_mem_numberField P
            (GlobalTheory.ToricTransport.toricRatioConjugates_of_transport
              hJ.2.2.1)
            GlobalTheory.SqTop.fieldDat
            (GlobalTheory.SqTop.lNe_of_functionalEquation (GlobalTheory.Published.HeckeTateFunctionalEquation.abs ht) GlobalTheory.HeckeStrip.completedLBoundedInStrips
              GlobalTheory.SqTop.fieldDat))
          (_root_.GlobalTheory.RowEx.bottomField_isNumberField P GlobalTheory.NormSum.inp_all))
        (GlobalTheory.Mem.LiteralAutomorphy.nfSq_of_fieldDat GlobalTheory.NormSum.intSt_and_archSt.1 GlobalTheory.SqTop.fieldDat
          (GlobalTheory.ToricExist.torEx hJ.2.1 GlobalTheory.SqTop.fieldDat
            (GlobalTheory.SqTop.lNe_of_functionalEquation (GlobalTheory.Published.HeckeTateFunctionalEquation.abs ht) GlobalTheory.HeckeStrip.completedLBoundedInStrips
              GlobalTheory.SqTop.fieldDat))
          GlobalTheory.SqTop.BotSmallProof.botSmall_holds)
        CarryGrid.carryG (GlobalTheory.RowEx.carryW_of_weil P.weilRepresentationUnitaryPair) GlobalTheory.RowEx.carryS trEasy
        (PhaseCarry.trPhase_of_trFlip GlobalTheory.RowEx.Carry.flippedTensorsTransferToGrid_proof) (Jet.trJet_of_trFlip GlobalTheory.RowEx.Carry.flippedTensorsTransferToGrid_proof) GlobalTheory.RowEx.trBot_holds
        GlobalTheory.Mem.LiteralAutomorphy.trSq_holds keyFin_holds GlobalTheory.Mem.LiteralAutomorphy.gKeyFin)
end GlobalTheory.Mem.LiteralAutomorphy
end
