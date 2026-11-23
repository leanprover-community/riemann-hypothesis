module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormDifferentEqProd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStrips
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMemBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioConjugatesOfTransport
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfied
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CarrySecond
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CarryWeilUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExFieldOfKeyFinExKey
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExKeyOf
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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RowSumOfHyp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaPairLiftCuspidalOfHypotheses
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistRatioMemNumberField
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedBaseExistence
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedConstantExistence
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDictionaryEventuallyLarge
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedGridExistenceOfIdentity
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
namespace GlobalTheory.RowEx
theorem exists_extension_field_of_join : GlobalTheory.Published.HoweDualityReal → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Mem.LiteralAutomorphy.JoinOut → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → ExField :=
  fun hw hm P hJ ht K WC LM TA FS =>
    exField_of_keyFin_exKey keyFin_holds
      (exKey_of (_root_.GlobalTheory.RowEx.twisted_grid_existence_of_identity P)
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
        CarryGrid.carryG (GlobalTheory.RowEx.carryW_of_weil P.weilRepresentationUnitaryPair) GlobalTheory.RowEx.carryS trEasy
        (PhaseCarry.trPhase_of_trFlip GlobalTheory.RowEx.Carry.flippedTensorsTransferToGrid_proof) (Jet.trJet_of_trFlip GlobalTheory.RowEx.Carry.flippedTensorsTransferToGrid_proof) GlobalTheory.RowEx.trBot_holds)
end GlobalTheory.RowEx
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

theorem _root_.GlobalTheory.T.theta_lift_extension_field_exists : GlobalTheory.Published.HoweDualityReal → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Mem.LiteralAutomorphy.JoinOut → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → ExField := by
  exact @_root_.GlobalTheory.RowEx.exists_extension_field_of_join
end
