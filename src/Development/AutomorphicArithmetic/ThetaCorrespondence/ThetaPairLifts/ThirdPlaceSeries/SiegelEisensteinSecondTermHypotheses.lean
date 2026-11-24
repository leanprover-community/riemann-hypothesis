module

public import Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BernsteinUnitaryProductIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Hyps
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Prm1
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumRangeEqRoots
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowRatWOfRowTest
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoMemOfMkEq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.EvaluationGridOfJoin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FunctionalsSeparateOfHoweUnramOfSiegelWeil
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TestVectorAtDatumOfJoin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareLocalMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareThetaIntegralsEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedWeilRepresentationConvergence
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.At23OfAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FourierCoefficientFitOfJoin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HypothesesNonemptyOfUnramifiedExponents
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedBundlesL3OfOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OpenAndLinkedOfStrongerExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OpenOrbitOfUnramifiedExponents
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowFunAtGridA
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SurjectiveAndLowWeightOfUnramifiedExponents
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopPlug
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithAtProperty
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithOrigin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricWeakTies

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.Lit
open UpperTheory.Top
theorem nonempty_hyps_definite_side_of_closed_bound : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → _root_.GlobalTheory.CovTop.CovolumeBoundOfX → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists), (∀ cDep : ℝ, _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep) (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L fun 𝒞 => Formalism.MainNotions.Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm)) → Nonempty (_root_.GlobalTheory.Fc.HypsAlt S0.NL _root_.GlobalTheory.Fc.DefiniteSideCondition) := by
  intro P F hA hM hX hL hN
  have C := P.litN
  have hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate :=
    _root_.UpperTheory.Lit.functionalsSeparate_of_howeUnram_of_siegelWeil F GlobalTheory.Hk3.howeUnram_holds P.siegelWeilUnitaryConvergent
  have hRat : S0.RowRat := GlobalTheory.Mem.LiteralAutomorphy.rowRatW_of_rowTest (_root_.GlobalTheory.T.test_vector_assembly_holds F.siegelSetUnitary F.howeDualityReal
    P.greenCuspidal F C.join C.fe hA hM hS)
  have hFit : _root_.GlobalTheory.BigTop.Fun.ConstantFunctionFits @GlobalTheory.BigTop.Fun.Fld := _root_.GlobalTheory.BigTop.Fun.Close.fourier_coefficient_fit_of_join_alt F C.join C.fe hA hM hS (_root_.GlobalTheory.Fc.S0.ontoX_and_lamLow_of_unitaryGroupHypotheses' P).2
  obtain ⟨CF1, hCF1⟩ := _root_.GlobalTheory.Mem.LiteralAutomorphy.evaluation_grid_of_join F.howeDualityReal hM F C.join C.fe hA
    (_root_.GlobalTheory.WeilConv.twisted_weil_representation_convergence F.siegelSetUnitary F) (_root_.GlobalTheory.T.twisted_local_factors_match F.howeDualityReal F hA hM)
    (_root_.GlobalTheory.T.twisted_square_theta_integrals_eq F hA hM) hS
  obtain ⟨CF0, hCF0⟩ := _root_.GlobalTheory.Fc.StageOne.rowFun_at_gridA_alt P.discreteSeriesCover P.harishChandraModules P.cuspRapidDecay P.casselmanWallach
    P.rayClassFieldSt hFit
  have hEv : EvLgG (GridA (max CF0 CF1)) := hCF1 _ (le_max_right _ _)
  have hOpen1 : _root_.GlobalTheory.Fc.S0.OpenParameterStatements (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL (max CF0 CF1)) := _root_.GlobalTheory.T.open0_of_unitary_group_hypotheses P hL (max CF0 CF1)
  have hMono := _root_.GlobalTheory.Glob.open_and_linked_of_stronger_extension_alt hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL (max CF0 CF1))
    (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL (max CF0 CF1)) (GridA (max CF0 CF1))) SExt.none (geoCl anyGeometry)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1.1⟩)
  have hOpenA := hMono.2 hOpen1
  have hFun := hCF0 (max CF0 CF1) (le_max_left _ _) hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL (max CF0 CF1)) SExt.none (geoCl anyGeometry)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1⟩) hOpenA
  have hL3 := _root_.GlobalTheory.Glob.CovolRow.linked_bundles_l3_of_open_alt P.discreteSeriesCover P.harishChandraModules P.cuspRapidDecay
    P.casselmanWallach P.rayClassFieldSt hX hL (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL (max CF0 CF1)) (GridA (max CF0 CF1)))
    SExt.none (geoCl anyGeometry) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1.1.1⟩) hOpenA
  exact _root_.GlobalTheory.Fc.S0.StageU.hypotheses_nonempty_of_unramified_exponents_alt P hRat hL (max CF0 CF1) (GridA (max CF0 CF1)) hEv (hN (max CF0 CF1)) hFun hL3
theorem every_character_of_theta_integrals_local_matching (P : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses) (F : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hA : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) (hX : _root_.GlobalTheory.CovTop.CovolumeBoundOfX) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hV : VWin) :
    UpperTheory.EveryCharacter :=
  _root_.UpperTheory.Top.every_character_of_green_v_win (GlobalTheory.GreenBridge.green_of_regular P.greenRegularCharacters) hV
    (_root_.UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound P F hA hM hX hL fun cDep => _root_.UpperTheory.N.boundAtTwoThree_linked_of_recT P.nLink (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep))
end UpperTheory.Lit
end
end
