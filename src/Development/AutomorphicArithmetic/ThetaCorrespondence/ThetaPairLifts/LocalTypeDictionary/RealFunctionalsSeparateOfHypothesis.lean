module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodNonvanishingAscentOfDepthDataStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixedStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowTowerMultiplicitySpacesOfArrowStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsPrincipalLevelAreRowsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LargeScaleSizesImplyGapConditionsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSeparationByRealFunctionalsOfChainStepsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchPeriod
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BesselSeparate
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConvergenceOfSeparatingFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsSeesawPairOfThetaData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RapidDecayOfSeparatingFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SeparatingFamilyExtendsByTwistedRow
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SeparatingFamilyHasModels
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SeparatingModelsOfSeparatingData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCoreSurjectiveOfLocalComponents
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
namespace UpperTheory.Lit
theorem real_functionals_separate_of_hypothesis
    (P : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hHowe : GlobalTheory.Hk3.HoweUnram)
    (hSW : GlobalTheory.Published.SiegelWeilUnitaryConvergent)
    (realIn : Branch.RealInputE) :
    GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate := by
  have rowModels := _root_.GlobalTheory.T.exists_models_of_separating_data P
  have rowStep := _root_.GlobalTheory.T.separating_family_extend_by_twist P (_root_.GlobalTheory.T.exists_seesaw_pair_of_theta_data P) rowModels
  have rowTower := GlobalTheory.T.firstRowTower_multiplicitySpaces_of_arrow rowModels rowStep
  have conv := _root_.GlobalTheory.T.convergence_of_separating_family P rowTower
  have per := Branch.periodNe_of_eigen P.harishChandraModules P.casselmanWallach P.cuspRapidDecay realIn
  have onto := _root_.GlobalTheory.T.twist_core_surjective P P.harishChandraFinite P.cuspRapidDecay P.discreteSeriesCover
    P.harishChandraModules P.casselmanWallach hHowe P.weilRepresentationUnitaryPair
    P.weilSiegelFormulaUnitary hSW P.doublingMethod P.unramifiedDoublingGL
  have weak := GlobalTheory.T.rowSeparation_by_realFunctionals_of_chain_steps GlobalTheory.T.largeScaleSizes_imply_gapConditions (_root_.GlobalTheory.T.exists_separating_models P) (_root_.GlobalTheory.T.rapid_decay_of_separating_family P rowTower) per onto
    (GlobalTheory.T.bessel_period_nonvanishing_ascent_of_depth_data GlobalTheory.T.dependence_fixed)
  exact _root_.UpperTheory.Lit.bessel_separate_of_step_gap P rowTower GlobalTheory.T.largeScaleSizes_imply_gapConditions GlobalTheory.T.goodRows_principalLevel_are_rows conv weak
end UpperTheory.Lit
end
