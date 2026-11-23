module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaLiftInnerProductFormulaOfPublishedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLiftMemCuspFormMultiplicitySpaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLiftScalarOfInnerProductFormulaBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteZetaIntegralEulerProductOfPartialLStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitenessInputsRealData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeRealPlaceUpperBoundOfHarishChandraStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMassLowerBoundOfOrthonormalLatticeFramesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKTranslate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasDerivAtLogCosh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MatrixEntryNormSumUpperRightBlockElementPLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.T2SpaceIsNonarchimedeanLocalFieldSingleBlock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivEqZeroOfEven
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumSourceLevelCharacterLawStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteZetaIntegralThetaLiftEqPartialLValueStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorMatrixCoefficientFormulaStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLevelIndexMulSchwartzNormFormulaStatement
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SecOfDm
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle

@[expose] public section

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
namespace GlobalTheory.LowRowAdel
theorem adelC_of_siegelWeil_of_doubling_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent →
    _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → AdelC R F := by
  intro hCusp hWS _hSWc hDbl hUnr hBZ hFD D G _ _ Pl0 T A Ks _ _ _ R F hL hStd
  have hHM : GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts.HarmonicModule :=
    GlobalTheory.HarmModule.harmonicModule_of GlobalTheory.FockDecay.harmonicDecay GlobalTheory.CartanInt.coshIntegral
  have hLoc : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock := GlobalTheory.SingleBlock.localIntegralSingleBlock
  have hPM : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D := GlobalTheory.PlaceTensor.placeModels D
  exact GlobalTheory.T.adelicLift_scalar_of_innerProductFormula R F (GlobalTheory.T.adelicLift_mem_cuspForm_multiplicitySpace hCusp R F) (GlobalTheory.T.finiteDatum_sourceLevelCharacter_law hLoc R F hPM)
    (GlobalTheory.T.twistedThetaLift_innerProductFormula_of_hypotheses hCusp hWS (_root_.ResidueKilled.sec_of_dm hDbl) R F hL)
    (GlobalTheory.T.fockVector_matrixCoefficient_formula hHM R F hPM) (deltaNorm_all D)
    (GlobalTheory.T.finiteZetaIntegral_eulerProduct_of_partialL R F (GlobalTheory.T.finiteZetaIntegral_thetaLift_eq_partialLValue hCusp hBZ hUnr R F)) (GlobalTheory.T.thetaLevelIndex_mul_schwartzNorm_formula hLoc R F hPM)
    (GlobalTheory.T.unitaryMassLowerBound_of_orthonormalLatticeFrames D hStd) (GlobalTheory.T.formalDegreeRealPlaceUpperBound_of_harishChandra hFD R F)
end GlobalTheory.LowRowAdel
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

theorem _root_.GlobalTheory.T.adelC_of_parameter_choice_stdV : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.FormalDegreeCompactDual → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → StdV D → AdelC R F := by
  exact @_root_.GlobalTheory.LowRowAdel.adelC_of_siegelWeil_of_doubling_alt
end
