module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsUIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormDifferentEqProd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStrips
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMemBelow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AtDatRowTestOfExField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjKOfSeparatesLinB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftExtensionFieldExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftRowPropertiesConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaPairLiftCuspidalOfHypotheses
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TowerOfThetaMatching
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleExistenceOfTheta
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedLinearBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedLocalFactorRatioHolds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareLocalMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareThetaIntegralsEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedWeilRepresentationConvergence
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
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3
theorem GlobalTheory.RowTestAssembly.test_vector_at_datum_of_join : GlobalTheory.Published.SiegelSetUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Mem.LiteralAutomorphy.JoinOut → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → AtDat fun _ _ _ _ _ _ _ _ z => Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) :=
  fun sg hw g P hJ a12 K LM T3 =>
    have s1 := _root_.GlobalTheory.WeilConv.twisted_weil_representation_convergence sg P
    have s2 := _root_.GlobalTheory.SquareLM.twisted_square_local_matching hw P K LM
    have s3 := _root_.GlobalTheory.SquareAgree.twisted_theta_integrals_agree P K LM
    have j := _root_.GlobalTheory.RowClaim.Join.thetaLift_row_properties_conj P K LM s1 s2 s3
    have l := GlobalTheory.SqTop.lNe_of_functionalEquation a12.abs GlobalTheory.HeckeStrip.completedLBoundedInStrips GlobalTheory.SqTop.fieldDat
    GlobalTheory.Twist.atDat_rowTest_of_exField g P.cuspRapidDecay j.2.2.1
      (GlobalTheory.RowEx.injK_of_separates_linB T3 (_root_.GlobalTheory.RowEx.twisted_linear_bound P (_root_.GlobalTheory.PairLift.thetaPairLift_cuspidal_of_hypotheses P)))
      j.2.1 j.1 j.2.2.2.1 j.2.2.2.2
      (_root_.GlobalTheory.RowClaim.twisted_local_factor_ratio_holds P K LM j.2.1 l (_root_.GlobalTheory.SqTop.triEx_holds_alt hw P K LM l) (_root_.GlobalTheory.SqTower.tower_alt_bis P K LM l))
      (_root_.GlobalTheory.T.theta_lift_extension_field_exists hw LM P hJ a12 K s1 s2 s3 T3)
end

section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.test_vector_assembly_holds : GlobalTheory.Published.SiegelSetUnitary → GlobalTheory.Published.HoweDualityReal → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Mem.LiteralAutomorphy.JoinOut → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → AtDat fun _ _ _ _ _ _ _ _ z => Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) := by
  first | exact @_root_.GlobalTheory.RowTestAssembly.test_vector_at_datum_of_join | exact _root_.GlobalTheory.RowTestAssembly.test_vector_at_datum_of_join | (intros; apply _root_.GlobalTheory.RowTestAssembly.test_vector_at_datum_of_join <;> assumption)
end
