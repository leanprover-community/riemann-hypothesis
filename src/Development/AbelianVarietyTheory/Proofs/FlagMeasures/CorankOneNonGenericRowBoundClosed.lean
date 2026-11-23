module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOnePairsNonGenericRowBoundOfRemainingPremiStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGenericMassPositiveBoundedProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGroupSumFactorsRowWeightAmplitudeProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyLocalObjectsExistAtTermsProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyRowWeightSumUnfoldingIdentityProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericCorankOneTermsFamilyCutByDefectStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NongenericRowStatementsOfFamilyStatementsStatement
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

@[expose] public section

open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

namespace GlobalTheory.NGRowClose

theorem rowNGP_of_formNGVanish (hSW : PI.VolStabS.MassDataS.SWXS) (hC : StepChoiceConstantsC)
    (hP : StepPinExists) (hF : Formalism.L2.SG.NGVanish.FormNGC) (hB : StepThmBPinnedP) :
    RowNGP := by
  obtain ⟨h5, hw, h4, he⟩ := GlobalTheory.T.nongeneric_row_statements_of_family_statements GlobalTheory.T.non_generic_corank_one_terms_family_cut_by_defect
  exact GlobalTheory.T.corankOnePairsNonGenericRowBound_of_remaining_premises hC hP hF hB (h5 GlobalTheory.T.familyRowWeightSumUnfoldingIdentity) (hw (GlobalTheory.T.familyGenericMassPositiveBounded_proof hSW))
    (h4 GlobalTheory.T.familyGroupSumFactorsRowWeightAmplitude_proof) (he GlobalTheory.T.familyLocalObjectsExistAtTerms_proof)

theorem close : PI.VolStabS.MassDataS.SWXS → StepChoiceConstantsC → StepPinExists →
    Formalism.L2.SG.NGVanish.FormNGC → StepThmBPinnedP → RowNGP :=
  fun hSW hC hP hF hB => rowNGP_of_formNGVanish hSW hC hP hF hB

end GlobalTheory.NGRowClose
