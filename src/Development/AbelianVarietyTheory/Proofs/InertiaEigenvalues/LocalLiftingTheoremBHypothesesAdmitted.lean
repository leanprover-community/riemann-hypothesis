module

public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleArcDatumGivesArcPropertyStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcTheoremToolsOfWachModuleConclusionsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCrystallineExtensionCriterionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSplittingAlongArcsOfAdmissibleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineUniversalPartCaseAStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DDeRhamEqDCrisOfUnramifiedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DcrisExactStrictElementwiseCrystallineStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineDcrisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFullFaithfulExactPsiStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGenerationUnramifiedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrExtensionClassFormula
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsExactAdm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatementsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHoldStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedFormsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachRelayLemmaArcCoordinateHypothesesStatement
import Formalism.SharpRestriction.LevelLetterCocycles.DivisibilityInvariantMulLinear
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TheoremBAdm

theorem admissible_ranks_of_CMDatum : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      ArcLiftingSetup.admitted D HW F Cm 10 23 32 32 8 := by
  intro hBK hTD hEC D HW F Cm
  have hN1 := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  obtain ⟨hP1, -, -, -, -, hP6, -, hP8, hP9, -⟩ := hN1
  have h54 := GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hBK hTD hEC D HW F Cm
  obtain ⟨-, ⟨hWX, -⟩, hW1, -, -, hH, -, -⟩ := h54
  have hB := GlobalTheory.T.arcTheorem_tools_of_wachModuleConclusions D HW F Cm
  obtain ⟨hSat, -, hSatP, hPi0, hKL, hKill, -, hF1, -⟩ := hB
  obtain ⟨hRelay, hArcAdm⟩ := GlobalTheory.T.wachRelayLemma_arcCoordinateHypotheses hBK hTD hEC D HW F Cm
  have hA11 := GlobalTheory.T.ramifiedCoefficientChains_adm11 D
  have hArc := GlobalTheory.T.arcCoordinatesCaseA_of_admArcA_of_P1free_of_adm11 D HW F Cm hArcAdm hP1 hA11
  have hJ := (GlobalTheory.jumps_exact_adm D HW F).2
  have hExt := GlobalTheory.HerrExtClass.herr_extension_class_formula D HW F
  have hAdm9 := GlobalTheory.T.dcris_exact_strict_elementwise_crystalline D
  have hSplit := GlobalTheory.T.classSplitting_along_arcs_of_admissible D HW F Cm ⟨hP8, hP9, hW1, hJ, hExt, hF1, hRelay, hArc⟩ hArcAdm hP1 hP6 hWX
    (GlobalTheory.T.fontaine_fullFaithful_exact_psi D HW F) hJ hAdm9 hA11
  have hUniv := GlobalTheory.T.crystallineUniversalPart_caseA D HW F Cm ⟨hSat, hKL, hPi0, hArc⟩ hP9 hH (GlobalTheory.T.dDeRham_eq_dCris_of_unramified D)
  exact ⟨(GlobalTheory.T.wachModuleLocalConclusions_usedForms D HW F Cm).1, GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hBK hTD hEC D HW F Cm, hSat, hSatP, hKill,
    ArcLiftingSetup.content_divisibility_clause D, GlobalTheory.T.h1fGeneratorBoundAll_loc D, hRelay, hArc, hSplit, hUniv, hAdm9, GlobalTheory.T.blochKato_crystalline_extension_criterion D⟩

end GlobalTheory.TheoremBAdm
