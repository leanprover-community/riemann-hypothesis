module

public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcTheoremToolsOfWachModuleConclusionsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGenerationUnramifiedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeCrystallineSequences
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatementsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulCocycle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHoldStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedFormsStatement
import Formalism.SharpRestriction.LevelLetterCocycles.ExtensionInvariantClause
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.AdmThmE

theorem admitted_all : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), WachCoordinates.admitted D HW F Cm 10 := by
  intro hBK hTD hEC D HW F Cm
  obtain ⟨hU, hE⟩ := GlobalTheory.T.wachModuleLocalConclusions_usedForms D HW F Cm
  obtain ⟨pL, pW, _, _, pWR, pH, pTr, _⟩ := GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hBK hTD hEC D HW F Cm
  obtain ⟨_, hSatE, _, _, _, _, hKillE, _, hF1E, _, hF2E, hTools, hBC⟩ := GlobalTheory.T.arcTheorem_tools_of_wachModuleConclusions D HW F Cm
  obtain ⟨p1, _, _, _, _, _, _, p8, p9, _, _, a, _⟩ := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  have hX := GlobalTheory.HerrExtUnit.main D HW F
  exact ⟨hU, pL, pW, pWR, pH, pTr, hTools, hSatE, hF1E, hF2E, hKillE, GlobalTheory.T.h1fGeneratorBoundAll_loc D, hBC,
    GlobalTheory.HodgeCrysSeq.hodge_crystalline_sequences D, hE,
    Formalism.MainNotions.UnusedSlot35.extension_clause D HW F ⟨p1, p8, hX⟩,
    Formalism.MainNotions.UnusedSlot35.extension_invariant_clause D HW F ⟨p1, p8, p9, a, hX⟩⟩

end GlobalTheory.AdmThmE
