module

public import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcTheoremToolsOfWachModuleConclusionsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatementsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHoldStatement
import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible
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

namespace GlobalTheory.NQ

theorem relay_and_arc_inputs : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.RelayArcLifting D HW F ∧ UnusedSlot80.AdmArcA D HW F Cm := by
  intro hBK hTD hEC D HW F Cm
  obtain ⟨_, _, p3, p4, p5, _, _, _, p9, _⟩ := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  obtain ⟨_, _, hW1, _, _, hH, hTr, _⟩ := GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hBK hTD hEC D HW F Cm
  obtain ⟨hSat, _, _, _, _, _, _, hF1, _, hF2, _⟩ := GlobalTheory.T.arcTheorem_tools_of_wachModuleConclusions D HW F Cm
  exact ⟨UnusedSlot80.relay_general_statement D HW F ⟨p5, p9, hH, hTr, hSat, hF1, hF2⟩,
    ⟨p3, p4, p5, p9, hH, hTr, hW1, hSat⟩⟩

end GlobalTheory.NQ
