module

public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAndDecompletion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFullFaithfulExactPsiStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremEHypothesesAdmittedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecordCaseA
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitGenExists
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalCorollaryConstant
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

namespace GlobalTheory.ThmECorA

open Formalism.BasicNotions.Loc

theorem closing (hBK : GlobalTheory.Published.BlochKatoLocal) (hTD : Formalism.GaloisCohomology.LocalTateDualityK)
    (hEC : Formalism.GaloisCohomology.LocalEulerCharK) :
    ∃ C₀ : ℝ, ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      WachCoordinates.Conclusion1 D 800 ∧ ∀ C₂ : ℝ, C₀ ≤ C₂ → WachCoordinates.Conclusion2 D C₂ := by
  refine ⟨Formalism.MainNotions.N.Ln03.localCorollaryConstant, fun D HW F Cm => ?_⟩
  have hDdR := fun (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL) =>
    GlobalTheory.Per.DdREqDcris.record_caseA D l K LL h
  have h9 := GlobalTheory.Decompl.fontaine_and_decompletion D HW F
  have hFont := GlobalTheory.T.fontaine_fullFaithful_exact_psi D HW F
  have hUG : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL), 5 ≤ l →
      ∃ e, Formalism.MainNotions.WachCoordinates.Br.UnitGen ((HW l).W K 1 LL h.2.2) e :=
    fun l _ K LL h _ => GlobalTheory.WachUnit.unitGen_exists D HW F l K 1 LL h.2.2
  have hA := GlobalTheory.T.localLifting_theoremE_hypotheses_admitted hBK hTD hEC D HW F Cm
  refine ⟨(Formalism.MainNotions.N.Ln03.local_corollary_of_de_rham D HW F Cm 10 800 _ rfl le_rfl hDdR h9 hFont hUG hA).1, fun C₂ hC₂ => ?_⟩
  exact (Formalism.MainNotions.N.Ln03.local_corollary_of_de_rham D HW F Cm 10 800 C₂ rfl hC₂ hDdR h9 hFont hUG hA).2

end GlobalTheory.ThmECorA
