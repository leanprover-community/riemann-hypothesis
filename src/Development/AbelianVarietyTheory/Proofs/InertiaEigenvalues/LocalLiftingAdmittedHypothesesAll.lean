module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllOfTateDualityEulerCharStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumpsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneSurjectiveWittTiltStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionCorestrictionH1fStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StrictAdm
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.AdmAllRecords

theorem localLifting_admittedHypotheses_all_alt : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      ElementDenominator.Adm2 D HW F := by
  intro hBK hTD hEC D HW F _
  exact ⟨GlobalTheory.T.restriction_corestriction_H1f D HW F, GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hBK hTD hEC D, GlobalTheory.Per.FontaineAdm.fontaine_bounds D,
    GlobalTheory.Per.StrictAdm.strict_adm D, GlobalTheory.T.crystalline_restrict_finite_extension_jumps D, GlobalTheory.T.frobenius_sub_one_surjective_witt_tilt⟩

end GlobalTheory.AdmAllRecords
