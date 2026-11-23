module

public import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller
public import Formalism.SharpRestriction.LevelLetterCocycles.KillerLevCoreOf
public import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorGeneralOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.PsCoprimeOf
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.KL

def KillLevFacts (D : D7) (HW : HWOf D.loc) : Prop :=
  AtCaseA fun l _ K LL hG => LevGrad ((HW l).W K 1 LL hG)

theorem annihilator_levels_of_grading (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hK : KillLevFacts D HW) : KillerLevelsTheorem D HW F Cm := by
  rintro ⟨-, h9⟩
  intro l _ K LL hG hC h5
  have hfd : FiniteDimensional (Padic l) ↥(K0 K) := by
    first
    | exact inferInstance
    | exact ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank (Padic l) ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hR := ring_condition_uniformizer_polynomial D HW F h9 l K LL hC
  have hT := tool_algebra_of_ring_condition D HW F h9 l K LL hC h5
  exact KL.killerLevCore_of _ (KF.psUnitE_of _ hR hT) (KF.psCoprime_of _ hR) (hK l K LL hG hC h5)
    (KF.psStable_of _ hR) hR.1

end Formalism.MainNotions.UnusedSlot80
