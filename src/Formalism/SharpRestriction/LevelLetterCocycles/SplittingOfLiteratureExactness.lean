module

public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
public import Formalism.SharpRestriction.LevelLetterCocycles.SplittingOfExactnessAndData
public import Formalism.SharpRestriction.LevelLetterCocycles.CancelUnitMulUniformizerPow
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem ddExactL_of_litFont (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F) : Split.DDExactL D HW := by
  intro l _ K LL hG hCA _ T₂ Y ι π _ _ hses
  obtain ⟨hinj, -, hker⟩ := (h l K LL hCA).2.1 T₂ Y _ ι π hses
  refine ⟨fun x => (hker _).2 ⟨x, rfl⟩, fun x hx => hinj (by rw [hx, map_zero]), fun u hu => (hker u).1 hu⟩

theorem splitting_of_literature_exactness (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : AdmSplitA D HW F Cm) (h6 : Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F) (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F)
    (hTr : Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F) (hWX : Formalism.MainNotions.LiftingTheory.WachKillsQuotients D HW F) (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F)
    (hS : Split.SplitShapeL D HW) : SplittingArcLifting D HW F Cm :=
  splitting_general_of_exactness D HW F Cm hA h6 hH hTr hWX (ddExactL_of_litFont D HW F hFont) hS

end Formalism.MainNotions.UnusedSlot80
