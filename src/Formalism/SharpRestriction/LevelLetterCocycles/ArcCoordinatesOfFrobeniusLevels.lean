module

public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfLevelZeroParts
public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesAdmittedOfLevels
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsPrimOfGood
public import Formalism.SharpRestriction.LevelLetterCocycles.SplitShapeLRec
public import Formalism.SharpRestriction.LevelLetterCocycles.SplittingOfLiteratureExactness
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

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem arc_coordinates_of_frobenius (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (h2 : LevelZeroModPRefinedLocal D HW) : ArcCoordinatesTheorem D HW F Cm := fun hA =>
  arc_coordinates_of_levels D HW F Cm (lev0MpL_of D HW F Cm hA h4 h9) h2 hA

theorem arc_coordinates_of_frobenius_levels (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hA : AdmArcA D HW F Cm) (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (h2 : LevelZeroModPRefinedLocal D HW) : ArcLiftingCoordinates D HW F Cm :=
  arc_coordinates_of_frobenius D HW F Cm h4 h9 h2 hA

theorem split_case_A_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hA : AdmSplitA D HW F Cm) (hArc : AdmArcA D HW F Cm)
    (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm) (h6 : Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F) (hTr : Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F) (hWX : Formalism.MainNotions.LiftingTheory.WachKillsQuotients D HW F)
    (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F) (h17 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D)
    (h2 : LevelZeroModPRefinedLocal D HW) : SplittingArcLifting D HW F Cm :=
  splitting_of_literature_exactness D HW F Cm hA h6 hH hTr hWX hFont
    (splitShapeL_rec D HW F Cm hArc (lev0MpL_of D HW F Cm hArc h4 h9) h2 h23 h17)

end Formalism.MainNotions.UnusedSlot80
