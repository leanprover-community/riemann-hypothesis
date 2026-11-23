module

public import Formalism.SharpRestriction.PageFix
public import Formalism.SharpRestriction.Divisibility.SmallFirstModulusBelowScale
public import Formalism.SharpRestriction.GlobalSchurBounds.WeightVectorSmallSharesEight
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
public import Formalism.SharpRestriction.LevelLetterCocycles.AlignN
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PageDutiesOfClassSeven
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightAdmissibleSmallSharesAtPoint
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
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth

@[expose] public section

namespace GlobalTheory.EX.DQ

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk GlobalTheory.EX GlobalTheory.Fc

theorem duty_seven_library : ∀ (eps : ℝ) (Fm : FamP eps), DQ.Duty7 Fm → Formalism.MainNotions.PageFix Fm ∧ Formalism.MainNotions.PageWin Fm ∧
    Formalism.MainNotions.DIV.Align.SmallFirstModulusBelowScale Fm ∧ Formalism.MainNotions.TameDistinctF Fm ∧ Formalism.MainNotions.ChosenWall Fm ∧ DQ.TupUsedF Fm ∧ DQ.TwAllF Fm := by
  intro eps Fm h
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  refine ⟨a, b, fun x hx i => (c x hx i).2.2.2.2.1, ?_, ⟨Fm.x1 + 1, fun x hx i => ?_⟩, f, g⟩
  · unfold DC.TameDistinctF at d
    unfold Formalism.MainNotions.TameDistinctF
    simpa only [tameDistinct_iff] using d
  · exact weightAdmissible_smallShares_at_point _ _ (e x (by linarith) i)

end GlobalTheory.EX.DQ
