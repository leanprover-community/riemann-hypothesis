module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestrictedBoundsWeakenFromNineToEight
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FinrankEqSpanGen
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestBCdimOfYbc
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def OpenConditionsOrthogonal (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestOrth C0 CE1 CE2 X CM ∧ RestWin C0 CE1 CE2 X CM ∧ RestLvlDim C0 CE1 CE2 X

def OrthogonalityWindowLevelDimOnAdmissible (D : Formalism.BasicNotions.D7) : Prop :=
  TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → OpenConditionsOrthogonal C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem open_conditions_base_change (D : Formalism.BasicNotions.D7) (hY : RestYbc) (h : OrthogonalityWindowLevelDimOnAdmissible D) : RestOpen9E D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c⟩ := hP Ckap Cs CM hCM X hA hH
    exact ⟨restBClvl_of C0 CE1 CE2 X hY, a, b, c⟩) h

theorem integrality_from_metric_of_orthogonality_window (D : Formalism.BasicNotions.D7) (hY : RestYbc) (h : OrthogonalityWindowLevelDimOnAdmissible D) : IntegralityFromMetricForLargeConstants D :=
  theorem_A_closed_of_nine_open_bounds D (open_conditions_base_change D hY h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
