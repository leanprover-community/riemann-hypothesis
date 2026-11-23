module

public import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.BranchingInterlacingPairs
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.DroppingPropositionHolds
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.GenericFramesLetters
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneEightHolds
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.PointsPropertyOfD7
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.RamificationTwoAndConjugationAtQAndD
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SecondPropositionEveryLocalisation
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.NoThreeConsecutiveThickPlaces

@[expose] public section

namespace Formalism.MainNotions.UnusedSlot33

open Formalism.BasicNotions

theorem field_lemmas_two_to_six (D : D7) (sc : Scale) :
    Conclusion2 D ∧ PointsLemma D ∧ Conclusion4 D 100 ∧ TorusPairsWithVariant D ∧ Conclusion6 D sc :=
  ⟨second_proposition_every_localisation D, points_property_of_d7 D, generic_frames_letters D, no_three_consecutive_thick_places D, branching_interlacing_pairs D sc⟩

theorem field_lemmas_except_seven : ∃ C₅ : ℝ, ∀ (D : D7) (sc : Scale),
    Conclusion1 D ∧ Conclusion2 D ∧ PointsLemma D ∧ Conclusion4 D 100 ∧ Conclusion5 D C₅ ∧ TorusPairsWithVariant D ∧ Conclusion6 D sc ∧ Conclusion8 D := by
  obtain ⟨C, hC⟩ := dropping_proposition_holds
  refine ⟨C, fun D sc => ?_⟩
  obtain ⟨h2, h3, h4, h5c, h6⟩ := field_lemmas_two_to_six D sc
  exact ⟨ramification_two_and_conjugation_at_q_and_d D, h2, h3, h4, hC D, h5c, h6, lemma_one_eight_holds D⟩

end Formalism.MainNotions.UnusedSlot33
