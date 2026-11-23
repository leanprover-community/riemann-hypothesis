module

public import Formalism.HermitianCurvature.StatementFr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleRecOfAdmissibleWord
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CommuteLevelZeroElement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbedLoweringConstant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FreeOf2OfFourEntries
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FreeOf2RmatrixTranspose
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaussFormMinusLetter
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.KroneckerEmbedMulApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinusLetterFrameOfData
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PlusLetterFrameOfData
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionInsertionDiagonalCompat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QEFirstMulSecondEqSwap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuasiDeterminantFromEntries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

namespace Formalism.FourierDecayAlt.P

theorem plus_letter_maps_frames : Formalism.FourierDecayAlt.Fr.PlusStep :=
  plus_letter_frame_of_data position_insertion_mul_compat position_insertion_star_compat position_insertion_diagonal_compat position_insertion_free_compat letter_module_plus
    rtt_relation_entries plus_letter_form plus_letter_tau plus_letter_l

theorem minus_letter_maps_frames : Formalism.FourierDecayAlt.Fr.MinusStep :=
  minus_letter_frame_of_data position_insertion_mul_compat position_insertion_star_compat position_insertion_diagonal_compat position_insertion_free_compat letter_module_minus
    rtt_relation_entries minus_letter_form minus_letter_tau minus_letter_l

theorem frame_of_admissible_word : Formalism.FourierDecayAlt.Fr.FrameAll :=
  (frame_of_steps start_is_frame initial_module_structure plus_letter_maps_frames minus_letter_maps_frames
    frame_free_of_new_position frame_module_of_word).1

theorem frame_eq_word_module : Formalism.FourierDecayAlt.Fr.FrameWord :=
  (frame_of_steps start_is_frame initial_module_structure plus_letter_maps_frames minus_letter_maps_frames
    frame_free_of_new_position frame_module_of_word).2

theorem frame_of_recursive_word : Formalism.FourierDecayAlt.Fr.FrameAllRec :=
  frame_rec_of_steps start_is_frame initial_module_structure plus_letter_maps_frames minus_letter_maps_frames
    frame_free_of_new_position

end Formalism.FourierDecayAlt.P
