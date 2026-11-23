module

public import Formalism.HermitianCurvature.StatementC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualCovolumeChangeOfVariables
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstNormRealNonneg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelSizesJointMean
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroEstimateProduct
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalConditionsAndQuotientSplitting
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C

noncomputable section

theorem real_inputs_by_parts : C.RealInputsConcreteOfParts := by
  intro hEmb hEF hTD hLG hGram hWP hWave hPI hLift hBlock hE hCut E _ _ _ Wp Wq _ _ _ _ S jv H _ _ Vt C₄ hg1 hg2 hP hG hI hP1 hP23 hT hLE hPG Kr hK0 Th e
  exact ⟨hGram E Wp Wq S hP hG Kr hK0 Th e, hWP E Wp Wq S hG Kr hK0 Th e, hWave E Wp Wq S hG hI hP1 Kr hK0 Th e,
    hPI hEmb hEF hTD hLG E Wp Wq S hg1 hg2 hP hG hI Kr hK0 Th e, hLift E Wp Wq S hP23 Kr hK0 Th e,
    hBlock E Wp Wq S C₄ hT Kr hK0 Th e, hE E Wp Wq S jv hG hLE Kr hK0 Th e,
    hCut E Wp Wq S H Vt hPG Kr hK0 Th e⟩

theorem real_inputs_concrete_holds : C.RealInputsConcrete :=
  real_inputs_by_parts embedding_facts euclidean_frame trace_dual_alt
    lattice_facts_general gram_positive_semidefinite words_pos_of_parts wave_estimate_of_integral
    poisson_input_of_parts lift_estimate_of_base block_estimate_of_base level_zero_estimate_product
    cutoff_of_parts

end

end Formalism.FourierDecayAlt.P
