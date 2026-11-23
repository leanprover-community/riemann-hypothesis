module

public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdditiveCharacterPsi
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BudgetTopConvergence
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChangeOfVariablesXy
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSizesOfHypotheses
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CorollaryU1Plain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CorollaryU1Truncated
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopCellsOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeakToStrongSmoothnessReal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

theorem coordinate_sizes_in_norm : Formalism.FourierDecayAlt.U.SliceCoordinateSizes :=
  coordinate_sizes_of_parts slice_membership block3_apply_embedding aux_statement_17 hat_z_on_slice level_determinant_z

theorem norm_decay_in_coordinates : Formalism.FourierDecayAlt.U.CoordinateDecay :=
  norm_decay_of_coordinate_sizes coordinate_sizes_in_norm

theorem phi_pointwise_bound : Formalism.FourierDecayAlt.U.PointwiseIntegralBound :=
  phi_bound_of_parts slice_membership derivative_cost_bound norm_decay_in_coordinates weight_integrability

theorem theorem_u : Formalism.FourierDecayAlt.U.TheoremU :=
  theorem_u_of_parts phi_pointwise_bound phi_support_determinant weak_to_strong_smoothness

theorem phi_support_level_function : Formalism.FourierDecayAlt.U.PhiSuppG :=
  phi_support_level_of_parts level_function_slice level_determinant_z hat_z_on_slice

theorem corollary_u2_germ_hypothesis : Formalism.FourierDecayAlt.U.GermExpansionHypothesis :=
  corollary_u2_of_parts theorem_u corollary_u1_truncated_alt star_projection budget_second_corollary
    thresholds_second_corollary phi_support_level_function

theorem germ_expansion_applies : Formalism.FourierDecayAlt.U.UseGerm :=
  germ_expansion_of_parts germ_rate det_weyl_matrix corollary_u2_germ_hypothesis derivative_bound_of_decay
    power_matching scale_matching

theorem germ_expansion_top_level : Formalism.FourierDecayAlt.U.UseGermTop :=
  germ_top_level_of_parts germ_rate det_weyl_matrix top_cells derivative_bound_of_decay

end Formalism.FourierDecayAlt.P
