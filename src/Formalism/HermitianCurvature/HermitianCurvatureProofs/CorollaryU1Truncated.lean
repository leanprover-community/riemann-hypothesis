module

public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSizesOfHypotheses
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UsCost
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

theorem Formalism.FourierDecayAlt.P.derivative_cost_bound : Formalism.FourierDecayAlt.U.DerivativeCost := by
  have hS : Formalism.FourierDecayAlt.U.SliceMem := Formalism.FourierDecayAlt.P.slice_membership
  have h21 : Formalism.FourierDecayAlt.U.SliceCoordinateSizes :=
    Formalism.FourierDecayAlt.P.Ux6.coordinate_sizes_of_hypotheses hS Formalism.FourierDecayAlt.P.block3_apply_embedding Formalism.FourierDecayAlt.P.aux_statement_17
      Formalism.FourierDecayAlt.P.hat_z_on_slice
  exact operator_word_cost hS Formalism.FourierDecayAlt.P.radical_parametrisation Formalism.FourierDecayAlt.P.slice_right_coordinates
    Formalism.FourierDecayAlt.P.slice_left_coordinates Formalism.FourierDecayAlt.P.slice_z_coordinates Formalism.FourierDecayAlt.P.directions_in_parabolic h21
