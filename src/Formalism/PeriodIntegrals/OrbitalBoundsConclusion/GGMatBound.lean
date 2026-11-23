module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGCardUni
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGConvScalar
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGGenRatio
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.GamOneReal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.GgMatrixBoundOfLitOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.IrreducibleOfMinimal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.JointEigenvectorExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.MatrixCoefficientEquation
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.ProdFormula
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MatrixCoefficientBound.SpectrumPositiveSemidefinite
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem gg_matrix_bound : Formalism.L2.SG.GGMirabolic.GGMatrixBoundOfLit :=
  PI.GGMatBoundW.ggMatrixBoundOfLit_of PI.GGMatBoundW.matrix_coefficient_equation PI.GGMatBoundW.totally_hermitian_form
    (PI.GGMatBoundW.eigBound_of PI.GGMatBoundW.local_place_bound PI.GGMatBoundW.joint_eigenvector_exists
      PI.GGMatBoundW.prod_formula')
    PI.GGMatBoundW.spectrum_positive_semidefinite convolution_scalar generic_ratio_bound mirabolic_card_unipotent
