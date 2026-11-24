module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CovariantHatSqOfLin
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmMove
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmStar
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovDet
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovHat
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovLin
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnEabGl
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnEabPres
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRdSkew
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnYLeibniz
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.HermitianAlgebraGeneration
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.ContractionsCovariantIff

@[expose] public section

theorem qnHermHaar : Formalism.FourierDecayAlt.Q.HermHaar :=
  PI.QnHermHaar.qnHermHaar_of_alg PI.QnHermHaar.hermitian_algebra_generation qnRdSkew quantum_minor_star
    (PI.contractionsCovariant_iff.2
      ⟨covariant_det_of_lin covariant_linear, covariant_hat_of_lin covariant_linear, covariant_hat_sq_of_lin covariant_linear⟩)
    quantum_minor_move.1 quantum_minor_move.2 qnYLeibniz qnEabGl qnEabPres
