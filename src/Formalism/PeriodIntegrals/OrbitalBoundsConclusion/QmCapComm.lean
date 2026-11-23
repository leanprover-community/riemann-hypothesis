module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnEabGl
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnEabPres
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuantumDeterminantCommute.CapelliOperatorCongruence
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuantumDeterminantCommute.QuantumDeterminantCommutes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuantumDeterminantCommute.Transfer
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

@[expose] public section

theorem qmCapComm_of : Formalism.FourierDecayAlt.Q.EabPres → Formalism.FourierDecayAlt.Q.EabGlLev → Formalism.FourierDecayAlt.Q.CapCommute :=
  fun hP hG => QmCapCommW.capelli_operator_transfer QmCapCommW.capelli_operator_congruence QmCapCommW.quantum_determinant_commutes hP hG

theorem qmCapComm_of_gl : Formalism.FourierDecayAlt.Q.EabGlLev → Formalism.FourierDecayAlt.Q.CapCommute :=
  qmCapComm_of qnEabPres

theorem capelli_det_commute : Formalism.FourierDecayAlt.Q.CapCommute :=
  qmCapComm_of_gl qnEabGl
