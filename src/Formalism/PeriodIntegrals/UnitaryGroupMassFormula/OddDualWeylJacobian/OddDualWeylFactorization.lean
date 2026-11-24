module

public import Formalism.PeriodIntegrals.OddDualWeyl
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.AevalMulHomog
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.DegreeBalance
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.EvalDuality
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.ExistsEqMulOfColumnSpanLe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.HighestWeightDualOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.HighestWeightMultiplicity
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.HighestWeightVectorUnique
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.JacobiMinorIdentity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.MnrUpdateEqZero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.RevColOneTranspose
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.TransvectionMulApply
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace PI.OddDualWeyl

theorem odd_dual_weyl_factorization {K : Type} [Field K] (O : Type) [CommRing O] [Algebra O K] (m : ℕ)
    (lam : Fin (m + 1) → ℤ) : OddFact (K := K) O m lam :=
  oddDualWeyl_of rowOpIntertwining highest_weight_multiplicity highest_weight_divisibility hermitianDiagonalization lowestWeightMem (highestWeightDual_of jacobiMinorReverse) weight_homomorphism degreeBalance
    evalDuality highest_weight_vector_unique columnSpanDual reverseSignUnit twistedWeylStep O m lam

end PI.OddDualWeyl
