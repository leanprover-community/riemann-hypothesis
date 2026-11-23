module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermCL
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LatticesCloseLocally
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LocalIntegralOfSubstitution
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermXB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.TcoordBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UJClassMassOfHerm
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem tensor_localization : TensLoc := tensLocX_of local_integral_of_substitution

theorem hermitian_approximation : HermApprox :=
  hermitian_approximation_of_parts local_switching_lattice tensor_localization lattices_close_locally wPlace bcU gramOK

theorem unitary_class_mass : PI.UJClassMass2.UJClassMass :=
  uJClassMass_of_herm hermitian_approximation

set_option pp.fullNames true in
#check @PI.UnitaryGroupMassFormula.UJClassMass.hermitian_approximation
set_option pp.fullNames true in
#check @PI.UnitaryGroupMassFormula.UJClassMass.unitary_class_mass
#print axioms PI.UnitaryGroupMassFormula.UJClassMass.tensor_localization
#print axioms PI.UnitaryGroupMassFormula.UJClassMass.hermitian_approximation
#print axioms PI.UnitaryGroupMassFormula.UJClassMass.unitary_class_mass

end PI.UnitaryGroupMassFormula.UJClassMass

end
