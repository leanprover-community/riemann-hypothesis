module

public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ContragredientIrreducibleGeneratedByHighestWeigh
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ContragredientLatticeFGOfIrreducible
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.DividedPowerReverseDividedPowerEqSelf
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.HighestWeightSpaceEqSpanHighestWeightVector
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.NablaDualLatticeOfIrreducibleLowestGenerated
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.MainNotions.G.ColumnFamilies

theorem lattice_generated_lowest_weight (D : Formalism.BasicNotions.D7) : DeltaGeneratedByLowestWeightVector := deltaGenerated_of_extremalVector_of_dualInjective lowest_weight_extremal_vector (dualFunctional_lowestWeight_injective D)

theorem lattice_nabla_eq (D : Formalism.BasicNotions.D7) : NablaContragredientEqDualLatticeDelta := nablaDualLattice_of_irreducible_lowest_generated (contragredientIrreducible_generated D) (dualFunctional_lowestWeight_injective D) (lattice_generated_lowest_weight D)

theorem admissible_lattice_biduality (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.WeylDualityLattice D :=
  weylDualityLattice_of_nabla_fg_bidual D (lattice_nabla_eq D) (contragredientLatticeFG_of_irreducible (contragredientIrreducible_generated D)) integral_lattice_bidual

end Formalism.MainNotions.G.ColumnFamilies
