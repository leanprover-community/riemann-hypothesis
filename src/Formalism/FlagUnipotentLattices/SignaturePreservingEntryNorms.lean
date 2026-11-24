module

public import Formalism.FlagUnipotentLattices.DetIndexProductHyperbolicInequality
public import Formalism.FlagUnipotentLattices.DetIndexProductPlacesInequalitySq
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ComplexMultiplicationRoot
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LocalIntegralStructure
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

namespace Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure

theorem torsionIndex : Formalism.HermitianLatticeCounting.LocalIntegralStructure.TorsionIndex := Formalism.HermitianLatticeCounting.P.card_range_nsmul_mul_card_le
theorem perpCompl : Formalism.HermitianLatticeCounting.LocalIntegralStructure.PerpCompl := Formalism.HermitianLatticeCounting.P.orthogonal_complement_formula
theorem cofactorVec : Formalism.HermitianLatticeCounting.LocalIntegralStructure.CofactorVec := Formalism.HermitianLatticeCounting.P.cofactor_vector_formula
theorem localCongr : Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocalCongr := Formalism.HermitianLatticeCounting.P.local_congruence_condition
theorem thmB : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ThmB := Formalism.HermitianLatticeCounting.P.theorem_B_statement

theorem gramDetGen : Formalism.HermitianLatticeCounting.LocalIntegralStructure.GramDetGen := Formalism.HermitianLatticeCounting.P.gram_determinant_general
theorem gramNondeg : Formalism.HermitianLatticeCounting.LocalIntegralStructure.GramNondeg := Formalism.HermitianLatticeCounting.P.gram_matrix_nondegenerate
theorem arithmetic_square_bound_fourth : Formalism.HermitianLatticeCounting.LocalIntegralStructure.DetIndexProductInequalitySq := Formalism.HermitianLatticeCounting.P.L4_arithmetic_square
theorem arithmetic_square_bound_fifth : Formalism.HermitianLatticeCounting.LocalIntegralStructure.DetIndexProductPlacesInequalitySq := Formalism.HermitianLatticeCounting.P.L5_arithmetic_square

end Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure
