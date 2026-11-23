module

public import Formalism.GaloisIrreducibility.Statement
public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.AltNotSolvable
public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.IrredOf
public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.JordanPrime
public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.LemmaAOf
public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.NoSolvableOf
public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.OrbitSubSum
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PermSubSumInv
public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PowerPCycle
public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PrimitiveOfPCycle
public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.RestrictRoots
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

namespace Formalism.GaloisIrreducibility

theorem lemmaA : LemmaA := lemmaAOf_statement orbit_subset_sum restrict_roots_to_subfield

theorem irred : Irred := irreducible_of_galois_conditions lemmaA
theorem permSubSumInv : PermSubSumInv := permutation_subset_sum_invariant

theorem primitiveOfPCycle : PrimitiveOfPCycle := primitive_of_p_cycle
theorem jordanPrime : JordanPrime := jordan_prime_cycle_theorem

theorem noSolvableTransitive : NoSolvableTransitive :=
  no_solvable_subgroup_of power_of_p_cycle primitive_of_p_cycle jordan_prime_cycle_theorem alternating_group_not_solvable

end Formalism.GaloisIrreducibility
