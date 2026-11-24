module

public import ReciprocityTheory.DualLattices.SubgroupFreenessStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.DualLattices.HasColengthEqPowMulPow
import ReciprocityTheory.DualLattices.MemSupOfRestrictToSubgroupMemSq

@[expose] public section

namespace ReciprocityTheory.PGsh.L2

theorem h3 (C R : Type) [Field C] [CommRing R] [Algebra R C] :
    SubgroupFreenessStatement (C := C) (R := R) := by
  intro hC hC0 v hv N _ _ _ K _ _ _ AA
  haveI := hC
  haveI := hC0
  exact ⟨exists_coset_basis hv AA K, mem_of_restrictToSubgroup_eq_zero hv AA K, hasColength_eq_pow_mul_pow hv AA K, mem_sup_of_restrictToSubgroup_mem_sq hv AA K⟩

end ReciprocityTheory.PGsh.L2
