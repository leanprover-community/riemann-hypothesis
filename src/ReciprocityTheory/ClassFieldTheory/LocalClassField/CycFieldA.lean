module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.CycDefs
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
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
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsD

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p}

theorem finiteDimensional_base_field : FiniteDimensional ℚ_[p] (Q0 p) := inferInstance

theorem ramification_mul_inertia_base_field : eK p (Q0 p) * fK p (Q0 p) = 1 := by
  rw [eK_mul_fK p (Q0 p) finiteDimensional_base_field]
  exact IntermediateField.finrank_bot

theorem residue_cardinality_base_field : qK p (Q0 p) = p := by
  rw [qK_eq_pow_fK p (Q0 p) finiteDimensional_base_field, Nat.eq_one_of_mul_eq_one_left ramification_mul_inertia_base_field, pow_one]

theorem norm_eq_one_of_pow {n : ℕ} (hn : n ≠ 0) {z : PadicAlgCl p} (hz : z ^ n = 1) : ‖z‖ = 1 := by
  have h : ‖z‖ ^ n = 1 := by rw [← norm_pow, hz, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn).1 h

end ReciprocityTheory.DiscreteGroups.LocalClassField
