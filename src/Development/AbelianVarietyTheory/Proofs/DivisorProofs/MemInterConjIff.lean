module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.ConjugateIntersectionMembership

theorem mem_inter_conj_iff {H : Type} [Group H] {T L : Subgroup H} {x g : H} :
    g ∈ GlobalTheory.LKLoc.locPart T L x ↔ g ∈ T ∧ x⁻¹ * g * x ∈ L := by
  rw [GlobalTheory.LKLoc.locPart, Subgroup.mem_inf, Subgroup.mem_map]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨x⁻¹ * g * x, h, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · simp [MulAut.conj_apply, mul_assoc]

end GlobalTheory.ConjugateIntersectionMembership
