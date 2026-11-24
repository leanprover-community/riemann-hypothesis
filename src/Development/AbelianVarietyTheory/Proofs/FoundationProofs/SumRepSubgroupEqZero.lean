module

public import Formalism.JacquetSubsetSums.JacquetSubsetSum
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.NoFixedCharSum

theorem sum_rep_subgroup_eq_zero {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ G V) (N : Subgroup G) [Fintype N]
    (h : ∀ v : V, (∀ n ∈ N, τ n v = v) → v = 0) : ∑ n : N, τ (n : G) = 0 := by
  ext v
  simp only [LinearMap.sum_apply, LinearMap.zero_apply]
  apply h
  intro m hm

  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨m, hm⟩ : N)) _ _ ?_
  intro n
  simp [map_mul]

theorem noFixedSum : Formalism.PacketSums.NoFixedSum := by
  intro G V _ _ _ _ τ N _ h x y
  have h0 := sum_rep_subgroup_eq_zero τ N h
  have : ∑ n : N, τ (x * (n : G) * y) = τ x * (∑ n : N, τ (n : G)) * τ y := by
    simp [Finset.mul_sum, Finset.sum_mul, map_mul]

  rw [← map_sum, this, h0]
  simp

end GlobalTheory.NoFixedCharSum
