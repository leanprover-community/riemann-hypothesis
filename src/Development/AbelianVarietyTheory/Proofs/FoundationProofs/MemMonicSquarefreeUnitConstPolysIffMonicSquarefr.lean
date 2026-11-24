module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
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

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem mem_sqSet_iff (g : ℕ) [Fact g.Prime] (N : ℕ) (f : (ZMod g)[X]) :
    f ∈ sqSet g N ↔ f.Monic ∧ f.natDegree = N ∧ Squarefree f ∧ f.coeff 0 ≠ 0 := by
  unfold sqSet
  rw [Finset.mem_filter, Finset.mem_image, ← and_assoc (a := f.Monic)]
  refine and_congr_left fun _ => ⟨?_, ?_⟩
  · rintro ⟨c, -, rfl⟩
    have hd : (∑ i : Fin N, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).degree < N := degree_sum_fin_lt c
    refine ⟨monic_X_pow_add hd, ?_⟩
    apply natDegree_eq_of_degree_eq_some
    rw [degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
  · rintro ⟨hm, rfl⟩
    refine ⟨fun i => f.coeff i, Finset.mem_univ _, ?_⟩
    rw [Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i)]
    exact hm.as_sum.symm

end GlobalTheory.BadShare
