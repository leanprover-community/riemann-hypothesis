module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open Finset

theorem exists_int_avoid {f : ℕ} (Z : Finset (Fin f → ℝ)) (hZ : ∀ z ∈ Z, z ≠ 0) :
    ∃ t : Fin f → ℤ, ∀ z ∈ Z, ∑ j, z j * (t j : ℝ) ≠ 0 := by
  classical
  let P : (Fin f → ℝ) → Polynomial ℝ := fun z => ∑ j, Polynomial.C (z j) * Polynomial.X ^ (j : ℕ)
  have hP : ∀ z ∈ Z, P z ≠ 0 := by
    intro z hz h0
    apply hZ z hz
    funext j
    have h1 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p (j : ℕ)) h0
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_zero] at h1
    rw [Finset.sum_eq_single j (fun i _ hij => by
      rw [if_neg (fun h => hij (Fin.ext h.symm)), mul_zero]) (by simp)] at h1
    simpa using h1
  obtain ⟨T, hT⟩ : ∃ T : ℕ, (T : ℝ) ∉ Z.biUnion (fun z => (P z).roots.toFinset) := by
    by_contra h
    push_neg at h
    have hinf : Set.Infinite (Set.range (fun n : ℕ => (n : ℝ))) :=
      Set.infinite_range_of_injective Nat.cast_injective
    exact hinf ((Z.biUnion (fun z => (P z).roots.toFinset)).finite_toSet.subset
      (by rintro _ ⟨n, rfl⟩; exact h n))
  refine ⟨fun j => (T : ℤ) ^ (j : ℕ), fun z hz h0 => ?_⟩
  apply hT
  rw [Finset.mem_biUnion]
  refine ⟨z, hz, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hP z hz), Polynomial.IsRoot]
  simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  push_cast at h0
  exact h0

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
