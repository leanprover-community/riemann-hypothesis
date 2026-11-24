module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
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
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Polynomial Finset

theorem SchProdOneSubRootsOfUnity.proof : SchProdOneSubRootsOfUnity.Statement := by
  intro k hk
  have hk0 : 0 < k := hk
  have : NeZero k := ⟨Nat.pos_iff_ne_zero.mp hk0⟩
  have hζ : IsPrimitiveRoot (rootOfUnity k) k := by
    unfold rootOfUnity
    exact Complex.isPrimitiveRoot_exp k (Nat.pos_iff_ne_zero.mp hk0)
  set p : ℂ[X] := ∏ i ∈ range k, (1 - C (rootOfUnity k ^ i) * X) with hp
  set q : ℂ[X] := 1 - X ^ k with hq
  have hpdeg : p.natDegree ≤ k := by
    have h1 : ∀ i ∈ range k, (1 - C (rootOfUnity k ^ i) * X).natDegree ≤ 1 := fun i _ => by
      compute_degree
    refine (natDegree_prod_le _ _).trans ((sum_le_sum h1).trans ?_)
    simp
  have hqdeg : q.natDegree ≤ k := by
    rw [hq]; compute_degree
  have hdeg : (p - q).degree < #(insert (0 : ℂ) (nthRootsFinset k (1 : ℂ))) := by
    rw [card_insert_of_notMem (by simp [mem_nthRootsFinset hk0, zero_pow hk0.ne']),
      hζ.card_nthRootsFinset]
    refine (degree_le_of_natDegree_le ((natDegree_sub_le _ _).trans (max_le hpdeg hqdeg))).trans_lt ?_
    exact_mod_cast Nat.lt_succ_self k
  refine eq_of_degree_sub_lt_of_eval_finset_eq _ hdeg fun x hx => ?_
  rcases mem_insert.mp hx with rfl | hx
  · simp [hp, hq, eval_prod, zero_pow hk0.ne']
  · have hxk : x ^ k = 1 := (mem_nthRootsFinset hk0 _).mp hx
    have hinv : x⁻¹ ^ k = 1 := by rw [inv_pow, hxk, inv_one]
    obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one hinv
    have hx0 : x ≠ 0 := by
      rintro rfl; simp [zero_pow hk0.ne'] at hxk
    have hzero : p.eval x = 0 := by
      rw [hp, eval_prod]
      refine prod_eq_zero (mem_range.mpr hi) ?_
      simp [hi', inv_mul_cancel₀ hx0]
    rw [hzero, hq]
    simp [hxk]

end GroundTheory.Heights₂.Heights.RestTerms
