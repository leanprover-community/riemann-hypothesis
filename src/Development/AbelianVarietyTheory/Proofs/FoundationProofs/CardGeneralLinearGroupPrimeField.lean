module

public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
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

theorem prod_pow_sub_pow_eq (g N : ℕ) :
    ∏ i ∈ Finset.range N, (g ^ N - g ^ i)
      = g ^ (N * (N - 1) / 2) * ∏ i ∈ Finset.range N, (g ^ (i + 1) - 1) := by
  have h1 : ∀ i ∈ Finset.range N, g ^ N - g ^ i = g ^ i * (g ^ (N - 1 - i + 1) - 1) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [Nat.mul_sub, mul_one, ← pow_add]
    congr 2
    omega
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_range_id, Finset.prod_range_reflect (fun i => g ^ (i + 1) - 1) N]

theorem card_GG_eq (g : ℕ) [Fact g.Prime] (N : ℕ) :
    Fintype.card (GG g N)
      = g ^ (N * (N - 1) / 2) * ∏ i ∈ Finset.range N, (g ^ (i + 1) - 1) := by
  rw [← prod_pow_sub_pow_eq, ← Nat.card_eq_fintype_card]
  have h := Matrix.card_GL_field (𝔽 := ZMod g) N
  rw [ZMod.card] at h
  rw [← Fin.prod_univ_eq_prod_range (fun i => g ^ N - g ^ i) N]
  exact h

end GlobalTheory.BadShare
