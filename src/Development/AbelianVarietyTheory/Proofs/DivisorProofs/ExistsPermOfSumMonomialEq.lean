module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMvPolynomialPickPoint
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Mathlib.Geometry.Manifold.StructureGroupoid
import Mathlib.NumberTheory.ModularForms.SlashActions

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem sum_eval_eq_of_sum_monomial_eq {ι S : Type} [Fintype ι] [Fintype S] (x y : ι → S → ℂ)
    (h : ∀ μ : S → ℕ, ∑ i, ∏ s, x i s ^ μ s = ∑ i, ∏ s, y i s ^ μ s) (Q : MvPolynomial S ℂ) :
    ∑ i, MvPolynomial.eval (x i) Q = ∑ i, MvPolynomial.eval (y i) Q := by
  simp only [MvPolynomial.eval_eq']
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, h d]

theorem exists_perm_of_sum_monomial_eq :
    ∀ (ι S : Type) [Fintype ι] [Fintype S] (x y : ι → S → ℂ),
      (∀ μ : S → ℕ, ∑ i, ∏ s, x i s ^ μ s = ∑ i, ∏ s, y i s ^ μ s) →
      ∃ ρ : Equiv.Perm ι, ∀ i, x i = y (ρ i) := by
  classical
  intro ι S _ _ x y h
  have hcard : ∀ p : S → ℂ, Fintype.card {i // x i = p} = Fintype.card {i // y i = p} := by
    intro p
    obtain ⟨Q, hQ1, hQ0⟩ := exists_mvPolynomial_pick_point S
      (Finset.univ.image x ∪ Finset.univ.image y) p
    have key : ∀ z : ι → S → ℂ, (∀ i, z i ∈ Finset.univ.image x ∪ Finset.univ.image y) →
        ∑ i, MvPolynomial.eval (z i) Q = (Fintype.card {i // z i = p} : ℂ) := by
      intro z hz
      have : ∀ i, MvPolynomial.eval (z i) Q = if z i = p then 1 else 0 := by
        intro i
        split_ifs with hi
        · rw [hi, hQ1]
        · exact hQ0 _ (hz i) hi
      simp only [this]
      rw [Finset.sum_boole, Fintype.card_subtype]
    have h1 := key x (fun i => by simp)
    have h2 := key y (fun i => by simp)
    have h3 := sum_eval_eq_of_sum_monomial_eq x y h Q
    rw [h1, h2] at h3
    exact_mod_cast h3
  refine ⟨Equiv.ofFiberEquiv (f := x) (g := y) (fun p => Fintype.equivOfCardEq (hcard p)),
    fun i => ?_⟩
  exact (Equiv.ofFiberEquiv_map _ i).symm

end GlobalTheory.QFam
