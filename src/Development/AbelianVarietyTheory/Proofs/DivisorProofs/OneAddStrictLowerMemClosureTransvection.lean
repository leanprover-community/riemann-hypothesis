module

public import Mathlib.LinearAlgebra.Matrix.Transvection
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCassemLemmas

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory

theorem one_add_strictLower_mem_closure_transvection (R : Type) [CommRing R] (N : ℕ)
    (c : Matrix (Fin N) (Fin N) R) (hc : ∀ a b, a ≤ b → c a b = 0) :
    1 + c ∈ Submonoid.closure
      {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := by
  classical
  have key : ∀ S : Finset (Fin N × Fin N), ∀ c : Matrix (Fin N) (Fin N) R,
      (∀ a b, a ≤ b → c a b = 0) → (∀ a b, (a, b) ∉ S → c a b = 0) →
      1 + c ∈ Submonoid.closure
        {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := by
    intro S
    induction S using Finset.induction_on_max_value (fun p : Fin N × Fin N => p.2) with
    | empty =>
      intro c _ h
      have : c = 0 := by
        ext a b
        simpa using h a b (by simp)
      rw [this, add_zero]
      exact Submonoid.one_mem _
    | insert p S hp hmax ih =>
      intro c hc hS
      obtain ⟨a, b⟩ := p
      by_cases hab : a ≤ b
      · refine ih c hc fun i j hij => ?_
        by_cases h : (i, j) = (a, b)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          exact hc _ _ hab
        · exact hS i j (by simp only [Finset.mem_insert, not_or]; exact ⟨h, hij⟩)
      · have hba : b < a := lt_of_not_ge hab
        set c' : Matrix (Fin N) (Fin N) R := c - Matrix.single a b (c a b) with hc'
        have h2 : ∀ i j, (i, j) ∉ S → c' i j = 0 := by
          intro i j hij
          by_cases h : (i, j) = (a, b)
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
            simp [hc']
          · have h0 : c i j = 0 :=
              hS i j (by simp only [Finset.mem_insert, not_or]; exact ⟨h, hij⟩)
            have h' : ¬ (a = i ∧ b = j) := by
              rintro ⟨rfl, rfl⟩; exact h rfl
            simp [hc', h0, Matrix.single_apply, h']
        have h1 : ∀ i j, i ≤ j → c' i j = 0 := by
          intro i j hij
          have h' : ¬ (a = i ∧ b = j) := by
            rintro ⟨rfl, rfl⟩; exact hab hij
          simp [hc', hc i j hij, Matrix.single_apply, h']
        have h3 : c' * Matrix.single a b (c a b) = 0 := by
          ext i j
          have hz : c' i a = 0 := by
            apply h2
            intro hmem
            exact absurd (hmax _ hmem) (not_le.mpr hba)
          rw [Matrix.mul_apply]
          refine Finset.sum_eq_zero fun e _ => ?_
          by_cases he : a = e
          · subst he; simp [hz]
          · simp [Matrix.single_apply, he]
        have h4 : 1 + c = (1 + c') * Matrix.transvection a b (c a b) := by
          rw [Matrix.transvection, add_mul, one_mul, mul_add, mul_one, h3, add_zero, hc']
          abel
        rw [h4]
        exact Submonoid.mul_mem _ (ih c' h1 h2)
          (Submonoid.subset_closure ⟨a, b, _, hba.ne', rfl⟩)
  exact key Finset.univ c hc (by simp)

end GlobalTheory
