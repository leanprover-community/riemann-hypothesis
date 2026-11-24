module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.CasimirElement.casC :
    {n : ℕ} → (Fin n → ℂ) → ℂ :=
    fun {n : ℕ} (τ : Fin n → ℂ) ↦
      ∑ a : Fin n, τ a ^ (2 : ℕ) + ∑ a : Fin n, ∑ b : Fin n, if a < b then τ a - τ b else (0 : ℂ)

namespace YgaHelp

private lemma inner_left {n : ℕ} (σ : Fin n → ℂ) (a : Fin n) :
    (∑ b : Fin n, if a < b then σ a else (0 : ℂ)) = σ a * (((n : ℂ) - 1) - ((a : ℕ) : ℂ)) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    Finset.filter_lt_eq_Ioi, Fin.card_Ioi, nsmul_eq_mul]
  have h : (a : ℕ) ≤ n - 1 := by omega
  have h1 : 1 ≤ n := by omega
  rw [Nat.cast_sub h, Nat.cast_sub h1]
  push_cast; ring

private lemma inner_right {n : ℕ} (σ : Fin n → ℂ) (b : Fin n) :
    (∑ a : Fin n, if a < b then σ b else (0 : ℂ)) = σ b * ((b : ℕ) : ℂ) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    Finset.filter_gt_eq_Iio, Fin.card_Iio, nsmul_eq_mul]
  ring

end YgaHelp

theorem UpperTheory.Reformulated.B.CasimirElement.main :
    ∀ {n : ℕ} (σ : Fin n → ℂ),
      UpperTheory.Reformulated.B.CasimirElement.casC σ =
        ∑ a : Fin n, σ a ^ (2 : ℕ) + ∑ a : Fin n, σ a * ((↑n : ℂ) - (1 : ℂ) - (2 : ℂ) * (↑(↑a : ℕ) : ℂ)) := by
  intro n σ
  unfold UpperTheory.Reformulated.B.CasimirElement.casC
  congr 1
  have hsplit : ∀ a b : Fin n, (if a < b then σ a - σ b else (0 : ℂ)) =
      (if a < b then σ a else 0) - (if a < b then σ b else 0) := by
    intro a b; split_ifs <;> simp
  simp_rw [hsplit, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => if a < b then σ b else (0 : ℂ))]
  simp_rw [YgaHelp.inner_left, YgaHelp.inner_right]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro a _
  ring
