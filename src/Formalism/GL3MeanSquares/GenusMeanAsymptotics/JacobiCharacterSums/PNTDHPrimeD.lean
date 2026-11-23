module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPrimeC
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPrimeB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff

@[expose] public section

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter

lemma dhpr_large {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1) (k : ℕ)
    {σ η : ℝ} (hσ : 1 ≤ σ) (hση : σ - 1 = η) (hη : 0 < η) (hη1 : η ≤ 1) (v0 V : ℕ) (hV : v0 ≤ V)
    {A CH : ℝ} (hA : 0 ≤ A) (hCH : 0 ≤ CH)
    (hHyp : ∀ v : ℕ, ∑ n ∈ Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊,
        (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤
          A + CH * M * (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2)))) :
    ∑ n ∈ Ioc ⌊Real.exp (v0 : ℝ)⌋₊ ⌊Real.exp (V : ℝ)⌋₊, dhprF χ₁ k σ n ≤
      2 * A * (2 * Real.exp 2 * ((k : ℝ) + 2) * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 2))
      + 2 * CH * M * (Real.exp 1 * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 1) *
          (20 * Real.exp (-((v0 : ℝ) / 4)))) := by
  have hw : ∀ v : ℕ, ((v : ℝ) + 1) ^ (k + 1) * Real.exp (-(η * v)) ≤
      Real.exp 1 * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 1) := by
    intro v
    have h := dhpr_wsup (k + 1) hη hη1 v
    rw [Nat.factorial_succ] at h
    push_cast at h
    exact h
  have hS : ∑ v ∈ Ico v0 V, ((v : ℝ) + 1) ^ (k + 1) * Real.exp (-(η * v)) ≤
      2 * Real.exp 2 * ((k : ℝ) + 2) * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 2) := by
    have h := dhpr_wsum (k + 1) hη hη1 v0 V
    rw [Nat.factorial_succ] at h
    push_cast at h
    refine h.trans (le_of_eq ?_)
    ring
  have hE := dhpr_esum v0 V
  have hA2 : 0 ≤ 2 * A := mul_nonneg (by norm_num) hA
  have hC2 : 0 ≤ 2 * CH * (M : ℝ) := mul_nonneg (mul_nonneg (by norm_num) hCH) (Nat.cast_nonneg _)
  have hK : 0 ≤ Real.exp 1 * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 1) :=
    div_nonneg (by positivity) (pow_nonneg hη.le _)
  rw [dhpr_blocks _ v0 V hV]
  calc _ ≤ ∑ v ∈ Ico v0 V, (2 * A * (((v : ℝ) + 1) ^ (k + 1) * Real.exp (-(η * v))) +
        2 * CH * M * ((((v : ℝ) + 1) ^ (k + 1) * Real.exp (-(η * v))) *
          (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2))))) := by
        apply Finset.sum_le_sum
        intro v _
        have h := dhpr_block χ₁ h1 k hσ v _ (hHyp v)
        rw [hση] at h
        refine h.trans (le_of_eq ?_)
        ring
    _ = 2 * A * ∑ v ∈ Ico v0 V, (((v : ℝ) + 1) ^ (k + 1) * Real.exp (-(η * v))) +
        2 * CH * M * ∑ v ∈ Ico v0 V, ((((v : ℝ) + 1) ^ (k + 1) * Real.exp (-(η * v))) *
          (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2)))) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hS hA2
        · apply mul_le_mul_of_nonneg_left _ hC2
          calc _ ≤ ∑ v ∈ Ico v0 V, (Real.exp 1 * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 1)) *
                (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2))) := by
                apply Finset.sum_le_sum
                intro v _
                exact mul_le_mul_of_nonneg_right (hw v) (by positivity)
            _ = (Real.exp 1 * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 1)) *
                ∑ v ∈ Ico v0 V, (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2))) := by
                rw [← Finset.mul_sum]
            _ ≤ _ := mul_le_mul_of_nonneg_left hE hK

end Formalism.HermitianLattices.Ext.PrimesInProgressions
