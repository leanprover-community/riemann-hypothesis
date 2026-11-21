import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockNormExtremalVectorEqBoundedNat
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import BuildAid.ForwardExisting

section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockNorm_extremal_vector_eq_bounded_nat : ∀ (n : ℕ) (lam : DomWeight n) (R : ℕ), (∀ i, lam.natW i ≤ R) → ∃ s : ℕ, 0 < s ∧ s ≤ (n.factorial) ^ (2 * R) * (R.factorial) ^ n ∧ ∀ (K : Type) [Field K] [StarRing K] [CharZero K], fockS (extremal K n lam) (extremal K n lam) = (s : K) := by
  first | exact @GlobalTheory.ExtremalNorm.fockS_extremal_eq_nat | exact GlobalTheory.ExtremalNorm.fockS_extremal_eq_nat | (intros; apply GlobalTheory.ExtremalNorm.fockS_extremal_eq_nat <;> assumption)
end

section
namespace GlobalTheory

theorem log_factorial_pow_mul_factorial_pow_le :
    ∀ (n R₀ : ℕ) (R : ℝ), 1 ≤ R → (R₀ : ℝ) ≤ R →
      Real.log (((n.factorial) ^ (2 * R₀) * (R₀.factorial) ^ n : ℕ) : ℝ)
        ≤ 4 * (n : ℝ) * R * Real.log (n * R) := by
  intro n R₀ R hR hR₀
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hf1 : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have hf2 : (0 : ℝ) < (R₀.factorial : ℝ) := by exact_mod_cast R₀.factorial_pos
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hlR : 0 ≤ Real.log R := Real.log_nonneg hR
  have h0 : (0 : ℝ) ≤ (R₀ : ℝ) := Nat.cast_nonneg _
  have h1 : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    rw [← Real.log_pow]
    apply Real.log_le_log hf1
    exact_mod_cast n.factorial_le_pow
  have h2 : Real.log (R₀.factorial : ℝ) ≤ R * Real.log R := by
    have h3 : (R₀.factorial : ℝ) ≤ R ^ R₀ := by
      calc (R₀.factorial : ℝ) ≤ (R₀ : ℝ) ^ R₀ := by exact_mod_cast R₀.factorial_le_pow
        _ ≤ R ^ R₀ := pow_le_pow_left₀ h0 hR₀ _
    calc Real.log (R₀.factorial : ℝ) ≤ Real.log (R ^ R₀) := Real.log_le_log hf2 h3
      _ = R₀ * Real.log R := Real.log_pow _ _
      _ ≤ R * Real.log R := mul_le_mul_of_nonneg_right hR₀ hlR
  have hlf : 0 ≤ Real.log (n.factorial : ℝ) :=
    Real.log_nonneg (by exact_mod_cast n.factorial_pos)
  push_cast
  rw [Real.log_mul (pow_pos hf1 _).ne' (pow_pos hf2 _).ne', Real.log_pow, Real.log_pow,
    Real.log_mul (by linarith) (by linarith)]
  push_cast
  have h4 : (R₀ : ℝ) * Real.log (n.factorial : ℝ) ≤ R * (n * Real.log n) :=
    mul_le_mul hR₀ h1 hlf (by linarith)
  have h5 : (n : ℝ) * Real.log (R₀.factorial : ℝ) ≤ n * (R * Real.log R) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have h6 : 0 ≤ R * (n * Real.log n) := by positivity
  have h7 : 0 ≤ (n : ℝ) * (R * Real.log R) := by positivity
  nlinarith [h4, h5, h6, h7]

end GlobalTheory
end

section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_factorial_pow_mul_factorial_pow_le' : ∀ (n R₀ : ℕ) (R : ℝ), 1 ≤ R → (R₀ : ℝ) ≤ R → Real.log (((n.factorial) ^ (2 * R₀) * (R₀.factorial) ^ n : ℕ) : ℝ) ≤ 4 * (n : ℝ) * R * Real.log (n * R) := by
  atlas_forward_decl GlobalTheory.log_factorial_pow_mul_factorial_pow_le
end

section
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem extNorm_eq_nat_log_le_bound : ∀ (K : Type) [Field K] [StarRing K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∃ s : ℕ, 0 < s ∧ extNorm K lam = (s : K) ∧ Real.log s ≤ bound (Fintype.card ι) n R := by
  intro K _ _ _ ι _ n lam R hR hS
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hw : ∀ τ i, (lam τ).natW i ≤ ⌊R⌋₊ := by
    intro τ i
    have hn : 0 < n := Fin.pos i
    have h := hS τ i ⟨n - 1, by omega⟩
    have h2 : (lam τ).w i - (lam τ).w ⟨n - 1, by omega⟩ ≤ (⌊R⌋₊ : ℤ) := by
      rw [Int.natCast_floor_eq_floor hR0]
      exact Int.le_floor.mpr h
    unfold DomWeight.natW DomWeight.detShift
    rw [dif_pos hn]
    omega
  choose s hs0 hs1 hs2 using fun τ => GlobalTheory.T.fockNorm_extremal_vector_eq_bounded_nat n (lam τ) ⌊R⌋₊ (hw τ)
  refine ⟨∏ τ, s τ, Finset.prod_pos fun τ _ => hs0 τ, ?_, ?_⟩
  · unfold extNorm
    rw [Nat.cast_prod]
    exact Finset.prod_congr rfl fun τ _ => hs2 τ K
  · rw [Nat.cast_prod, Real.log_prod (fun τ _ => by exact_mod_cast (hs0 τ).ne')]
    have hb := GlobalTheory.T.log_factorial_pow_mul_factorial_pow_le' n ⌊R⌋₊ R hR (Nat.floor_le hR0)
    have h1 : ∀ τ, Real.log (s τ) ≤ 4 * (n : ℝ) * R * Real.log (n * R) := fun τ =>
      le_trans (Real.log_le_log (by exact_mod_cast hs0 τ) (by exact_mod_cast hs1 τ)) hb
    calc ∑ τ, Real.log (s τ) ≤ ∑ _τ : ι, 4 * (n : ℝ) * R * Real.log (n * R) :=
          Finset.sum_le_sum fun τ _ => h1 τ
      _ = bound (Fintype.card ι) n R := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          unfold bound
          ring

end GlobalTheory
end

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_normalising_constant_log_le_bound : ∀ (K : Type) [Field K] [StarRing K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∃ s : ℕ, 0 < s ∧ extNorm K lam = (s : K) ∧ Real.log s ≤ bound (Fintype.card ι) n R := by
  atlas_forward_decl GlobalTheory.extNorm_eq_nat_log_le_bound
end
