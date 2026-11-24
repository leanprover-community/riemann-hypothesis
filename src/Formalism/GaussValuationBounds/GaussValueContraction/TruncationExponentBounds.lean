module

public import Formalism.GaussValuationBounds.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.NOK

theorem powMemSpanOfLe : RelVanish := by
  intro A _ ℓ X u p E M j r hM hE
  rw [Ideal.mem_span_singleton, mul_pow, mul_pow, ← Finset.prod_pow, mul_assoc]
  have h1 : X ^ M ∣ X ^ r := pow_dvd_pow X hM
  have h2 : ∏ s ∈ Finset.range j, p s ^ E ∣ ∏ s ∈ Finset.range j, (p s ^ (ℓ - 1)) ^ r :=
    Finset.prod_dvd_prod_of_dvd _ _ fun s _ => by
      rw [← pow_mul]
      exact pow_dvd_pow _ hE
  exact Dvd.dvd.mul_left (mul_dvd_mul h1 h2) _

private theorem prime_sub_one_mul_padicValNat_factorial_le (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) :
    ((ℓ : ℝ) - 1) * (padicValNat ℓ r.factorial : ℝ) ≤ r := by
  have h2 : (ℓ - 1) * padicValNat ℓ r.factorial ≤ r := by
    rw [Nat.padicValNat_def, (Fact.out : ℓ.Prime).sub_one_mul_multiplicity_factorial]
    exact Nat.sub_le _ _
  have h1 : 1 ≤ ℓ := (Fact.out : ℓ.Prime).one_lt.le
  have h3 : (((ℓ - 1) * padicValNat ℓ r.factorial : ℕ) : ℝ) ≤ r := by exact_mod_cast h2
  push_cast [Nat.cast_sub h1] at h3
  exact h3

theorem truncationExponentBounds : SigNum := by
  intro ℓ _ hℓ E M j r hj
  have hℓ' : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hL0 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hM0 : (0 : ℝ) ≤ (M : ℝ) / (ℓ : ℝ) ^ (j - 1) := by positivity
  have hsig : ((E : ℝ) + (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 < sigNOK ℓ E M j := by
    unfold sigNOK
    push_cast
    exact Nat.lt_floor_add_one _
  have hleg := prime_sub_one_mul_padicValNat_factorial_le ℓ r
  have hsub : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one]
  constructor
  · intro hr
    have hr' : ((ℓ : ℝ) - 1) * r < E := by
      have h := (Nat.cast_lt (α := ℝ)).2 hr
      push_cast [hsub] at h
      exact h
    have key : ((r + padicValNat ℓ r.factorial : ℕ) : ℝ) < sigNOK ℓ E M j := by
      refine lt_of_le_of_lt ?_ hsig
      rw [le_div_iff₀ (by positivity)]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hleg hL0.le, mul_le_mul_of_nonneg_right hr'.le (by linarith : (0 : ℝ) ≤ ℓ)]
    exact_mod_cast key
  · refine le_trans ?_ hsig.le
    rcases le_or_gt (((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) 0 with h | h
    · rw [max_eq_left h, sub_zero, div_le_div_iff₀ hL0 (by positivity)]
      have h' : ((ℓ : ℝ) - 1) * r ≤ E + (M : ℝ) / (ℓ : ℝ) ^ (j - 1) := by linarith
      nlinarith [mul_le_mul_of_nonneg_right h' (by positivity : (0 : ℝ) ≤ ℓ * ((ℓ : ℝ) - 1))]
    · rw [max_eq_right h.le]
      have hneg : (ℓ : ℝ) - ((ℓ : ℝ) - 1) ^ 2 < 0 := by nlinarith
      have e : (r : ℝ) * ℓ / ((ℓ : ℝ) - 1) - (((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) -
          ((E : ℝ) + (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 =
          (((ℓ : ℝ) - 1) * r - (E + (M : ℝ) / (ℓ : ℝ) ^ (j - 1))) * ((ℓ : ℝ) - ((ℓ : ℝ) - 1) ^ 2) /
            ((ℓ : ℝ) - 1) ^ 2 := by
        field_simp
        ring
      have hn : (((ℓ : ℝ) - 1) * r - (E + (M : ℝ) / (ℓ : ℝ) ^ (j - 1))) * ((ℓ : ℝ) - ((ℓ : ℝ) - 1) ^ 2) /
          ((ℓ : ℝ) - 1) ^ 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg.le) (sq_nonneg _)
      linarith

end Formalism.NOK
