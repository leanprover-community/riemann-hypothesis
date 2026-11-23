module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDividedPowersOfCompOnGeneratorsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersAugmentationIdealStatement
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem uniformBell_comp_coeff (m : ℕ) {n N : ℕ} (hn : n ≠ 0) (hN : N ≠ 0) :
    n.uniformBell N ^ m * m.uniformBell (n * N) = m.uniformBell n * (m * n).uniformBell N := by
  have h1 := Nat.uniformBell_mul_eq n hN
  have h2 := Nat.uniformBell_mul_eq m (Nat.mul_ne_zero hn hN)
  have h3 := Nat.uniformBell_mul_eq m hn
  have h4 := Nat.uniformBell_mul_eq (m * n) hN
  have hpos : 0 < m.factorial * n.factorial ^ m * N.factorial ^ (m * n) := by positivity
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc n.uniformBell N ^ m * m.uniformBell (n * N) * (m.factorial * n.factorial ^ m * N.factorial ^ (m * n))
      = m.uniformBell (n * N) * (n.uniformBell N * N.factorial ^ n * n.factorial) ^ m * m.factorial := by ring
    _ = (m * (n * N)).factorial := by rw [h1, h2]
    _ = ((m * n) * N).factorial := by rw [Nat.mul_assoc]
    _ = (m * n).uniformBell N * N.factorial ^ (m * n) * (m.uniformBell n * n.factorial ^ m * m.factorial) := by
      rw [h3, h4]
    _ = m.uniformBell n * (m * n).uniformBell N * (m.factorial * n.factorial ^ m * N.factorial ^ (m * n)) := by ring

theorem exists_dividedPowers_aug : ∀ (B : Type) [CommRing B] (Q : PDPoly B),
    ∃ η : DividedPowers Q.aug, ∀ n : ℕ, η.dpow n (Q.e 1) = Q.e n := by
  intro B _ Q
  obtain ⟨γ, hγ, he⟩ := GlobalTheory.T.exists_isPreDividedPowers_augmentationIdeal B Q
  have hcomp : ∀ x ∈ Set.range (fun k : ℕ ↦ Q.e (k + 1)), ∀ m n : ℕ, n ≠ 0 →
      γ m (γ n x) = (m.uniformBell n : Q.P) * γ (m * n) x := by
    rintro _ ⟨k, rfl⟩ m n hn
    obtain ⟨j, hj⟩ : ∃ j, n * (k + 1) = j + 1 := ⟨n * (k + 1) - 1, by
      have : 0 < n * (k + 1) := Nat.mul_pos (Nat.pos_of_ne_zero hn) k.succ_pos
      omega⟩
    have hmem : Q.e (n * (k + 1)) ∈ Q.aug := hj ▸ Q.e_succ_mem_aug j
    have key := congrArg (Nat.cast (R := Q.P)) (uniformBell_comp_coeff m hn k.succ_ne_zero)
    push_cast at key
    rw [he n k, hγ.mul m _ _ hmem, hj, he m j, ← hj, he (m * n) k, ← Nat.mul_assoc]
    linear_combination key * Q.e (m * n * (k + 1))
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_dividedPowers_of_comp_on_generators Q.P Q.aug γ (Set.range fun k : ℕ ↦ Q.e (k + 1)) hγ rfl hcomp
  refine ⟨δ, fun n ↦ ?_⟩
  rw [hδ]
  have := he n 0
  simpa [Nat.uniformBell_one_right] using this

end GlobalTheory.PDA
