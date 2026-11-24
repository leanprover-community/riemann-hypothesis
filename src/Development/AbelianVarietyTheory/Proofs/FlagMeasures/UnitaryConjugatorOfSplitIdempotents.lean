module

public import ReciprocityTheory.Automorphisms.Unitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix

namespace GlobalTheory

open ReciprocityTheory.Aut

theorem unitary_conjugator_of_split_idempotents :
  ∀ (R : Type) [CommRing R] (σ : R →+* R), (∀ a, σ (σ a) = a) → ∀ (m n : ℕ) (ι : Type) [Fintype ι] (ε : ι → R), (∀ j, ε j * ε j = ε j) → (∀ j, ε j * σ (ε j) = 0) → (∀ j k, j ≠ k → ε j * ε k = 0 ∧ ε j * σ (ε k) = 0) → ∀ (Z P : Matrix (Fin m) (Fin n) R) (Z' P' : Matrix (Fin n) (Fin m) R), Z * Z' = 1 → Z' * Z = 1 → P * P' = 1 → P' * P = 1 → ∃ c : GL (Fin n) R, (c : Matrix (Fin n) (Fin n) R) * ReciprocityTheory.Aut.conjT σ (c : Matrix (Fin n) (Fin n) R) = 1 ∧ ∀ j, ε j • (Z * (c : Matrix (Fin n) (Fin n) R)) = ε j • P ∧ ε j • (((c⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * Z') = ε j • P' := by
  intro R _ σ hσ m n ι _ ε hidem hself hcross Z P Z' P' hZZ' hZ'Z hPP' hP'P
  classical

  obtain ⟨e, he⟩ : ∃ e : R, e = ∑ j, ε j := ⟨_, rfl⟩
  have hje : ∀ j, ε j * e = ε j := by
    intro j
    rw [he, Finset.mul_sum, Finset.sum_eq_single j (fun k _ hk => (hcross j k (Ne.symm hk)).1)
      (fun h => absurd (Finset.mem_univ j) h), hidem]
  have hjse : ∀ j, ε j * σ e = 0 := by
    intro j

    rw [he, map_sum, Finset.mul_sum]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    by_cases hk : j = k
    · subst hk; exact hself j
    · exact (hcross j k hk).2
  have hee : e * e = e := by
    nth_rewrite 1 [he]
    rw [Finset.sum_mul]
    simp only [hje]
    exact he.symm
  have hese : e * σ e = 0 := by
    nth_rewrite 1 [he]
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero (fun j _ => hjse j)
  obtain ⟨e', he'⟩ : ∃ e' : R, e' = σ e := ⟨_, rfl⟩
  rw [← he'] at hese hjse
  have he'e' : e' * e' = e' := by rw [he', ← map_mul, hee]
  have he'e : e' * e = 0 := by rw [mul_comm, hese]
  have hσe' : σ e' = e := by rw [he', hσ]
  obtain ⟨f, hf⟩ : ∃ f : R, f = 1 - e - e' := ⟨_, rfl⟩
  have hσf : σ f = f := by rw [hf, map_sub, map_sub, map_one, hσe', ← he']; ring
  have hfe : f * e = 0 := by rw [hf]; linear_combination -hee - he'e
  have hfe' : f * e' = 0 := by rw [hf]; linear_combination -hese - he'e'
  have hff : f * f = f := by rw [hf]; linear_combination hee + he'e' + 2 * hese
  have hef : e * f = 0 := by rw [mul_comm, hfe]
  have he'f : e' * f = 0 := by rw [mul_comm, hfe']
  have hee'' : e * e' = 0 := hese
  have hsum : f + e + e' = 1 := by rw [hf]; ring

  have cadd : ∀ A B : Matrix (Fin n) (Fin n) R, conjT σ (A + B) = conjT σ A + conjT σ B := by
    intro A B; ext i j; simp [conjT]
  have csmul : ∀ (a : R) (A : Matrix (Fin n) (Fin n) R), conjT σ (a • A) = σ a • conjT σ A := by
    intro a A; ext i j; simp [conjT]
  set X : Matrix (Fin n) (Fin n) R := Z' * P with hX
  set Y : Matrix (Fin n) (Fin n) R := conjT σ (P' * Z) with hY
  set c : Matrix (Fin n) (Fin n) R := f • (1 : Matrix (Fin n) (Fin n) R) + e • X + e' • Y with hc
  have hcT : conjT σ c = f • (1 : Matrix (Fin n) (Fin n) R) + e' • conjT σ X + e • (P' * Z) := by
    rw [hc, cadd, cadd, csmul, csmul, csmul, conjT_one, hσf, hY, conjT_conjT σ hσ, hσe', ← he']
  have hXY : X * conjT σ Y = 1 := by
    rw [hY, conjT_conjT σ hσ, hX, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP', Matrix.one_mul, hZ'Z]
  have hYX : Y * conjT σ X = 1 := by
    rw [hY, ← conjT_mul, ← hXY, hY, conjT_conjT σ hσ]
    rw [hX, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP', Matrix.one_mul, hZ'Z, conjT_one]
  have hcc : c * conjT σ c = 1 := by
    rw [hcT, hc]
    have hYeq : P' * Z = conjT σ Y := by rw [hY, conjT_conjT σ hσ]
    rw [hYeq]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hff, hfe, hfe', hef, he'f, hee, hee'', he'e, he'e', zero_smul, add_zero, zero_add,
      Matrix.one_mul, Matrix.mul_one, hXY, hYX, smul_add]
    conv_rhs => rw [← one_smul R (1 : Matrix (Fin n) (Fin n) R), ← hsum]
    simp only [add_smul]
    abel
  have hcc' : conjT σ c * c = 1 := mul_eq_one_comm.mp hcc
  refine ⟨⟨c, conjT σ c, hcc, hcc'⟩, hcc, fun j => ⟨?_, ?_⟩⟩
  · show ε j • (Z * c) = ε j • P
    have hjf : ε j * f = 0 := by
      rw [hf]; linear_combination -hje j - hjse j
    rw [hc, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
      smul_add, smul_add, smul_smul, smul_smul, smul_smul, hjf, hje, hjse, zero_smul, zero_smul,
      zero_add, add_zero, hX, ← Matrix.mul_assoc, hZZ', Matrix.one_mul]
  · show ε j • (conjT σ c * Z') = ε j • P'
    have hjf : ε j * f = 0 := by
      rw [hf]; linear_combination -hje j - hjse j
    rw [hcT, Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul,
      smul_add, smul_add, smul_smul, smul_smul, smul_smul, hjf, hje, hjse, zero_smul, zero_smul,
      zero_add, zero_add, Matrix.mul_assoc, hZZ', Matrix.mul_one]

end GlobalTheory
