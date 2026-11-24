module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Matrix.Mul
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.Yzd3.Phi :
    (n : ℕ) → (R : Type) → [CommRing R] → Matrix (Fin n) (Fin n) R :=
    fun (n : ℕ) (R : Type) [CommRing R] ↦
      (Matrix.of : (Fin n → Fin n → R) → Matrix (Fin n) (Fin n) R) fun (i j : Fin n) ↦
        if (↑i : ℕ) + (↑j : ℕ) + (1 : ℕ) = n then (-1 : R) ^ (↑i : ℕ) else (0 : R)

theorem UpperTheory.Reformulated.B.Yzd3.phi_mul_self :
    ∀ (a : ℕ) {R : Type} [inst : CommRing R],
      UpperTheory.Reformulated.B.Yzd3.Phi a R * UpperTheory.Reformulated.B.Yzd3.Phi a R = (-1 : R) ^ (a - (1 : ℕ)) • (1 : Matrix (Fin a) (Fin a) R) := by
  intro a R _
  ext i k
  have hi := i.2
  have hk := k.2
  have hj : a - 1 - (i : ℕ) < a := by omega
  simp only [Matrix.mul_apply, UpperTheory.Reformulated.B.Yzd3.Phi, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (⟨a - 1 - (i : ℕ), hj⟩ : Fin a)]
  · have h1 : (i : ℕ) + (a - 1 - (i : ℕ)) + 1 = a := by omega
    dsimp only
    rw [if_pos h1]
    by_cases hik : i = k
    · subst hik
      have h2 : (a - 1 - (i : ℕ)) + (i : ℕ) + 1 = a := by omega
      rw [if_pos h2, if_pos rfl, mul_one, ← pow_add]
      congr 1
      omega
    · have h2 : ¬ ((a - 1 - (i : ℕ)) + (k : ℕ) + 1 = a) := by
        intro h
        exact hik (Fin.ext (by omega))
      rw [if_neg h2, if_neg hik, mul_zero, mul_zero]
  · intro j _ hne
    have h1 : ¬ ((i : ℕ) + (j : ℕ) + 1 = a) := by
      intro h
      exact hne (Fin.ext (by simp only []; omega))
    rw [if_neg h1, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
