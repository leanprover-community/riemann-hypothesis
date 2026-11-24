module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Denchar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primval
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Finset UpperTheory.V.Bern

private theorem dirichletCharacter_unit_isIntegral {R : Type} [CommRing R] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter R N) (u : (ZMod N)ˣ) : IsIntegral ℤ (χ u) := by
  have hpos : 0 < orderOf u := orderOf_pos u
  refine IsIntegral.of_pow hpos ?_
  have h1 : χ (u : ZMod N) ^ orderOf u = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
  rw [h1]
  exact isIntegral_one

theorem UpperTheory.V.Bern.b_primmem :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} [NeZero N] (k : ℕ) (χ : DirichletCharacter R N), (∀ A : Subalgebra ℚ R, (∀ u : (ZMod N)ˣ, χ u ∈ A) → Bprim k χ ∈ A) ∧ (∀ A : Subring R, (∀ u : (ZMod N)ˣ, χ u ∈ A) → (den N k : R) * Bprim k χ ∈ A) ∧ IsIntegral ℤ ((den N k : R) * Bprim k χ) ∧ IsIntegral ℤ ((den N k : R) * genB k χ) := by
  intro R _ _ N _ k χ
  have hN : N ≠ 0 := NeZero.ne N
  have hc : 0 < χ.conductor :=
    Nat.pos_of_ne_zero fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ χ.conductor_dvd_level))
  have hdvd : den χ.conductor k ∣ den N k := den_dvd χ.conductor_dvd_level k
  have hB : Bprim k χ = genB k (⇑χ.primitiveCharacter) := rfl
  have hint : ∀ a : ZMod N, IsIntegral ℤ (χ a) := by
    intro a
    by_cases ha : IsUnit a
    · obtain ⟨u, rfl⟩ := ha
      exact dirichletCharacter_unit_isIntegral χ u
    · rw [MulChar.map_nonunit χ ha]
      exact isIntegral_zero
  have part2 : ∀ A : Subring R, (∀ u : (ZMod N)ˣ, χ u ∈ A) → (den N k : R) * Bprim k χ ∈ A := by
    intro A hA
    obtain ⟨m, hm⟩ := hdvd
    have hmem : (den χ.conductor k : R) * genB k (⇑χ.primitiveCharacter) ∈ A := by
      refine b_denchar k _ A hc ?_
      intro x
      rcases b_primval χ x with h | ⟨u, h⟩
      · rw [h]; exact A.zero_mem
      · rw [h]; exact hA u
    rw [hB, hm, Nat.cast_mul, mul_comm ((den χ.conductor k : ℕ) : R) (m : R), mul_assoc]
    exact A.mul_mem (natCast_mem A m) hmem
  refine ⟨?_, part2, ?_, ?_⟩
  · intro A hA
    rw [hB]
    refine genB_mem k _ A ?_
    intro x
    rcases b_primval χ x with h | ⟨u, h⟩
    · rw [h]; exact A.zero_mem
    · rw [h]; exact hA u
  · have := part2 (integralClosure ℤ R).toSubring (fun u => dirichletCharacter_unit_isIntegral χ u)
    exact this
  · have := b_denchar k (⇑χ) (integralClosure ℤ R).toSubring (Nat.pos_of_ne_zero hN) (fun a => hint a)
    exact this
