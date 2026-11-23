module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Free

@[expose] public section

namespace GlobalTheory


open Module in
theorem _root_.GlobalTheory.exists_representatives_mod_nsmul : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : ℕ), 1 ≤ k → (∀ a b : X, k • a = k • b → a = b) ∧ ∃ e : Fin (k ^ Module.finrank ℤ X) → X, ∀ χ : X, ∃! i, ∃ m : X, χ = e i + k • m := by
  intro X _ _ _ k hk
  classical
  set n := Module.finrank ℤ X
  let b : Basis (Fin n) ℤ X := Module.finBasis ℤ X
  have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast (omega : k ≠ 0)
  have hkpos : (0 : ℤ) < k := by exact_mod_cast (omega : 0 < k)
  have coord : ∀ (x y : X) (j : Fin n), b.repr (x + k • y) j = b.repr x j + k * b.repr y j := by
    intro x y j
    rw [← Nat.cast_smul_eq_nsmul ℤ]
    simp
  refine ⟨fun x y h => ?_, ?_⟩
  · apply b.ext_elem
    intro j
    have hj : b.repr (0 + k • x) j = b.repr (0 + k • y) j := by rw [h]
    rw [coord, coord] at hj
    simp only [map_zero, Finsupp.zero_apply, zero_add] at hj
    exact mul_left_cancel₀ hk0 hj
  let d : Fin (k ^ n) → Fin n → ℤ := fun i j => ((finFunctionFinEquiv.symm i j : ℕ) : ℤ)
  refine ⟨fun i => ∑ j, d i j • b j, fun χ => ?_⟩
  have rep : ∀ i j, b.repr (∑ j', d i j' • b j') j = d i j := by
    intro i j
    rw [b.repr_sum_self]
  let r : Fin n → Fin k := fun j => ⟨(b.repr χ j % k).toNat, by
    have h1 := Int.emod_nonneg (b.repr χ j) hk0
    have h2 := Int.emod_lt_of_pos (b.repr χ j) hkpos
    omega⟩
  refine ⟨finFunctionFinEquiv r, ⟨∑ j, (b.repr χ j / k) • b j, ?_⟩, ?_⟩
  · apply b.ext_elem
    intro j
    rw [coord, rep, b.repr_sum_self]
    simp only [d, Equiv.symm_apply_apply, r]
    have h1 := Int.emod_nonneg (b.repr χ j) hk0
    rw [Int.toNat_of_nonneg h1, Int.emod_def]
    ring
  · rintro i ⟨m, hm⟩
    apply finFunctionFinEquiv.symm.injective
    rw [Equiv.symm_apply_apply]
    funext j
    have h : b.repr χ j = b.repr (∑ j', d i j' • b j' + k • m) j := by rw [hm]
    rw [coord, rep] at h
    have hd : d i j < k := by
      show ((finFunctionFinEquiv.symm i j : ℕ) : ℤ) < k
      exact_mod_cast (finFunctionFinEquiv.symm i j).isLt
    have hd0 : 0 ≤ d i j := Int.natCast_nonneg _
    have hmod : b.repr χ j % k = d i j := by
      rw [h, Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt hd0 hd
    apply Fin.ext
    show (finFunctionFinEquiv.symm i j : ℕ) = (b.repr χ j % k).toNat
    rw [hmod]
    exact (Int.toNat_natCast _).symm

end GlobalTheory
