module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

private theorem coeff_mul_sum {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] [Fintype Γ]
    (z w : MonoidAlgebra A Γ) (g : Γ) : (z * w).coeff g = ∑ h, z.coeff (g * h⁻¹) * w.coeff h := by
  rw [MonoidAlgebra.mul_apply_right, Finsupp.sum_fintype]
  intro h
  simp

theorem UpperTheory.V.B5.coords_mul_eq_quotientMatrix_mulVec :
    ∀ {A : Type} [CommRing A] {Γ : Type} [CommGroup Γ] [Finite Γ] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∀ z w : MonoidAlgebra A Γ, coord c ε (z * w) = (mat c ε z).mulVec (coord c ε w) := by
  intro A _ Γ _ _ c ε hc hc1 hε z w
  haveI := Fintype.ofFinite Γ
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hεA : (ε : A) * ε = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → A) hε
  funext i
  simp only [coord, Matrix.mulVec, dotProduct, mat, Matrix.of_apply, coeff_mul_sum]
  rw [sum_rep hc hc1, sum_rep hc hc1, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : rep i * (c * rep j)⁻¹ = c * (rep i * (rep j)⁻¹) := by
    rw [mul_inv, hci, mul_left_comm]
  have e2 : c * rep i * (c * rep j)⁻¹ = rep i * (rep j)⁻¹ := by
    rw [mul_inv, hci, mul_mul_mul_comm, hc, one_mul]
  have e3 : c * rep i * (rep j)⁻¹ = c * (rep i * (rep j)⁻¹) := mul_assoc _ _ _
  rw [e2, e1, e3]
  linear_combination (-(z.coeff (c * (rep i * (rep j)⁻¹)) * w.coeff (c * rep j))) * hεA
