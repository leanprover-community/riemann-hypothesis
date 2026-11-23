module

public import Development.EtaleCohomology.EtaleSheaves.HensCut
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace LateralTheory.E.IdemPartPf

open Finset

theorem prod_erase_mul_prod_erase {A : Type} [CommRing A] {n : ℕ} (y : Fin n → A)
    (h0 : ∏ l, y l = 0) {l m : Fin n} (hlm : l ≠ m) :
    (∏ k ∈ univ.erase l, y k) * (∏ k ∈ univ.erase m, y k) = 0 := by
  have hl : l ∈ (univ : Finset (Fin n)).erase m := mem_erase.2 ⟨hlm, mem_univ l⟩
  rw [← mul_prod_erase _ y hl, ← mul_assoc, mul_comm (∏ k ∈ univ.erase l, y k) (y l),
    mul_prod_erase _ y (mem_univ l), h0, zero_mul]

theorem IdemPart_of : LateralTheory.E.HensCut.IdemPart := by
  intro A _ n y h0 hu
  obtain ⟨u, hu⟩ := hu
  let e : Fin n → A := fun l => (↑u⁻¹ : A) * ∏ m ∈ univ.erase l, y m
  have horth : ∀ l m, l ≠ m → e l * e m = 0 := by
    intro l m hlm
    have := prod_erase_mul_prod_erase y h0 hlm
    calc e l * e m = (↑u⁻¹ : A) * ↑u⁻¹ * ((∏ k ∈ univ.erase l, y k) * (∏ k ∈ univ.erase m, y k)) := by
          simp only [e]; ring
      _ = 0 := by rw [this, mul_zero]
  have hsum : ∑ l, e l = 1 := by
    simp only [e]
    rw [← mul_sum, ← hu, Units.inv_mul]
  refine ⟨e, ?_, horth, hsum, ?_⟩
  · intro l
    unfold IsIdempotentElem
    calc e l * e l = e l * ∑ m, e m := by
          rw [mul_sum, sum_eq_single l]
          · intro m _ hml; exact horth l m (Ne.symm hml)
          · intro h; exact absurd (mem_univ l) h
      _ = e l := by rw [hsum, mul_one]
  · intro l
    simp only [e]
    rw [mul_assoc, mul_comm (∏ m ∈ univ.erase l, y m) (y l), mul_prod_erase _ y (mem_univ l), h0, mul_zero]

end LateralTheory.E.IdemPartPf
