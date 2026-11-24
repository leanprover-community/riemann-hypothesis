module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem map_mul_inv_ne_one_of_isUnit_map_sub {O k : Type} [CommRing O] [Field k] (a : O →+* k) (u v : Oˣ)
    (h : IsUnit (a ↑u - a ↑v)) : a ↑(u * v⁻¹) ≠ 1 := by
  intro h1
  have h2 : a ↑(u * v⁻¹) * a ↑v = 1 * a ↑v := by rw [h1]
  rw [Units.val_mul, ← map_mul, mul_assoc, Units.inv_mul, mul_one, one_mul] at h2
  exact h.ne_zero (sub_eq_zero.2 h2)

theorem UpperTheory.V.Ws.Gys.rootCharacters_ne_one_at_basepoint :
    ∀ {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k), Φ.Ok a → a (Φ.rt (-wAl) Φ.g0) ≠ 1 ∧ a (Φ.rt (-wPs) Φ.g0) ≠ 1 ∧ a (Φ.rt (-wAl + -wPs) Φ.g0) ≠ 1 := by
  intro O Γ k _ _ _ _ Φ a hΦ
  have e1 : Φ.rt (-wAl) Φ.g0 = Φ.χ 1 Φ.g0 * (Φ.χ 0 Φ.g0)⁻¹ := by
    simp [Fr.rt, wAl]
  have e2 : Φ.rt (-wPs) Φ.g0 = Φ.χ 2 Φ.g0 * (Φ.χ 0 Φ.g0)⁻¹ := by
    simp [Fr.rt, wPs]
  have hm : Φ.χ 1 Φ.g0 * Φ.χ 2 Φ.g0 = Φ.χ 0 Φ.g0 * Φ.χ 3 Φ.g0 := by
    have h1 := hΦ.mul 1 Φ.g0
    have h0 := hΦ.mul 0 Φ.g0
    have r1 : Fin.rev (1 : Fin 4) = 2 := by decide
    have r0 : Fin.rev (0 : Fin 4) = 3 := by decide
    rw [r1] at h1
    rw [r0] at h0
    rw [h1, h0]
  have e3 : Φ.rt (-wAl + -wPs) Φ.g0 = Φ.χ 3 Φ.g0 * (Φ.χ 0 Φ.g0)⁻¹ := by
    rw [Fr.rt_add, e1, e2, mul_mul_mul_comm, hm, mul_comm (Φ.χ 0 Φ.g0), mul_assoc, mul_inv_cancel_left]
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]
    exact map_mul_inv_ne_one_of_isUnit_map_sub a _ _ (hΦ.dist 1 0 (by decide))
  · rw [e2]
    exact map_mul_inv_ne_one_of_isUnit_map_sub a _ _ (hΦ.dist 2 0 (by decide))
  · rw [e3]
    exact map_mul_inv_ne_one_of_isUnit_map_sub a _ _ (hΦ.dist 3 0 (by decide))
