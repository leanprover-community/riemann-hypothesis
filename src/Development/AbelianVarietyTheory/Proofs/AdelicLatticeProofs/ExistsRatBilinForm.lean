module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.BilinearMap
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
public import Mathlib.Data.Rat.Cast.CharZero

@[expose] public section

namespace GlobalTheory.RationalValueRealScalar

theorem map_rat_smul_real {U : Type} [AddCommGroup U] [Module ℝ U] {V : Type} [AddCommGroup V]
    [Module ℚ V] (p : V →+ U) (c : ℚ) (x : V) : p (c • x) = (c : ℝ) • p x := by
  have h1 : (c.den : ℤ) • (c • x) = c.num • x := by
    rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    congr 1
    rw [Int.cast_natCast, mul_comm, Rat.mul_den_eq_num]
  have h2 : (c.den : ℝ) • p (c • x) = (c.num : ℝ) • p x := by
    rw [← Int.cast_natCast, Int.cast_smul_eq_zsmul ℝ, Int.cast_smul_eq_zsmul ℝ, ← map_zsmul, ← map_zsmul, h1]
  have hd : (c.den : ℝ) ≠ 0 := by positivity
  calc p (c • x) = ((c.den : ℝ)⁻¹ * c.den) • p (c • x) := by rw [inv_mul_cancel₀ hd, one_smul]
    _ = (c.den : ℝ)⁻¹ • ((c.den : ℝ) • p (c • x)) := by rw [smul_smul]
    _ = (c.den : ℝ)⁻¹ • ((c.num : ℝ) • p x) := by rw [h2]
    _ = (c : ℝ) • p x := by rw [smul_smul, Rat.cast_def, inv_mul_eq_div]

theorem exists_rat_value {U : Type} [AddCommGroup U] [Module ℝ U] (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    {V : Type} [AddCommGroup V] (p : V →+ U) (L : AddSubgroup V)
    (hL : ∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = (k : ℝ)) (u v : V) :
    ∃ q : ℚ, (q : ℝ) = -(om (p u) (p v)) := by
  obtain ⟨N, hN, hNu⟩ := hL u
  obtain ⟨M, hM, hMv⟩ := hL v
  obtain ⟨k, hk⟩ := hint _ hNu _ hMv
  simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at hk
  refine ⟨-(k / (N * M) : ℚ), ?_⟩
  have hNM : (N : ℝ) * M ≠ 0 := by positivity
  push_cast
  rw [neg_inj, div_eq_iff hNM, ← hk]
  ring

theorem exists_rat_bilinForm {U : Type} [AddCommGroup U] [Module ℝ U] (om : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    {V : Type} [AddCommGroup V] [Module ℚ V] (p : V →+ U) (L : AddSubgroup V)
    (hL : ∀ x : V, ∃ N : ℕ, 0 < N ∧ N • x ∈ L)
    (hint : ∀ x ∈ L, ∀ y ∈ L, ∃ k : ℤ, om (p x) (p y) = (k : ℝ)) :
    ∃ B : LinearMap.BilinForm ℚ V, ∀ u v : V, ((B u v : ℚ) : ℝ) = -(om (p u) (p v)) := by
  choose q hq using exists_rat_value om p L hL hint
  refine ⟨LinearMap.mk₂ ℚ q ?_ ?_ ?_ ?_, fun u v => hq u v⟩
  · intro u1 u2 v
    apply Rat.cast_injective (α := ℝ)
    rw [Rat.cast_add, hq, hq, hq, map_add (f := _), LinearMap.map_add (f := _), LinearMap.add_apply]
    ring
  · intro c u v
    apply Rat.cast_injective (α := ℝ)
    rw [smul_eq_mul, Rat.cast_mul, hq, hq, map_rat_smul_real, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  · intro u v1 v2
    apply Rat.cast_injective (α := ℝ)
    rw [Rat.cast_add, hq, hq, hq, map_add (f := _), LinearMap.map_add (f := _)]
    ring
  · intro c u v
    apply Rat.cast_injective (α := ℝ)
    rw [smul_eq_mul, Rat.cast_mul, hq, hq, map_rat_smul_real, LinearMap.map_smul, smul_eq_mul]
    ring

end GlobalTheory.RationalValueRealScalar
