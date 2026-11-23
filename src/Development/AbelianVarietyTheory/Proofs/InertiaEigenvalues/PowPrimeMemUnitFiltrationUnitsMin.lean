module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeAndRangePowLe
public import GroundTheory.LocalFields.UnramifiedHensel
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem exists_one_add_pow_eq {R : Type*} [CommRing R] (y : R) (k : ℕ) :
    ∃ w : R, (1 + y) ^ k = 1 + (k : R) * y + y ^ 2 * w := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨(1 + y) * w + k, ?_⟩
    rw [pow_succ, hw]; push_cast; ring

theorem one_add_pow_sub_one_mem {R : Type*} [CommRing R] (I : Ideal R) {n e k : ℕ} {y : R}
    (hy : y ∈ I ^ n) (hk : (k : R) ∈ I ^ e) :
    (1 + y) ^ k - 1 ∈ I ^ min (2 * n) (n + e) := by
  obtain ⟨w, hw⟩ := exists_one_add_pow_eq y k
  have h : (1 + y) ^ k - 1 = (k : R) * y + y ^ 2 * w := by rw [hw]; ring
  rw [h]
  refine Ideal.add_mem _ ?_ ?_
  · refine Ideal.pow_le_pow_right (min_le_right _ _) ?_
    rw [add_comm n e, pow_add]
    exact Ideal.mul_mem_mul hk hy
  · refine Ideal.pow_le_pow_right (min_le_left _ _) ?_
    refine Ideal.mul_mem_right _ _ ?_
    rw [two_mul, pow_add, pow_two]
    exact Ideal.mul_mem_mul hy hy

theorem natCast_mem_maximalIdeal_pow_of_ordIs {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {p e : ℕ} (h : OrdIs F p e) : (p : 𝒪[F]) ∈ 𝓂[F] ^ e := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hϖ]
  rw [OrdIs] at h
  rw [h]
  simp

theorem pow_mem_unitFiltrationUnits (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p e n : ℕ) (hp : OrdIs F p e) :
    ∀ x ∈ unitFiltrationUnits F n, x ^ p ∈ unitFiltrationUnits F (min (2 * n) (n + e)) := by
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨u ^ p, ?_, by simp⟩
  rw [SetLike.mem_coe, mem_unitFiltration] at hu ⊢
  have := one_add_pow_sub_one_mem (𝓂[F]) hu (natCast_mem_maximalIdeal_pow_of_ordIs hp)
  simpa using this

end GlobalTheory.PMon.Ram

end
