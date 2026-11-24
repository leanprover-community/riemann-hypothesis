module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.ValGeneric

theorem exists_pow_mem_of_ne_zero (R : Type) [CommRing R] [IsDomain R] [ValuationRing R]
    [Ring.DimensionLEOne R] :
    ∃ π : R, π ≠ 0 ∧ ∀ b : R, b ≠ 0 → ∃ (n : ℕ) (c : R), π ^ n = b * c := by
  by_cases hm : IsLocalRing.maximalIdeal R = ⊥
  · refine ⟨1, one_ne_zero, fun b hb => ?_⟩
    have hu : IsUnit b := by
      by_contra h
      have hbm : b ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal b).2 h
      rw [hm] at hbm
      exact hb (by simpa using hbm)
    obtain ⟨u, rfl⟩ := hu
    exact ⟨0, ((u⁻¹ : Rˣ) : R), by simp⟩
  · obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
    refine ⟨π, hπ0, fun b hb => ?_⟩
    by_cases hu : IsUnit b
    · obtain ⟨u, rfl⟩ := hu
      exact ⟨0, ((u⁻¹ : Rˣ) : R), by simp⟩
    have hrad : π ∈ (Ideal.span {b}).radical := by
      rw [Ideal.radical_eq_sInf]
      refine Ideal.mem_sInf.2 ?_
      rintro J ⟨hbJ, hJ⟩
      have hbJ' : b ∈ J := hbJ (Ideal.mem_span_singleton_self b)
      have hJ0 : J ≠ ⊥ := fun h => hb (by simpa [h] using hbJ')
      have hmax := Ring.DimensionLEOne.maximalOfPrime hJ0 hJ
      rw [IsLocalRing.eq_maximalIdeal hmax]
      exact hπ
    obtain ⟨n, hn⟩ := hrad
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
    exact ⟨n, c, by rw [← hc, mul_comm]⟩

theorem isOpenImmersion_spMap_fraction :
    ∀ (C : Type) [Field C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C], IsOpenImmersion (spMap (algebraMap R C)) := by
  intro C _ R _ _ _ _ _ _
  obtain ⟨π, hπ0, h⟩ := exists_pow_mem_of_ne_zero R
  have inj := IsFractionRing.injective R C
  haveI : IsLocalization.Away π C := by
    refine IsLocalization.Away.mk π ?_ ?_ ?_
    · exact ((map_ne_zero_iff _ inj).2 hπ0).isUnit
    · intro s
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) s
      obtain ⟨n, c, hc⟩ := h b (nonZeroDivisors.ne_zero hb)
      refine ⟨n, a * c, ?_⟩
      have hb' : algebraMap R C b ≠ 0 :=
        (map_ne_zero_iff _ inj).2 (nonZeroDivisors.ne_zero hb)
      rw [← map_pow, hc, map_mul, map_mul]
      field_simp
    · intro a b hab
      exact ⟨0, by rw [inj hab]⟩
  exact IsOpenImmersion.of_isLocalization π

end GlobalTheory.CompanionTheory.ValGeneric
