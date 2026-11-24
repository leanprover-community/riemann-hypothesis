module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory.EssFiniteDescent

theorem essFiniteType_of_eq_div : ∀ (K : Type) [Field K] (c : ℂ →+* K) (R : Subring K) (hcR : ∀ a, c a ∈ R) (E : ValuationSubring K) (hcE : ∀ a, c a ∈ E), R ≤ E.toSubring → (c.codRestrict R hcR).FiniteType → (∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s) → (c.codRestrict E hcE).EssFiniteType := by
  intro K _ c R hcR E hcE hRE hft hloc
  let f : R →+* E :=
    { toFun := fun r => ⟨(r : K), hRE r.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let M : Submonoid R :=
    { carrier := {s | (s : K) ≠ 0 ∧ (s : K)⁻¹ ∈ E}
      mul_mem' := by
        rintro a b ⟨ha0, ha⟩ ⟨hb0, hb⟩
        refine ⟨by simpa using mul_ne_zero ha0 hb0, ?_⟩
        have : ((a * b : R) : K)⁻¹ = (b : K)⁻¹ * (a : K)⁻¹ := by
          push_cast; exact mul_inv_rev _ _
        rw [this]; exact E.mul_mem _ _ hb ha
      one_mem' := ⟨by simp, by simpa using E.one_mem⟩ }
  letI : Algebra ℂ R := (c.codRestrict R hcR).toAlgebra
  letI : Algebra R E := f.toAlgebra
  letI : Algebra ℂ E := (c.codRestrict E hcE).toAlgebra
  haveI : IsScalarTower ℂ R E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType ℂ R := hft
  haveI : IsLocalization M E := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨s, hs0, hs⟩
      refine isUnit_iff_exists_inv.mpr ⟨⟨_, hs⟩, ?_⟩
      apply Subtype.ext
      change (s : K) * (s : K)⁻¹ = 1
      exact mul_inv_cancel₀ hs0
    · rintro ⟨e, he⟩
      obtain ⟨a, ha, s, hs, hsE, rfl⟩ := hloc e he
      by_cases hs0 : s = 0
      · refine ⟨(0, 1), ?_⟩
        apply Subtype.ext
        change a / s * ((1 : M) : R) = (((0 : R)) : K)
        simp [hs0]
      · refine ⟨(⟨a, ha⟩, ⟨⟨s, hs⟩, by simpa using hs0, hsE⟩), ?_⟩
        apply Subtype.ext
        change a / s * s = a
        exact div_mul_cancel₀ a hs0
    · intro x y hxy
      refine ⟨1, ?_⟩
      have : (x : K) = y := congrArg (fun z : E => (z : K)) hxy
      simp [Subtype.ext this]
  haveI : Algebra.EssFiniteType R E := Algebra.EssFiniteType.of_isLocalization E M
  have h : Algebra.EssFiniteType ℂ E := Algebra.EssFiniteType.comp ℂ R E
  exact h

end GlobalTheory.EssFiniteDescent
