module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory.RestrictDVR

theorem isDiscreteValuationRing_comap (K L : Type) [Field K] [Field L] (φ : K →+* L)
    (hfin : (letI := φ.toAlgebra; FiniteDimensional K L))
    (V : ValuationSubring L) [IsDiscreteValuationRing V] :
    IsDiscreteValuationRing (V.comap φ) := by
  letI := φ.toAlgebra
  set E := V.comap φ with hE
  have memE : ∀ x : K, x ∈ E ↔ φ x ∈ V := fun x => ValuationSubring.mem_comap
  let g : E →+* V := (φ.comp E.subtype).codRestrict V (fun x => (memE x).1 x.2)
  have hg : ∀ x : E, ((g x : V) : L) = φ x := fun x => rfl

  have hpid : IsPrincipalIdealRing E := by
    refine ⟨fun I => ?_⟩
    by_cases hI : I = ⊥
    · subst hI; exact bot_isPrincipal
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    let f : E → ℕ∞ := fun y => IsDiscreteValuationRing.addVal V (g y)
    let s : Set E := {y | y ∈ I ∧ y ≠ 0}
    have hs : x ∈ s := ⟨hxI, hx0⟩
    set x0 := Function.argminOn f s ⟨x, hs⟩ with hx0def
    have hx0s : x0 ∈ s := Function.argminOn_mem f s ⟨x, hs⟩
    refine ⟨x0, le_antisymm ?_ ?_⟩
    · intro y hy
      rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton']
      by_cases hy0 : y = 0
      · exact ⟨0, by simp [hy0]⟩
      have hle : f x0 ≤ f y := Function.argminOn_le f s ⟨hy, hy0⟩
      obtain ⟨c, hc⟩ := (IsDiscreteValuationRing.addVal_le_iff_dvd).1 hle
      have hx0K : (x0 : K) ≠ 0 := fun h => hx0s.2 (Subtype.ext h)
      have hφx0 : φ x0 ≠ 0 := (map_ne_zero φ).2 hx0K
      have hcL : φ ((y : K) / x0) = (c : L) := by
        have := congrArg Subtype.val hc
        simp only [hg, MulMemClass.coe_mul] at this
        rw [map_div₀, this]; field_simp
      refine ⟨⟨(y : K) / x0, (memE _).2 (hcL ▸ c.2)⟩, Subtype.ext ?_⟩
      simp only [MulMemClass.coe_mul]
      field_simp
    · rw [Ideal.submodule_span_eq, Ideal.span_singleton_le_iff_mem]
      exact hx0s.1

  have hnf : IsLocalRing.maximalIdeal E ≠ ⊥ := by
    intro hbot
    have hall : ∀ x : K, φ x ∈ V := by
      intro x
      rcases E.mem_or_inv_mem x with h | h
      · exact (memE x).1 h
      by_cases hx : x = 0
      · simp [hx]
      have hu : IsUnit (⟨x⁻¹, h⟩ : E) := by
        by_contra hnu
        have : (⟨x⁻¹, h⟩ : E) ∈ IsLocalRing.maximalIdeal E := hnu
        rw [hbot, Ideal.mem_bot] at this
        exact inv_ne_zero hx (congrArg Subtype.val this)
      obtain ⟨u, hu⟩ := hu.exists_right_inv
      have : x = (u : K) := by
        have h1 := congrArg Subtype.val hu
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
        field_simp at h1; exact h1.symm
      rw [this]; exact (memE _).1 u.2
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
    have hπ0 : (π : L) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
    let ψ : K →+* V := φ.codRestrict V hall
    have hint : IsIntegral K ((π : L)⁻¹) := Algebra.IsIntegral.isIntegral _
    obtain ⟨p, hpm, hp⟩ := hint
    have hintV : IsIntegral V ((π : L)⁻¹) := by
      refine ⟨p.map ψ, hpm.map ψ, ?_⟩
      have hcomp : (algebraMap V L).comp ψ = algebraMap K L := by ext; rfl
      rw [Polynomial.eval₂_map, hcomp]
      exact hp
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := L)).mp hintV
    apply hπ.not_isUnit
    refine IsUnit.of_mul_eq_one y (Subtype.ext ?_)
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one]
    have : (y : L) = (π : L)⁻¹ := hy
    rw [this, mul_inv_cancel₀ hπ0]
  exact { hpid with not_a_field' := hnf }

theorem main : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V], IsDiscreteValuationRing (V.comap φ) := by
  intro K L _ _ φ hfin V _
  exact isDiscreteValuationRing_comap K L φ hfin V

end GlobalTheory.RestrictDVR
