module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem punctured_line_open_cofinite : ∀ (k : Type) [Field k] (V : Set (Sp (Localization.Away (Polynomial.X : Polynomial k)))), IsOpen V → ∀ (χ₁ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k), spMap χ₁.toRingHom (IsLocalRing.closedPoint k) ∈ V → Set.Finite {c : k | c ≠ 0 ∧ ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k, χ (algebraMap (Polynomial k) _ Polynomial.X) = c → spMap χ.toRingHom (IsLocalRing.closedPoint k) ∉ V} := by
  intro k _ V hV χ₁ h₁
  classical

  have key : ∀ (χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k)
      (g : Localization.Away (Polynomial.X : Polynomial k)),
      g ∉ PrimeSpectrum.asIdeal (spMap χ.toRingHom (IsLocalRing.closedPoint k)) ↔ χ g ≠ 0 := by
    intro χ g
    rw [Spec.map_base]
    change g ∉ (PrimeSpectrum.comap χ.toRingHom (IsLocalRing.closedPoint k)).asIdeal ↔ _
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    have hb : (IsLocalRing.closedPoint k).asIdeal = ⊥ := IsLocalRing.maximalIdeal_eq_bot
    rw [hb, Ideal.mem_bot]
    rfl
  have hV' : IsOpen (V : Set (PrimeSpectrum (Localization.Away (Polynomial.X : Polynomial k)))) := hV
  obtain ⟨_, ⟨g, rfl⟩, hg, hgV⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens).exists_subset_of_mem_open h₁ hV'
  have hg₁ : χ₁ g ≠ 0 := (key χ₁ g).1 hg
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (Polynomial.X : Polynomial k) g
  have hXu : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k,
      χ (algebraMap (Polynomial k) _ Polynomial.X) ≠ 0 := fun χ =>
    ((IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Polynomial k)).map χ).ne_zero
  have hev : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k, ∀ q : Polynomial k,
      χ (algebraMap (Polynomial k) _ q) = q.eval (χ (algebraMap (Polynomial k) _ Polynomial.X)) := by
    intro χ q
    have : χ.comp (IsScalarTower.toAlgHom k (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)))
        = Polynomial.aeval (χ (algebraMap (Polynomial k) _ Polynomial.X)) := by
      apply Polynomial.algHom_ext
      simp
    have h2 := congrArg (fun φ => φ q) this
    simpa [Polynomial.coe_aeval_eq_eval] using h2
  have hχp : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k,
      χ (algebraMap (Polynomial k) _ p) = χ g * (χ (algebraMap (Polynomial k) _ Polynomial.X)) ^ n := by
    intro χ
    rw [← hp, map_mul, map_pow]
  have hp0 : p ≠ 0 := by
    rintro rfl
    have := hχp χ₁
    rw [map_zero, map_zero] at this
    exact mul_ne_zero hg₁ (pow_ne_zero _ (hXu χ₁)) this.symm
  refine (Polynomial.finite_setOf_isRoot hp0).subset ?_
  rintro c ⟨hc0, hcall⟩
  by_contra hroot
  have hunit : ∀ y : Submonoid.powers (Polynomial.X : Polynomial k),
      IsUnit (Polynomial.aeval c (y : Polynomial k)) := by
    rintro ⟨_, m, rfl⟩
    simp [hc0]
  let χc : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k :=
    IsLocalization.liftAlgHom (M := Submonoid.powers (Polynomial.X : Polynomial k)) hunit
  have hχc : χc (algebraMap (Polynomial k) _ Polynomial.X) = c := by
    simp [χc, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  apply hcall χc hχc
  apply hgV
  refine (key χc g).2 ?_
  intro h0
  apply hroot
  have := hχp χc
  rw [h0, zero_mul, hev, hχc] at this
  exact this

end GlobalTheory
