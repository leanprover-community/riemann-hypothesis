module

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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
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


open Polynomial in
theorem poly_eq_C_of_eq_aeval_invSelf {K : Type} [CommRing K] (p q : K[X])
    (h : algebraMap K[X] (Localization.Away (X : K[X])) p =
      aeval (IsLocalization.Away.invSelf (X : K[X]) : Localization.Away (X : K[X])) q) :
    p = C (p.eval 0) := by
  set L := Localization.Away (X : K[X])
  set n := q.natDegree
  letI : Invertible (algebraMap K[X] L X) :=
    ⟨IsLocalization.Away.invSelf (X : K[X]),
      by rw [mul_comm]; exact IsLocalization.Away.mul_invSelf _, IsLocalization.Away.mul_invSelf _⟩
  have hr : (q.reflect n).natDegree ≤ n := natDegree_reflect_le.trans (by simp [n])
  have key := eval₂_reflect_mul_pow (algebraMap K L) (algebraMap K[X] L X) n (q.reflect n) hr
  rw [reflect_reflect] at key
  have hev : ∀ r : K[X], eval₂ (algebraMap K L) (algebraMap K[X] L X) r = algebraMap K[X] L r :=
    fun r => eval₂_algebraMap_X r (IsScalarTower.toAlgHom K K[X] L)
  have h2 : algebraMap K[X] L (p * X ^ n) = algebraMap K[X] L (q.reflect n) := by
    rw [map_mul, map_pow, h, aeval_def, ← hev (q.reflect n)]
    exact key
  have hinj : Function.Injective (algebraMap K[X] L) :=
    IsLocalization.injective L (Submonoid.powers_le.2 X_mem_nonzeroDivisors)
  have h3 := hinj h2
  have hdeg : (p * X ^ n).natDegree ≤ n := h3 ▸ hr
  have hp0 : p.natDegree = 0 := by
    by_cases hp : p = 0
    · simp [hp]
    have hc : (p * X ^ n).coeff (p.natDegree + n) ≠ 0 := by
      rw [coeff_mul_X_pow]; exact mt leadingCoeff_eq_zero.mp hp
    have := le_natDegree_of_ne_zero hc
    omega
  rw [← coeff_zero_eq_eval_zero]
  exact eq_C_of_natDegree_eq_zero hp0

end GlobalTheory

namespace GlobalTheory

theorem chart_map_into_affine_const (K : Type) [CommRing K] (Y : Scheme.{0}) (W : Y.Opens)
    (hW : IsAffineOpen W) (g₀ g₁ : Sp (Polynomial K) ⟶ Y) (h₀ : ∀ x, g₀ x ∈ W) (h₁ : ∀ x, g₁ x ∈ W)
    (h : spMap (algebraMap (Polynomial K) (Localization.Away (Polynomial.X : Polynomial K))) ≫ g₀ =
      spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial K) :
        Localization.Away (Polynomial.X : Polynomial K))).toRingHom ≫ g₁) :
    g₀ = spMap (algebraMap K (Polynomial K)) ≫ spMap (Polynomial.evalRingHom 0) ≫ g₀ := by
  haveI := hW.isOpenImmersion_fromSpec
  have r₀ : Set.range g₀.base ⊆ Set.range hW.fromSpec.base := by
    rw [hW.range_fromSpec]; rintro _ ⟨x, rfl⟩; exact h₀ x
  have r₁ : Set.range g₁.base ⊆ Set.range hW.fromSpec.base := by
    rw [hW.range_fromSpec]; rintro _ ⟨x, rfl⟩; exact h₁ x
  obtain ⟨φ₀, hφ₀⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec g₀ r₀)
  obtain ⟨φ₁, hφ₁⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec g₁ r₁)
  have e₀ : Spec.map φ₀ ≫ hW.fromSpec = g₀ := by rw [hφ₀]; exact IsOpenImmersion.lift_fac _ _ _
  have e₁ : Spec.map φ₁ ≫ hW.fromSpec = g₁ := by rw [hφ₁]; exact IsOpenImmersion.lift_fac _ _ _
  rw [← e₀, ← e₁] at h
  simp only [spMap, ← Category.assoc, ← Spec.map_comp, cancel_mono] at h
  rw [Spec.map_inj] at h
  have key : ∀ a, φ₀ a = Polynomial.C ((φ₀ a).eval 0) := fun a =>
    poly_eq_C_of_eq_aeval_invSelf (φ₀ a) (φ₁ a) (congrArg (fun f => f.hom a) h)
  rw [← e₀]
  simp only [spMap, ← Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact key a

end GlobalTheory
