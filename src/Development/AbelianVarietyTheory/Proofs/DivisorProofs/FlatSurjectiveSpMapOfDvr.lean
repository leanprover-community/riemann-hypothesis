module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem flat_surjective_spMap_of_dvr : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → Flat (spMap (algebraMap R W)) ∧ Surjective (spMap (algebraMap R W)) := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  have hinj : Function.Injective (algebraMap R W) := by
    have h1 : (algebraMap W K').comp (algebraMap R W) = (algebraMap K K').comp (algebraMap R K) := by
      rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
    have h2 : Function.Injective ((algebraMap K K').comp (algebraMap R K)) :=
      (algebraMap K K').injective.comp (IsFractionRing.injective R K)
    rw [← h1] at h2
    exact Function.Injective.of_comp h2
  have hfl : Module.Flat R W := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨⟨a, ha⟩, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    change a • x = 0 at hax
    rw [Algebra.smul_def] at hax
    rcases mul_eq_zero.1 hax with h0 | h0
    · exact absurd (hinj (h0.trans (map_zero _).symm)) ha0
    · simp [h0]
  have hloc : IsLocalHom (algebraMap R W) := by
    refine ((IsLocalRing.local_hom_tfae (algebraMap R W)).out 1 3).2 ?_
    rw [h]
  have hff : Module.FaithfullyFlat R W := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hrf : (algebraMap R W).FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.2 hff
  obtain ⟨h1, h2⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R W))).2 hrf
  exact ⟨h1, h2⟩

end GlobalTheory
