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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open PrimeSpectrum in
theorem prime_line_mem_range_comap_mapRingHom {R K : Type} [CommRing R] [Field K] (χ : R →+* K)
    (hχ : Function.Surjective χ) (P : PrimeSpectrum (Polynomial R))
    (hP : PrimeSpectrum.comap (algebraMap R (Polynomial R)) P = PrimeSpectrum.comap χ (IsLocalRing.closedPoint K)) :
    P ∈ Set.range (PrimeSpectrum.comap (Polynomial.mapRingHom χ)) := by
  have hker : RingHom.ker χ ≤ Ideal.comap Polynomial.C P.asIdeal := by
    intro a ha
    have h1 := congrArg PrimeSpectrum.asIdeal hP
    simp only [PrimeSpectrum.comap_asIdeal] at h1
    have : a ∈ Ideal.comap (algebraMap R (Polynomial R)) P.asIdeal := by
      rw [h1, Ideal.mem_comap, RingHom.mem_ker.mp ha]
      exact Ideal.zero_mem _
    exact this
  rw [range_comap_of_surjective _ _ (Polynomial.map_surjective χ hχ), PrimeSpectrum.mem_zeroLocus,
    Polynomial.ker_mapRingHom, SetLike.coe_subset_coe]
  exact Ideal.map_le_iff_le_comap.mpr hker

theorem fibre_line_over_surjection : ∀ (R K : Type) [CommRing R] [Field K] (χ : R →+* K), Function.Surjective χ → ∀ (x : Sp (Polynomial R)), spMap (algebraMap R (Polynomial R)) x = spMap χ (IsLocalRing.closedPoint K) → x ∈ Set.range (spMap (Polynomial.mapRingHom χ)) := by
  intro R K _ _ χ hχ x hx
  exact prime_line_mem_range_comap_mapRingHom χ hχ x hx

end GlobalTheory
