module

public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory

theorem exponent_uniformiser_unique {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {ϖ : V} (hϖ : Irreducible ϖ) (a b : ℤ) (w w' : Vˣ)
    (h : algebraMap V (FractionRing V) ϖ ^ a * algebraMap V (FractionRing V) (w : V) =
      algebraMap V (FractionRing V) ϖ ^ b * algebraMap V (FractionRing V) (w' : V)) : a = b := by
  have hinj : Function.Injective (algebraMap V (FractionRing V)) :=
    IsFractionRing.injective V (FractionRing V)
  have hx : algebraMap V (FractionRing V) ϖ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact hϖ.ne_zero
  have hw : algebraMap V (FractionRing V) (w : V) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact w.ne_zero
  have key : ∀ (n : ℕ) (u : Vˣ), algebraMap V (FractionRing V) ϖ ^ n =
      algebraMap V (FractionRing V) (u : V) → n = 0 := by
    intro n u hn
    rw [← map_pow] at hn
    have h1 := hinj hn
    by_contra hne
    apply hϖ.not_isUnit
    rw [← isUnit_pow_iff hne, h1]; exact u.isUnit
  have hab : algebraMap V (FractionRing V) ϖ ^ (a - b) =
      algebraMap V (FractionRing V) ((w' * w⁻¹ : Vˣ) : V) := by
    rw [zpow_sub₀ hx, Units.val_mul, map_mul, map_units_inv, div_eq_iff (zpow_ne_zero _ hx)]
    field_simp
    linear_combination h
  rcases Int.eq_nat_or_neg (a - b) with ⟨n, hn | hn⟩
  · rw [hn, zpow_natCast] at hab
    have := key n _ hab
    omega
  · rw [hn, zpow_neg, zpow_natCast] at hab
    have h2 : algebraMap V (FractionRing V) ϖ ^ n =
        algebraMap V (FractionRing V) (((w' * w⁻¹)⁻¹ : Vˣ) : V) := by
      rw [map_units_inv, ← hab, inv_inv]
    have := key n _ h2
    omega

end GlobalTheory
