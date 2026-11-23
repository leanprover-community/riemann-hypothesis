module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.CubicNormMulIdentity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.RegC

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.UUA
open ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

variable (D : DegPre R)

section Descent

open IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem exists_hasVal {ϖ : V} (hϖ : Irreducible ϖ) (x : FractionRing V) (hx : x ≠ 0) : ∃ n : ℤ, HasVal ϖ x n := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨m1, u1, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨m2, u2, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hϖ
  refine ⟨(m1 : ℤ) - m2, u1 * u2⁻¹, ?_⟩
  have hp : algebraMap V (FractionRing V) ϖ ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap V (FractionRing V))]
    exact fun h => hϖ.ne_zero (IsFractionRing.injective V (FractionRing V) h)
  have hu2 : algebraMap V (FractionRing V) (u2 : V) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap V (FractionRing V))]
    exact fun h => u2.ne_zero (IsFractionRing.injective V (FractionRing V) h)
  have hinv : algebraMap V (FractionRing V) ((u2⁻¹ : Vˣ) : V) =
      (algebraMap V (FractionRing V) (u2 : V))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  simp only [Units.val_mul, map_mul, map_pow, hinv]
  rw [zpow_sub₀ hp, zpow_natCast, zpow_natCast]
  field_simp

variable {D : DegData V (maximalIdeal V)} (F : Type) [Field F] [Algebra (FractionRing V) F]

end Descent

end ReciprocityTheory.ChartRestriction.G.PullbackSections.RegC
