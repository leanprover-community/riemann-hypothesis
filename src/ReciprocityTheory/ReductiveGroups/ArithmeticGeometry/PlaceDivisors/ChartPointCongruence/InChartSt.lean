module

public import Mathlib.RingTheory.AdicCompletion.Basic
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
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt

attribute [local instance] Over.cartesianMonoidalCategory

def SepSt : Prop :=
  ∀ (T A O : Type) [CommRing T] [CommRing A] [Algebra T A] [CommRing O] [Algebra T O] (p : O),
    IsHausdorff (Ideal.span {p}) O → ∀ h h' : A →ₐ[T] O,
      (∀ n : ℕ, (Ideal.Quotient.mkₐ T (Ideal.span {p ^ n})).comp h = (Ideal.Quotient.mkₐ T _).comp h') → h = h'

def AlgLimSt : Prop :=
  ∀ (T A O : Type) [CommRing T] [CommRing A] [Algebra T A] [CommRing O] [Algebra T O] (p : O),
    IsAdicComplete (Ideal.span {p}) O → ∀ a : ∀ n : ℕ, A →ₐ[T] O ⧸ Ideal.span {p ^ n},
      (∀ (n : ℕ) (z : A) (y : O), Ideal.Quotient.mk _ y = a (n + 1) z → Ideal.Quotient.mk _ y = a n z) →
      ∃ h : A →ₐ[T] O, ∀ n, (Ideal.Quotient.mkₐ T (Ideal.span {p ^ n})).comp h = a n

end ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
