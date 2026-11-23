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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.factor_closedImmersion_of_affine_points :
    ∀ {X Z T : Scheme.{0}} (i : Z ⟶ X), IsClosedImmersion i → ∀ (g : T ⟶ X),
      (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ T), ∃ y : Sp R' ⟶ Z, y ≫ i = x ≫ g) →
      ∃ z : T ⟶ Z, z ≫ i = g := by
  intro X Z T i hi g h
  let 𝒰 := T.affineCover
  have hj : ∀ j, ∃ y : 𝒰.X j ⟶ Z, y ≫ i = 𝒰.f j ≫ g := fun j => h _ (𝒰.f j)
  choose y hy using hj
  have hc : ∀ a b, pullback.fst (𝒰.f a) (𝒰.f b) ≫ y a = pullback.snd (𝒰.f a) (𝒰.f b) ≫ y b := by
    intro a b
    rw [← cancel_mono i, Category.assoc, Category.assoc, hy, hy, ← Category.assoc, ← Category.assoc,
      pullback.condition]
  refine ⟨𝒰.glueMorphisms y hc, ?_⟩
  refine 𝒰.hom_ext _ _ fun j => ?_
  rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, hy]
