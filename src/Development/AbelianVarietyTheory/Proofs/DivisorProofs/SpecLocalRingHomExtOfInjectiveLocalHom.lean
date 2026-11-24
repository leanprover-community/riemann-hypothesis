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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.spec_local_hom_ext_of_injective (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (φ : R →+* R') (hl : IsLocalHom φ) (hi : Function.Injective φ) (Y : Scheme.{0}) (x y : Sp R ⟶ Y)
    (h : spMap φ ≫ x = spMap φ ≫ y) : x = y := by
  have hc : (spMap φ) (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R := by
    have : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom φ)) := hl
    exact Spec_closedPoint (R := CommRingCat.of R) (S := CommRingCat.of R') (f := CommRingCat.ofHom φ)
  have hp : x (IsLocalRing.closedPoint R) = y (IsLocalRing.closedPoint R) := by
    rw [← hc]
    change (spMap φ ≫ x) (IsLocalRing.closedPoint R') = (spMap φ ≫ y) (IsLocalRing.closedPoint R')
    rw [h]
  obtain ⟨p, hpx⟩ : ∃ p, x (IsLocalRing.closedPoint R) = p := ⟨_, rfl⟩
  have ex : ∀ z : Sp R ⟶ Y, z (IsLocalRing.closedPoint R) = p →
      ∃ a, Spec.map a ≫ Y.fromSpecStalk p = z := by
    intro z hz
    subst hz
    exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of R) z⟩
  obtain ⟨a, rfl⟩ := ex x hpx
  obtain ⟨b, rfl⟩ := ex y (hp ▸ hpx)
  have h2 : spMap φ ≫ Spec.map a = spMap φ ≫ Spec.map b := by
    rw [← Category.assoc, ← Category.assoc] at h
    exact (cancel_mono _).1 h
  have h3 : a ≫ CommRingCat.ofHom φ = b ≫ CommRingCat.ofHom φ := by
    apply Spec.map_injective
    simpa [spMap, Spec.map_comp] using h2
  have hab : a = b := by
    ext s
    apply hi
    have := congrArg (fun g => g.hom s) h3
    simpa using this
  rw [hab]
