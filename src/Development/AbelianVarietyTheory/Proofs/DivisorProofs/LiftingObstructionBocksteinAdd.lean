module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem Bock_add : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (h₀ : φ₀ ≫ s = s₀ ≫ spMap σ₀) (x x' : HO1 s') (z z' : HO2 s₀), Bock h h₀ t x z → Bock h h₀ t x' z' → Bock h h₀ t (x + x') (z + z') := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ x x' z z'
  rintro ⟨f, w, hd, ⟨c, hc, hcx⟩, ⟨e, he, hez⟩⟩ ⟨f', w', hd', ⟨c', hc', hcx'⟩, ⟨e', he', hez'⟩⟩
  refine ⟨f + f', w + w', by rw [map_add (f := _), hd, hd', smul_add], ⟨c + c', fun p q a ↦ ?_, ?_⟩,
    ⟨e + e', fun p q r a b ↦ ?_, ?_⟩⟩
  · simp only [Submodule.coe_add, Pi.add_apply, hc, hc', map_add (f := _)]
  · rw [map_add (f := _), hcx, hcx', map_add (f := _)]
  · simp only [Submodule.coe_add, Pi.add_apply, he, he', map_add (f := _)]
  · rw [map_add (f := _), hez, hez', map_add (f := _)]

end GlobalTheory.AbCoh
