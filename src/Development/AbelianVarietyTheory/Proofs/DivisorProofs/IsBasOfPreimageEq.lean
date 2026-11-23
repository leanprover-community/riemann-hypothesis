module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

theorem isBas_of_preimage_eq (X X₀ : Scheme.{0}) (i : X₀ ⟶ X) [IsClosedImmersion i] [Surjective i] (C : Type)
    [Category.{0} C] (V : C → X.Opens) (V₀ : C → X₀.Opens) (hV : ∀ T, i ⁻¹ᵁ V T = V₀ T) (h : IsBas V₀) :
    IsBas V := by
  have hle : ∀ (t : C) (U : X.Opens), V₀ t ≤ i ⁻¹ᵁ U → V t ≤ U := by
    intro t U htU z hz
    obtain ⟨w, rfl⟩ := i.surjective z
    have hw : w ∈ V₀ t := by rw [← hV t]; exact hz
    exact htU hw
  have hmem : ∀ (t : C) (y : X₀), y ∈ V₀ t → i y ∈ V t := by
    intro t y hy
    rw [← hV t] at hy
    exact hy
  have hmem' : ∀ (t : C) (y : X₀), i y ∈ V t → y ∈ V₀ t := by
    intro t y hy
    rw [← hV t]
    exact hy
  refine ⟨fun x U hx ↦ ?_, fun t₁ t₂ x U hx h₁ h₂ ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := i.surjective x
    obtain ⟨t, hyt, htU⟩ := h.1 y (i ⁻¹ᵁ U) hx
    exact ⟨t, hmem t y hyt, hle t U htU⟩
  · obtain ⟨y, rfl⟩ := i.surjective x
    obtain ⟨t₃, a₁, a₂, hy₃, h₃U⟩ := h.2 t₁ t₂ y (i ⁻¹ᵁ U) hx (hmem' t₁ y h₁) (hmem' t₂ y h₂)
    exact ⟨t₃, a₁, a₂, hmem t₃ y hy₃, hle t₃ U h₃U⟩

end GlobalTheory.LBObs
