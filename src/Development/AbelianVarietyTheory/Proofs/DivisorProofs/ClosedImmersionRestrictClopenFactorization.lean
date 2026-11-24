module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem clopen_cut_closedImmersion : ∀ {X Z₁ : Scheme.{0}} (i : Z₁ ⟶ X), IsClosedImmersion i → ∀ (U : X.Opens), IsClosed (U : Set X) → ∃ (Z : Scheme.{0}) (j : Z ⟶ X), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X), ((∃ z : T ⟶ Z, z ≫ j = g) ↔ (∃ y : T ⟶ Z₁, y ≫ i = g) ∧ Set.range g.base ⊆ (U : Set X)) := by
  intro X Z₁ i hi U hU
  have hVc : IsClosed (Set.range (i ⁻¹ᵁ U).ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact hU.preimage i.base.hom.continuous
  haveI : IsClosedImmersion (i ⁻¹ᵁ U).ι := IsClosedImmersion.of_isPreimmersion _ hVc
  refine ⟨(i ⁻¹ᵁ U), (i ⁻¹ᵁ U).ι ≫ i, inferInstance, fun T g => ?_⟩
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨⟨z ≫ (i ⁻¹ᵁ U).ι, by simp⟩, ?_⟩
    rintro _ ⟨t, rfl⟩
    have : ((i ⁻¹ᵁ U).ι.base (z.base t)) ∈ (i ⁻¹ᵁ U : Set Z₁) := by
      rw [← Scheme.Opens.range_ι]; exact ⟨_, rfl⟩
    simpa [Scheme.Hom.comp_base] using this
  · rintro ⟨⟨y, rfl⟩, hg⟩
    have h : Set.range y.base ⊆ Set.range (i ⁻¹ᵁ U).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      have := hg ⟨t, rfl⟩
      simpa using this
    exact ⟨IsOpenImmersion.lift (i ⁻¹ᵁ U).ι y h, by rw [← Category.assoc, IsOpenImmersion.lift_fac]⟩

end GlobalTheory
