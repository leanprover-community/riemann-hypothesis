module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_nhds_nonzero_of_isClosedMap :
    ∀ (Z Y : Scheme.{0}) (p : Z ⟶ Y), IsClosedMap p.base → ∀ (L : LB Z) (V : Y.Opens) (u : LB.Sec (L.pull (p ⁻¹ᵁ V).ι)) (y : Y), y ∈ V → (∀ z : (p ⁻¹ᵁ V).toScheme, p ((p ⁻¹ᵁ V).ι z) = y → z ∈ nonzeroLocus u) → ∃ V₁ : Y.Opens, y ∈ V₁ ∧ V₁ ≤ V ∧ ∀ z : (p ⁻¹ᵁ V).toScheme, p ((p ⁻¹ᵁ V).ι z) ∈ V₁ → z ∈ nonzeroLocus u := by
  intro Z Y p hp L V u y hy h
  have hO : IsOpen ((p ⁻¹ᵁ V).ι '' (nonzeroLocus u : Set (p ⁻¹ᵁ V).toScheme)) :=
    (p ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap _ (nonzeroLocus u).isOpen
  have hC : IsClosed (p.base '' ((p ⁻¹ᵁ V).ι '' (nonzeroLocus u : Set (p ⁻¹ᵁ V).toScheme))ᶜ) :=
    hp _ hO.isClosed_compl
  refine ⟨V ⊓ ⟨_, hC.isOpen_compl⟩, ⟨hy, ?_⟩, inf_le_left, ?_⟩
  · rintro ⟨c, hc, hcy⟩
    have hcV : c ∈ p ⁻¹ᵁ V := by
      change p c ∈ V
      have : p c = y := hcy
      rw [this]; exact hy
    exact hc ⟨⟨c, hcV⟩, h ⟨c, hcV⟩ hcy, rfl⟩
  · intro z hz
    have h2 : (p ⁻¹ᵁ V).ι z ∈ (p ⁻¹ᵁ V).ι '' (nonzeroLocus u : Set (p ⁻¹ᵁ V).toScheme) := by
      by_contra hn
      exact hz.2 ⟨_, hn, rfl⟩
    obtain ⟨w, hw, hwz⟩ := h2
    have : w = z := (p ⁻¹ᵁ V).ι.isOpenEmbedding.injective hwz
    subst this
    exact hw

end GlobalTheory.Mum
