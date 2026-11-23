module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct

namespace GlobalTheory

theorem finiteFlatSurj_affine_algebra : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian Y] (V₀ : Y.Opens), IsAffineOpen V₀ →
    letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
    IsNoetherianRing Γ(Y, V₀) ∧ Module.Finite Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) ∧ Module.FaithfullyFlat Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := by
  intro X Y f _ _ _ _ V₀ hV₀
  letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
  have hV : IsAffineOpen (f ⁻¹ᵁ V₀) := hV₀.preimage f
  refine ⟨IsLocallyNoetherian.component_noetherian ⟨V₀, hV₀⟩, ?_, ?_⟩
  · exact IsFinite.finite_app f V₀ hV₀
  · have hflat : (f.app V₀).hom.Flat := by
      have := Flat.flat_appLE f hV₀ hV le_rfl
      rwa [Scheme.Hom.appLE_eq_app] at this
    haveI : Module.Flat Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := hflat
    apply Module.FaithfullyFlat.of_comap_surjective
    intro p
    have hsq := IsAffineOpen.SpecMap_appLE_fromSpec f hV₀ hV le_rfl
    rw [Scheme.Hom.appLE_eq_app] at hsq
    have hy : hV₀.fromSpec p ∈ (V₀ : Set Y) := by
      rw [← hV₀.range_fromSpec]; exact ⟨p, rfl⟩
    obtain ⟨x, hx⟩ := f.surjective (hV₀.fromSpec p)
    have hxV : x ∈ Set.range hV.fromSpec := by
      rw [hV.range_fromSpec]
      show f x ∈ (V₀ : Set Y)
      rw [hx]; exact hy
    obtain ⟨q, rfl⟩ := hxV
    refine ⟨q, ?_⟩
    apply hV₀.fromSpec.isOpenEmbedding.injective
    have := congrArg (fun g => g q) (congrArg (fun h => h.base) hsq)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
    rw [← hx]
    convert this using 2
    rw [Spec.map_base]
    rfl

end GlobalTheory
