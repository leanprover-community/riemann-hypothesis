module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppBijectiveOfFlatBaseChangeGlobalFunctionsStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MorDesc

theorem factor_of_isIso_appTop {X T A : Scheme.{0}} (f : X ⟶ T) [IsIso f.appTop] [IsAffine A]
    (g : X ⟶ A) : ∃ g₀ : T ⟶ A, f ≫ g₀ = g := by
  refine ⟨T.toSpecΓ ≫ Spec.map (g.appTop ≫ inv f.appTop) ≫ A.isoSpec.inv, ?_⟩
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Category.assoc (Spec.map _),
    ← Spec.map_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]

theorem morphism_descends : ∀ (R : Type) [CommRing R] (S Y Z W : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → Function.Bijective π.appTop.hom → Flat y → IsPullback p q y π → ∀ (O : Z.Opens) (h : O.toScheme ⟶ W) (y₀ : Y) (w : W), (∀ z : Z, p z = y₀ → z ∈ O) → (∀ z : O.toScheme, p (O.ι z) = y₀ → h z = w) → ∃ (V : Y.Opens) (hV : p ⁻¹ᵁ V ≤ O) (h₀ : V.toScheme ⟶ W), y₀ ∈ V ∧ (p ∣_ V) ≫ h₀ = Z.homOfLE hV ≫ h := by
  intro R _ S Y Z W π y p q hprop _ hbij hflat hpb O h y₀ w hfib hconst
  haveI : IsProper π := hprop
  haveI : IsProper p := MorphismProperty.of_isPullback (P := @IsProper) hpb.flip hprop
  obtain ⟨O', hO', hwO', -⟩ := exists_isAffineOpen_mem_and_subset (show w ∈ (⊤ : W.Opens) from trivial)
  haveI : IsAffine O'.toScheme := hO'
  let T : Z.Opens := O.ι ''ᵁ (h ⁻¹ᵁ O')
  have hTO : T ≤ O := Scheme.Opens.ι_image_le O _
  have hcl : IsClosed (p '' (T : Set Z)ᶜ) := p.isClosedMap _ T.isOpen.isClosed_compl
  let V : Y.Opens := ⟨(p '' (T : Set Z)ᶜ)ᶜ, hcl.isOpen_compl⟩
  have hVT : p ⁻¹ᵁ V ≤ T := by
    intro z hz
    by_contra hzT
    exact hz ⟨z, hzT, rfl⟩
  have hy₀ : y₀ ∈ V := by
    rintro ⟨z, hzT, hz⟩
    apply hzT
    have hzO := hfib z hz
    refine ⟨⟨z, hzO⟩, ?_, Scheme.Opens.ι_apply O _⟩
    show h ⟨z, hzO⟩ ∈ O'
    rw [hconst ⟨z, hzO⟩ (by rw [Scheme.Opens.ι_apply]; exact hz)]
    exact hwO'
  have hV : p ⁻¹ᵁ V ≤ O := hVT.trans hTO
  have hrange : Set.range (Z.homOfLE hV ≫ h) ⊆ Set.range O'.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨u, hu, hux⟩ := hVT x.2
    have : Z.homOfLE hV x = u := by
      apply Subtype.ext
      refine (Scheme.homOfLE_apply hV x).trans ?_
      exact hux.symm.trans (Scheme.Opens.ι_apply O u)
    show h (Z.homOfLE hV x) ∈ O'
    rw [this]
    exact hu
  have hg := IsOpenImmersion.lift_fac O'.ι _ hrange
  haveI hiso : IsIso (p.app (V.ι ''ᵁ ⊤)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (GlobalTheory.T.app_bijective_of_flat_baseChange_globalFunctions R S Y Z π y p q inferInstance inferInstance hbij hflat hpb _)
  haveI : IsIso (p ∣_ V).appTop := by
    rw [morphismRestrict_appTop]
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ hiso ?_
    first
      | exact Functor.map_isIso _ _
      | exact (Z.presheaf.mapIso (eqToIso _).op).isIso_hom
      | (apply Functor.map_isIso)
  obtain ⟨g₀, hg₀⟩ := factor_of_isIso_appTop (p ∣_ V) (IsOpenImmersion.lift O'.ι _ hrange)
  refine ⟨V, hV, g₀ ≫ O'.ι, hy₀, ?_⟩
  rw [← Category.assoc, hg₀, hg]

end GlobalTheory.MorDesc
