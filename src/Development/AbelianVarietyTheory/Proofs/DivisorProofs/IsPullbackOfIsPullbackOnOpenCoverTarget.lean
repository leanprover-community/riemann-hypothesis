module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem isPullback_of_openCover_target : ∀ (X G S B : Scheme.{0}) (β : X ⟶ G) (f : X ⟶ S) (g : G ⟶ B) (π : S ⟶ B), β ≫ g = f ≫ π → ∀ (J : Type) (Y P : J → Scheme.{0}) (ψ : ∀ j, Y j ⟶ G) (e : ∀ j, P j ⟶ X) (p : ∀ j, P j ⟶ Y j) (q : ∀ j, P j ⟶ S), (∀ j, IsOpenImmersion (ψ j)) → (∀ y : G, ∃ j, y ∈ Set.range (ψ j)) → (∀ j, IsOpenImmersion (e j)) → (∀ j, IsPullback (p j) (q j) (ψ j ≫ g) π) → (∀ j, e j ≫ β = p j ≫ ψ j) → (∀ j, e j ≫ f = q j) → (∀ (j : J) (x : X), β x ∈ Set.range (ψ j) → x ∈ Set.range (e j)) → IsPullback β f g π := by
  intro X G S B β f g π w J Y P ψ e p q hψ hcov he hP hβ hf hr
  let ψ' : ∀ j, P j ⟶ pullback g π := fun j =>
    pullback.lift (p j ≫ ψ j) (q j) (by rw [Category.assoc]; exact (hP j).w)
  have hψ'f : ∀ j, ψ' j ≫ pullback.fst g π = p j ≫ ψ j := fun j => pullback.lift_fst _ _ _
  have hψ's : ∀ j, ψ' j ≫ pullback.snd g π = q j := fun j => pullback.lift_snd _ _ _
  have sq : ∀ j, IsPullback (ψ' j) (p j) (pullback.fst g π) (ψ j) := fun j =>
    (IsPullback.of_bot (v₁₁ := ψ' j) (v₂₁ := pullback.snd g π) (by rw [hψ's]; exact hP j)
      (hψ'f j).symm (IsPullback.of_hasPullback g π)).flip
  haveI : ∀ j, IsOpenImmersion (ψ' j) := fun j =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (sq j).flip (hψ j)
  have hc : ∀ z : (pullback g π : Scheme), ∃ j y, ψ' j y = z := by
    intro z
    obtain ⟨j, y, hy⟩ := hcov (pullback.fst g π z)
    obtain ⟨t, ht, -⟩ := Scheme.exists_preimage_of_isPullback (sq j) z y hy.symm
    exact ⟨j, t, ht⟩
  let c : X ⟶ pullback g π := pullback.lift β f w
  have hcf : c ≫ pullback.fst g π = β := pullback.lift_fst _ _ _
  have hce : ∀ j, e j ≫ c = ψ' j := fun j => by
    apply pullback.hom_ext
    · rw [Category.assoc, hcf, hβ, hψ'f]
    · rw [Category.assoc, pullback.lift_snd, hf, hψ's]
  have loc : ∀ j, IsPullback (e j) (𝟙 (P j)) c (ψ' j) := fun j => by
    haveI := he j
    refine (IsOpenImmersion.isPullback (𝟙 (P j)) (e j) (ψ' j) c
      (by rw [hce, Category.id_comp]) ?_).flip
    ext x
    change c x ∈ Set.range (ψ' j) ↔ x ∈ Set.range (e j)
    constructor
    · rintro ⟨y, hy⟩
      apply hr j x
      refine ⟨p j y, ?_⟩
      rw [← hcf, Scheme.Hom.comp_apply, ← hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hψ'f]
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [← Scheme.Hom.comp_apply, hce]⟩
  have key : ∀ j : J, (MorphismProperty.isomorphisms Scheme) (pullback.snd c (ψ' j)) := fun j => by
    rw [← (loc j).isoPullback_inv_snd,
      MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.isomorphisms Scheme)]
    exact MorphismProperty.isomorphisms.infer_property _
  have hiso : (MorphismProperty.isomorphisms Scheme) c :=
    IsZariskiLocalAtTarget.of_openCover (Scheme.Cover.mkOfCovers J P ψ' hc) fun j => key j
  haveI : IsIso c := hiso
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end GlobalTheory.Mum
