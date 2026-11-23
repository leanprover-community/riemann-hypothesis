module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LiftLocal

theorem toStalk_bijective (R : Type) [CommRing R] [IsLocalRing R] (q : PrimeSpectrum R)
    (hq : q = IsLocalRing.closedPoint R) : Function.Bijective (StructureSheaf.toStalk R q).hom := by
  subst hq
  let e := IsLocalization.atUnits R (IsLocalRing.closedPoint R).asIdeal.primeCompl
    (S := (Spec.structureSheaf R).presheaf.stalk (IsLocalRing.closedPoint R)) (fun y hy => by
      rw [IsUnit.mem_submonoid_iff]
      by_contra h
      exact hy ((IsLocalRing.mem_maximalIdeal y).mpr h))
  have : ⇑(StructureSheaf.toStalk R (IsLocalRing.closedPoint R)).hom = ⇑e :=
    funext fun r => (e.commutes r).symm
  rw [this]
  exact e.bijective

theorem isLocalHom_of_bijective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Bijective f) : IsLocalHom f :=
  ⟨fun a ha => by
    have h2 : (RingEquiv.ofBijective f hf).symm (f a) = a := (RingEquiv.ofBijective f hf).symm_apply_apply a
    rw [← h2]
    exact ha.map _⟩

theorem lift : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X Y : Scheme.{0}) (π : Y ⟶ X) [IsAffineHom π] [Flat π]
    [Surjective π] (x : Sp R ⟶ X), ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (φ : R →+* R'),
    IsLocalHom φ ∧ Function.Injective φ ∧ ∃ x' : Sp R' ⟶ Y, x' ≫ π = spMap φ ≫ x := by
  intro R _ _ X Y π _ _ _ x
  obtain ⟨p, hp⟩ := (pullback.fst x π).surjective (IsLocalRing.closedPoint R)
  have hb := toStalk_bijective R _ hp
  have hτ : IsLocalHom (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom := isLocalHom_of_bijective _ hb
  letI : Algebra ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p) :=
    ((pullback.fst x π).stalkMap p).hom.toAlgebra
  haveI : Module.Flat ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p) :=
    Flat.stalkMap (pullback.fst x π) p
  haveI : IsLocalHom (algebraMap ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p)) :=
    inferInstanceAs (IsLocalHom ((pullback.fst x π).stalkMap p).hom)
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := (Sp R).presheaf.stalk ((pullback.fst x π) p)) (B := (pullback x π).presheaf.stalk p)
  have hψ : Function.Injective ((pullback.fst x π).stalkMap p).hom := FaithfulSMul.algebraMap_injective _ _
  have hψl : IsLocalHom ((pullback.fst x π).stalkMap p).hom := inferInstance
  refine ⟨(pullback x π).presheaf.stalk p, inferInstance, inferInstance,
    ((pullback.fst x π).stalkMap p).hom.comp (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom,
    ⟨fun a ha => hτ.map_nonunit a (hψl.map_nonunit _ ha)⟩, hψ.comp hb.1,
    (pullback x π).fromSpecStalk p ≫ pullback.snd x π, ?_⟩
  have hS : spMap (((pullback.fst x π).stalkMap p).hom.comp (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom) =
      Spec.map ((pullback.fst x π).stalkMap p) ≫ (Sp R).fromSpecStalk ((pullback.fst x π) p) := by
    rw [AlgebraicGeometry.Spec.fromSpecStalk_eq']
    exact (Spec.map_comp (StructureSheaf.toStalk R ((pullback.fst x π) p)) ((pullback.fst x π).stalkMap p))
  rw [Category.assoc, ← pullback.condition, hS, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]

end GlobalTheory.LiftLocal
