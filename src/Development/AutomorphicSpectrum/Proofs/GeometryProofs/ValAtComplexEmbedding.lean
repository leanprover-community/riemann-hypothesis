module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.PullVal

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem genMap_stalkSpecializes (ξ : Spec (CommRingCat.of Ω) ⟶ X) {c c' : X} (hc : c' = c) (h : genPt ξ ⤳ c)
    (h' : genPt ξ ⤳ c') (s : X.presheaf.stalk c) :
    genMap ξ ⟨c', h'⟩ (X.presheaf.stalkSpecializes (specializes_of_eq hc) s) = genMap ξ ⟨c, h⟩ s := by
  subst hc
  simp [TopCat.Presheaf.stalkSpecializes_refl]

theorem closedPoint_specMap_fromSpecStalk {R : CommRingCat.{0}} [IsLocalRing R] (x : X)
    (φ : X.presheaf.stalk x ⟶ R) [IsLocalHom φ.hom] :
    (Spec.map φ ≫ X.fromSpecStalk x) (IsLocalRing.closedPoint R) = x := by
  change X.fromSpecStalk x ((Spec.map φ) (IsLocalRing.closedPoint R)) = x
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

private theorem stalkSpecializes_comp_comp_eq_of_eq {x y : X} (h1 : x ⤳ y) (h2 : y ⤳ x) (hxy : x = y)
    {R : CommRingCat.{0}} (g : X.presheaf.stalk x ⟶ R) :
    X.presheaf.stalkSpecializes h2 ≫ X.presheaf.stalkSpecializes h1 ≫ g = g := by
  subst hxy
  simp only [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

theorem stalkSpecializes_stalkClosedPointTo {K : Type} [Field K] (x : X)
    (φ : X.presheaf.stalk x ⟶ CommRingCat.of K) [IsLocalHom φ.hom]
    (hc : (Spec.map φ ≫ X.fromSpecStalk x) (IsLocalRing.closedPoint (CommRingCat.of K)) = x) :
    X.presheaf.stalkSpecializes (specializes_of_eq hc) ≫
      Scheme.stalkClosedPointTo (Spec.map φ ≫ X.fromSpecStalk x) = φ := by
  have key := (SpecToEquivOfLocalRing (X := X) (R := CommRingCat.of K)).apply_symm_apply ⟨x, ⟨φ, inferInstance⟩⟩
  obtain ⟨h, h2⟩ := SpecToEquivOfLocalRing_eq_iff.mp key
  rw [show Scheme.stalkClosedPointTo (Spec.map φ ≫ X.fromSpecStalk x) = _ from h2,
    TopCat.Presheaf.stalkCongr_hom]
  exact stalkSpecializes_comp_comp_eq_of_eq _ _ hc.symm φ

theorem valAt_of_field_map {K K' : Type} [Field K] [Field K'] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (w : Spec (CommRingCat.of K) ⟶ X) (w' : Spec (CommRingCat.of K') ⟶ X) (f : K →+* K')
    (e : Spec.map (CommRingCat.ofHom f) ≫ w = w') {a : Ω} {u : K} (hv : ValAt ξ w a u) :
    ValAt ξ w' a (f u) := by
  obtain ⟨h, s, hs, hr⟩ := hv
  subst e
  obtain ⟨ψ, hψ⟩ : ∃ ψ : X.presheaf.stalk (centre w) ⟶ CommRingCat.of K',
      ψ = Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f := ⟨_, rfl⟩
  have : IsLocalHom ψ.hom := by
    rw [show ψ.hom = f.comp (Scheme.stalkClosedPointTo w).hom by subst hψ; rfl]
    exact @RingHom.isLocalHom_comp _ _ _ _ _ _ f (Scheme.stalkClosedPointTo w).hom
      inferInstance (Scheme.isLocalHom_stalkClosedPointTo' (R := K) w)
  have hφ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk w
  have hw' : Spec.map (CommRingCat.ofHom f) ≫ w = Spec.map ψ ≫ X.fromSpecStalk (centre w) := by
    rw [hψ]
    erw [Spec.map_comp, Category.assoc]
    exact congrArg (Spec.map (CommRingCat.ofHom f) ≫ ·) hφ.symm
  rw [hw']
  have hc := closedPoint_specMap_fromSpecStalk (centre w) ψ
  have hc' : centre (Spec.map ψ ≫ X.fromSpecStalk (centre w)) = centre w := hc
  have h' : genPt ξ ⤳ centre (Spec.map ψ ≫ X.fromSpecStalk (centre w)) := by
    rw [hc']
    exact h
  refine ⟨h', X.presheaf.stalkSpecializes (specializes_of_eq hc') s, ?_, ?_⟩
  · exact (genMap_stalkSpecializes ξ hc' h h' s).trans hs
  · have H3 := stalkSpecializes_stalkClosedPointTo (centre w) ψ hc
    have H : (X.presheaf.stalkSpecializes (specializes_of_eq hc) ≫
        Scheme.stalkClosedPointTo (Spec.map ψ ≫ X.fromSpecStalk (centre w))).hom s = ψ.hom s :=
      congrArg (fun g => g.hom s) H3
    have hψs : ψ.hom s = f u := by
      rw [← hr]
      subst hψ
      rfl
    exact H.trans hψs

theorem valAt_complex : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (L : Type) [Field L] [NumberField L]
    (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ) (a : Ω) (u : L),
    ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) a u → ValAt ξ (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) a (σ u) := by
  intro X Ω _ ξ L _ _ z σ a u hv
  exact valAt_of_field_map ξ _ _ σ (by rw [← Category.assoc]; congr 1; exact (Spec.map_comp _ _).symm) hv

end GlobalTheory.CompanionTheory.Ar.RootHt.PullVal
