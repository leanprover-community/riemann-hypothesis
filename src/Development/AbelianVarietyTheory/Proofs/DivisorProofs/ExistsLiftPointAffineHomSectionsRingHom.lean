module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

namespace GlobalTheory.AffinePointLift

theorem specMap_fromSpec_appLE {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {R : CommRingCat.{0}}
    (g : Γ(X, U) ⟶ R) (h : ⊤ ≤ (Spec.map g ≫ hU.fromSpec) ⁻¹ᵁ U) :
    (Spec.map g ≫ hU.fromSpec).appLE U ⊤ h ≫ (Scheme.ΓSpecIso R).hom = g := by
  have h0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have e0 : hU.fromSpec.appLE U ⊤ h0 = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  have e : (Spec.map g ≫ hU.fromSpec).appLE U ⊤ h = hU.fromSpec.appLE U ⊤ h0 ≫ (Spec.map g).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [e, e0, Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

theorem specMap_appLE_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {R : CommRingCat.{0}}
    (ξ : Spec R ⟶ X) (h : ⊤ ≤ ξ ⁻¹ᵁ U) :
    Spec.map (ξ.appLE U ⊤ h ≫ (Scheme.ΓSpecIso R).hom) ≫ hU.fromSpec = ξ := by
  rw [Spec.map_comp, Category.assoc, hU.SpecMap_appLE_fromSpec ξ (isAffineOpen_top _), IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem exists_lift : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsAffineHom π], ∀ (U : Z.affineOpens) (V V' : Type) [CommRing V]
    [IsLocalRing V] [CommRing V'] [IsLocalRing V'] (ξ : Sp V ⟶ Z) (hξ : ⊤ ≤ ξ ⁻¹ᵁ U.1) (f : V →+* V')
    (ρ : Γ(Y, π ⁻¹ᵁ U.1) →+* V'),
    ρ.comp (π.app U.1).hom = f.comp (ξ.appLE U.1 ⊤ hξ ≫ (Scheme.ΓSpecIso (.of V)).hom).hom →
    ∃ ψ : Sp V' ⟶ Y, ψ ≫ π = spMap f ≫ ξ ∧
      ∀ I : Y.IdealSheafData, idlAlong I ψ = (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩).map ρ := by
  intro Y Z π _ U V V' _ _ _ _ ξ hξ f ρ h
  have hW : IsAffineOpen (π ⁻¹ᵁ U.1) := U.2.preimage π
  let g : Γ(Y, π ⁻¹ᵁ U.1) ⟶ CommRingCat.of V' := CommRingCat.ofHom ρ
  refine ⟨Spec.map g ≫ hW.fromSpec, ?_, fun I => ?_⟩
  · have e : π.appLE U.1 (π ⁻¹ᵁ U.1) le_rfl ≫ g =
        (ξ.appLE U.1 ⊤ hξ ≫ (Scheme.ΓSpecIso (.of V)).hom) ≫ CommRingCat.ofHom f := by
      rw [← Scheme.Hom.app_eq_appLE]
      exact CommRingCat.hom_ext h
    rw [Category.assoc, ← U.2.SpecMap_appLE_fromSpec π hW le_rfl, ← Spec.map_comp_assoc, e, Spec.map_comp,
      Category.assoc, specMap_appLE_fromSpec U.2 ξ hξ]
  · have hle : ⊤ ≤ (Spec.map g ≫ hW.fromSpec) ⁻¹ᵁ (π ⁻¹ᵁ U.1) :=
      fun q _ => hW.fromSpec_preimage_self.ge (x := Spec.map g q) trivial
    rw [GlobalTheory.TraitOrder.idlAlong_eq_map I _ ⟨π ⁻¹ᵁ U.1, hW⟩ hle]
    exact congrArg (fun k : Γ(Y, π ⁻¹ᵁ U.1) ⟶ CommRingCat.of V' => Ideal.map k.hom _)
      (specMap_fromSpec_appLE hW g hle)

end GlobalTheory.AffinePointLift
