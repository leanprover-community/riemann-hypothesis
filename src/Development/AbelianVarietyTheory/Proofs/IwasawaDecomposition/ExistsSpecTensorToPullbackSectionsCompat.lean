module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory

theorem fromSpec_appLE_self_top {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) (e : ⊤ ≤ hW.fromSpec ⁻¹ᵁ W) :
    hW.fromSpec.appLE W ⊤ e = (Scheme.ΓSpecIso Γ(Y, W)).inv := by
  rw [Scheme.Hom.appLE, hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  rw [show (eqToHom hW.fromSpec_preimage_self).op ≫ (homOfLE e).op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id, Category.comp_id]

theorem appLE_SpecMap_comp_fromSpec_hom {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) {S : CommRingCat.{0}}
    (φ : Γ(Y, W) ⟶ S) (h : ⊤ ≤ (Spec.map φ ≫ hW.fromSpec) ⁻¹ᵁ W) :
    (Spec.map φ ≫ hW.fromSpec).appLE W ⊤ h ≫ (Scheme.ΓSpecIso S).hom = φ := by
  have e1 : (⊤ : (Spec Γ(Y, W)).Opens) ≤ hW.fromSpec ⁻¹ᵁ W := by simp
  have e2 : (⊤ : (Spec S).Opens) ≤ Spec.map φ ⁻¹ᵁ ⊤ := by simp
  have e3 : (Spec.map φ).appLE ⊤ ⊤ e2 = (Spec.map φ).appTop := (Spec.map φ).appLE_eq_app
  have e4 := Scheme.Hom.appLE_comp_appLE (Spec.map φ) hW.fromSpec W ⊤ ⊤ e1 e2
  rw [← e4, fromSpec_appLE_self_top, e3, Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

theorem appLE_SpecMap_comp_fromSpec {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) {S : CommRingCat.{0}}
    (φ : Γ(Y, W) ⟶ S) (h : ⊤ ≤ (Spec.map φ ≫ hW.fromSpec) ⁻¹ᵁ W) (c : Γ(Y, W)) :
    (Scheme.ΓSpecIso S).hom.hom (((Spec.map φ ≫ hW.fromSpec).appLE W ⊤ h).hom c) = φ.hom c := by
  rw [← CommRingCat.comp_apply, appLE_SpecMap_comp_fromSpec_hom]

theorem specTensor_to_pullback : ∀ {X Y' : Scheme.{0}} (ρ : Y' ⟶ X) {R : Type} [CommRing R] (ξ : Sp R ⟶ X) (U : X.affineOpens) (hle : ⊤ ≤ ξ ⁻¹ᵁ (U : X.Opens)) (W : Y'.affineOpens) (hW : (W : Y'.Opens) ≤ ρ ⁻¹ᵁ (U : X.Opens)), letI := (ρ.appLE U W hW).hom.toAlgebra; letI := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra; ∃ (κ : Spec (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R)) ⟶ pullback ξ ρ) (hκ : ⊤ ≤ (κ ≫ pullback.snd ξ ρ) ⁻¹ᵁ (W : Y'.Opens)), (∀ c : Γ(Y', W), (Scheme.ΓSpecIso _).hom.hom (((κ ≫ pullback.snd ξ ρ).appLE W ⊤ hκ).hom c) = c ⊗ₜ[Γ(X, U)] (1 : R)) ∧ ∀ r : R, (Scheme.ΓSpecIso _).hom.hom (κ.appTop.hom ((pullback.fst ξ ρ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = (1 : Γ(Y', W)) ⊗ₜ[Γ(X, U)] r := by
  intro X Y' ρ R _ ξ U hle W hW
  letI := (ρ.appLE U W hW).hom.toAlgebra
  letI := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra
  let incL : Γ(Y', W) →+* Γ(Y', W) ⊗[Γ(X, U)] R := Algebra.TensorProduct.includeLeftRingHom
  let incR : R →ₐ[Γ(X, U)] Γ(Y', W) ⊗[Γ(X, U)] R := Algebra.TensorProduct.includeRight
  have hξ : Spec.map (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) ≫ U.2.fromSpec = ξ := by
    rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec ξ U.2 (isAffineOpen_top _) hle,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id,
      Category.id_comp]
  have hρ : W.2.fromSpec ≫ ρ = Spec.map (ρ.appLE U W hW) ≫ U.2.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec ρ U.2 W.2 hW).symm
  have hring : (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) ≫ CommRingCat.ofHom incR.toRingHom =
      ρ.appLE U W hW ≫ CommRingCat.ofHom incL := by
    ext b
    exact (incR.commutes b).trans ((Algebra.TensorProduct.includeLeft (R := Γ(X, U)) (S := Γ(X, U))
      (A := Γ(Y', W)) (B := R)).commutes b).symm
  have hw : Spec.map (CommRingCat.ofHom incR.toRingHom) ≫ ξ =
      (Spec.map (CommRingCat.ofHom incL) ≫ W.2.fromSpec) ≫ ρ := by
    refine (congrArg (Spec.map (CommRingCat.ofHom incR.toRingHom) ≫ ·) hξ.symm).trans ?_
    rw [Category.assoc, hρ, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hring]
  let κ := pullback.lift _ _ hw
  have hsnd : κ ≫ pullback.snd ξ ρ = Spec.map (CommRingCat.ofHom incL) ≫ W.2.fromSpec := pullback.lift_snd _ _ _
  have hfst : κ ≫ pullback.fst ξ ρ = Spec.map (CommRingCat.ofHom incR.toRingHom) := pullback.lift_fst _ _ _
  have hκ : ⊤ ≤ (κ ≫ pullback.snd ξ ρ) ⁻¹ᵁ (W : Y'.Opens) := by
    rw [hsnd]
    intro x _
    show (Spec.map (CommRingCat.ofHom incL) ≫ W.2.fromSpec) x ∈ (W : Set Y')
    rw [Scheme.Hom.comp_apply, ← W.2.range_fromSpec]
    exact ⟨_, rfl⟩
  refine ⟨κ, hκ, fun c => ?_, fun r => ?_⟩
  · have key : ∀ (f : Spec (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R)) ⟶ Y')
        (_ : f = Spec.map (CommRingCat.ofHom incL) ≫ W.2.fromSpec) (h' : ⊤ ≤ f ⁻¹ᵁ (W : Y'.Opens)),
        (Scheme.ΓSpecIso _).hom.hom ((f.appLE W ⊤ h').hom c) = c ⊗ₜ[Γ(X, U)] (1 : R) := by
      rintro f rfl h'
      exact appLE_SpecMap_comp_fromSpec W.2 (CommRingCat.ofHom incL) h' c
    exact key _ hsnd hκ
  · rw [← CommRingCat.comp_apply (pullback.fst ξ ρ).appTop κ.appTop, ← Scheme.Hom.comp_appTop, hfst,
      ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    rfl

end GlobalTheory
