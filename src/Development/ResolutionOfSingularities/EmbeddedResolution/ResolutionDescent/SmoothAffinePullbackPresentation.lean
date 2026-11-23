module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothAffineLiftRelativeDimension
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace PresentedSmoothChart

theorem smooth_specMap_comp_isoSpec_inv {A : Scheme.{u}} [AlgebraicGeometry.IsAffine A]
    {B' : CommRingCat.{u}} (σ : Γ(A, ⊤) ⟶ B')
    (hσ : RingHom.IsStandardSmooth (CommRingCat.Hom.hom σ)) :
    AlgebraicGeometry.Smooth (Spec.map σ ≫ A.isoSpec.inv) := by
  have hs : RingHom.Smooth (CommRingCat.Hom.hom σ) := by
    let := (CommRingCat.Hom.hom σ).toAlgebra
    have : Algebra.IsStandardSmooth ↥Γ(A, ⊤) ↥B' := hσ
    exact ⟨inferInstance, inferInstance⟩
  have h1 : AlgebraicGeometry.Smooth (Spec.map σ) :=
    (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Smooth)).mpr hs
  have h2 : AlgebraicGeometry.Smooth A.isoSpec.inv := inferInstance
  exact MorphismProperty.comp_mem (@AlgebraicGeometry.Smooth) _ _ h1 h2

theorem exists_affineOpen_isPullback_specMap {A X Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine A] [AlgebraicGeometry.IsAffine X]
    (i : X ⟶ A) [AlgebraicGeometry.IsClosedImmersion i] (r : ℕ) (h : Y ⟶ X)
    [AlgebraicGeometry.SmoothOfRelativeDimension r h] (y : ↥Y) :
    ∃ (V : Y.Opens) (_ : y ∈ V) (_ : AlgebraicGeometry.IsAffineOpen V) (B' : CommRingCat.{u})
      (σ : Γ(A, ⊤) ⟶ B') (j : (V : Scheme.{u}) ⟶ Spec B'),
      RingHom.IsStandardSmoothOfRelativeDimension r (CommRingCat.Hom.hom σ) ∧
        AlgebraicGeometry.IsClosedImmersion j ∧
        CategoryTheory.IsPullback j (V.ι ≫ h) (Spec.map σ ≫ A.isoSpec.inv) i := by
  obtain ⟨V, hyV, hV, hsm⟩ :=
    SmoothChartRelativeDimension.exists_affineOpen_isStandardSmoothOfRelativeDimension r h y
  have : AlgebraicGeometry.IsAffine (V : Scheme.{u}) := hV
  obtain ⟨B', σ, ψ, hσ, hψ, hpo⟩ :=
    SmoothChartRelativeDimension.exists_lift_isPushout_of_isStandardSmoothOfRelativeDimension
      (Scheme.Hom.appTop i)
      (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine i).2
      (Scheme.Hom.appTop (V.ι ≫ h)) r hsm
  have S1 : CategoryTheory.IsPullback (Spec.map ψ)
      (Spec.map (Scheme.Hom.appTop (V.ι ≫ h))) (Spec.map σ)
      (Spec.map (Scheme.Hom.appTop i)) := hpo.op.map Scheme.Spec
  have L : CategoryTheory.IsPullback (V : Scheme.{u}).isoSpec.hom (V.ι ≫ h)
      (Spec.map (Scheme.Hom.appTop (V.ι ≫ h))) X.isoSpec.hom :=
    CategoryTheory.IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality (V.ι ≫ h)⟩
  have C1 := L.paste_horiz S1
  rw [Scheme.isoSpec_hom_naturality i] at C1
  refine ⟨V, hyV, hV, B', σ, (V : Scheme.{u}).isoSpec.hom ≫ Spec.map ψ, hσ, ?_, ?_⟩
  · have := AlgebraicGeometry.IsClosedImmersion.spec_of_surjective ψ hψ
    infer_instance
  · have t : CategoryTheory.IsPullback (𝟙 (Spec B')) (Spec.map σ ≫ A.isoSpec.inv)
        (Spec.map σ) A.isoSpec.hom :=
      CategoryTheory.IsPullback.of_horiz_isIso ⟨by simp⟩
    have p : ((V : Scheme.{u}).isoSpec.hom ≫ Spec.map ψ) ≫ (Spec.map σ ≫ A.isoSpec.inv)
        = (V.ι ≫ h) ≫ i := by
      rw [← Category.assoc, C1.w]
      simp
    have s : CategoryTheory.IsPullback
        (((V : Scheme.{u}).isoSpec.hom ≫ Spec.map ψ) ≫ 𝟙 (Spec B')) (V.ι ≫ h)
        (Spec.map σ) (i ≫ A.isoSpec.hom) := by
      rw [Category.comp_id]
      exact C1
    exact CategoryTheory.IsPullback.of_right s p t

end PresentedSmoothChart

end FunctorialResolution.EmbeddedResolution

end
