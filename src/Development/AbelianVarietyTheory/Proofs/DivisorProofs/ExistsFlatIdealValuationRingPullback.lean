module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace GlobalTheory.FlatHilbAff


attribute [local instance] Algebra.TensorProduct.rightAlgebra in
theorem exists_flat_ideal : ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) [IsAffine X] [IsAffine X'] (p : X ⟶ Spec (CommRingCat.of V)) (p' : X' ⟶ Spec (CommRingCat.of K)) (b : X' ⟶ X), IsPullback b p' p (Spec.map (CommRingCat.ofHom (algebraMap V K))) → ∀ I : Ideal Γ(X', ⊤), ∃ J : Ideal Γ(X, ⊤), ((Ideal.Quotient.mk J).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).Flat ∧ Ideal.map b.appTop.hom J = I := by
  intro V K _ _ _ _ _ _ X X' _ _ p p' b h I
  set φ : V →+* Γ(X, ⊤) := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom with hφ
  letI : Algebra V Γ(X, ⊤) := φ.toAlgebra
  have H0 := isPushout_appTop_of_isPullback h
  have H : IsPushout (CommRingCat.ofHom (algebraMap V K)) (CommRingCat.ofHom (algebraMap V Γ(X, ⊤)))
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p'.appTop) b.appTop := by
    refine H0.flip.of_iso (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · exact Scheme.ΓSpecIso_naturality _
    · ext x; simp [φ, RingHom.algebraMap_toAlgebra]
    · simp
    · simp
  let e : K ⊗[V] Γ(X, ⊤) ≃+* Γ(X', ⊤) :=
    ((CommRingCat.isPushout_tensorProduct V K Γ(X, ⊤)).isoPushout ≪≫
      H.isoPushout.symm).commRingCatIsoToRingEquiv
  have he : ∀ x : Γ(X, ⊤), e (Algebra.TensorProduct.includeRight x) = b.appTop.hom x := by
    intro x
    have h1 := congr($((CommRingCat.isPushout_tensorProduct V K Γ(X, ⊤)).inr_isoPushout_hom).hom x)
    have h4 := congr($(H.inr_isoPushout_inv).hom x)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1 h4
    have : e (Algebra.TensorProduct.includeRight x) = H.isoPushout.inv.hom
        ((CommRingCat.isPushout_tensorProduct V K Γ(X, ⊤)).isoPushout.hom.hom
          (Algebra.TensorProduct.includeRight x)) := rfl
    rw [this]
    exact (congrArg H.isoPushout.inv.hom h1).trans h4
  obtain ⟨J, ⟨hJf, hJ⟩, -⟩ := GlobalTheory.ValuativeQuotient.main V K Γ(X, ⊤) (I.comap e.toRingHom)
  refine ⟨J, ?_, ?_⟩
  · have : (algebraMap V (Γ(X, ⊤) ⧸ J)) =
        (Ideal.Quotient.mk J).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom) :=
      rfl
    rw [← this, RingHom.flat_algebraMap_iff]
    exact hJf
  · have hb : b.appTop.hom = e.toRingHom.comp
        (Algebra.TensorProduct.includeRight : Γ(X, ⊤) →ₐ[V] K ⊗[V] Γ(X, ⊤)).toRingHom := by
      ext x; exact (he x).symm
    rw [hb, ← Ideal.map_map]
    change Ideal.map e.toRingHom (J.map (Algebra.TensorProduct.includeRight : Γ(X, ⊤) →ₐ[V] K ⊗[V] Γ(X, ⊤))) = I
    rw [hJ]
    exact Ideal.map_comap_of_surjective _ e.surjective I

end GlobalTheory.FlatHilbAff
