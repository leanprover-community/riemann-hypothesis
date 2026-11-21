import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.LogPair

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)

theorem isEtCoord_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (U : X.Opens) (d : ℕ) (t : Fin d → Γ(X, U)), IsPullback π f' f (spMap φ) → IsAffineOpen U → IsEtCoord f U t → IsAffineOpen (π ⁻¹ᵁ U) ∧ IsEtCoord f' (π ⁻¹ᵁ U) (fun a => (π.app U).hom (t a)) := by
  intro R R' _ _ φ X X' f f' π U d t H hU ht
  refine ⟨GlobalTheory.TopForm.isAffineOpen_preimage_of_isPullback H hU, ?_⟩
  letI := φ.toAlgebra
  letI := MvPolynomial.algebraMvPolynomial (R := R) (S := R') (σ := Fin d)
  have h₁ := (CommRingCat.isPushout_of_isPushout R R' (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R')).flip
  have hx : (MvPolynomial.eval₂Hom (algX f U) t).Etale := ht
  have key : ∀ (W : X'.Opens) (hle : W ≤ π ⁻¹ᵁ U),
      IsPushout (CommRingCat.ofHom (algX f U)) (CommRingCat.ofHom (algebraMap R R'))
        (π.appLE U W hle) (CommRingCat.ofHom (algX f' W)) →
      (MvPolynomial.eval₂Hom (algX f' W) fun a => (π.appLE U W hle).hom (t a)).Etale := by
    intro W hle h₂
    have e₁ : CommRingCat.ofHom (algX f U) = CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin d) R)) ≫
        CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX f U) t) := by
      ext a
      exact (MvPolynomial.eval₂Hom_C _ _ a).symm
    have e₂ : CommRingCat.ofHom (algX f' W) =
        CommRingCat.ofHom (algebraMap R' (MvPolynomial (Fin d) R')) ≫
        CommRingCat.ofHom (MvPolynomial.eval₂Hom (algX f' W) fun a => (π.appLE U W hle).hom (t a)) := by
      ext a
      exact (MvPolynomial.eval₂Hom_C _ _ a).symm
    have hw := h₂.w
    rw [e₁, e₂] at h₂
    have h₃ := h₂.of_left (CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun a => ?_) fun a => ?_)) h₁
    · have := RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
      exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty RingHom.Etale) h₃.flip hx
    · change (π.appLE U W hle).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)) =
        MvPolynomial.eval₂Hom _ _ (MvPolynomial.map φ (MvPolynomial.C a))
      rw [MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      exact congrArg (fun g => (CommRingCat.Hom.hom g) a) hw
    · change (π.appLE U W hle).hom (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X a)) =
        MvPolynomial.eval₂Hom _ _ (MvPolynomial.map φ (MvPolynomial.X a))
      rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
  have h₄ := key _ inf_le_left (isPushout_sections f f' π H U hU)
  have tr : ∀ (W : X'.Opens) (hle : W ≤ π ⁻¹ᵁ U), W = π ⁻¹ᵁ U →
      (MvPolynomial.eval₂Hom (algX f' W) fun a => (π.appLE U W hle).hom (t a)).Etale →
      IsEtCoord f' (π ⁻¹ᵁ U) (fun a => (π.app U).hom (t a)) := by
    rintro W hle rfl h
    rw [Scheme.Hom.app_eq_appLE]
    exact h
  exact tr _ _ (inf_top_eq _) h₄

end GlobalTheory.LogPair
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCoordinatesOnOpen_baseChange_preimage : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (U : X.Opens) (d : ℕ) (t : Fin d → Γ(X, U)), IsPullback π f' f (spMap φ) → IsAffineOpen U → IsEtCoord f U t → IsAffineOpen (π ⁻¹ᵁ U) ∧ IsEtCoord f' (π ⁻¹ᵁ U) (fun a => (π.app U).hom (t a)) := by
  first | exact @GlobalTheory.LogPair.isEtCoord_baseChange | exact GlobalTheory.LogPair.isEtCoord_baseChange | (intros; apply GlobalTheory.LogPair.isEtCoord_baseChange <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem sncChart_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (C : SncChart f d L σ), IsPullback π f' f (spMap φ) → ∃ C' : SncChart f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π), C'.U = π ⁻¹ᵁ C.U := by
  intro R R' _ _ φ X X' f f' π d s L σ C hP
  obtain ⟨hA, hE⟩ := GlobalTheory.T.isEtaleCoordinatesOnOpen_baseChange_preimage R R' φ X X' f f' π C.U d C.t hP C.affine C.etale
  refine ⟨{
    U := π ⁻¹ᵁ C.U
    affine := hA
    t := fun a => (π.app C.U).hom (C.t a)
    etale := hE
    c := fun i => fun _ => C.c i
    le := fun i => (π.preimage_mono (C.le i)).trans (Cartier.pull_U (L i) π fun _ => C.c i).ge
    e := C.e
    inj := C.inj
    u := fun i => Units.map (π.app C.U).hom (C.u i)
    eq := fun i => ?_ }, rfl⟩
  show resG X' _ (resG X' _ ((π.app _).hom ((σ i).f (C.c i)))) = _
  rw [Cartier.resG_resG, ← Cartier.app_resG π (C.le i), C.eq i, map_mul]
  rcases h : C.e i with _ | a
  · simp
  · simp
end LogPair
end GlobalTheory
end
