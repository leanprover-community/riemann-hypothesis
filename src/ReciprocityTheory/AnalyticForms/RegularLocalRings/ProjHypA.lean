module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FromSpecResidueFieldAppTopIso
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjDehomA
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems

@[expose] public section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isUnit_mapId_mk_iff {A : Type} [CommRing A] [Algebra ℂ A]
    (𝒜 : ℕ → Submodule ℂ A) [GradedAlgebra 𝒜] (f : A) (x : ProjectiveSpectrum 𝒜)
    (H : Submonoid.powers f ≤ x.asHomogeneousIdeal.toIdeal.primeCompl)
    (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (Submonoid.powers f)) :
    IsUnit (HomogeneousLocalization.mapId 𝒜 H (HomogeneousLocalization.mk z)) ↔
      z.num.1 ∉ x.asHomogeneousIdeal := by
  have hv : (HomogeneousLocalization.mapId 𝒜 H (HomogeneousLocalization.mk z)).val =
      IsLocalization.mk' (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) (z.num : A)
        (⟨z.den, H z.den_mem⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl) := by
    rw [← Localization.mk_eq_mk']; rfl
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val, hv, IsLocalization.AtPrime.isUnit_mk'_iff]
  rfl

theorem evaluation_awayToSection_eq_zero_iff {A : Type} [CommRing A] [Algebra ℂ A]
    (𝒜 : ℕ → Submodule ℂ A) [GradedAlgebra 𝒜] (f : A) (x : Proj 𝒜)
    (hx : x ∈ Proj.basicOpen 𝒜 f)
    (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (Submonoid.powers f)) :
    (Proj 𝒜).evaluation (Proj.basicOpen 𝒜 f) x hx
        (Proj.awayToSection 𝒜 f (HomogeneousLocalization.mk z)) = 0 ↔
      z.num.1 ∈ ProjectiveSpectrum.asHomogeneousIdeal (𝒜 := 𝒜) x := by
  have e1 : (Proj 𝒜).evaluation (Proj.basicOpen 𝒜 f) x hx
        (Proj.awayToSection 𝒜 f (HomogeneousLocalization.mk z)) = 0 ↔
      ¬ IsUnit ((Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 f) x hx
        (Proj.awayToSection 𝒜 f (HomogeneousLocalization.mk z))) :=
    (IsLocalRing.residue_eq_zero_iff _).trans (by rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact Iff.rfl)
  refine e1.trans ?_
  have h := congrArg (fun φ => φ.hom (HomogeneousLocalization.mk z))
    (ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 f x hx)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  have h2 := (Iff.of_eq (congrArg IsUnit h)).trans
    (isUnit_map_iff (Proj.stalkIso' 𝒜 x).symm _)
  refine (Iff.not h2).trans ?_
  let x' : ProjectiveSpectrum 𝒜 := x
  have H : Submonoid.powers f ≤ x'.asHomogeneousIdeal.toIdeal.primeCompl :=
    Submonoid.powers_le.mpr (by exact hx)
  exact (not_congr (isUnit_mapId_mk_iff 𝒜 f x' H z)).trans not_not

end

end ReciprocityTheory.AnForm.R
