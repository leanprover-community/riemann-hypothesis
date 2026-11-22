module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.SegreIdealIsHomogeneous

@[expose] public section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

noncomputable section

theorem eval₂_mul_const_of_isHomogeneous {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (g : R →+* S) (y : σ → S) (t : S) {f : MvPolynomial σ R} {n : ℕ} (hf : f.IsHomogeneous n) :
    eval₂ g (fun i => y i * t) f = eval₂ g y f * t ^ n := by
  rw [eval₂_eq, eval₂_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    have h := hf (mem_support_iff.1 hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  rw [Finset.prod_congr rfl (fun i _ => mul_pow (y i) t (d i)), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem eval₂_mk_one {τ : Type} (I : Ideal (MvPolynomial τ ℂ)) (M : Submonoid (MvPolynomial τ ℂ ⧸ I))
    {σ : Type} (Y : σ → MvPolynomial τ ℂ) (f : MvPolynomial σ ℂ) :
    eval₂ (algebraMap ℂ (Localization M)) (fun q => Localization.mk (Ideal.Quotient.mk I (Y q)) 1) f =
      Localization.mk (Ideal.Quotient.mk I (aeval Y f)) 1 := by
  simp only [Localization.mk_one_eq_algebraMap]
  have h := MvPolynomial.eval₂_comp_left
    ((algebraMap (MvPolynomial τ ℂ ⧸ I) (Localization M)).comp (Ideal.Quotient.mk I))
    (algebraMap ℂ (MvPolynomial τ ℂ)) Y f
  rw [RingHom.comp_apply] at h
  rw [aeval_def, h]
  congr 1

variable [Nonempty K]

section Proj

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

theorem toSpecZero_appLE_basicOpen {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv ≫ (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 f) le_top =
      CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f)) ≫ Proj.awayToSection 𝒜 f := by
  have hg : Proj.basicOpenToSpec 𝒜 f ≫ Proj.awayι 𝒜 f f_deg hm = (Proj.basicOpen 𝒜 f).ι := by
    show (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).hom ≫
      ((Proj.basicOpenIsoSpec 𝒜 f f_deg hm).inv ≫ (Proj.basicOpen 𝒜 f).ι) = _
    rw [Iso.hom_inv_id_assoc]
  have hB : (Proj.basicOpen 𝒜 f).ι ≫ Proj.toSpecZero 𝒜 = Proj.basicOpenToSpec 𝒜 f ≫
      Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f))) := by
    rw [← Proj.awayι_toSpecZero 𝒜 f f_deg hm, ← Category.assoc, hg]
  have h1 : (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 f) le_top ≫
      (Proj.basicOpen 𝒜 f).topIso.inv =
      (Proj.toSpecZero 𝒜).appTop ≫ (Proj.basicOpen 𝒜 f).ι.appTop := by
    rw [Scheme.Opens.topIso_inv]
    erw [Scheme.Hom.appLE_map]
  have h2 : (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 f) le_top ≫
      (Proj.basicOpen 𝒜 f).topIso.inv =
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).hom ≫
        CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f)) ≫ Proj.awayToSection 𝒜 f) ≫
        (Proj.basicOpen 𝒜 f).topIso.inv := by
    rw [h1, ← Scheme.Hom.comp_appTop, hB, Scheme.Hom.comp_appTop]
    have hA : Scheme.Hom.appTop (Proj.basicOpenToSpec 𝒜 f) =
        (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).hom ≫
          Proj.awayToSection 𝒜 f ≫ (Proj.basicOpen 𝒜 f).topIso.inv :=
      Proj.basicOpenToSpec_app_top 𝒜 f
    rw [hA]
    rw [← Category.assoc, Scheme.ΓSpecIso_naturality]
    simp only [Category.assoc]
  have h3 := (cancel_mono (Proj.basicOpen 𝒜 f).topIso.inv).1 h2
  rw [h3, Iso.inv_hom_id_assoc]

end Proj

end

end ReciprocityTheory.AnForm.R
