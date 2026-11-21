import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDegreeClassesDieOnEtaleCover
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianIff
import BuildAid.ForwardExisting

section
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etale_surjective_section_of_SH : ∀ (A : Type) [CommRing A], SH A → ∀ (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of A)), Etale f → Surjective f →
      ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _ := by
  intro A _ hA Y f hf hs
  obtain ⟨hH, hsep⟩ := hA
  haveI := hH
  obtain ⟨y, hy⟩ := f.surjective (IsLocalRing.closedPoint A)
  let 𝒰 := Y.affineOpenCover
  let i := 𝒰.idx y
  obtain ⟨z, hz⟩ := 𝒰.covers y
  let g : Spec (𝒰.X i) ⟶ Spec (CommRingCat.of A) := 𝒰.f i ≫ f
  haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
  haveI : Etale g := inferInstance
  let φ : CommRingCat.of A ⟶ 𝒰.X i := Spec.preimage g
  have hφ : Spec.map φ = g := Spec.map_preimage g
  have hEt : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale), hφ]; infer_instance
  letI : Algebra A (𝒰.X i) := φ.hom.toAlgebra
  haveI : Algebra.Etale A (𝒰.X i) := hEt
  have hq : z.asIdeal.comap (algebraMap A (𝒰.X i)) = IsLocalRing.maximalIdeal A := by
    have h1 : (Spec.map φ).base z = IsLocalRing.closedPoint A := by
      rw [hφ]; show f.base ((𝒰.f i).base z) = _; rw [hz, hy]
    have h2 := congrArg PrimeSpectrum.asIdeal h1
    exact h2
  haveI : z.asIdeal.IsPrime := PrimeSpectrum.isPrime z
  obtain ⟨s, -⟩ := (GlobalTheory.StrictHensel.strictlyHenselian_iff A).2 ⟨hH, hsep⟩ (𝒰.X i) z.asIdeal hq
  refine ⟨Spec.map (CommRingCat.ofHom s.toRingHom) ≫ 𝒰.f i, ?_⟩
  rw [Category.assoc]
  change Spec.map (CommRingCat.ofHom s.toRingHom) ≫ g = _
  rw [← hφ, ← Spec.map_comp]
  have : φ ≫ CommRingCat.ofHom s.toRingHom = 𝟙 _ := by
    ext a
    exact s.commutes a
  exact (congrArg Spec.map this).trans (Spec.map_id _)

end GlobalTheory.EtC
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_of_etale_surjective_of_SH : ∀ (A : Type) [CommRing A], SH A → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of A)), Etale f → Surjective f → ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _ := by
  atlas_forward_decl GlobalTheory.EtC.etale_surjective_section_of_SH
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem heightFunctionalStatement_of_pairingProperties (hA5 : A5)
    (hsect : ∀ (A : Type) [CommRing A], SH A → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of A)),
      Etale f → Surjective f → ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _) : B2 := by
  intro R _ A _ hA F n hn
  have key : ∀ x : H R (sp A) F n, x = 0 := by
    intro x
    obtain ⟨Y, f, hf, hs, hx⟩ := hA5 R (Spec (CommRingCat.of A)) F n hn x
    obtain ⟨s, hsf⟩ := hsect A hA Y f hf hs
    calc x = pull R (𝟙 (sp A)) F n x := (pull_id R _ F n x).symm
      _ = pull R (sch.map (s ≫ f)) F n x := by rw [hsf, CategoryTheory.Functor.map_id]
      _ = pull R (sch.map s) F n (pull R (sch.map f) F n x) := by
          rw [CategoryTheory.Functor.map_comp, pull_comp]
      _ = 0 := by rw [hx, map_zero]
  exact ⟨fun x y => by rw [key x, key y]⟩

theorem b2 : B2 := heightFunctionalStatement_of_pairingProperties GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover GlobalTheory.T.exists_section_of_etale_surjective_of_SH

end GlobalTheory.EtC
end
