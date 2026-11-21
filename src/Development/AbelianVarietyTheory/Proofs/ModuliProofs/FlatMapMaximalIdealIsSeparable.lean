import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec

section
open CategoryTheory IsLocalRing

namespace GlobalTheory.LocalIndEtaleUnramified

theorem exists_local_of_algHom {A S B : Type} [CommRing A] [IsLocalRing A] [CommRing S]
    [IsLocalRing S] [Algebra A S] [IsLocalHom (algebraMap A S)] [CommRing B] [Algebra A B]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] (g : B →ₐ[A] S) (b : B) :
    ∃ (L : Type) (_ : CommRing L) (_ : IsLocalRing L) (_ : Algebra A L)
      (_ : IsLocalHom (algebraMap A L)) (_ : Algebra.FormallyUnramified A L)
      (_ : Algebra.EssFiniteType A L) (φ : L →ₐ[A] S) (_ : IsLocalHom φ) (x : L),
      φ x = g b := by
  let P : Ideal B := (maximalIdeal S).comap (g : B →+* S)
  haveI hP : P.IsPrime := Ideal.comap_isPrime _ _
  have hu : ∀ y : P.primeCompl, IsUnit (g y) := by
    intro y
    by_contra h
    exact y.2 (show (g : B →+* S) y ∈ maximalIdeal S from h)
  let φ : Localization.AtPrime P →ₐ[A] S := IsLocalization.liftAlgHom (M := P.primeCompl) hu
  have hφ : ∀ y : B, φ (algebraMap B (Localization.AtPrime P) y) = g y := fun y =>
    IsLocalization.lift_eq (M := P.primeCompl) (g := (g : B →+* S)) hu y
  have hloc : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl a
    refine (IsLocalization.AtPrime.isUnit_mk'_iff _ P y s).2 ?_
    have h1 : φ (IsLocalization.mk' (Localization.AtPrime P) y s) * g s = g y := by
      rw [← hφ, ← map_mul, IsLocalization.mk'_spec, hφ]
    have h2 : IsUnit (g y) := h1 ▸ ha.mul (hu s)
    intro hy
    exact (show (g : B →+* S) y ∈ maximalIdeal S from hy) h2
  have hA : IsLocalHom (algebraMap A (Localization.AtPrime P)) := by
    refine ⟨fun a ha => ?_⟩
    have := ha.map φ
    rw [AlgHom.commutes] at this
    exact IsLocalHom.map_nonunit a this
  haveI : Algebra.FormallyUnramified B (Localization.AtPrime P) :=
    Algebra.FormallyUnramified.of_isLocalization P.primeCompl
  haveI : Algebra.EssFiniteType B (Localization.AtPrime P) :=
    Algebra.EssFiniteType.of_isLocalization _ P.primeCompl
  exact ⟨Localization.AtPrime P, inferInstance, inferInstance, inferInstance, hA,
    Algebra.FormallyUnramified.comp A B _, Algebra.EssFiniteType.comp A B _, φ, hloc,
    algebraMap B _ b, hφ b⟩

theorem exists_local_unramified_of_isIndEtale {A S : Type} [CommRing A] [IsLocalRing A]
    [CommRing S] [IsLocalRing S] [Algebra A S] [IsLocalHom (algebraMap A S)]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) (s : S) :
    ∃ (L : Type) (_ : CommRing L) (_ : IsLocalRing L) (_ : Algebra A L)
      (_ : IsLocalHom (algebraMap A L)) (_ : Algebra.FormallyUnramified A L)
      (_ : Algebra.EssFiniteType A L) (φ : L →ₐ[A] S) (_ : IsLocalHom φ) (x : L),
      φ x = s := by
  obtain ⟨J, _, _, D, t, c, hc, H⟩ := h
  obtain ⟨j, b, hb⟩ := Limits.Concrete.isColimit_exists_rep D hc s
  obtain ⟨hE, hcomp⟩ := H j
  let f : A →+* D.obj j := (t.app j).hom
  let g₀ : D.obj j →+* S := (c.app j).hom
  letI : Algebra A (D.obj j) := f.toAlgebra
  haveI : Algebra.Etale A (D.obj j) := hE
  have hg : ∀ a : A, g₀ (f a) = algebraMap A S a := fun a =>
    congrArg (fun k : CommRingCat.of A ⟶ CommRingCat.of S => k.hom a) hcomp
  let g : D.obj j →ₐ[A] S := { g₀ with commutes' := hg }
  have hb' : g b = s := hb
  rw [← hb']
  exact exists_local_of_algHom g b

end GlobalTheory.LocalIndEtaleUnramified
end

section
open CategoryTheory Limits IsLocalRing

namespace GlobalTheory.IndEtaleLocal

theorem exists_etale_factor {A S Z : Type} [CommRing A] [CommRing S] [Algebra A S]
    [CommRing Z] [Algebra A Z] [Algebra.FinitePresentation A Z]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) (g : Z →ₐ[A] S) :
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra A W) (_ : Algebra.Etale A W)
      (u : Z →ₐ[A] W) (v : W →ₐ[A] S), v.comp u = g := by
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := h
  obtain ⟨i, g', h1, h2⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    (CommRingCat.of A) D t (S := CommRingCat.of Z) (CommRingCat.ofHom (algebraMap A Z))
    (Cocone.mk _ s) hs
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)
    (CommRingCat.ofHom g.toRingHom) (fun i => by
      rw [(hst i).2]
      ext a
      simp)
  let : Algebra A (D.obj i) := (t.app i).hom.toAlgebra
  have het : Algebra.Etale A (D.obj i) := (hst i).1
  refine ⟨D.obj i, inferInstance, inferInstance, het,
    { toRingHom := g'.hom, commutes' := fun a => congr($(h1).hom a) },
    { toRingHom := (s.app i).hom, commutes' := fun a => congr($((hst i).2).hom a) }, ?_⟩
  ext z
  exact (congr($(h2).hom z)).symm

theorem flat_of_isIndEtale {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) : Module.Flat A S := by
  refine Module.Flat.of_forall_isTrivialRelation fun {l f x} hfx => ?_
  let p : MvPolynomial (Fin l) A := ∑ i, f i • MvPolynomial.X i
  let I : Ideal (MvPolynomial (Fin l) A) := Ideal.span {p}
  have : Algebra.FinitePresentation A (MvPolynomial (Fin l) A ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton p)
  let g : (MvPolynomial (Fin l) A ⧸ I) →ₐ[A] S :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval x) (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      have : MvPolynomial.aeval x p = 0 := by
        simp only [p, map_sum, map_smul, MvPolynomial.aeval_X, hfx]
      rw [map_mul, this, mul_zero])
  obtain ⟨W, _, _, _, u, v, huv⟩ := exists_etale_factor h g
  let w : Fin l → W := fun i => u (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))
  have hw : ∀ i, v (w i) = x i := fun i => by
    have := DFunLike.congr_fun huv (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))
    exact this.trans (MvPolynomial.aeval_X x i)
  have hrel : ∑ i, f i • w i = 0 := by
    have h0 : Ideal.Quotient.mkₐ A I p = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self p)
    have : u (Ideal.Quotient.mkₐ A I p) = 0 := by rw [h0, map_zero]
    simpa only [p, map_sum, map_smul] using this
  obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := A) (M := W) hrel
  refine ⟨k, a, fun j => v (y j), fun i => ?_, ha⟩
  rw [← hw, hy, map_sum]
  simp only [map_smul]

theorem exists_local_unramified {A S : Type} [CommRing A] [IsLocalRing A] [CommRing S]
    [IsLocalRing S] [Algebra A S] [IsLocalHom (algebraMap A S)]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) (s : S) :
    ∃ (L : Type) (_ : CommRing L) (_ : IsLocalRing L) (_ : Algebra A L)
      (_ : IsLocalHom (algebraMap A L)) (_ : Algebra.FormallyUnramified A L)
      (_ : Algebra.EssFiniteType A L) (φ : L →ₐ[A] S) (_ : IsLocalHom φ) (x : L), φ x = s := by
  first
  | exact @_root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale
  | exact _root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale
  | (apply _root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalIndEtaleUnramified.exists_local_unramified_of_isIndEtale ..)

theorem flat_map_maximalIdeal_isSeparable (A S : Type) [CommRing A] [IsLocalRing A] [CommRing S]
    [IsLocalRing S] [Algebra A S] [IsLocalHom (algebraMap A S)]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) :
    Module.Flat A S ∧ (maximalIdeal A).map (algebraMap A S) = maximalIdeal S ∧
      Algebra.IsSeparable (ResidueField A) (ResidueField S) := by
  refine ⟨flat_of_isIndEtale h, le_antisymm ?_ fun s hs => ?_, ⟨fun r => ?_⟩⟩
  · exact ((local_hom_TFAE (algebraMap A S)).out 0 2 rfl rfl).mp inferInstance
  · obtain ⟨L, _, _, _, _, _, _, φ, hφ, x, rfl⟩ := exists_local_unramified h s
    have hx : x ∈ maximalIdeal L := fun hx => hs (hx.map φ)
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := A)] at hx
    have := Ideal.mem_map_of_mem (φ : L →+* S) hx
    rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this
  · obtain ⟨s, rfl⟩ := residue_surjective r
    obtain ⟨L, _, _, _, _, _, _, φ, hφ, x, rfl⟩ := exists_local_unramified h s
    have : IsLocalHom (φ : L →+* S) := ⟨hφ.1⟩
    let ψ : ResidueField L →ₐ[ResidueField A] ResidueField S :=
      { toRingHom := ResidueField.map (φ : L →+* S)
        commutes' := fun a => by
          obtain ⟨a, rfl⟩ := residue_surjective a
          simp [ResidueField.algebraMap_residue] }
    have := (Algebra.IsSeparable.isSeparable (ResidueField A) (residue L x)).map ψ ψ.injective
    exact this

end GlobalTheory.IndEtaleLocal
end
